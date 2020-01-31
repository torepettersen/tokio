use crate::loom::sync::Mutex;
use crate::loom::sync::atomic::AtomicU8;
use crate::util::linked_list::{self, LinkedList};

use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::Ordering::SeqCst;
use std::task::{Context, Poll, Waker};

/// Notify a single waiting task.
#[derive(Debug)]
pub struct Notify {
    state: AtomicU8,
    waiters: Mutex<LinkedList<Waiter>>,
}

#[derive(Debug)]
struct Waiter {
    /// Waiting task's waker
    waker: Option<Waker>,

    /// `true` if the notification has been assigned to this waiter.
    notified: bool,
}

#[derive(Debug)]
struct RecvFuture<'a> {
    /// The `Notify` being received on.
    notify: &'a Notify,

    /// The current state of the receiving process.
    state: RecvState,

    /// Entry in the waiter `LinkedList`.
    waiter: linked_list::Entry<Waiter>,
}

#[derive(Debug)]
enum RecvState {
    Init,
    Waiting,
    Done,
}

/// Initial "idle" state
const EMPTY: u8 = 0;

/// One or more threads are currently waiting to be notified.
const WAITING: u8 = 1;

/// Pending notification
const NOTIFIED: u8 = 2;

impl Notify {
    /// TODO
    pub fn new() -> Notify {
        Notify {
            state: AtomicU8::new(0),
            waiters: Mutex::new(LinkedList::new()),
        }
    }

    /// TODO
    pub async fn recv(&self) {
        RecvFuture {
            notify: self,
            state: RecvState::Init,
            waiter: linked_list::Entry::new(Waiter {
                waker: None,
                notified: false,
            }),
        }.await
    }

    /// TODO
    pub fn notify_one(&self) {
        // Load the current state
        let mut curr = self.state.load(SeqCst);

        // If the state is `EMPTY`, transition to `NOTIFIED` and return.
        loop {
            match curr {
                EMPTY | NOTIFIED => {
                    // The compare-exchange from `NOTIFIED` -> `NOTIFIED` is
                    // intended a happens-before synchronization must happen
                    // between this atomic operation and a task calling
                    // `recv()`.
                    let res = self.state.compare_exchange(curr, NOTIFIED, SeqCst, SeqCst);

                    match res {
                        // No waiters, no further work to do
                        Ok(_) => return,
                        Err(actual) => {
                            curr = actual;
                        }
                    }
                }
                _ => break,
            }
        }

        // There are waiters, the lock must be acquired to notify.
        let mut waiters = self.waiters.lock().unwrap();

        // The state must be reloaded while the lock is held. The state may only
        // transition out of WAITING while the lock is held.
        curr = self.state.load(SeqCst);

        if let Some(waker) = notify_locked(&mut waiters, &self.state, curr) {
            drop(waiters);
            waker.wake();
        }
    }
}

fn notify_locked(
    waiters: &mut LinkedList<Waiter>,
    state: &AtomicU8,
    mut curr: u8) -> Option<Waker>
{
    loop {
        match curr {
            EMPTY | NOTIFIED => {
                let res = state.compare_exchange(curr, NOTIFIED, SeqCst, SeqCst);

                match res {
                    Ok(_) => return None,
                    Err(actual) => {
                        curr = actual;
                    }
                }
            }
            WAITING => {
                // At this point, it is guaranteed that the state will not
                // concurrently change as holding the lock is required to
                // transition **out** of `WAITING`.
                //
                // Get a pending waiter
                let mut waiter = waiters.pop_back().unwrap();

                assert!(!waiter.notified);

                waiter.notified = true;
                let waker = waiter.waker.take();

                if waiters.is_empty() {
                    // As this the **final** waiter in the list, the state
                    // must be transitioned to `EMPTY`. As transitioning
                    // **from** `WAITING` requires the lock to be held, a
                    // `store` is sufficient.
                    state.store(EMPTY, SeqCst);
                }

                return waker;
            }
            _ => unreachable!(),
        }
    }
}

// ===== impl RecvFuture =====

impl RecvFuture<'_> {
    fn project(self: Pin<&mut Self>)
        -> (&Notify, &mut RecvState, Pin<&mut linked_list::Entry<Waiter>>)
    {
        unsafe {
            // Safety: both `notify` and `state` are `Unpin`.

            is_unpin::<&Notify>();
            is_unpin::<AtomicU8>();

            let me = self.get_unchecked_mut();
            (&me.notify, &mut me.state, Pin::new_unchecked(&mut me.waiter))
        }
    }
}

impl Future for RecvFuture<'_> {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        use RecvState::*;

        let (notify, state, mut waiter) = self.project();

        'outer:
        loop {
            match *state {
                Init => {
                    // Optimistically try acquiring a pending notification
                    let res = notify
                        .state
                        .compare_exchange(NOTIFIED, EMPTY, SeqCst, SeqCst);

                    let mut curr = match res {
                        Ok(_) => {
                            // Acquired the notification
                            *state = Done;
                            continue 'outer;
                        }
                        Err(actual) => actual,
                    };

                    // Acquire the lock and attempt to transition to the waiting
                    // state.
                    let mut waiters = notify.waiters.lock().unwrap();

                    // Transition the state to WAITING.
                    loop {
                        match curr {
                            EMPTY => {
                                // Transition to WAITING
                                let res = notify.state.compare_exchange(EMPTY, WAITING, SeqCst, SeqCst);

                                if let Err(actual) = res {
                                    curr = actual;
                                    continue;
                                }
                            }
                            WAITING => {}
                            NOTIFIED => {
                                // Try consuming the notification
                                let res = notify.state.compare_exchange(NOTIFIED, EMPTY, SeqCst, SeqCst);

                                match res {
                                    Ok(_) => {
                                        // Acquired the notification
                                        *state = Done;
                                        continue 'outer;
                                    }
                                    Err(actual) => {
                                        curr = actual;
                                        continue;
                                    }
                                }
                            }
                            _ => unreachable!(),
                        }

                        // The state has been transitioned to waiting
                        break;
                    }

                    // Safety: called while locked.
                    unsafe {
                        (*waiter.as_mut().get()).waker = Some(cx.waker().clone());

                        // Insert the waiter into the linked list
                        waiters.push_front(waiter.as_mut());
                    }

                    *state = Waiting;
                }
                Waiting => {
                    let mut waiters = notify.waiters.lock().unwrap();

                    {
                        // Safety: called while locked
                        let w = unsafe { &mut *waiter.as_mut().get() };

                        if w.notified {
                            w.waker = None;
                            w.notified = false;

                            // Remove the entry from the linked list. The entry
                            // may only be in the linked list while the state is
                            // `Waiting`.
                            //
                            // Safety: called while the lock is held
                            unsafe { waiters.remove(waiter.as_mut()); }

                            *state = Done;
                        } else {
                            if !w.waker.as_ref().unwrap().will_wake(cx.waker()) {
                                w.waker = Some(cx.waker().clone());
                            }

                            return Poll::Pending;
                        }
                    }
                }
                Done => return Poll::Ready(()),
            }
        }
    }
}

impl Drop for RecvFuture<'_> {
    fn drop(&mut self) {
        use RecvState::*;

        // Safety: The type only transitions to a "Waiting" state when pinned.
        let (notify, state, mut waiter) = unsafe { Pin::new_unchecked(self).project() };

        // This is where we ensure safety. The `RecvFuture` is being dropped,
        // which means we must ensure that the waiter entry is no longer stored
        // in the linked list.
        if let Waiting = *state {
            let mut waiters = notify.waiters.lock().unwrap();

            // remove the entry from the list
            //
            // safety: the waiter is only added to `waiters` by virtue of it
            // being the only `LinkedList` available to the type.
            unsafe { waiters.remove(waiter.as_mut()) };

            if waiters.is_empty() {
                notify.state.store(EMPTY, SeqCst);
            }

            // See if the node was notified but not received. In this case, the
            // notification must be sent to another waiter.
            //
            // Safety: with the entry removed from the linked list, there can be
            // no concurrent access to the entry
            let notified = unsafe { (*waiter.as_mut().get()).notified };

            if notified {
                if let Some(waker) = notify_locked(&mut waiters, &notify.state, WAITING) {
                    drop(waiters);
                    waker.wake();
                }
            }
        }
    }
}

fn is_unpin<T: Unpin>() {}
