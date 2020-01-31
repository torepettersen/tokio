//! An intrusive double linked list of data
//!
//! The data structure supports tracking pinned nodes. Most of the data
//! structure's APIs are `unsafe` as they require the caller to ensure the
//! specified node is actually

use core::cell::UnsafeCell;
use core::marker::PhantomPinned;
use core::pin::Pin;
use core::ptr::{NonNull};

/// An intrusive linked list of nodes, where each node carries associated data
/// of type `T`.
#[derive(Debug)]
pub(crate) struct LinkedList<T> {
    head: Option<NonNull<Entry<T>>>,
    tail: Option<NonNull<Entry<T>>>,
}

unsafe impl<T: Send> Send for LinkedList<T> {}
unsafe impl<T: Sync> Sync for LinkedList<T> {}

/// A node which carries data of type `T` and is stored in an intrusive list.
#[derive(Debug)]
pub(crate) struct Entry<T> {
    /// The previous node in the list. null if there is no previous node.
    prev: Option<NonNull<Entry<T>>>,

    /// The next node in the list. null if there is no previous node.
    next: Option<NonNull<Entry<T>>>,

    /// The data which is associated to this list item
    data: UnsafeCell<T>,

    /// Prevents `Entry`s from being `Unpin`. They may never be moved, since
    /// the list semantics require addresses to be stable.
    _pin: PhantomPinned,
}

unsafe impl<T: Send> Send for Entry<T> {}
unsafe impl<T: Sync> Sync for Entry<T> {}

impl<T> LinkedList<T> {
    /// Creates an empty linked list
    pub(crate) fn new() -> Self {
        LinkedList {
            head: None,
            tail: None,
        }
    }

    /// Adds an item to the back of the linked list.
    ///
    /// # Safety
    ///
    /// The function is only safe as long as valid pointers are stored inside
    /// the linked list.
    pub(crate) unsafe fn push_front(&mut self, entry: Pin<&mut Entry<T>>) {
        let mut entry: NonNull<Entry<T>> = entry.get_unchecked_mut().into();

        entry.as_mut().next = self.head;
        entry.as_mut().prev = None;

        if let Some(head) = &mut self.head {
            head.as_mut().prev = Some(entry);
        }

        self.head = Some(entry);

        if self.tail.is_none() {
            self.tail = Some(entry);
        }
    }

    /// Removes the first element and returns it, or `None` if the list is empty.
    ///
    /// The function is safe as the lifetime of the entry is bound to `&mut
    /// self`.
    pub(crate) fn pop_back(&mut self) -> Option<Pin<&mut T>> {
        unsafe {
            let mut last = match self.tail {
                Some(tail) => {
                    self.tail = tail.as_ref().prev;
                    tail
                }
                None => return None,
            };

            if let Some(mut prev) = last.as_mut().prev {
                prev.as_mut().next = None;
            } else {
                self.head = None
            }

            last.as_mut().prev = None;
            last.as_mut().next = None;

            let val = &mut *last.as_mut().data.get();

            Some(Pin::new_unchecked(val))
        }
    }

    /// Returns whether the linked list doesn not contain any node
    pub(crate) fn is_empty(&self) -> bool {
        if !self.head.is_none() {
            return false;
        }

        assert!(self.tail.is_none());
        true
    }

    /// Removes the given item from the linked list.
    ///
    /// # Safety
    ///
    /// The caller **must** ensure that `entry` is currently contained by
    /// `self`.
    pub(crate) unsafe fn remove(&mut self, entry: Pin<&mut Entry<T>>) -> bool {
        let mut entry = NonNull::from(entry.get_unchecked_mut());

        if let Some(mut prev) = entry.as_mut().prev {
            debug_assert_eq!(prev.as_ref().next, Some(entry));
            prev.as_mut().next = entry.as_ref().next;
        } else {
            if self.head != Some(entry) {
                return false;
            }

            self.head = entry.as_ref().next;
        }

        if let Some(mut next) = entry.as_mut().next {
            debug_assert_eq!(next.as_ref().prev, Some(entry));
            next.as_mut().prev = entry.as_ref().prev;
        } else {
            // This might be the last item in the list
            if self.tail != Some(entry) {
                return false;
            }

            self.tail = entry.as_ref().prev;
        }

        entry.as_mut().next = None;
        entry.as_mut().prev = None;

        true
    }
}

impl<T> Entry<T> {
    /// Creates a new node with the associated data
    pub(crate) fn new(data: T) -> Entry<T> {
        Entry {
            prev: None,
            next: None,
            data: UnsafeCell::new(data),
            _pin: PhantomPinned,
        }
    }

    /// Get a raw pointer to the inner data
    pub(crate) fn get(&self) -> *mut T {
        self.data.get()
    }
}

#[cfg(test)]
#[cfg(not(loom))]
mod tests {
    use super::*;

    fn collect_list<T: Copy>(list: &mut LinkedList<T>) -> Vec<T> {
        let mut ret = vec![];

        while let Some(v) = list.pop_back() {
            ret.push(*v);
        }

        ret
    }

    /*
    unsafe fn collect_reverse_list<T: Copy>(list: LinkedList<T>) -> Vec<T> {
        list.into_reverse_iter()
            .map(|item| (*(*item).deref()))
            .collect()
    }
    */

    unsafe fn push_all(
        list: &mut LinkedList<i32>,
        entries: &mut [Pin<&mut Entry<i32>>],
    ) {
        for entry in entries.iter_mut() {
            list.push_front(entry.as_mut());
        }
    }

    macro_rules! assert_clean {
        ($e:ident) => {{
            assert!($e.next.is_none());
            assert!($e.prev.is_none());
        }};
    }

    #[test]
    fn push_and_drain() {
        pin! {
            let a = Entry::new(5);
            let b = Entry::new(7);
            let c = Entry::new(31);
        }

        let mut list = LinkedList::new();
        assert!(list.is_empty());

        unsafe {
            list.push_front(a);
            assert!(!list.is_empty());
            list.push_front(b);
            list.push_front(c);
        }

        let items: Vec<i32> = collect_list(&mut list);
        assert_eq!([5, 7, 31].to_vec(), items);

        assert!(list.is_empty());
    }

    #[test]
    fn push_pop_push_pop() {
        pin! {
            let a = Entry::new(5);
            let b = Entry::new(7);
        }

        let mut list = LinkedList::new();

        unsafe {
            list.push_front(a);
        }

        let v = list.pop_back().unwrap();
        assert_eq!(5, *v);
        assert!(list.is_empty());

        unsafe {
            list.push_front(b);
        }

        let v = list.pop_back().unwrap();
        assert_eq!(7, *v);

        assert!(list.is_empty());
        assert!(list.pop_back().is_none());
    }

    #[test]
    fn remove_by_address() {
        pin! {
            let a = Entry::new(5);
            let b = Entry::new(7);
            let c = Entry::new(31);
        }

        unsafe {
            // Remove first
            let mut list = LinkedList::new();

            push_all(&mut list, &mut [c.as_mut(), b.as_mut(), a.as_mut()]);
            assert!(list.remove(a.as_mut()));
            assert_clean!(a);
            // `a` should be no longer there and can't be removed twice
            assert!(!list.remove(a.as_mut()));
            assert!(!list.is_empty());

            assert!(list.remove(b.as_mut()));
            assert_clean!(b);
            // `b` should be no longer there and can't be removed twice
            assert!(!list.remove(b.as_mut()));
            assert!(!list.is_empty());

            assert!(list.remove(c.as_mut()));
            assert_clean!(c);
            // `b` should be no longer there and can't be removed twice
            assert!(!list.remove(c.as_mut()));
            assert!(list.is_empty());

            /*
            // Validate the state of things
            assert_eq!(&mut b as *mut Entry<i32>, list.head);
            assert_eq!(&mut c as *mut Entry<i32>, b.next);
            assert_eq!(&mut b as *mut Entry<i32>, c.prev);

            let items: Vec<i32> = collect_list(list);
            assert_eq!([7, 31].to_vec(), items);

            let mut list = LinkedList::new();
            add_nodes(&mut list, &mut [&mut c, &mut b, &mut a]);
            assert_eq!(true, list.remove(&mut a));
            assert_clean(&mut a);
            // a should be no longer there and can't be removed twice
            assert_eq!(false, list.remove(&mut a));
            assert_eq!(&mut c as *mut Entry<i32>, b.next);
            assert_eq!(&mut b as *mut Entry<i32>, c.prev);
            let items: Vec<i32> = collect_reverse_list(list);
            assert_eq!([31, 7].to_vec(), items);
            */
        }

        /*
        {
            // Remove middle
            let mut list = LinkedList::new();
            add_nodes(&mut list, &mut [&mut c, &mut b, &mut a]);
            assert_eq!(true, list.remove(&mut b));
            assert_clean(&mut b);
            assert_eq!(&mut c as *mut Entry<i32>, a.next);
            assert_eq!(&mut a as *mut Entry<i32>, c.prev);
            let items: Vec<i32> = collect_list(list);
            assert_eq!([5, 31].to_vec(), items);

            let mut list = LinkedList::new();
            add_nodes(&mut list, &mut [&mut c, &mut b, &mut a]);
            assert_eq!(true, list.remove(&mut b));
            assert_clean(&mut b);
            assert_eq!(&mut c as *mut Entry<i32>, a.next);
            assert_eq!(&mut a as *mut Entry<i32>, c.prev);
            let items: Vec<i32> = collect_reverse_list(list);
            assert_eq!([31, 5].to_vec(), items);
        }

        {
            // Remove last
            let mut list = LinkedList::new();
            add_nodes(&mut list, &mut [&mut c, &mut b, &mut a]);
            assert_eq!(true, list.remove(&mut c));
            assert_clean(&mut c);
            assert!(b.next.is_null());
            assert_eq!(&mut b as *mut Entry<i32>, list.tail);
            let items: Vec<i32> = collect_list(list);
            assert_eq!([5, 7].to_vec(), items);

            let mut list = LinkedList::new();
            add_nodes(&mut list, &mut [&mut c, &mut b, &mut a]);
            assert_eq!(true, list.remove(&mut c));
            assert_clean(&mut c);
            assert!(b.next.is_null());
            assert_eq!(&mut b as *mut Entry<i32>, list.tail);
            let items: Vec<i32> = collect_reverse_list(list);
            assert_eq!([7, 5].to_vec(), items);
        }

        {
            // Remove first of two
            let mut list = LinkedList::new();
            add_nodes(&mut list, &mut [&mut b, &mut a]);
            assert_eq!(true, list.remove(&mut a));
            assert_clean(&mut a);
            // a should be no longer there and can't be removed twice
            assert_eq!(false, list.remove(&mut a));
            assert_eq!(&mut b as *mut Entry<i32>, list.head);
            assert_eq!(&mut b as *mut Entry<i32>, list.tail);
            assert!(b.next.is_null());
            assert!(b.prev.is_null());
            let items: Vec<i32> = collect_list(list);
            assert_eq!([7].to_vec(), items);

            let mut list = LinkedList::new();
            add_nodes(&mut list, &mut [&mut b, &mut a]);
            assert_eq!(true, list.remove(&mut a));
            assert_clean(&mut a);
            // a should be no longer there and can't be removed twice
            assert_eq!(false, list.remove(&mut a));
            assert_eq!(&mut b as *mut Entry<i32>, list.head);
            assert_eq!(&mut b as *mut Entry<i32>, list.tail);
            assert!(b.next.is_null());
            assert!(b.prev.is_null());
            let items: Vec<i32> = collect_reverse_list(list);
            assert_eq!([7].to_vec(), items);
        }

        {
            // Remove last of two
            let mut list = LinkedList::new();
            add_nodes(&mut list, &mut [&mut b, &mut a]);
            assert_eq!(true, list.remove(&mut b));
            assert_clean(&mut b);
            assert_eq!(&mut a as *mut Entry<i32>, list.head);
            assert_eq!(&mut a as *mut Entry<i32>, list.tail);
            assert!(a.next.is_null());
            assert!(a.prev.is_null());
            let items: Vec<i32> = collect_list(list);
            assert_eq!([5].to_vec(), items);

            let mut list = LinkedList::new();
            add_nodes(&mut list, &mut [&mut b, &mut a]);
            assert_eq!(true, list.remove(&mut b));
            assert_clean(&mut b);
            assert_eq!(&mut a as *mut Entry<i32>, list.head);
            assert_eq!(&mut a as *mut Entry<i32>, list.tail);
            assert!(a.next.is_null());
            assert!(a.prev.is_null());
            let items: Vec<i32> = collect_reverse_list(list);
            assert_eq!([5].to_vec(), items);
        }

        {
            // Remove last item
            let mut list = LinkedList::new();
            add_nodes(&mut list, &mut [&mut a]);
            assert_eq!(true, list.remove(&mut a));
            assert_clean(&mut a);
            assert!(list.head.is_null());
            assert!(list.tail.is_null());
            let items: Vec<i32> = collect_list(list);
            assert!(items.is_empty());
        }

        {
            // Remove missing
            let mut list = LinkedList::new();
            list.add_front(&mut b);
            list.add_front(&mut a);
            assert_eq!(false, list.remove(&mut c));
        }

        {
            // Remove null
            let mut list = LinkedList::new();
            list.add_front(&mut b);
            list.add_front(&mut a);
            assert_eq!(false, list.remove(null_mut()));
        }
        */
    }
}
