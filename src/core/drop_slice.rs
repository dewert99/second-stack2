use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr::{drop_in_place, slice_from_raw_parts_mut, NonNull};

/// Slice that owns its elements but not the memory they are stored in
pub struct DropSlice<'a, T>(NonNull<[T]>, PhantomData<(&'a (), T)>);

impl<'a, T> Drop for DropSlice<'a, T> {
    fn drop(&mut self) {
        unsafe { drop_in_place(self.0.as_ptr()) }
    }
}

impl<'a, T> Deref for DropSlice<'a, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<'a, T> DerefMut for DropSlice<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}

unsafe impl<'a, T: Send> Send for DropSlice<'a, T> {}

unsafe impl<'a, T: Sync> Sync for DropSlice<'a, T> {}

impl<'a, T> DropSlice<'a, T> {
    pub(super) fn new(ptr: *mut [T]) -> Self {
        debug_assert!(!ptr.is_null());
        DropSlice(unsafe { NonNull::new_unchecked(ptr) }, PhantomData)
    }

    /// Removes and returns the first element
    pub fn pop_front(&mut self) -> Option<T> {
        let len = self.0.len();
        if self.0.len() == 0 {
            None
        } else {
            let ptr = self.0.as_ptr() as *mut T;
            let res = unsafe { ptr.read() };
            let slice = slice_from_raw_parts_mut(unsafe { ptr.add(1) }, len - 1);
            self.0 = unsafe { NonNull::new_unchecked(slice) };
            Some(res)
        }
    }

    /// Removes and returns the last element
    pub fn pop_back(&mut self) -> Option<T> {
        let len = self.0.len();
        if self.0.len() == 0 {
            None
        } else {
            let ptr = self.0.as_ptr() as *mut T;
            let res = unsafe { ptr.add(len - 1).read() };
            let slice = slice_from_raw_parts_mut(ptr, len - 1);
            self.0 = unsafe { NonNull::new_unchecked(slice) };
            Some(res)
        }
    }
}

impl<'a, T> Default for DropSlice<'a, T> {
    fn default() -> Self {
        let slice = slice_from_raw_parts_mut(NonNull::dangling().as_ptr(), 0);
        DropSlice(unsafe { NonNull::new_unchecked(slice) }, PhantomData)
    }
}
