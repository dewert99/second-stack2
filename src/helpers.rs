use crate::core::*;
use stackbox::StackBox;
use std::convert::Infallible;
use std::mem::MaybeUninit;
// Conveince functions

/// Place a potentially very large value on the second stack.
///
/// ## Example
/// ```rust
/// second_stack2::uninit(|arr| {
///   let arr: &mut [u8; 2048] = arr.write([0; 2048]);
///   // use arr
/// })
/// ```
#[inline]
pub fn uninit<T, F, R>(f: F) -> R
where
    F: FnOnce(&mut MaybeUninit<T>) -> R,
{
    uninit_slice(1, |x| f(&mut x[0]))
}

impl<'a, T> Extend<T> for StackVec<'a, T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(|x| self.push(x))
    }
}

/// Tries to buffer an iterator to a slice on the second stack.
/// If successful it calls `f` with temporary access to that slice
/// Panics when running out of memory (e.g. if the iterator is unbounded)
pub fn try_buffer<T, F, R, I, E>(i: I, f: F) -> Result<R, E>
where
    I: Iterator<Item = Result<T, E>>,
    F: FnOnce(&mut [T]) -> Result<R, E>,
{
    with_stack_vec(|mut s| {
        let mut res = Ok(());
        let i1 = i.map_while(|r| match r {
            Ok(r) => Some(r),
            Err(e) => {
                res = Err(e);
                None
            }
        });
        s.extend(i1);
        res?;
        f(&mut s.into_slice())
    })
}

/// Buffers an iterator to a slice on the second stack and gives temporary access to that slice.
/// Panics when running out of memory (e.g. if the iterator is unbounded)
///
/// ## Example
/// ```
/// // Buffer fully consumes an iterator,
/// // writes each item to a slice on the second stack,
/// // and gives you mutable access to the slice.
/// // This API supports Drop.
/// second_stack2::buffer(0..1000, |items| {
///     assert_eq!(items.len(), 1000);
///     assert_eq!(items[19], 19);
/// })
// ```
pub fn buffer<T, F, R, I>(i: I, f: F) -> R
where
    I: Iterator<Item = T>,
    F: FnOnce(&mut [T]) -> R,
{
    with_stack_vec(|mut s| {
        s.extend(i);
        f(&mut s.into_slice())
    })
}

/// Alternate version of [`try_buffer`] avoids checking the invariant for each element of the
/// iterator, but walks the iterator by repeatedly calling [`Iterator::next`] instead of using
/// [`Iterator::try_for_each`]
pub fn try_buffer_alt<T, F, R, I, E>(i: I, f: F) -> Result<R, E>
where
    I: Iterator<Item = Result<T, E>>,
    F: FnOnce(&mut [T]) -> Result<R, E>,
{
    let mut i = i;
    with_stack_vec(|mut s| {
        while let Some(e) = i.next() {
            // Safety s is in the same scope it was originally created in
            unsafe {
                s.push_unchecked(e?);
            }
        }
        f(&mut *s.into_slice())
    })
}

/// Alternate version of [`buffer`] avoids checking the invariant for each element of the
/// iterator, but walks the iterator by repeatedly calling [`Iterator::next`] instead of using
/// [`Iterator::for_each`]
pub fn buffer_alt<T, F, R, I>(i: I, f: F) -> R
where
    I: Iterator<Item = T>,
    F: FnOnce(&mut [T]) -> R,
{
    match try_buffer_alt(i.map(Ok::<_, Infallible>), |x| Ok(f(x))) {
        Ok(x) => x,
        Err(e) => match e {},
    }
}

impl<'a, T: 'a> IntoIterator for StackVec<'a, T> {
    type Item = T;

    type IntoIter = <StackBox<'a, [T]> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.into_slice().into_iter()
    }
}
