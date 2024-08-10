use stackbox::StackBox;
use std::alloc::{alloc, dealloc, Layout};
use std::any::type_name;
use std::cell::Cell;
use std::cmp::{max, min};
use std::marker::PhantomData;
use std::mem::{align_of, size_of, ManuallyDrop, MaybeUninit};
use std::ptr::{copy_nonoverlapping, drop_in_place, null_mut, slice_from_raw_parts_mut};

type UByte = MaybeUninit<u8>;

struct ResetAllocation;

const BASE_ALIGN: usize = 16;
const DEFAULT_CAP: usize = 1024;

impl Drop for ResetAllocation {
    fn drop(&mut self) {
        assert_eq!(LEN.get(), 0);
        BASE.set(null_mut::<UByte>().wrapping_add(BASE_ALIGN));
        CAP.set(0);
        ALIGN_REQUIREMENT.set(BASE_ALIGN);
    }
}

struct FreeElt(*mut UByte, Layout);

impl Drop for FreeElt {
    fn drop(&mut self) {
        unsafe { dealloc(self.0 as *mut _, self.1) }
    }
}

// Invariants:
// ALIGN_REQUIREMENT is a monotonically increasing power of two that is at least BASE_ALIGN
// BASE is aligned to ALIGN_REQUIREMENT
// BASE points to an allocation of length CAP
// the memory in BASE[LEN..CAP] is owned by the thread (has not yet been handed out)
// elements of FREE_LIST correspond to calls to alloc
// the memory in all but the last element of FREE_LIST is owned by the thread
// the last element is BASE so it is also owned by the thread when LEN == 0
thread_local! {
    static BASE: Cell<*mut UByte>  = const {Cell::new(null_mut::<UByte>().wrapping_add(BASE_ALIGN))};
    static LEN: Cell<usize> = const{Cell::new(0)};
    static CAP: Cell<usize> = const{Cell::new(0)};
    static ALIGN_REQUIREMENT: Cell<usize> = const{Cell::new(BASE_ALIGN)};
    static FREE_LIST: (ResetAllocation, Cell<Vec<FreeElt>>) = const{(ResetAllocation, Cell::new(Vec::new()))};
}

#[cold]
fn realloc_exact(new_cap: usize) {
    let layout = Layout::from_size_align(new_cap, ALIGN_REQUIREMENT.get()).unwrap();
    let new = unsafe { alloc(layout) } as *mut UByte;
    FREE_LIST.with(|(_, cell)| {
        let mut elts = cell.take();
        elts.push(FreeElt(new, layout));
        cell.set(elts)
    });
    // if LEN > CAP then the extra bytes are just padding bytes so they don't need to be copied
    let len = min(LEN.get(), CAP.get());
    unsafe { copy_nonoverlapping(BASE.get(), new, len) };
    BASE.set(new);
    CAP.set(new_cap);
}

#[cold]
#[inline(never)]
fn realloc(required: usize) {
    let mut new_cap = CAP.get();
    if new_cap == 0 {
        new_cap = DEFAULT_CAP;
    }
    while new_cap < required {
        new_cap *= 2;
    }
    realloc_exact(new_cap)
}

/// Typed region of the second stack obtained using [`with_stack_vec`].
///
/// I notably does *not* implement `Deref<Target=[T]>`, and only can only be used as a slice after
/// calling [`StackVec::into_slice`] which prevents new elements from being added
///
/// It does not implement `Send` since the second stack is thread local.
// Invariants:
// slice_offset % align_of::<T> == 0
// ALIGN_REQUIREMENT % align_of::<T> == 0
// # Since ALIGN_REQUIREMENT is a monotonically increasing power of two this is stable
// slice_offset + slice_len * size_of::<T> == LEN
// # LEN can be modified by other `StackVec`s created by `with_stack_vec` or `uninit_slice`,
// # but the functions passed to those functions have `Send` bounds so they cannot use this
// # `StackVec`, after they end they restore LEN to its previous value so this stack vec won't
// # notice the change
pub struct StackVec<'a, T> {
    slice_offset: usize,
    slice_len: usize,
    // Important that `StackVec` is not `Send`
    phantom: PhantomData<(&'a (), T, *mut u8)>,
}

impl<'a, T> StackVec<'a, T> {
    /// Assert that this `StackVec` satisfies its invariant
    ///
    /// This is initially true for a `StackVec` that is created using [`with_stack_vec`].
    ///
    /// The invariant is preserved by all of `StackVec`s methods
    ///
    /// Calling [`with_stack_vec`] breaks the invariant of the `StackVec` created from the previous
    /// call to [`with_stack_vec`] during the call of the passed in function but restores it again
    /// afterwards, so a `StackVec` with a broken invariant can be observed by smuggling a
    /// `StackVec` into the function using external crates
    ///
    /// ```should_panic
    /// use send_wrapper::SendWrapper;
    /// use second_stack2::{with_stack_vec, StackVec};
    /// with_stack_vec(|mut s: StackVec<u32>| {
    ///     let s = SendWrapper::new(s);
    ///     with_stack_vec(|_: StackVec<u32>| {
    ///         s.assert_inv(); // panics
    ///     })
    /// })
    /// ```
    #[inline]
    pub fn assert_inv(&self) {
        assert_eq!(
            LEN.get(),
            self.slice_offset + self.slice_len * size_of::<T>(),
            "This stack-vec was smuggled into the scope of another stack-vec"
        )
    }

    #[inline]
    fn slice_ptr(&mut self) -> *mut [T] {
        let data = unsafe { BASE.get().add(self.slice_offset) as *mut T };
        slice_from_raw_parts_mut(data, self.slice_len)
    }

    /// Converts the vector into a [`StackBox`] which implements `Deref<Target=[T]>`
    #[inline]
    pub fn into_slice(self) -> StackBox<'a, [T]> {
        let mut this = ManuallyDrop::new(self);
        unsafe { StackBox::assume_owns(&mut *(this.slice_ptr() as *mut ManuallyDrop<[T]>)) }
    }

    /// Converts the vector into a [`StackBox`] which implements `Deref<Target=[T]>` and
    /// returns another stackvec that can be used to continue growing the second stack
    ///
    /// # Examples
    ///
    /// ```
    /// use second_stack2::with_stack_vec;
    /// with_stack_vec(|mut vec1| {
    ///     vec1.extend_from_slice(&[true, false]);
    ///     let (slice1, mut vec2) = vec1.into_slice_full();
    ///     vec2.extend_from_slice(&[1, 2, 3]);
    ///     assert_eq!(&*slice1, &[true, false]);
    ///     assert_eq!(&*vec2.into_slice(), &[1, 2, 3]);
    /// })
    /// ```
    #[inline]
    pub fn into_slice_full<U>(self) -> (StackBox<'a, [T]>, StackVec<'a, U>) {
        (self.into_slice(), stack_vec())
    }

    /// Uncheck version of [`push`](StackVec::push)
    ///
    /// # Safety
    ///
    /// The invariant must not be currently broken (see [`assert_inv`](StackVec::assert_inv))
    ///
    /// Creating a closure that calls `push_unchecked` is very dangerous since that closure could
    /// be smuggled into another scope and then called leading to undefined behaviour
    #[inline]
    pub unsafe fn push_unchecked(&mut self, e: T) {
        let len = LEN.get();
        let needed = len + size_of::<T>();
        if CAP.get() < needed {
            realloc(needed);
        }
        let ptr = unsafe { BASE.get().add(len) } as *mut T;
        unsafe { ptr.write(e) };
        LEN.set(needed);
        self.slice_len += 1;
    }

    /// Appends an element to the back of the vector.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity of the second stack exceeds `isize::MAX` _bytes_.
    ///
    /// Panics if the invariant is broken (see [`assert_inv`](StackVec::assert_inv))
    ///
    /// # Examples
    ///
    /// ```
    /// use second_stack2::with_stack_vec;
    /// with_stack_vec(|mut vec| {
    ///     vec.push(1);
    ///     vec.push(2);
    ///     vec.push(3);
    ///     assert_eq!(&*vec.into_slice(), &[1, 2, 3]);
    /// })
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes amortized *O*(1) time. If the second stacks length would exceed its
    /// capacity after the push, *O*(*capacity*) time is taken to copy the
    /// vector's elements to a larger allocation. This expensive operation is
    /// offset by the *capacity* *O*(1) insertions it allows.
    #[inline]
    pub fn push(&mut self, e: T) {
        self.assert_inv();
        unsafe {
            self.push_unchecked(e);
        }
    }

    #[inline]
    // Safety: it must be possible to copy out of `s`
    unsafe fn extend_from_slice_raw(&mut self, s: *const T, s_len: usize) {
        let len = LEN.get();
        let needed = len + (size_of::<T>() * s_len);
        if CAP.get() < needed {
            realloc(needed);
        }
        let ptr = unsafe { BASE.get().add(len) } as *mut T;
        unsafe { copy_nonoverlapping(s, ptr, s_len) };
        LEN.set(needed);
        self.slice_len += s_len;
    }

    /// Copies the elements of `s` to the back of the vector.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity of the second stack exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// use second_stack2::with_stack_vec;
    /// with_stack_vec(|mut vec| {
    ///     vec.extend_from_slice(&[0, 1, 2]);
    ///     vec.push(3);
    ///     assert_eq!(&*vec.into_slice(), &[0, 1, 2, 3]);
    /// })
    /// ```
    #[inline]
    pub fn extend_from_slice(&mut self, s: &[T])
    where
        T: Copy,
    {
        self.assert_inv();
        // Safety `T: Copy` so we can copy out of it
        unsafe { self.extend_from_slice_raw(s as *const [T] as *const T, s.len()) }
    }

    /// Moves the elements out of `s` to the back of the vector.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity of the second stack exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// use stackbox::mk_slot;
    /// use second_stack2::with_stack_vec;
    /// with_stack_vec(|mut vec| {
    ///     let mut s = mk_slot();
    ///     let s = s.stackbox([Box::new(0), Box::new(1), Box::new(2)]);
    ///     vec.extend_from_owned_slice(s.into_slice());
    ///     vec.push(Box::new(4));
    ///     assert_eq!(&*vec.into_slice(), &[Box::new(0), Box::new(1), Box::new(2), Box::new(4)])
    /// })
    /// ```
    #[inline]
    pub fn extend_from_owned_slice(&mut self, s: StackBox<[T]>) {
        self.assert_inv();
        let len = s.len();
        let s = ManuallyDrop::new(s);
        // Safety `StackBox` is repr(transparent) of a pointer
        let s = unsafe { core::mem::transmute::<_, *const [T]>(s) };
        // Safety s is in a `ManuallyDrop` and owns the data so we can copy of it
        unsafe { self.extend_from_slice_raw(s as *const T, len) }
    }

    /// Uncheck version of [`pop`](StackVec::pop)
    ///
    /// # Safety
    ///
    /// The invariant must not be currently broken (see [`assert_inv`](StackVec::assert_inv))
    ///
    /// Creating a closure that calls `push_unchecked` is very dangerous since that closure could
    /// be smuggled into another scope and then called leading to undefined behaviour
    #[inline]
    pub unsafe fn pop_unchecked(&mut self) -> Option<T> {
        if self.slice_len == 0 {
            return None;
        }
        self.slice_len -= 1;
        let len = LEN.get();
        let new_len = len - size_of::<T>();
        let ptr = unsafe { BASE.get().add(new_len) } as *mut T;
        let res = unsafe { ptr.read() };
        LEN.set(new_len);
        Some(res)
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use second_stack2::with_stack_vec;
    /// with_stack_vec(|mut vec| {
    ///     vec.push(1);
    ///     vec.push(2);
    ///     vec.push(3);
    ///     assert_eq!(vec.pop(), Some(3));
    ///     assert_eq!(vec.pop(), Some(2));
    ///     assert_eq!(vec.pop(), Some(1));
    ///     assert_eq!(vec.pop(), None);
    /// })
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) time.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        self.assert_inv();
        unsafe { self.pop_unchecked() }
    }
}

impl<'a, T> Drop for StackVec<'a, T> {
    fn drop(&mut self) {
        unsafe { drop_in_place(self.slice_ptr()) }
    }
}
struct ResetLen(usize);

impl Drop for ResetLen {
    fn drop(&mut self) {
        LEN.set(self.0)
    }
}

/// Create a [`StackVec`] that can be used in the scope of the function `f`.
///
/// ## Example
/// ```
/// use second_stack2::with_stack_vec;
/// with_stack_vec(|mut v1| {
///    v1.push(42);
///    v1.push(25);
///    assert_eq!(v1.pop(), Some(25));
///    with_stack_vec(|mut v2| {
///        v2.push("Hello World".to_string());
///        assert_eq!(v2.pop().as_deref(), Some("Hello World"));
///    });
///    assert_eq!(v1.pop(), Some(42));
/// })
/// ```
///
/// Note: `f` is currently required to implement `Send` even though it will run on the same thread.
///
/// This is to prevent a [`StackVec`] from being used within the scope of a second call to
/// [`with_stack_vec`]
///
/// ## Example
/// ```compile_fail
/// use second_stack2::with_stack_vec;
/// with_stack_vec(|mut v1| {
///    v1.push(42);
///    v1.push(25);
///    assert_eq!(v1.pop(), Some(25));
///    with_stack_vec(|mut v2| {
///        v2.push("Hello World".to_string());
///        v1.push(15); // This could lead to UB if allowed
///        assert_eq!(v2.pop().as_deref(), Some("Hello World"));
///    });
///    assert_eq!(v1.pop(), Some(42));
/// })
/// ```
///
/// In the future this bound may be relaxed to a custom auto trait once they become stable
pub fn with_stack_vec<T, R, F>(f: F) -> R
where
    F: FnOnce(StackVec<T>) -> R + Send,
{
    let reset_len = ResetLen(LEN.get());
    let res = f(stack_vec());
    drop(reset_len);
    res
}

#[inline]
fn ensure_alignment<T>() {
    assert!(
        align_of::<T>().is_power_of_two(),
        "alignment of {} is not a power of two",
        type_name::<T>()
    );
    if align_of::<T>() > BASE_ALIGN && align_of::<T>() > ALIGN_REQUIREMENT.get() {
        ALIGN_REQUIREMENT.set(align_of::<T>());
        if BASE.get().align_offset(align_of::<T>()) != 0 {
            realloc_exact(CAP.get())
        }
    }
}

fn stack_vec<T>() -> StackVec<'static, T> {
    ensure_alignment::<T>();

    let old_len = LEN.get();
    let base_len = ((old_len + align_of::<T>()) / align_of::<T>()) * align_of::<T>();
    assert!(
        base_len > old_len,
        "base_len = {base_len}, old_len = {old_len}, align = {}",
        align_of::<T>()
    );
    let res = StackVec {
        slice_offset: base_len,
        slice_len: 0,
        phantom: PhantomData,
    };

    LEN.set(base_len);
    res
}

fn pre_uninit_slice<T>(len: usize) -> StackVec<'static, MaybeUninit<T>> {
    ensure_alignment::<T>();
    let old_len = LEN.get();
    // size_of::<u8> == 1 so align_offset will succeed see https://github.com/rust-lang/rust/issues/62420
    let offset = null_mut::<u8>()
        .wrapping_add(old_len)
        .align_offset(align_of::<T>());
    let base_len = old_len + offset;
    let needed = base_len + len * size_of::<T>();
    if CAP.get() < needed {
        realloc(needed);
    }
    LEN.set(needed);
    StackVec {
        slice_offset: base_len,
        slice_len: len,
        phantom: PhantomData,
    }
}

/// Allocates an uninit slice from the second stack.
///
/// See [`with_stack_vec`] for details on the `Send` bound
pub fn uninit_slice<T, F, R>(len: usize, f: F) -> R
where
    F: FnOnce(&mut [MaybeUninit<T>]) -> R + Send,
{
    let reset_len = ResetLen(LEN.get());
    let res = f(&mut pre_uninit_slice(len).into_slice());
    drop(reset_len);
    res
}

/// Increases the second stacks capacity to `new_cap` bytes if it isn't already that large
pub fn reserve_buffer_capacity(new_cap: usize) {
    if new_cap > CAP.get() {
        realloc_exact(new_cap)
    }
}

/// Similar to [`reserve_buffer_capacity`] but also makes sure the memory aligned to `new_align`
/// This prevents a reallocation from being needed when first using a type whose alignment is more
/// than 16
pub fn reserve_buffer_align_capacity(new_align: usize, new_cap: usize) {
    assert!(
        new_align.is_power_of_two(),
        "new_align = {new_align} is not a power of two"
    );
    if new_align > ALIGN_REQUIREMENT.get() {
        ALIGN_REQUIREMENT.set(new_align);
    }
    realloc_exact(max(CAP.get(), new_cap))
}
