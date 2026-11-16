//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of the seal fixtures, built OPTIMIZED: its generic fns reach
//! the crate that calls them as optimized MIR, with std's own fns inlined
//! into them. Its fns are safe to call, and sound. `Make` hides the type a
//! caller's marker makes behind an associated type, so that no type argument
//! of these fns holds a sealed value.

pub trait Make {
    type Out;
    fn make() -> Self::Out;
}

/// Empties `into` and moves `from`'s values in: `Vec::clear` and
/// `Vec::append`, which optimization inlines here down to a raw copy.
pub fn refill<M: Make>(into: &mut Vec<M::Out>, from: &mut Vec<M::Out>) {
    into.clear();
    into.append(from);
}

/// Swaps two slices: `swap_with_slice`.
pub fn swap_all<M: Make>(a: &mut [M::Out], b: &mut [M::Out]) {
    a.swap_with_slice(b);
}

/// Swaps two values by their bytes, as `mem::swap` may: the pointers are
/// given the type `*mut u8`, and nothing after that names the values' type.
pub fn exchange<M: Make>(a: &mut M::Out, b: &mut M::Out) {
    let size = std::mem::size_of::<M::Out>();
    let (a, b) = (a as *mut M::Out as *mut u8, b as *mut M::Out as *mut u8);
    // SAFETY: two distinct live values of one type, `size` bytes each.
    unsafe { std::ptr::swap_nonoverlapping(a, b, size) }
}

/// Pushes one new value: `Vec::push`, whose helper optimization shows.
pub fn fill<M: Make>(into: &mut Vec<M::Out>) {
    into.push(M::make());
}

/// Calls `visit` on each item: a loop, with one temporary a turn.
pub fn each<I: Iterator>(items: I, mut visit: impl FnMut(I::Item)) {
    for item in items {
        visit(item)
    }
}

// ----- review 14: sound `unsafe` code, and code a trusted fn is handed -----

/// Swaps two values by their bytes, the pointers read back out of an
/// `Option<&mut T>` given the type `*mut u8` by a transmute: no pointer cast
/// at all.
pub fn exchange_through<M: Make>(a: &mut M::Out, b: &mut M::Out) {
    let size = std::mem::size_of::<M::Out>();
    // SAFETY: an `Option<&mut T>` of a sized `T` that is `Some` is a thin,
    // non-null pointer; two distinct live values of one type, `size` bytes
    // each.
    unsafe {
        let a: *mut u8 = std::mem::transmute(Some(a));
        let b: *mut u8 = std::mem::transmute(Some(b));
        std::ptr::swap_nonoverlapping(a, b, size)
    }
}

/// A small-value container that keeps one `M::Out` IN BYTES OF ITS OWN: its
/// type names only the marker. Safe to use, and sound: it hands out `&` and
/// `&mut` under the usual borrows and never drops the value (a leak).
#[repr(C, align(16))]
pub struct Inline<M: Make> {
    bytes: [std::mem::MaybeUninit<u8>; 64],
    marker: std::marker::PhantomData<(*mut (), fn() -> M)>,
}

#[repr(C)]
union Raw<T> {
    value: std::mem::ManuallyDrop<T>,
    bytes: [std::mem::MaybeUninit<u8>; 64],
}

impl<M: Make> Inline<M> {
    pub fn make() -> Self {
        assert!(std::mem::size_of::<M::Out>() <= 64 && std::mem::align_of::<M::Out>() <= 16);
        let raw = Raw::<M::Out> { value: std::mem::ManuallyDrop::new(M::make()) };
        // SAFETY: every byte of a union may be read as `MaybeUninit<u8>`.
        Inline { bytes: unsafe { raw.bytes }, marker: std::marker::PhantomData }
    }
    pub fn get_mut(&mut self) -> &mut M::Out {
        // SAFETY: `make` put an `M::Out` at offset 0, aligned for it.
        unsafe { &mut *(self.bytes.as_mut_ptr() as *mut M::Out) }
    }
}

/// A guard that swaps what it borrows when it is dropped: safe code only.
pub struct SwapOnDrop<'a, M: Make>(pub &'a mut M::Out, pub &'a mut M::Out);
impl<M: Make> Drop for SwapOnDrop<'_, M> {
    fn drop(&mut self) {
        std::mem::swap(self.0, self.1)
    }
}

/// The bytes of an implementor may be written, each with any value.
///
/// # Safety
/// `bytes` hands back a pointer to that many bytes, live and writable for as
/// long as `self` is borrowed, for which every bit pattern is valid.
pub unsafe trait Bytes {
    fn bytes(&mut self) -> (*mut u8, usize);
}

/// Sets every byte of `target`.
pub fn blank<B: Bytes>(target: &mut B, byte: u8) {
    let (at, len) = target.bytes();
    // SAFETY: the trait's contract.
    unsafe { std::ptr::write_bytes(at, byte, len) }
}

/// A `&mut` of what a marker makes, as a type of this crate.
#[repr(transparent)]
pub struct Handle<'a, M: Make>(pub &'a mut M::Out);

mod thin {
    pub trait Sealed {}
    impl<M: super::Make> Sealed for super::Handle<'_, M> {}
}

/// Implemented for `Handle` and nothing else: every value behind a `dyn
/// Thin` is a thin pointer to `size()` writable bytes of the type `kind()`.
pub trait Thin: thin::Sealed {
    fn size(&self) -> usize;
    fn kind(&self) -> std::any::TypeId;
}
impl<M: Make> Thin for Handle<'_, M>
where
    M::Out: 'static,
{
    fn size(&self) -> usize {
        std::mem::size_of::<M::Out>()
    }
    fn kind(&self) -> std::any::TypeId {
        std::any::TypeId::of::<M::Out>()
    }
}

/// Swaps what two handles of one type point to. It names no type: it is
/// not generic, and no instance of it is ever read.
pub fn swap_thin(a: &mut dyn Thin, b: &mut dyn Thin) {
    if a.kind() != b.kind() {
        return;
    }
    let size = a.size();
    // SAFETY: only `Handle` implements `Thin`, so each value behind the
    // `dyn` is a thin pointer to `size` writable bytes of one type, and two
    // `&mut` never overlap.
    unsafe {
        let a = *(a as *mut dyn Thin as *mut *mut u8);
        let b = *(b as *mut dyn Thin as *mut *mut u8);
        std::ptr::swap_nonoverlapping(a, b, size)
    }
}

/// Swaps two values by their bytes, the pointers read back out of a `dyn
/// Send` THIS fn made of them: a std trait, and a fn that is not generic
/// (and so is never read) on the other side.
pub fn exchange_erased<M: Make>(a: &mut M::Out, b: &mut M::Out)
where
    M::Out: Send,
{
    let size = std::mem::size_of::<M::Out>();
    let (mut a, mut b) = (a, b);
    swap_behind(&mut a, &mut b, size)
}

#[inline(never)]
fn swap_behind(a: &mut dyn Send, b: &mut dyn Send, size: usize) {
    // SAFETY (this crate's own contract): every caller hands two `&mut` to
    // distinct live values of one type, `size` bytes each.
    unsafe {
        let a = *(a as *mut dyn Send as *mut *mut u8);
        let b = *(b as *mut dyn Send as *mut *mut u8);
        std::ptr::swap_nonoverlapping(a, b, size)
    }
}

/// Hands back the `&` it is given, through a raw pointer: it writes nothing.
pub fn peek<M: Make>(value: &mut M::Out) -> &M::Out {
    // SAFETY: a live, borrowed value.
    unsafe { &*(value as *const M::Out) }
}

/// Safe code only: runs `with` on the value.
pub fn visit<M: Make>(value: &mut M::Out, mut with: impl FnMut(&mut M::Out)) {
    with(value)
}
