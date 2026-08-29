/*!
A specialized copy-on-write byte string for the `memmem` needle.

`Cow` is not in core, and a `Box<[u8]>` is a third smaller than the `Vec<u8>`
a `Cow<[u8]>` would carry — nothing here ever grows a needle. With `alloc`
disabled the type degrades to a plain `&[u8]` with no owned variant.

Every operation is a free function rather than an inherent method: a call to an
inherent associated constructor resurfaces in the caller as an absent callee
whose panic path stays reachable. See `crate::scan` for the full rule set.
*/

/// A borrowed or owned byte string.
#[derive(Clone, Debug)]
pub(crate) struct CowBytes<'a>(Imp<'a>);

#[cfg(feature = "alloc")]
#[derive(Clone, Debug)]
enum Imp<'a> {
    Borrowed(&'a [u8]),
    Owned(alloc::boxed::Box<[u8]>),
}

#[cfg(not(feature = "alloc"))]
#[derive(Clone, Debug)]
struct Imp<'a>(&'a [u8]);

/// Wrap a borrowed byte string.
#[cfg(feature = "alloc")]
#[inline(always)]
pub(crate) fn borrowed(bytes: &[u8]) -> CowBytes<'_> {
    CowBytes(Imp::Borrowed(bytes))
}

/// Wrap a borrowed byte string.
#[cfg(not(feature = "alloc"))]
#[inline(always)]
pub(crate) fn borrowed(bytes: &[u8]) -> CowBytes<'_> {
    CowBytes(Imp(bytes))
}

/// Wrap an owned byte string.
#[cfg(feature = "alloc")]
#[inline(always)]
pub(crate) fn owned(bytes: alloc::boxed::Box<[u8]>) -> CowBytes<'static> {
    CowBytes(Imp::Owned(bytes))
}

/// Borrow the byte string, whether it is owned or borrowed internally.
#[cfg(feature = "alloc")]
#[inline(always)]
pub(crate) fn as_slice<'c>(cow: &'c CowBytes<'_>) -> &'c [u8] {
    match cow.0 {
        Imp::Owned(ref bytes) => bytes,
        Imp::Borrowed(bytes) => bytes,
    }
}

/// Borrow the byte string, whether it is owned or borrowed internally.
#[cfg(not(feature = "alloc"))]
#[inline(always)]
pub(crate) fn as_slice<'c>(cow: &'c CowBytes<'_>) -> &'c [u8] {
    cow.0.0
}

/// Take ownership of the byte string, copying it if it was borrowed.
#[cfg(feature = "alloc")]
#[inline(always)]
pub(crate) fn into_owned(cow: CowBytes<'_>) -> CowBytes<'static> {
    match cow.0 {
        Imp::Borrowed(bytes) => CowBytes(Imp::Owned(alloc::boxed::Box::from(bytes))),
        Imp::Owned(bytes) => CowBytes(Imp::Owned(bytes)),
    }
}
