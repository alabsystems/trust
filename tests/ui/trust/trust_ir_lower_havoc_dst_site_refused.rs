//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on --crate-type=lib
//! Trust (HAVOC-SITE-DST-1, 2026-10-13): **a generic call site whose args make a thin slot of a
//! FORCED-HAVOC declaration fat is refused, so the crate module still validates.**
//!
//! A call whose callee args still mention the CALLER's type parameters cannot be resolved, so
//! `resolve_callee` admits it as a forced-havoc bodyless declaration. That declaration's
//! parameter list is signed from the UNINSTANTIATED signature (`recover_callee_param_tys`, its
//! `generic_but_thin` arm), where `*const T` and `&Self` are the thin `ptr`. The site's args can
//! make that position fat: `meta::<[T]>(p)` passes a `*const [T]` (`(ptr, i64)`), and
//! `<str as Hashy>::feed::<H>(s, h)` passes a `&str` (`fatptr<str>`). The validator then
//! rejected the WHOLE crate module (measured on this file before the fix):
//!
//!     CallArgTypeMismatch { callee: "!trust_bodyless_instance::meta::…", arg_index: 0,
//!     expected: "ptr", actual: "(ptr, i64)", .. }
//!     CallArgTypeMismatch { callee: "Hashy::feed", arg_index: 0, expected: "ptr",
//!     actual: "fatptr<str>", .. }
//!
//! — the two shapes that kept `core`'s crate module from validating
//! (`<*const [T]>::len` calling `ptr::metadata::metadata`, `<Location as Hash>::hash` calling
//! `Hash::hash` on a `&str`; docs/KNOWN_HAZARDS.md, the `core` entry of 2026-10-05). The site is
//! now refused (`Call(DST-incoherent havoc site)`): its body is lowered for coverage only and
//! never spliced, and the rest of the module is assembled and validates. The thin controls
//! (`thin_meta`, `forwards_own_param`, `thin_feed`) still admit the havoc edge.
//!
//! No `.stderr` and no `dont-check-compiler-stderr`: the pin is that this lane prints NOTHING,
//! so the finalization warning fails this file on a producer that admits either fat site.

#[inline(never)]
pub fn meta<T: ?Sized>(_p: *const T) -> usize {
    0
}

// `meta::<[T]>`: the identity slot `*const T` is thin, this site's `*const [T]` is fat.
pub fn slice_meta<T>(p: *const [T]) -> usize {
    meta(p)
}

// Control: `meta::<T>` with a sized `T` is thin on both sides.
pub fn thin_meta<T>(p: *const T) -> usize {
    meta(p)
}

// Control: a generic caller forwarding its own `?Sized` param is thin on both sides.
pub fn forwards_own_param<T: ?Sized>(p: *const T) -> usize {
    meta(p)
}

pub trait Hashy {
    fn feed<H>(&self, h: &mut H) -> usize;
}

impl Hashy for str {
    #[inline(never)]
    fn feed<H>(&self, _h: &mut H) -> usize {
        self.len()
    }
}

impl Hashy for u32 {
    #[inline(never)]
    fn feed<H>(&self, _h: &mut H) -> usize {
        *self as usize
    }
}

// `<str as Hashy>::feed::<H>`: the identity slot `&Self` is thin, this site's `&str` is fat.
pub fn str_feed<H>(s: &str, h: &mut H) -> usize {
    s.feed(h)
}

// Control: `<u32 as Hashy>::feed::<H>` is thin on both sides.
pub fn thin_feed<H>(x: &u32, h: &mut H) -> usize {
    x.feed(h)
}
