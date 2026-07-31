//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (#171 Part B): `Self` used as a unit-struct CONSTRUCTOR lowers clean and AGREES.
//!
//! rustc spells `impl S { fn ctor() -> Self { Self } }` as `ExprKind::ZstLiteral`
//! (a `Res::SelfCtor` resolution), while the very same value written by NAME
//! (`fn f() -> S { S }`) is an `ExprKind::Adt`. The `Adt` spelling has always
//! lowered clean and Agreed; only the `Self` spelling was missing, so this is a
//! missing spelling of a lowering the producer already performs, not new
//! behaviour. Both now emit the identical instruction:
//!     %0 = const struct.N {  }
//!
//! THE DIRECTION MATTERS, and an earlier attempt got it backwards. Wave-TW first
//! made a drop-free ZST VALUE-LESS in every position; the corpus differential
//! caught it as "Call returns arity mismatch: expected 1, got 0". The producer's
//! SIGNATURE keys return value-ness on `fn_sig.output().is_unit()` — the real
//! `ty::Tuple([])` and nothing else — so a unit-struct return declares one return
//! however the body is spelled, and the MIR-side oracle agrees with the signature
//! (it models a ZST struct as value-BEARING). The repair is to make the BODY
//! produce the value its signature already declares.

pub struct ST5;

impl ST5 {
    // The shape this fixes.
    pub fn ctor() -> Self {
        Self
    }
}

// The reference that already worked — same value, written by name.
pub fn by_name() -> ST5 {
    ST5
}

// A braced-empty struct takes the same path.
pub struct Named {}
pub fn named() -> Named {
    Named {}
}

// The wave-TW discard-position skip must stay untouched: nothing consumes this
// value, so the statement still lowers to no instruction at all.
pub fn discard() {
    let _ = ST5;
}

fn main() {}
