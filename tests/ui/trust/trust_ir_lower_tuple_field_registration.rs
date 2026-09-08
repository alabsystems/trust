//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-FTR): a TUPLE-typed field read resolves its holder by the pure ledger scan FIRST
//! and by map-and-rollback only when that answers `None`.
//!
//! The scan alone was a guard reading a set populated LATER than the guard runs: the holder is
//! registered by `lower_expr(lhs)` ONE LINE BELOW the gate, so `Y.x.0` on a static and
//! `(*h).x.1` on a `&H` refused on a REGISTRATION-ORDER ACCIDENT rather than on a capability
//! boundary. The two sibling blocks immediately below it -- wave-PR's pointer lane and
//! wave-RF2's array lane -- already spell it the second way, and wave-RF2's comment states that
//! the pure scan "would therefore decline every measured body". The tuple lane was the last of
//! the three still on it.
//!
//! THE LANE EMITS NOTHING NEW. `fn now(h: H) -> i64 { h.x.0 }` -- the by-value twin, below --
//! already lowers clean and grades `equal=true, samples=7, mode=Agreed` against the MIR oracle
//! on the identical `ExtractField` pair. Only which spelling resolves the `StructId` changed.
//!
//! STRICTLY ADDITIVE by the scan-first ordering: an already-accepted read never reaches the
//! probe, so the probe runs only in bodies that are dirty today. The rollback drops TAGS, not
//! registrations (the shipped wave-PR posture), and the declared-equals-read equality is
//! untouched -- a holder registered opaque-tolerant spells this field `Ty::Unit`, which is not a
//! `Ty::Tuple`, so the `OperandTypeMismatch` the pre-wave comment measured stays closed.
//!
//! DISCLOSURE: the two holder spellings this lane retires are exactly the two the oracles
//! decline -- a `&H` holder is `mode=NotRun` ("param 0 (ptr) is READ ... opaque sampling
//! refused") and a static holder is seam-deferred -- so the retired bodies are COVERAGE-ONLY.
//! The semantic argument rests on the by-value twin being instruction-identical plus the
//! equality gate, not on oracle evidence for these shapes. Under `=strict` because none of them
//! can reach `DerivedAgreed` either: `to_mir` refuses a non-scalar `ExtractField` outright, so
//! the derived-MIR channel is structurally blind here and no body can flip.

#![allow(dead_code)]

struct H {
    x: (i64, i64),
    n: u8,
}

static Y: H = H { x: (5, 6), n: 1 };

// The by-value twin: ALREADY clean before this wave, and the differential-bearing control. The
// holder is a param, so `map_ty` registers it in the signature walk before the read.
pub fn now(h: H) -> i64 {
    h.x.0
}

// THE LANE, spelling 1: a `NamedConst` static holder, registered by nothing before the read.
pub fn from_static() -> i64 {
    Y.x.0
}

// THE LANE, spelling 2: the holder behind a shared reference.
pub fn through_ref(h: &H) -> i64 {
    (*h).x.1
}

// THE LANE, spelling 3: the `&self` receiver, which is spelling 2 written the way real code
// writes it. This is the `generic-default-type-params::{impl#2}::bar` corpus shape, where the
// refusal cascaded into six further tag kinds because `let (i, c) = self.a` left both bindings
// unbound and every use of them failed too.
struct G {
    a: (isize, u8),
}

impl G {
    pub fn destructure(&self) -> isize {
        let (i, _c) = self.a;
        i
    }
}

// The EMPTY-tuple exclusion is pinned SEPARATELY, in
// `trust_ir_lower_tuple_field_empty_declines.rs`: it must still push its tag, which is a
// compile ERROR under `=strict` and so cannot share a file with the positives above.

fn main() {}
