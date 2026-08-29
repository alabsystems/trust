//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Regression for the CTFE-freeze NARROWING: the MIR-side oracle must decline an unevaluated
//! const because its evaluation can reach a LOCAL body, never because of how rustc happened to
//! SPELL its initializer. Sibling of `trust_ir_lower_static_ctfe_no_cycle.rs`, which pins the
//! other direction — that the local shapes still decline and still compile.
//!
//! WHAT WENT WRONG. The freeze (`trust_mir_extract::ctfe_reentrancy`) is entered once at the
//! `mir_built` seam, which correctly answers *"am I inside `mir_built`"*. Its first form answered
//! the second half of the question — *"can THIS const's CTFE demand a local `mir_built`"* — by
//! proxy, keying on `matches!(c, mir::Const::Unevaluated(..))`. That proxy is not the cycle class:
//!
//!   * `pub const BITS: usize = 8` — an integer LITERAL. Built MIR holds `mir::Const::Val(8)`,
//!     which `try_to_bits` reads with NO query traffic, so the guard never sees it. It survived
//!     for a reason that has nothing to do with cycles.
//!   * `pub const MAX: i8 = i8::MAX` — a PATH. Built MIR keeps `mir::Const::Unevaluated`, so the
//!     guard declined it, the operand degraded to `ConstValue::OpaqueScalar` -> `Inst::Undef`,
//!     and the differential reported `MIR oracle carries a LIVE havoc (... offender: fn MAX undef
//!     ty i8)` and refused to sample the body. But `core::num::<impl i8>::MAX` is a FOREIGN def
//!     whose `mir_for_ctfe` comes from the metadata decoder — it can demand no local query at all.
//!
//! The two consts differ only in the spelling rustc chose. MEASURED cost of conflating that with
//! the cycle class, on the 2000-file ui sample: **132 Agreed rows**, against **zero** prevented
//! compile failures (`file_outcomes` was byte-identical with the freeze present and absent; the
//! freeze's entire measured benefit is on `library/core`, which is not in that corpus).
//!
//! It was also a MANUFACTURED DISAGREEMENT, which is why it cost coverage rather than precision:
//! the two lanes of the SAME differential, inside the SAME hook invocation, used DIFFERENT
//! predicates. The THIR producer gates on LOCALITY (`trust_thir_lower`'s `lower_named_const` and
//! `eval_nonlocal_scalar_const`: `if def_id.is_local() { … }`) and consults `frozen()` nowhere, so
//! it kept computing `127` for `i8::MAX` while this side emitted a havoc. The fix gives the MIR
//! side the locality gate the THIR side always had, so both ask one question.
//!
//! WHAT THIS FILE CAN AND CANNOT ASSERT. `check-pass` asserts the non-negotiable half: no shape
//! below is an `error[E0391]`. It cannot see the differential's verdict — that instrument is the
//! `RUSTC_LOG` event stream the producer scorecard parses, not compiler stderr. The witness pair's
//! CLASSIFICATION is therefore measured by the sweep, not here; what is pinned here is that the
//! narrowing never turns a compiling program into a failing one, which is the only direction in
//! which this change could be strictly worse than the regression it repairs.

// ------------------------------------------------------------------ the witness pair
// Verbatim the shape of `tests/ui/numbers-arithmetic/num-wrapping.rs`, which alone lost 20 of the
// 132 rows. `BITS` was Agreed throughout; `MAX`/`MIN` were the havoc.
pub mod i8w {
    pub const BITS: usize = 8; // LITERAL   -> mir::Const::Val      -> always survived
    pub const MAX: i8 = i8::MAX; // PATH, FOREIGN -> Const::Unevaluated -> was declined
    pub const MIN: i8 = i8::MIN;
}

// The same discriminator with no module indirection, and across widths/signedness so the recovery
// is not read off a single arm of `convert_const_operand`'s type match.
pub fn direct_i8_max() -> i8 {
    i8::MAX
}
pub fn direct_u64_max() -> u64 {
    u64::MAX
}
pub fn direct_i128_min() -> i128 {
    i128::MIN
}
pub fn direct_char_max() -> char {
    char::MAX
}
pub fn direct_usize_bits() -> u32 {
    usize::BITS
}

// ------------------------------------------------------------------ the local control
// A LOCAL const is still declined — the narrowing does not touch that half, and must not. The
// producer's THIR side defers it to `resolve_pending_consts` at the `analysis` seam and the MIR
// side keeps it opaque, so the body stays a coverage gap rather than becoming a value asymmetry.
pub const LOCAL_SRC: u32 = 7;
pub fn read_local_const() -> u32 {
    LOCAL_SRC
}

// ------------------------------------------------------------------ the E0391 guard
// The const twin of the `library/core` cycle (`core::task::wake`'s `RawWaker::NOOP`), restated
// here so this file fails on its own if the narrowing is ever widened to let a LOCAL def through.
// `NOOP` is an assoc const whose value holds `&VTABLE`, and `VTABLE` is a const whose closure
// names `RW::NOOP`; `const_eval_global_id_for_typeck(NOOP)` demands `mir_for_ctfe(NOOP)` ->
// `mir_borrowck` -> the nested closure's `mir_built`, closing the cycle. Both of the measured
// cycle edges are LOCAL defs, which is exactly why a locality-keyed decline keeps them broken.
pub struct VT {
    pub clone: fn(*const ()) -> RW,
}
#[derive(Copy, Clone)]
pub struct RW {
    pub data: *const (),
    pub vtable: &'static VT,
}
impl RW {
    pub const NOOP: RW = {
        const VTABLE: VT = VT { clone: |_| RW::NOOP };
        RW { data: core::ptr::null(), vtable: &VTABLE }
    };
}

// The sibling static shape, kept adjacent for the same reason: a local static's initializer CTFE
// reaches a local body through a sibling `const fn`, with no ancestry between them.
pub static S: u32 = g();
pub const fn g() -> u32 {
    let _p: *const u32 = &S;
    7
}

// ------------------------------------------------------------------ argument-driven dispatch
// The half of the narrowing whose COMPLETENESS is an ARGUMENT, not a measurement (see
// `convert::frozen_ctfe_may_reach_local_body`). Built MIR keeps the UNRESOLVED use-site
// projection — MEASURED: a built-MIR dump of the body below prints `const <LocalTy as Marker>::N`,
// and a foreign generic assoc const prints `const std::num::NonZero::<u32>::BITS`, i.e. def plus
// use-site args, unresolved. So a foreign trait's assoc const instantiated at a LOCAL type really
// does arrive at the guard as a NON-LOCAL `def` carrying a LOCAL type in `args`, and a
// locality-only narrowing would let its CTFE resolve onto a local impl. The `args` clause declines
// it; this shape exists so that decline has a compiling witness.
pub struct LocalTy;
pub trait Marker {
    const N: usize;
    // A defaulted body that dispatches back through `Self` is the shape the argument reaches
    // local code by; keep one here so the file exercises it and not just the projection spelling.
    const M: usize = Self::N + 1;
}
impl Marker for LocalTy {
    const N: usize = 3;
}
pub fn read_local_projection() -> usize {
    <LocalTy as Marker>::N
}
pub fn read_defaulted_projection() -> usize {
    <LocalTy as Marker>::M
}

// A FOREIGN generic assoc const at a FOREIGN argument — the control for the clause above. Nothing
// in its args names this crate, so it must NOT be declined.
pub fn foreign_generic_assoc_const() -> u32 {
    core::num::NonZero::<u32>::BITS
}

fn main() {}
