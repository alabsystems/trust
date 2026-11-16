//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ check-pass
#![crate_type = "lib"]
//! A singleton `&str` capture must not be field-read at the thin placeholder `Ty::Ptr`.
//!
//! Inside a non-`move` closure, every use of a variable `a: &str` THROUGH the reference
//! (`a.len()`, `a.to_string()`, `a.contains(..)`, `takes(a)`) is truncated by rustc's capture
//! analysis to the single place `a[Deref]`, `ByRef(Immutable)`, with `upvar_tys[i] == &str`.
//! `try_lower_upvar_shared_ref_pointee` (the wave-UD lane) reads that capture as
//!
//!     %agg = Load { ty: Tuple(<mapped upvar_tys>), ptr: %0 }
//!     %p   = ExtractField { ty: Ptr, %agg, i }
//!
//! whose `ty: Ptr` is well-typed ONLY because G8/G9r demand every mapped capture be a thin
//! `Ty::Ptr`. Wave-FUC (b7702555be) punched a `fat_str_lane` exemption through both gates for
//! a ONE-element env whose sole capture is `&str` — mapped `FatPtr(Str)` — and left the
//! emission unchanged. The field is declared `fatptr<str>`, the read is annotated `ptr`, and
//! the value then rides `borrow_ptrs` as if it were a thin address. Two faces, one mint:
//!
//!     ExtractField           -> OperandTypeMismatch { op: "extract_field", role: "field",
//!                                                     expected: "fatptr<str>", actual: "ptr" }
//!     the value as a `&str` call argument -> CallArgTypeMismatch { expected: "fatptr<str>",
//!                                                                  actual: "ptr" }
//!
//! Measured on the sealed toolchain trust-11aae56c: every `*_face` below fails module
//! validation, and the SAME shape blocks `ny-claims` (`extract::aggregate::{closure#0}`,
//! `extract::flight_event::{closure#2}`) and `clap_builder` (`util::eq_ignore_case`, arg 1).
//!
//! THE FLAG POSTURE. Measured, this shape is NOT masked under `-Ztrust-verify=on`: `len_face`
//! alone reports the same `OperandTypeMismatch` there (the per-body verifier only
//! runtime-checks its one obligation and finalization still validates the module). It is kept
//! at `-Ztrust-verify=off -Ztrust-ir-lower=on` anyway, because that is the posture under which
//! module validation is pinned independent of whatever the per-body verifier does first — the
//! #189 lesson, where a strict-policy run proved nothing about module validation.
//!
//! WHAT THE FIX IS NOT. It does not spell the field `FatPtr(Str)` and keep the `borrow_ptrs`
//! registration (every consumer of that ledger Loads through a THIN address), and it does not
//! relax the validator. It REFUSES: the `fat_str_lane` exemption is removed, so G8 declines the
//! `&str` singleton exactly as it already declines its `&[u8]` twin (`slice_control`), the
//! closure body falls back to `UpvarRef(disjoint/projected capture)`, and the emitted
//! `ExtractField { ty: Ptr }` is once again equal to the tuple element BY CONSTRUCTION
//! (`upvar_env_field_is_by_ref_capture`). These bodies stop being lowered and, under
//! `-Ztrust-verify=on`, still fail closed as unmodelled — an unblock, not a green build.

/// The ExtractField face — the smallest reproducer.
pub fn len_face(a: &str) -> usize {
    let c = || a.len();
    c()
}

/// The CallArg face — the mistyped value shipped to a `fatptr<str>` parameter.
fn takes(s: &str) -> usize {
    s.len()
}
pub fn call_face(a: &str) -> usize {
    let c = || takes(a);
    c()
}

/// ny-claims' exact shape (`extract::aggregate`'s `cite`): a `let`-bound closure that owns
/// the capture through `to_string()`.
pub struct Citation {
    pub artifact: String,
    pub line: Option<usize>,
    pub detail: String,
}
pub fn ny_face(artifact: &str, n: usize) -> Citation {
    let cite = |line: Option<usize>, detail: String| Citation {
        artifact: artifact.to_string(),
        line,
        detail,
    };
    cite(Some(n), format!("{n} hits"))
}

/// Not `let`-bound-specific: an iterator closure fails identically.
pub fn iter_face(a: &str, v: &[u32]) -> Vec<String> {
    v.iter().map(|_| a.to_string()).collect()
}

/// Not parameter-specific: a local `&str` fails identically.
pub fn local_face() -> usize {
    let a: &str = "abc";
    let c = || a.len();
    c()
}

// ── negative controls: the refusal must stay narrow ──────────────────────────

/// The `&[u8]` twin: G8 (`upvar_is_thin`) already refuses it, so the body is declined and
/// the module stays valid. This is the posture the fix restores for `&str`.
pub fn slice_control(a: &[u8]) -> usize {
    let c = || a.len();
    c()
}

/// A second capture makes the env non-singleton: the exemption never applied.
pub fn two_capture_control(a: &str, n: &u32) -> usize {
    let c = || a.len() + (*n as usize);
    c()
}

/// `move`: the capture is `ByValue`, so it is the whole-variable arm's non-thin refusal.
pub fn move_control(a: &str) -> usize {
    let c = move || a.len();
    c()
}

/// Borrowing the variable itself (`&a`) captures `a` by ref: a thin `&&str` env field.
pub fn reborrow_control(a: &str) -> usize {
    let c = || {
        let r = &a;
        r.len()
    };
    c()
}

/// Autoref through `==` captures `a` itself, not `a[Deref]`: thin, and it still lowers.
pub fn eq_control(a: &str, b: &String) -> bool {
    let c = || *b == a;
    c()
}

/// A thin pointee: the lane's ordinary, well-typed case.
pub fn thin_control(a: &u32) -> u32 {
    let c = || *a + 1;
    c()
}

/// A by-VALUE (`FnOnce`) env: G9v reads the module's declared capture and refuses.
fn once<R>(f: impl FnOnce() -> R) -> R {
    f()
}
pub fn once_control(a: &str) -> usize {
    once(|| a.len())
}
