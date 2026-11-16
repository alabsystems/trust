//@ revisions: liars holds userpow
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type=lib
//@[liars] check-fail
//@[holds] check-pass
//@[userpow] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `pow`'s overflow row for a symbolic exponent (POW-SYMEXP-1).
//!
//! `OverflowCall::Pow`'s symbolic-exponent arm (`trust_vcgen`'s
//! `v2_overflow_call_body`, since `576db732cd`, 2026-07-24) built its violation as
//! `base >= 2 AND exp >= W` (`W - 1` when signed). That condition GUARANTEES an
//! overflow; it is not one every overflow satisfies, so as the
//! satisfiable-iff-violation body it made the row UNSAT — `overflow:mul` PROVED,
//! clean-kernel `Certified` — for any negative base and for any guard that bounds
//! the exponent below the width. Every `liars` function panics with "attempt to
//! exponentiate with overflow" for some argument (`pow_symbolic_exponent_overflow_run.rs`
//! runs three of them): `3u32.pow(21)`, `(-2i32).pow(32)`, `1000u64.pow(7)`,
//! `(-3i32).pow(21)`; `klit` panics on every call. `strict_pow` takes the same row.
//!
//! The DEFAULT policy is the one that discriminates: `certify` and `memory-safe`
//! already refuse every function here, but only through the separate
//! `runtime_checked` panic-freedom row of the bundled
//! `core::num::imp::overflow_panic::pow`; the false overflow row itself was
//! PROVED in every policy and with `-Coverflow-checks` on or off (the scout's
//! policy x overflow-checks matrix on the same compiler).
//!
//! BEFORE (the stage 1 of `ec03f72395`, `scratchpad/stage1-w15r`, measured
//! 2026-10-05 with exactly these revisions' flags plus `-Zui-testing
//! -Zdeduplicate-diagnostics=no --emit=metadata --error-format=json
//! -Ztrust-verify-output=json`): `liars` exits 1, but its only 4 errors are the
//! two pinned refusals `g33` and `ctl_pos_b` (already refuted, at `b = 2, e = 32`
//! and `b = 2, e = 31`: exactly the old formula's edge). The 16 liars get NO error
//! — 32 of the 36 annotations below are missing — and every liar's
//! `overflow:mul` row is `proved` with clean-kernel `Certified` /
//! `KernelRechecked` evidence (its panic-freedom row `runtime_checked`). `holds`
//! exits 0 with both overflow rows `proved`.
//!
//! AFTER (predicted before the build; it held, MEASURED 2026-10-06 on the stage 1 of `9e11546767`): the body is exact and
//! linear (an interval of fitting bases per exponent, plus `exp >= W AND |b| >= 2`;
//! a literal base is `exp >= t` for its least overflowing exponent `t`), so every
//! liar's row is refuted with an overflowing pair and the default policy refuses
//! it: two errors per liar, annotated below. `safe2` (`e < 32`, `2^31` fits u32)
//! and `safe2i` (`e < 31`, `2^30` fits i32) stay proved, so `holds` exits 0.
//! The annotations were checked on the BEFORE compiler against a twin of this file
//! whose 16 liar bodies are replaced, line for line, by shapes it already refutes
//! (`2i32.pow(e)`, `if e < 33 { b.pow(e) }`, `2i32.pow(40)`, ...): exit 1 with 36
//! errors, every one on an annotated line with the annotated text, none missing
//! and none unexpected (the warnings are not required: `dont-require-annotations`).
//!
//! `userpow` (2026-10-06, the integration review of POW-SYMEXP-1): a USER function
//! or method that is merely NAMED `pow` owes no overflow row — its body is XOR here
//! and cannot overflow. `trust_vcgen`'s `overflow_arith_call` classified a callee as
//! core's `pow` by its last path segment alone, so each call below was charged std's
//! `overflow:mul` row over the user function's own arguments. The fix requires the
//! authenticated `core::num::<impl iN/uN>::pow` owner, the recognizer `strict_pow`
//! already takes. BEFORE, measured 2026-10-06 with this revision's flags plus
//! `--cfg userpow -Zui-testing -Zdeduplicate-diagnostics=no --emit=metadata
//! -Ztrust-verify-output=json`: on the stage 1 of `9e11546767` (the exact body)
//! `userpow` exits 1 with 8 errors — `up`, `upg`, `fp` and `fp2` each `overflow:mul`
//! failed (ay-in-process) with counterexamples such as `e = 32` (`fp`) and
//! `e = 2, m = 65536` (`upg`); on the stage 1 of `dc15b882f6` (the old body) it
//! exits 1 with the 2 errors of the unguarded `up` alone (refuted at `e = 32,
//! m = 2`), while `upg`, `fp` and `fp2` read `overflow:mul` `proved` with
//! clean-kernel evidence, for an operation the program never performs. AFTER: no
//! call mints a `pow` row and the revision compiles.

// Negative literal bases: `(-2i32)^31 == i32::MIN` fits, `(-2i32)^32` does not.
#[cfg(liars)]
pub fn lie_neg(e: u32) -> i32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::lie_neg`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::lie_neg`
    (-2i32).pow(e)
}

#[cfg(liars)]
pub fn n2(e: u32) -> i32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::n2`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::n2`
    (-2i32).pow(e)
}

#[cfg(liars)]
pub fn n3(e: u32) -> i64 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::n3`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::n3`
    (-3i64).pow(e)
}

// An exponent guard below the width does not bound the power: `3u32.pow(21)`.
#[cfg(liars)]
pub fn lie_guard(b: u32, e: u32) -> u32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::lie_guard`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::lie_guard`
    if e < 32 { b.pow(e) } else { 0 }
}

#[cfg(liars)]
pub fn upow(b: u32, e: u32) -> u32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::upow`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::upow`
    if e < 32 { b.pow(e) } else { 0 }
}

#[cfg(liars)]
pub fn ipow(b: i32, e: u32) -> i32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::ipow`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::ipow`
    if e < 31 { b.pow(e) } else { 0 }
}

// `1000u64.pow(7)`.
#[cfg(liars)]
pub fn upow64(b: u64, e: u32) -> u64 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::upow64`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::upow64`
    if e < 8 { b.pow(e) } else { 0 }
}

// `(-3i32).pow(21)`.
#[cfg(liars)]
pub fn ipow_neg(b: i32, e: u32) -> i32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::ipow_neg`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::ipow_neg`
    if b < 0 && e < 31 { b.pow(e) } else { 0 }
}

// The same guard as a precondition.
#[cfg(liars)]
pub fn upow_req(b: u32, e: u32) -> u32
//[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::upow_req`
//[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::upow_req`
    requires e < 32
{
    b.pow(e)
}

#[cfg(liars)]
pub fn negb(b: i32, e: u32) -> i32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::negb`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::negb`
    if b < 0 { b.pow(e) } else { 0 }
}

// A literal base under an exponent guard: `3^21 > u32::MAX`.
#[cfg(liars)]
pub fn c3(e: u32) -> u32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::c3`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::c3`
    if e < 32 { 3u32.pow(e) } else { 0 }
}

// `b < 2` admits every negative base.
#[cfg(liars)]
pub fn neg_b(b: i32, e: u32) -> i32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::neg_b`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::neg_b`
    if b < 2 { b.pow(e) } else { 0 }
}

// A constant exponent above the width with a negative symbolic base.
#[cfg(liars)]
pub fn kneg40_lit(x: i64) -> i64 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::kneg40_lit`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::kneg40_lit`
    if x < 0 { x.pow(70) } else { 0 }
}

// Both operands literal: panics on every call.
#[cfg(liars)]
pub fn klit() -> i32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::klit`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::klit`
    (-2i32).pow(40)
}

// `strict_pow` takes the same row.
#[cfg(liars)]
pub fn spn(e: u32) -> i32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::spn`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::spn`
    (-2i32).strict_pow(e)
}

#[cfg(liars)]
pub fn spg(b: u32, e: u32) -> u32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::spg`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::spg`
    if e < 32 { b.strict_pow(e) } else { 0 }
}

// Pinned refusals, refused before and after: `2u32.pow(32)` and `2i32.pow(31)`.
#[cfg(liars)]
pub fn g33(b: u32, e: u32) -> u32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::g33`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::g33`
    if e < 33 { b.pow(e) } else { 0 }
}

#[cfg(liars)]
pub fn ctl_pos_b(b: i32, e: u32) -> i32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `pow_symbolic_exponent_overflow::ctl_pos_b`
    //[liars]~^^ ERROR Trust strict verification failed for `pow_symbolic_exponent_overflow::ctl_pos_b`
    if b > -2 { b.pow(e) } else { 0 }
}

// Controls: a guard that excludes every overflow stays proved.
#[cfg(holds)]
pub fn safe2(e: u32) -> u32 {
    if e < 32 { 2u32.pow(e) } else { 0 }
}

#[cfg(holds)]
pub fn safe2i(e: u32) -> i32 {
    if e < 31 { 2i32.pow(e) } else { 0 }
}

// A user function or method NAMED `pow` is not core's `pow` (`userpow`).
#[cfg(userpow)]
pub struct M(pub u32);

#[cfg(userpow)]
impl M {
    pub fn pow(&self, e: u32) -> u32 {
        e ^ self.0
    }
}

#[cfg(userpow)]
pub fn pow(b: i32, e: u32) -> i32 {
    b ^ (e as i32)
}

#[cfg(userpow)]
pub fn up(m: &M, e: u32) -> u32 {
    m.pow(e)
}

#[cfg(userpow)]
pub fn upg(m: &M, e: u32) -> u32 {
    if e < 32 { m.pow(e) } else { 0 }
}

#[cfg(userpow)]
pub fn fp(e: u32) -> i32 {
    if e < 40 { pow(-2, e) } else { 0 }
}

#[cfg(userpow)]
pub fn fp2(b: u32, e: u32) -> i32 {
    if e < 31 { pow(b as i32, e) } else { 0 }
}
