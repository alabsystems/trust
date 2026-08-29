//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **I5 CONTROL 3 — THE CONST FIXTURE (CTFE COVERAGE).**
//! (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7.)
//!
//! The increment's acceptance criterion, verbatim:
//!
//! > **the const fixture** — `const X: u64 = f();` must traverse the gate.
//!
//! WHY A CONST, AND NOT JUST A CALL. The design places the faithfulness gate in
//! `clean_origin_mir(def)` as the **sole constructor** of a Clean-origin `Body`,
//! called by BOTH the `optimized_mir` and `mir_for_ctfe` provider arms,
//! precisely so that:
//!
//!   * compile-time evaluation is covered — a `const` never reaches
//!     `optimized_mir`, so a gate installed only there would be bypassed by
//!     every constant in the program, and the value would still be baked into
//!     the binary;
//!   * **no verification switch can disable it.** The gate is a
//!     compilation-correctness check on emitted code, not an obligation. This
//!     file is compiled with `-Z trust-verify=off` ON PURPOSE: when I5 lands,
//!     the gate must still run here. A gate that vanishes under
//!     `-Z trust-verify=off` is not a gate, it is a lint.
//!
//! ============================================================================
//! THIS FIXTURE IS GREEN AND ASSERTS THE CTFE **VALUE**, not merely that the
//! crate compiles — hence `run-pass` and the `assert_eq!` below.
//!
//! MEASURED 2026-08-22 on stage2 ec4783d80: the crate builds under
//! `-Z trust-verify=off`, and the produced binary exits 0 with `X == 6`. The
//! const reaches `inner_mir_for_ctfe`, the body is constructed and gated by
//! `clean_origin_mir`, and the gated value is baked into the binary. The gate
//! does NOT vanish under `-Z trust-verify=off`, which is the property this file
//! was written to hold.
//!
//! THE VISIBILITY DECISION IS SETTLED, AND THE EXPECTATION IT BLOCKED IS GONE.
//! This file used to pin `E0603` on the call below, on the strength of a mint
//! that planted `Visibility::Restricted`. The mint now plants
//! `Visibility::Public` (`rustc_resolve/src/build_reduced_graph.rs`,
//! `trust_mint_clean_island_decls`), so `crate::m::f` is nameable from crate
//! root exactly as `Crate.m.f` already was. MEASURED 2026-08-22: no `E0603` is
//! emitted here. **DO NOT MAKE THIS FILE GREEN BY MOVING THE CONST INTO `m`**
//! — the crate-root/`m` boundary is the whole point of the shape — and do not
//! drop `-Z trust-verify=off` to get a green.
//!
//! Never spell the annotation sigil literally in this prose: compiletest scans
//! EVERY line with a bare regex (`src/tools/compiletest/src/errors.rs:141`), so a
//! quoted sigil in a comment becomes a real, unsatisfiable expectation.
//!
//! THE TWO THINGS THAT WOULD HAVE BROKEN HERE FIRST — **BOTH ARE NOW FIXED**:
//!
//!   1. `hir_body_const_context` is called unconditionally on both provider
//!      arms (`rustc_mir_transform/src/lib.rs`), and it reads HIR. In
//!      `inner_mir_for_ctfe` its `None` arm is a hard
//!      `bug!("mir_for_ctfe called on non-const {def:?}")`. FIXED: the
//!      `clean_origin_mir` gate call is now the VERY FIRST statement of
//!      `inner_mir_for_ctfe` — before `is_constructor` and before
//!      `hir_body_const_context` — so a Clean-origin def returns its gated body
//!      and never reaches the `bug!`. The sibling call is at the top of
//!      `optimized_mir`, and `promoted_mir` (which the metadata encoder demands
//!      once a def is in `mir_keys`, and whose ordinary path reaches
//!      `mir_borrowck` -> `typeck` -> HIR) has its own early return.
//!   2. `mir_keys` seeds from `tcx.hir_body_owners()`, which a Clean-origin def
//!      is not. FIXED: `mir_keys` now also inserts every def the
//!      `clean_origin_mir::is_clean_origin` predicate accepts.
//!
//! BOTH OF THOSE ARE NOW REACHED RATHER THAN MERELY FIXED: the mint landed in
//! 7b5c5535b3, so `is_clean_origin` is true for `m::f` here, `mir_keys` carries
//! it, and the CTFE arm answers for it — which is what the `assert_eq!` below
//! observes end to end.
//!
//! THE SHAPE HERE IS NOT ARBITRARY — it was RETARGETED (2026-08-19) after the
//! fragment was measured. This fixture used to read `def f : UInt64 := 6` with
//! `const X: u64 = f();`, a nullary constant. That shape is the one the kernel
//! **refuses**: `tests/e6-fragment-probe/` runs the same comparison in the
//! opposite direction and records every `ConstantUint` probe as
//! `defeq-rejected` (f06-f09) or `unproved` (f04), while `Projection`
//! discharges (d01-d05, d08, d09). A const fixture written on the constant
//! shape would therefore have failed the gate for a reason that has nothing to
//! do with CTFE, and would have been "fixed" by weakening the gate. It is a
//! two-parameter projection called with constant arguments instead: the CTFE
//! coverage this fixture owns is unchanged, and the shape is one the kernel
//! demonstrably admits.
//! ============================================================================

mod m {
    clean {
        def f (a : UInt64) (b : UInt64) : UInt64 := a
    }
}

// MUST traverse the faithfulness gate at CTFE time, with verification OFF.
const X: u64 = crate::m::f(6, 7);

fn main() {
    assert_eq!(
        X, 6,
        "the CTFE-evaluated Clean-origin body must be the projection the Clean \
         `def` denotes (parameter 0), not the second argument"
    );
}
