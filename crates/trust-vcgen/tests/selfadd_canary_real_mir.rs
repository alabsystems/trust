//! REAL-ARTIFACT regression guard for the SELF-REFERENTIAL DEFINITION that made a
//! guarded out-of-bounds index read `proved`.
//!
//! The fixture is the compiler's OWN extracted verification input, captured verbatim:
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> selfadd_guarded_index.rs
//! ```
//!
//! # What went wrong
//!
//! `22213ceec9` (2026-08-21, "TWO FALSE-PROVES CLOSED") modeled a bare
//! `Rvalue::BinaryOp` as wrapping via `Eq(dest, wrapping_binop_modular_ite(lhs, rhs))`,
//! without requiring `dest` and `lhs` to be DISTINCT symbols. On
//!
//! ```text
//! pub fn f(mut i: usize, a: &[i32; 8]) -> i32 { if i < 4 { i += 100; a[i] } else { 0 } }
//! ```
//!
//! they are the same version, so the block gained `i = if i+100 >= 2^64 { .. } else { i+100 }`
//! — i.e. `i == i + 100`, UNSAT for any nonzero addend. ONE unsatisfiable hypothesis
//! vacuously discharges EVERY obligation in the block, so `certify` reported
//! `functions_verified: 1, total_proved: 3, total_failed: 0` while the linked binary died
//! with `index out of bounds: the len is 8 but the index is 101`.
//!
//! The staleness filter in `guards.rs` could not catch it: it exempts a def's own LHS
//! from the clobber kill (`Some(v) != lhs`), which is exactly the self-referential shape.
//!
//! Both directions are pinned below: the contradictory def is gone, AND the bounds
//! obligation that must do real work is still emitted.

use trust_types::{Formula, VcKind, VerifiableFunction};

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
    let text = std::fs::read_to_string(format!("{path}{name}.json"))
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("canary MIR fixture `{name}` must deserialize: {e}"))
}

/// Every `Eq(Var(v), rhs)` in the formula where `v` occurs free in `rhs`.
///
/// Such an equality is a recurrence, not a definition. It is either a tautology
/// (`x == x`) or unsatisfiable (`x == x + k`); as a conjoined hypothesis the
/// second kind proves every obligation it accompanies.
fn self_referential_defs(f: &Formula, out: &mut Vec<String>) {
    if let Formula::Eq(l, r) = f
        && let Some(name) = l.var_name()
        && r.free_variables().iter().any(|v| v.as_str() == name)
    {
        out.push(format!("{l:?} == {r:?}"));
    }
    match f {
        Formula::And(cs) | Formula::Or(cs) => {
            for c in cs {
                self_referential_defs(c, out);
            }
        }
        Formula::Not(a) => self_referential_defs(a, out),
        Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Implies(a, b) => {
            self_referential_defs(a, out);
            self_referential_defs(b, out);
        }
        Formula::Ite(c, a, b) => {
            self_referential_defs(c, out);
            self_referential_defs(a, out);
            self_referential_defs(b, out);
        }
        _ => {}
    }
}

/// The guard `i < 4` must not survive `i += 100` as a fact about the SAME symbol.
#[test]
fn selfadd_emits_no_self_referential_definition() {
    let func = load("selfadd_guarded_index");
    let mut offenders = Vec::new();
    for vc in trust_vcgen::generate_vcs(&func) {
        let mut found = Vec::new();
        self_referential_defs(&vc.formula, &mut found);
        for f in found {
            offenders.push(format!("{:?} @ {:?}: {f}", vc.kind, vc.location));
        }
    }
    assert!(
        offenders.is_empty(),
        "a definition names its own destination — UNSAT hypotheses prove every \
         obligation in the block:\n  {}",
        offenders.join("\n  ")
    );
}

/// Laundering control: the refusal must cost a PROOF, never an OBLIGATION. A
/// silently dropped VC at `a[i]` is the same false proof by another route.
#[test]
fn selfadd_still_carries_an_obligation_at_the_index() {
    let func = load("selfadd_guarded_index");
    // `a[i]`, cols 67-71 of the one-line fixture.
    let at_index: Vec<_> = trust_vcgen::generate_vcs(&func)
        .into_iter()
        .filter(|vc| vc.location.col_start == 67 && vc.location.col_end == 71)
        .collect();
    assert!(
        !at_index.is_empty(),
        "`a[i]` must still raise an obligation; dropping it would re-hide the \
         out-of-bounds read the self-referential def used to discharge"
    );
    // TWO acceptable outcomes, deliberately. Today the entry.rs backstop degrades
    // this to `UnsupportedMir` (`Bool(true)` — SAT, preclassified Unknown, never
    // `proved`). Once the mint/kill fork is fixed, `i_pre != i#s2_0` makes the
    // hypotheses consistent and a REAL, refutable bounds obligation survives
    // instead. Demanding `UnsupportedMir` alone would pin the fail-closed
    // workaround in place and fail the root-cause fix — a test that blocks the
    // correct repair is worse than no test. Vacuity itself is covered above.
    assert!(
        at_index.iter().any(|vc| matches!(
            vc.kind,
            VcKind::UnsupportedMir { .. } | VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck
        )),
        "`a[i]` must carry either a real bounds obligation or the fail-closed \
         UnsupportedMir; anything else means the obligation was laundered: {:?}",
        at_index.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}
