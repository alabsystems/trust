//! REAL-MIR rows for the if-without-else SKIP-EDGE fill of the single-switch
//! branch merge (`guards::single_switch_branch_merge_definitions`).
//!
//! ```text
//! pub fn h_stale(a: u64, b: u64, k: u8, small: u32) -> u64 {
//!     let mut x: u64 = 1;
//!     x = a % b;
//!     match k { 0 => x = u64::from(small) + 1, 1 => x = u64::from(small) + 2, _ => {} }
//!     x + 2                                               // line 9
//! }
//! pub fn h_stale2(a: u64, b: u64, k: u8, small: u32) -> u64 {
//!     let mut x: u64 = 1;
//!     x = a % b;
//!     if k == 0 { x = u64::from(small) + 1; }
//!     x + 2                                               // line 15
//! }
//! pub fn h_cast3(a: u64, b: u64, k: bool, small: u32) -> u64 {
//!     let mut x: u64 = 1;
//!     x = a % b;
//!     if k { x = small as u64; }
//!     x + 2                                               // line 21
//! }
//! ```
//!
//! The skip edge runs straight from the switch block to the join, so its value
//! for `x` is the switch block's EXIT value. The fill took it from
//! `incoming[switch]`, the block's ENTRY state (`x == 1`), and excluded only the
//! names the block had an EXTRACTED def for. Unsigned non-constant `Rem` is a
//! declined def, so the block's own write `x = a % b` was invisible, the stale
//! `x == 1` entered the merged `Ite`, and the reachable overflow (`a = MAX - 1`,
//! `b = MAX`, a non-taken arm: `x = MAX - 1`) PROVED. `h_cast3` proved on stage1
//! `7be75e9a80`; `h_stale`/`h_stale2` proved once the Call-hop admission
//! (MATCH-ARM-CALL-CHAIN) let their merge run.
//!
//! The fill's purpose (an ancestor-block initialiser the switch block does not
//! write, `if c { lo = 0 } hi - lo`) is pinned by the unit rows
//! `if_without_else_ancestor_init_recovers_ite` and
//! `chained_skip_join_ite_propagates_to_downstream_join`
//! (`generate/path_definition_map_tests.rs`): both still pass, and both fail with
//! the fill disabled.
//!
//! Fixtures: the compiler's own extracted verification input, captured with
//! `trustc --edition 2021 --crate-type lib -Ztrust-verify=on
//! -Ztrust-dump=mir:<dir> skip_fill_stale.rs` (stage1 `7be75e9a80`), minified.

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const H_STALE: &str = include_str!("fixtures/skip_fill_stale_h_stale_mir.json");
const H_STALE2: &str = include_str!("fixtures/skip_fill_stale_h_stale2_mir.json");
const H_CAST3: &str = include_str!("fixtures/skip_fill_stale_h_cast3_mir.json");

/// VC generation and the solver search both run on this thread; libtest's
/// default 2 MiB is not enough for the recursive `Formula` walks.
const SOLVER_STACK_BYTES: usize = 32 * 1024 * 1024;

fn add_overflow_verdicts(json: &'static str, line: u32) -> Vec<VerificationResult> {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let func: VerifiableFunction =
                serde_json::from_str(json).expect("fixture MIR must deserialize");
            let vcs: Vec<_> = trust_vcgen::generate_vcs(&func)
                .into_iter()
                .filter(|vc| {
                    matches!(vc.kind, VcKind::ArithmeticOverflow { .. })
                        && vc.location.line_start == line
                })
                .collect();
            assert!(
                !vcs.is_empty(),
                "{}: no overflow obligation at line {line}; an absent obligation is not a \
                 discharged one",
                func.name
            );
            let router = test_router::deterministic_test_router();
            router.verify_all(&vcs).into_iter().map(|(_, r)| r).collect()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

/// Refuted, not merely undecided: with the stale fill gone `x` on the skip arm
/// is the free `a % b`, and the solver has the real counterexample.
fn assert_refuted(json: &'static str, line: u32) {
    for verdict in add_overflow_verdicts(json, line) {
        assert!(
            matches!(verdict, VerificationResult::Failed { .. }),
            "line {line}: `x + 2` OVERFLOWS at a = u64::MAX - 1, b = u64::MAX on the skip \
             arm; anything but a refutation hides it; got {verdict:?}"
        );
    }
}

#[test]
fn a_switch_block_rem_write_is_not_filled_from_entry_on_a_match() {
    assert_refuted(H_STALE, 9);
}

#[test]
fn a_switch_block_rem_write_is_not_filled_from_entry_on_an_if() {
    assert_refuted(H_STALE2, 15);
}

#[test]
fn a_switch_block_rem_write_is_not_filled_from_entry_on_a_cast_arm() {
    assert_refuted(H_CAST3, 21);
}
