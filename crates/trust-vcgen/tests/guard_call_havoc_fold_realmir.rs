//! REAL-MIR regression for preview3 R3 (GUARD-CALL-HAVOC-FOLD, 2026-10-10): a
//! `format!` of the divisor on an early-return branch made every call in the body
//! havoc the divisor, so the `== 0` guard no longer reached the division.
//!
//! ```text
//! pub struct Cfg { pub heads: usize, pub groups: usize }
//! pub fn guarded_fmt_divisor(c: &Cfg) -> Result<usize, String> {
//!     if c.groups == 0 { return Err(String::new()); }
//!     if !c.heads.is_multiple_of(c.groups) { return Err(format!("{}", c.groups)); }
//!     Ok(c.heads / c.groups)                                         // line 7
//! }
//! ```
//!
//! (full source: `fixtures/guard_call_havoc_fold/guard_call_havoc_fold.rs`). This is
//! the nn-glm5 `config.rs:162` / nn-qwen3 `config.rs:108` `num_kv_groups` shape: its
//! DivisionByZero row and hardened twin were REFUTED with `divisor = 0` on stage1
//! `ed578e1a5` and were not in preview2 (`c797f90c1`).
//!
//! The `format!` lowers to `_12 = &(*_1).1; _11 = (move _12,); _21 = copy (_11.0)`.
//! `_21` is a reference LOADED FROM MEMORY (a tuple field), so CALL-HAVOC-ESCAPE-2
//! (`path_defs::stored_ref_pointee_names`) havocked `_21*` at every call — and the
//! name mint folds `*_21` to its referent `(*_1).1`, spelled `c*.1`. So the call
//! `is_multiple_of` (block 3, BEFORE the format, on the path to the division)
//! rebound `c*.1` to the fresh `c*.1#s3_t`, and the divisor read after it was
//! unconstrained. The same alias spelled `let r = &c.groups` (a retagged borrow) was
//! already kept by the fold invariant: `(*_1).1` is one `Deref` of a pinned shared
//! parameter. The fix asks that same question of a folded stored reference
//! (`path_defs::ref_local_folds_to_unstored_place`).
//!
//! The adversarial rows must stay NOT proved: `unguarded_fmt_divisor` never checks the
//! divisor, and `guard_then_mut_call` really zeroes it through `&mut` after the guard
//! (the ordinary call-havoc list, untouched by the fix).
//!
//! Every fixture is the compiler's OWN extracted verification input, captured with
//! `trustc --edition 2021 --crate-type lib -Ztrust-verify=on -Ztrust-dump=mir:<dir>
//! guard_call_havoc_fold.rs` (preview3 stage1 `ed578e1a5`, default optimisation),
//! minified, with the sysroot source path rewritten to `<sysroot-src>/` and the dump
//! directory stripped.

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const GUARDED_FMT_DIVISOR: &str =
    include_str!("fixtures/guard_call_havoc_fold/guarded_fmt_divisor.json");
const GUARDED_FMT_OTHER: &str =
    include_str!("fixtures/guard_call_havoc_fold/guarded_fmt_other.json");
const UNGUARDED_FMT_DIVISOR: &str =
    include_str!("fixtures/guard_call_havoc_fold/unguarded_fmt_divisor.json");
const GUARD_THEN_MUT_CALL: &str =
    include_str!("fixtures/guard_call_havoc_fold/guard_then_mut_call.json");

/// VC generation and the solver search both run on this thread; libtest's default
/// 2 MiB is not enough for the recursive `Formula` walks.
const SOLVER_STACK_BYTES: usize = 32 * 1024 * 1024;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

/// The `DivisionByZero` verdicts at source line `line`, decided by the real
/// in-process ay. An absent obligation fails the test: it is not a discharged one.
fn divzero_rows_at(json: &'static str, line: u32) -> Vec<VerificationResult> {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let func = load(json);
            let vcs: Vec<_> = trust_vcgen::generate_vcs(&func)
                .into_iter()
                .filter(|vc| {
                    matches!(vc.kind, VcKind::DivisionByZero) && vc.location.line_start == line
                })
                .collect();
            assert!(
                !vcs.is_empty(),
                "{}: no DivisionByZero obligation at line {line}; an absent obligation is \
                 not a discharged one",
                func.name
            );
            let router = test_router::deterministic_test_router();
            router.verify_all(&vcs).into_iter().map(|(_, r)| r).collect()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread")
}

#[test]
fn a_guarded_divisor_formatted_on_an_early_return_branch_is_proved_nonzero() {
    let rows = divzero_rows_at(GUARDED_FMT_DIVISOR, 7);
    assert!(rows.iter().all(VerificationResult::is_proved), "{rows:?}");
}

#[test]
fn control_formatting_the_other_field_is_proved() {
    let rows = divzero_rows_at(GUARDED_FMT_OTHER, 13);
    assert!(rows.iter().all(VerificationResult::is_proved), "{rows:?}");
}

#[test]
fn adversarial_an_unguarded_divisor_formatted_the_same_way_is_refuted() {
    let rows = divzero_rows_at(UNGUARDED_FMT_DIVISOR, 19);
    assert!(rows.iter().all(|r| matches!(r, VerificationResult::Failed { .. })), "{rows:?}");
}

#[test]
fn adversarial_a_call_that_zeroes_the_divisor_after_the_guard_is_not_proved() {
    let rows = divzero_rows_at(GUARD_THEN_MUT_CALL, 28);
    assert!(rows.iter().all(|r| !r.is_proved()), "{rows:?}");
    // `zero(c)` with `c.heads == 0` reaches `0 / 0`: a reachable counterexample exists.
    assert!(rows.iter().any(|r| matches!(r, VerificationResult::Failed { .. })), "{rows:?}");
}
