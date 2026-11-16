//! REAL-MIR falsification matrix for the havocked-callee-return reclassification.
//!
//! # What was wrong
//!
//! A `Terminator::Call` whose callee has no model writes its destination with
//! nothing constraining it. The destination is then a free variable of the
//! violation formula, the solver answers SAT by *choosing* a value for it, and
//! the obligation is reported REFUTED with a counterexample no execution can
//! produce. Measured on the fixtures below at the commit that introduced this
//! file, `100 / core::cmp::max(x, 1)` was refuted with
//!
//! ```text
//! [divzero] FAILED (ay-in-process); counterexample: _2 = 0, _3 = true, x = 0
//! ```
//!
//! — `max(0, 1) = 0`. That is the verifier accusing correct code with a witness
//! that is not a witness. An unmodelled callee means "I do not know", which is
//! UNKNOWN.
//!
//! # What this file pins
//!
//! Every fixture is the compiler's OWN extracted MIR, captured verbatim from
//! `tests/fixtures/hv_havoc_decline_fx.rs` with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> hv_havoc_decline_fx.rs
//! ```
//!
//! so the callee spellings under test (`core::cmp::max::<u32>`,
//! `core::mem::size_of::<u64>`, `core::num::<impl u32>::leading_zeros`) are the
//! ones the compiler actually emits.
//!
//! The matrix is symmetric on purpose — each DECLINE row is paired with a row
//! that must NOT move, and every one of those pairs was measured to separate:
//!
//! | direction | fixtures |
//! |---|---|
//! | unmodelled foreign call → divisor / addend / index: DECLINE | `hv_div_cmp_max`, `hv_add_cmp_min`, `hv_idx_cmp_min`, `hv_div_len_utf8` |
//! | `size_of`/`align_of` at a primitive: const-folded, PROVES | `hv_div_size_of`, `hv_div_align_of`, `hv_idx_size_of`, `hv_idx_align_of` |
//! | real bug, all operands LOCAL: still REFUTES | `hv_real_overflow`, `hv_real_divzero`, `hv_real_bounds` |
//! | SAME-CRATE callee: untouched (still refutes) | `hv_div_local_max` |
//! | modelled intrinsic pins the dest: untouched | `hv_div_leading_zeros` (refutes), `hv_idx_leading_zeros` (proves) |
//! | ANOTHER emitter's decline, swept for fail-closed polarity | `hv_slice_soft_len`, `hv_slice_soft_len_and_call` |
//!
//! The `hv_real_*` rows are the load-bearing half: reclassification must not
//! silence an obligation the verifier can actually decide.
//!
//! # Runtime oracle
//!
//! Every fixture's Rust body was compiled under STOCK rustc with
//! `-O -C debug-assertions=on`, `#[inline(never)]` and `black_box` inputs, and
//! run over its input domain inside `catch_unwind`. The DECLINE and PROVE rows
//! did not fault at any sampled input; the three `hv_real_*` rows and
//! `hv_div_leading_zeros` panic. `hv_real_divzero_via_call` also panics
//! (`core::cmp::min(0, 1) == 0`) and is reclassified to Unknown: that is a
//! COMPLETENESS loss the modularity boundary forces, recorded below as a
//! must-never-PROVE row rather than hidden. `hv_slice_soft_len` and
//! `hv_slice_soft_len_and_call` panic for every `end > v.len()`, first at
//! `(v.len(), end) = (0, 1)`.
//!
//! # This file is the ONLY coverage of the reclassification
//!
//! The `tests/trust-falsification` corpora do NOT reach it. Sweeping both at the
//! vcgen+ay layer — every `mutant/` and `proved/` body extracted with the HEAD
//! `trustc` and driven through the real `generate_vcs` + in-process ay — produced
//! ZERO `UnmodeledCalleeReturn` rows and a verdict-for-verdict identical result
//! to HEAD. A green falsification gate therefore says nothing about this pass;
//! the fixtures below are what tests it.
//!
//! One corpus fixture DOES discriminate a single condition: deleting the
//! same-crate exclusion in `callee_is_foreign_monomorphic` makes
//! `mutant/contract_skip_ensures_launder::caller` decline instead of refute, so
//! that mutant survives. The exclusion is load-bearing, and both that mutant and
//! `same_crate_callee_is_not_reclassified` below kill its removal.
use trust_types::{Formula, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

/// Stack for the generation/solver thread. Real extracted MIR carries deep
/// recursive `Formula` walks; the libtest default 2 MiB stack overflows on the
/// intrinsic fixtures (the same allowance `intrinsic_semantics_realmir` makes,
/// and for the same reason).
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/");
    let text = std::fs::read_to_string(format!("{path}{name}.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The machine-safety rows of `name`, each as `(kind_tag, verdict_tag)`.
///
/// `UnsupportedMir` rows are reported as they reach the compiler: it
/// preclassifies them to Unknown and never dispatches them to a solver (see
/// `generate::discharge::discharge_body_vcs`), so asking ay about one would
/// measure a question the pipeline does not ask.
fn safety_rows(name: &str) -> Vec<(String, String)> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let mut rows = Vec::new();
            for vc in &vcs {
                let tag = match &vc.kind {
                    VcKind::DivisionByZero => "divzero".to_string(),
                    VcKind::RemainderByZero => "remzero".to_string(),
                    VcKind::ArithmeticOverflow { .. } => "overflow".to_string(),
                    VcKind::IndexOutOfBounds => "bounds".to_string(),
                    VcKind::UnsupportedMir { kind, .. } => format!("decline:{kind}"),
                    _ => continue,
                };
                let verdict = if tag.starts_with("decline:") {
                    "UNKNOWN".to_string()
                } else {
                    let router = test_router::deterministic_test_router();
                    match router
                        .verify_all(std::slice::from_ref(vc))
                        .into_iter()
                        .next()
                        .expect("one verdict per VC")
                        .1
                    {
                        VerificationResult::Proved { .. } => "PROVED".to_string(),
                        VerificationResult::Failed { .. } => "REFUTED".to_string(),
                        other => format!("{other:?}").chars().take(24).collect(),
                    }
                };
                rows.push((tag, verdict));
            }
            rows
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

/// The single machine-safety row `name` is expected to have.
fn sole_row(name: &str) -> (String, String) {
    let rows = safety_rows(name);
    assert_eq!(
        rows.len(),
        1,
        "{name}: this fixture has exactly one machine-safety obligation; got {rows:?}"
    );
    rows.into_iter().next().expect("length checked")
}

/// Every fixture in this file, by name. Used by the fail-closed sweep below so a
/// fixture added to the matrix is covered by it automatically.
const ALL_FIXTURES: &[&str] = &[
    "hv_div_cmp_max",
    "hv_add_cmp_min",
    "hv_idx_cmp_min",
    "hv_div_len_utf8",
    "hv_real_overflow",
    "hv_real_divzero",
    "hv_real_bounds",
    "hv_div_local_max",
    "hv_div_leading_zeros",
    "hv_idx_leading_zeros",
    "hv_div_size_of",
    "hv_div_align_of",
    "hv_idx_size_of",
    "hv_idx_align_of",
    "hv_generic_size_of_index",
    "hv_real_divzero_via_call",
    "hv_slice_soft_len",
    "hv_slice_soft_len_and_call",
];

// ---------------------------------------------------------------------------
// FAIL-CLOSED POLARITY. The load-bearing invariant of the reclassification.
// ---------------------------------------------------------------------------

/// A VC is a VIOLATION formula: discharge means UNSAT. So every `UnsupportedMir`
/// row must carry `Bool(true)` — SAT, hence never discharged — exactly like the
/// other `UnsupportedMir` emitters in this crate.
///
/// `Bool(false)` would be UNSAT. Consumers that select rows by PROOF LEVEL
/// rather than by kind then read the row as PROVED, and `UnsupportedMir` is
/// `ProofLevel::L0Safety`: `trust_clean::whole_program::certify_function_in_graph`
/// and `::ensures_certified_modulo_3` both filter on `L0Safety` and hand
/// `vc.formula` to `vc_refute::check_refute_vc`, treating `RefutedModulo3` as
/// discharged. A declined row — one that means "I do not know" — would silently
/// certify the function.
///
/// The sweep covers EVERY fixture, so it also catches any other `UnsupportedMir`
/// emitter reached by this corpus, not just the reclassification. It found one:
/// `hv_slice_soft_len` reaches `panic_calls`'s soft-len arm, which built its
/// declined slice row with `Bool(false)` — and
/// `trust-clean/tests/unsupported_row_polarity_gate.rs` measures what that cost.
#[test]
fn every_unsupported_mir_row_carries_the_fail_closed_violation_formula() {
    let mut seen_decline = 0usize;
    let mut seen_other_emitter = 0usize;
    for name in ALL_FIXTURES {
        for (kind, formula) in unsupported_rows(name) {
            assert_eq!(
                formula,
                Formula::Bool(true),
                "{name}: UnsupportedMir row `{kind}` must carry the SAT (fail-closed) violation \
                 formula; an UNSAT one is read as DISCHARGED by the kind-blind kernel gates in \
                 trust_clean::whole_program"
            );
            if kind == "UnmodeledCalleeReturn" {
                seen_decline += 1;
            } else {
                seen_other_emitter += 1;
            }
        }
    }
    assert!(
        seen_decline >= 5,
        "the sweep must actually reach reclassified rows or it proves nothing; saw {seen_decline}"
    );
    assert!(
        seen_other_emitter >= 1,
        "the sweep must also reach an `UnsupportedMir` row this pass did NOT create, or it says \
         nothing about the other emitters; saw {seen_other_emitter}"
    );
}

/// The `(kind, formula)` of every `UnsupportedMir` row of `name`.
fn unsupported_rows(name: &str) -> Vec<(String, Formula)> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            trust_vcgen::generate_vcs(&func)
                .into_iter()
                .filter_map(|vc| match &vc.kind {
                    VcKind::UnsupportedMir { kind, .. } => Some((kind.clone(), vc.formula.clone())),
                    _ => None,
                })
                .collect::<Vec<_>>()
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

// ---------------------------------------------------------------------------
// DECLINE: an unmodelled FOREIGN call's return decides the obligation.
// ---------------------------------------------------------------------------

/// `100u32 / core::cmp::max(x, 1)`. `max(x, 1) >= 1` for every `x`, so no
/// execution divides by zero. The row must be a DECLINE, and in particular must
/// not be REFUTED — that was the census's `max(x, 1) = 0` witness.
#[test]
fn unmodelled_call_divisor_declines() {
    assert_eq!(
        sole_row("hv_div_cmp_max"),
        ("decline:UnmodeledCalleeReturn".to_string(), "UNKNOWN".to_string())
    );
}

/// `core::cmp::min(x, 10) + 1`, which is at most 11 and cannot overflow `u32`.
/// The OVERFLOW arm of the same defect.
#[test]
fn unmodelled_call_overflow_declines() {
    assert_eq!(
        sole_row("hv_add_cmp_min"),
        ("decline:UnmodeledCalleeReturn".to_string(), "UNKNOWN".to_string())
    );
}

/// `[1,2,3,4][core::cmp::min(x, 3)]`, always in bounds. The BOUNDS arm.
#[test]
fn unmodelled_call_bounds_declines() {
    assert_eq!(
        sole_row("hv_idx_cmp_min"),
        ("decline:UnmodeledCalleeReturn".to_string(), "UNKNOWN".to_string())
    );
}

/// `100usize / c.len_utf8()`. `len_utf8()` is in `1..=4` for every `char`, so
/// the divisor is never zero — a method call, not a free function, reaching the
/// same seam.
#[test]
fn unmodelled_method_divisor_declines() {
    assert_eq!(
        sole_row("hv_div_len_utf8"),
        ("decline:UnmodeledCalleeReturn".to_string(), "UNKNOWN".to_string())
    );
}

/// `&v[..end]` over an owned `Vec`: a DIFFERENT emitter's decline
/// (`panic_calls`'s soft-len arm), carried here so the polarity sweep above
/// reaches a row this pass did not create. The row stays a decline in this
/// lane — only its violation formula was wrong.
#[test]
fn owned_vec_soft_len_slice_declines() {
    assert_eq!(
        sole_row("hv_slice_soft_len"),
        ("decline:SliceBoundsCheck".to_string(), "UNKNOWN".to_string())
    );
}

/// Both passes on one body: this pass declines the divisor, and `panic_calls`
/// independently declines the slice. Generation must simply COMPLETE — a
/// crate-wide `debug_assert!` over every emitter's rows, added to this pass and
/// then reverted, aborted the compiler on exactly this shape.
///
/// It is not a guard against re-adding that assert: with the polarity of every
/// emitter now correct, such an assert would hold here. It pins the two-decline
/// interaction and keeps the shape in the corpus.
#[test]
fn a_foreign_decline_and_this_passs_decline_coexist() {
    assert_eq!(
        safety_rows("hv_slice_soft_len_and_call"),
        vec![
            ("decline:SliceBoundsCheck".to_string(), "UNKNOWN".to_string()),
            ("decline:UnmodeledCalleeReturn".to_string(), "UNKNOWN".to_string()),
        ]
    );
}

// ---------------------------------------------------------------------------
// MUST STILL REFUTE: real bugs whose operands are all LOCAL.
// ---------------------------------------------------------------------------

/// `x + 1` on `u32` overflows at `x == u32::MAX`. No call is involved, so the
/// reclassification must not touch it.
#[test]
fn local_operand_overflow_still_refutes() {
    assert_eq!(sole_row("hv_real_overflow"), ("overflow".to_string(), "REFUTED".to_string()));
}

/// `x / y` divides by zero at `y == 0`.
#[test]
fn local_operand_divzero_still_refutes() {
    assert_eq!(sole_row("hv_real_divzero"), ("divzero".to_string(), "REFUTED".to_string()));
}

/// `[1,2,3,4][i]` is out of bounds for `i >= 4`.
#[test]
fn local_operand_bounds_still_refutes() {
    assert_eq!(sole_row("hv_real_bounds"), ("bounds".to_string(), "REFUTED".to_string()));
}

/// A SAME-CRATE callee is deliberately outside the reclassification: its body is
/// available, so an undecided row there is a missing summary rather than the
/// modularity boundary, and the falsification corpus pins that reading
/// (`mutant/contract_skip_ensures_launder` indexes `a[idx(n)]` through a
/// same-crate `idx` and must keep refuting). `100 / hv_local_max(x, 1)` cannot
/// fault, so this row is a REMAINING false refutation, recorded as measured.
#[test]
fn same_crate_callee_is_not_reclassified() {
    assert_eq!(sole_row("hv_div_local_max"), ("divzero".to_string(), "REFUTED".to_string()));
}

// ---------------------------------------------------------------------------
// MODELLED callee: the dest is pinned, so nothing changes in either direction.
// ---------------------------------------------------------------------------

/// `100 / x.leading_zeros()` REALLY divides by zero for `x >= 0x8000_0000` (the
/// runtime oracle panics). `intrinsic_semantics` pins the dest to `0..=32`, so
/// the row is decidable and must keep its refutation — this is the control that
/// a modelled callee is never swept into the decline.
#[test]
fn modelled_intrinsic_keeps_its_refutation() {
    assert_eq!(sole_row("hv_div_leading_zeros"), ("divzero".to_string(), "REFUTED".to_string()));
}

/// `[0u8; 64][x.leading_zeros() as usize]` proves from the SAME pin
/// (`leading_zeros(x) <= 32 < 64`). The reclassification must not cost this
/// proof: a decline here would be a PROVED → UNKNOWN regression.
#[test]
fn modelled_intrinsic_keeps_its_proof() {
    assert_eq!(sole_row("hv_idx_leading_zeros"), ("bounds".to_string(), "PROVED".to_string()));
}

// ---------------------------------------------------------------------------
// size_of / align_of: compile-time constants of the INPUT PROGRAM.
// ---------------------------------------------------------------------------

/// `1024usize / core::mem::size_of::<u64>()` — a CLOSED, input-free body that
/// was refuted for division by zero (`_1 = 0`). `size_of::<u64>()` is 8 on every
/// target, so the fold makes the row provable rather than merely undecided.
#[test]
fn size_of_divisor_proves() {
    assert_eq!(sole_row("hv_div_size_of"), ("divzero".to_string(), "PROVED".to_string()));
}

/// `1024usize / core::mem::align_of::<u32>()`. The alignment of a primitive is
/// target-dependent and is NOT folded; `1 <= align_of::<T>() <= size_of::<T>()`
/// is enough to prove the divisor nonzero.
#[test]
fn align_of_divisor_proves() {
    assert_eq!(sole_row("hv_div_align_of"), ("divzero".to_string(), "PROVED".to_string()));
}

/// `[0u8; 16][core::mem::size_of::<u32>()]` — the same constant as an INDEX.
#[test]
fn size_of_index_proves() {
    assert_eq!(sole_row("hv_idx_size_of"), ("bounds".to_string(), "PROVED".to_string()));
}

/// `[0u8; 16][core::mem::align_of::<u64>()]` — the alignment BOUND direction.
/// `align_of::<u64>() <= size_of::<u64>() == 8 < 16` closes it without ever
/// claiming a specific alignment.
#[test]
fn align_of_index_proves() {
    assert_eq!(sole_row("hv_idx_align_of"), ("bounds".to_string(), "PROVED".to_string()));
}

/// `xs[core::mem::size_of::<T>()]` on a `[u8; 64]`, inside a GENERIC function —
/// `tests/trust-falsification/mutant/r3_generic_alias_sizeof_index.rs`, carried
/// here as its extracted MIR so this lane owns a copy of the boundary.
///
/// `T` is chosen by this function's caller, so the size is not an unmodelled
/// deterministic value but a UNIVERSALLY QUANTIFIED one: `T = [u64; 16]` gives
/// index 128 and panics. Two ways of getting this lane wrong both land here — a
/// size table applied to an unsubstituted parameter name would PROVE it, and
/// treating a generic callee as "foreign and unmodelled" would DECLINE it. It
/// must do neither.
#[test]
fn generic_size_of_index_still_refutes() {
    assert_eq!(sole_row("hv_generic_size_of_index"), ("bounds".to_string(), "REFUTED".to_string()));
}

// ---------------------------------------------------------------------------
// The honest cost, recorded rather than hidden.
// ---------------------------------------------------------------------------

/// `100u32 / core::cmp::min(x, 1)` divides by zero at `x == 0` — the runtime
/// oracle panics. The verifier cannot tell it apart from `max(x, 1)` without a
/// model of `min`, so it declines: a COMPLETENESS loss, not unsoundness. What
/// this test defends is the line that matters — the row must never be PROVED.
#[test]
fn real_bug_through_unmodelled_call_is_declined_never_proved() {
    let (kind, verdict) = sole_row("hv_real_divzero_via_call");
    assert_ne!(verdict, "PROVED", "a genuinely panicking division must never be proved");
    assert_eq!(
        (kind, verdict),
        ("decline:UnmodeledCalleeReturn".to_string(), "UNKNOWN".to_string()),
        "the modularity boundary forces a decline here; if this ever becomes REFUTED again \
         that is an improvement, but it must be a deliberate one"
    );
}
