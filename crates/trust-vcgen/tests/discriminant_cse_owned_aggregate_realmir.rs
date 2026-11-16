//! Real-MIR cover for class `v-refuted-unreachable` (2026-09-27 inventory), the
//! RE-READ half: rustc lowers a `match` over a TUPLE of enums into a cascade of
//! switches that re-read the same field's discriminant into fresh temps, each switch
//! covering only a SUBSET of the tags with `otherwise -> Unreachable`. Nothing tied
//! the re-reads to each other once they lay after a call, so the solver gave the
//! same field two different tags and accused the dead arm.
//!
//! The fixtures are `-Ztrust-dump=mir-only:<dir>` captures (at `-C opt-level=2`, the
//! inventory posture) of:
//!
//! ```ignore
//! pub trait Src { fn get(&self) -> Option<u32>; }
//! pub fn pair<S: Src>(a: &S, b: &S) -> u32 {
//!     match (a.get(), b.get()) {
//!         (None, None) => 0, (None, _) => 1, (_, None) => 2, (Some(x), Some(y)) => x ^ y,
//!     }
//! }
//! pub trait Fallible { fn next(&mut self) -> Result<Option<u32>, u8>; }
//! pub fn fallible_cmp<A: Fallible, B: Fallible>(mut a: A, mut b: B) -> Result<i8, u8> {
//!     loop {
//!         match (a.next()?, b.next()?) {
//!             (None, None) => return Ok(0),
//!             (None, _) => return Ok(-1),
//!             (_, None) => return Ok(1),
//!             (Some(x), Some(y)) => if x != y { return Ok(if x < y { -1 } else { 1 }); },
//!         }
//!     }
//! }
//! pub enum Mode<E> { Incomplete(u32), Backtrack(E), Cut(E) }
//! pub trait Merge { fn merge(self, o: Self) -> Self; }
//! pub fn or<E: Merge>(a: Mode<E>, b: Mode<E>) -> Mode<E> {
//!     match (a, b) {
//!         (Mode::Backtrack(e), Mode::Backtrack(o)) => Mode::Backtrack(e.merge(o)),
//!         (Mode::Incomplete(e), _) | (_, Mode::Incomplete(e)) => Mode::Incomplete(e),
//!         (Mode::Cut(e), _) | (_, Mode::Cut(e)) => Mode::Cut(e),
//!     }
//! }
//! ```
//!
//! `pair` is `(a.next(), b.next())` in `bit_vec::BitVec::cmp` and
//! `(env::var("TARGET"), env::var("HOST"))` in `pkg_config::Config::targeted_env_var`;
//! `fallible_cmp` is `fallible_iterator::FallibleIterator::{cmp,partial_cmp,eq,ne,lt,
//! le,gt,ge}` (the tuple rebuilt every iteration); `or` is `winnow::error::ErrMode::or`
//! (its reads precede every call, but the drop ladder AFTER the match partially writes
//! the tuple). MEASURED on trust main `8c39674bbb` (stage 1), all three: `[unreach]
//! FAILED` with the same field read as two different tags (`pair`: `_7 = 1`, `_8 = 0`
//! for `disc(_3.0)`). On trust main `144f74baff`, whose arm (b) ties post-call reads
//! of an aggregate no pointer reaches and no `Drop` names
//! (`local_defs::storage_never_aliased`), `pair` and `fallible_cmp` are solver-UNSAT
//! but NOT kernel-certifiable, and `or` is still REFUTED: its drop ladder's `Drop`s
//! make arm (b) refuse the whole tuple.
//!
//! THE FIX, two parts. Arm (c) of `generate::build_discriminant_cse_facts` licenses
//! each read on its own: a tuple that is never borrowed can be changed only by
//! statements that name it, so a re-read that no path from an invalidating event
//! (entry, storage marker, move-out, drop) reaches without passing the one
//! construction observes that construction's value — `or`'s match reads precede its
//! drop ladder. And a tie alone leaves each path's contradiction holding only modulo
//! the equality, which the clean-kernel re-check cannot use, so the path-guard splice
//! renders a tied temp through its group's first read
//! (`generate::discriminant_cse_anchor_map`), leaving each path a syntactic
//! contradiction the kernel closes (`trust-certify`'s unit witness).
//!
//! The two CONTROLS are the adversarial direction. Each holds an out-of-bounds read
//! that is reachable only if two reads of the same field DIFFER; a tie that should not
//! be there makes that path infeasible and PROVES the out-of-bounds read:
//!  * `borrowed_between` hands `&mut t.0` to a callee between the reads;
//!  * `loop_reconstructed` compares this iteration's read with the previous one's.
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

/// Every generated VC of `func` with its verdict from the in-process ay backend the
/// compiler's analysis seams use, on a big stack.
fn rows(func: VerifiableFunction) -> Vec<(trust_types::VerificationCondition, VerificationResult)> {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let router = test_router::deterministic_test_router();
            trust_vcgen::generate_vcs(&func)
                .into_iter()
                .map(|vc| {
                    let r = router.verify_one(&vc);
                    (vc, r)
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("join")
}

/// Every `Unreachable` row must be DISCHARGED the way the compiler discharges it under
/// `-Ztrust-policy=certify`: the solver must not REFUTE it (a model is a FALSE
/// REFUTATION of correct Rust), and the clean kernel must CERTIFY it. `certify_vc` is
/// both the authority `certify` demands of a solver `Proved` and the one door through
/// which the compiler promotes an inconclusive solver verdict
/// (`rustc_mir_transform::trust_verify::promote_kernel_certifiable`), so an
/// `Unknown`/`Timeout` passes here only together with that certificate.
///
/// MEASURED: `pair` and `fallible_cmp` are solver-`Proved`; `or` (51 paths through the
/// match and its drop ladder) is `Unknown ("incomplete self-check-rejected")` from
/// in-process ay — its strict proof self-check rejects the answer — and discharged by
/// the kernel certificate alone.
fn assert_unreachable_discharged(fixture: &str, what: &str) {
    let all = rows(load(fixture));
    let unreachable: Vec<_> =
        all.iter().filter(|(vc, _)| matches!(vc.kind, VcKind::Unreachable)).collect();
    assert!(!unreachable.is_empty(), "{what}: the fixture has an Unreachable block");
    for (vc, result) in unreachable {
        assert!(
            matches!(
                result,
                VerificationResult::Proved { .. }
                    | VerificationResult::Unknown { .. }
                    | VerificationResult::Timeout { .. }
            ),
            "{what}: the tuple match's `otherwise -> Unreachable` must be UNSAT — a model \
             here is a FALSE REFUTATION of correct Rust; got {result:?}\nformula: {:?}",
            vc.formula
        );
        assert!(
            trust_certify::certify_vc(vc).is_some(),
            "{what}: the proof must kernel-certify\nformula: {:?}",
            vc.formula
        );
    }
}

/// The out-of-bounds row of a control must stay REFUTED.
fn assert_bounds_refuted(fixture: &str, what: &str) {
    let all = rows(load(fixture));
    let bounds: Vec<_> = all
        .iter()
        .filter(|(vc, _)| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .collect();
    assert_eq!(bounds.len(), 1, "{what}: the fixture has exactly one bounds row: {all:#?}");
    let (vc, result) = bounds[0];
    assert!(
        matches!(result, VerificationResult::Failed { .. }),
        "{what}: `arr[i]` is reachable when the two reads differ — proving it is a FALSE \
         PROOF; got {result:?}\nformula: {:?}",
        vc.formula
    );
}

#[test]
fn a_tuple_of_two_call_results_is_matched_exhaustively() {
    assert_unreachable_discharged(
        include_str!("fixtures/discriminant_cse_owned_pair_mir.json"),
        "pair",
    );
}

#[test]
fn a_tuple_rebuilt_every_iteration_is_matched_exhaustively() {
    assert_unreachable_discharged(
        include_str!("fixtures/discriminant_cse_owned_fallible_cmp_mir.json"),
        "fallible_cmp",
    );
}

#[test]
fn a_by_value_tuple_with_drop_glue_after_the_match_is_matched_exhaustively() {
    assert_unreachable_discharged(
        include_str!("fixtures/discriminant_cse_owned_or_mir.json"),
        "or",
    );
}

#[test]
fn a_tuple_borrowed_mutably_between_two_reads_is_not_tied() {
    assert_bounds_refuted(
        include_str!("fixtures/discriminant_cse_owned_borrowed_between_mir.json"),
        "borrowed_between",
    );
}

#[test]
fn reads_of_different_iterations_are_not_tied() {
    assert_bounds_refuted(
        include_str!("fixtures/discriminant_cse_owned_loop_reconstructed_mir.json"),
        "loop_reconstructed",
    );
}
