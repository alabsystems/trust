//! REAL-MIR pin: two `Discriminant` reads of the same field of an OWNED, never
//! borrowed aggregate stay tied when a CALL precedes them (TRUST-10).
//!
//! # What was wrong
//!
//! bit-vec 0.9.1 (`src/lib.rs:1991`) has
//!
//! ```text
//! impl<B: BitBlock> Ord for BitVec<B> {
//!     fn cmp(&self, other: &Self) -> Ordering {
//!         let mut a = self.iter();
//!         let mut b = other.iter();
//!         loop {
//!             match (a.next(), b.next()) {
//!                 (Some(x), Some(y)) => match x.cmp(&y) { Ordering::Equal => {}, o => return o },
//!                 (None, None) => return Ordering::Equal,
//!                 (None, _) => return Ordering::Less,
//!                 (_, None) => return Ordering::Greater,
//!             }
//!         }
//!     }
//! }
//! ```
//!
//! Compiled with `-Ztrust-policy=advisory` it reported
//!
//! ```text
//! [unreach] FAILED (ay-in-process); counterexample: _10 = 0, _11 = 0, _12 = 1, _13 = 1, …
//! ```
//!
//! rustc lowers the tuple match to `_5 = (move _6, move _8)` and then reads
//! `discriminant(_5.1)` into THREE temps across the arms (`_10`, `_11`, `_13`),
//! each `SwitchInt` covering only a subset of the tags, with one shared
//! `otherwise -> Unreachable`. The `(_, None)` arm re-tests `_13 = discr(_5.1)`
//! on the edge block 6 took for `_10 == 0`, so its `otherwise` is dead only if
//! `_13 == _10`. `build_discriminant_cse_facts` ties exactly such reads — but it
//! refused every block reachable after a `Call` terminator, and here the four
//! `iter()`/`next()` calls precede the whole match. That barrier exists for the
//! shared-ref-deref shape, whose POINTEE a call may mutate through an alias; an
//! owned aggregate whose address is never taken has no alias a call could reach.
//! The counterexample `_10 = 0, _13 = 1` is not an execution.
//!
//! # The matrix
//!
//! | fixture | expectation |
//! |---|---|
//! | `cmp_slices` (bit-vec's `Ord::cmp` shape, reads after `next()` calls) | no `[unreach]` row REFUTED |
//! | `cmp_pair` (the same match, no call before the reads) | no `[unreach]` row REFUTED (the shape the builder already admitted) |
//!
//! The load-bearing negative half — an aggregate a call CAN reach (a shared or
//! mutable borrow of it, a raw address of the read field, an `Unsupported` alias,
//! a `Drop` of it between the reads) or a temp with a second value — is pinned on
//! hand-built MIR in `src/tests.rs`
//! (`exposed_owned_aggregate_field_discriminants_are_not_tied_after_a_call`,
//! `a_reused_temp_is_not_tied_even_before_any_barrier`), since rustc emits no such
//! re-read from safe source.
//!
//! # Fixtures
//!
//! `tests/fixtures/discr_cse_after_call_*_mir.json` are the compiler's own
//! extraction of the source below, captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> discr_cse_after_call.rs
//! ```
//!
//! ```text
//! use core::cmp::Ordering;
//! pub fn cmp_slices(a: &[bool], b: &[bool]) -> Ordering {
//!     let mut a = a.iter();
//!     let mut b = b.iter();
//!     loop {
//!         match (a.next(), b.next()) {
//!             (Some(x), Some(y)) => match x.cmp(y) {
//!                 Ordering::Equal => {}
//!                 otherwise => return otherwise,
//!             },
//!             (None, None) => return Ordering::Equal,
//!             (None, _) => return Ordering::Less,
//!             (_, None) => return Ordering::Greater,
//!         }
//!     }
//! }
//! pub fn cmp_pair(a: Option<&bool>, b: Option<&bool>) -> Ordering {
//!     match (a, b) {
//!         (Some(x), Some(y)) => x.cmp(y),
//!         (None, None) => Ordering::Equal,
//!         (None, _) => Ordering::Less,
//!         (_, None) => Ordering::Greater,
//!     }
//! }
//! ```
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

/// Stack for the generation/solver thread; real extracted MIR carries deep
/// recursive `Formula` walks (the same allowance the other realmir files make).
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/discr_cse_after_call_");
    let text = std::fs::read_to_string(format!("{path}{name}_mir.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The verdict of every `[unreach]` row of `name`, each dispatched to the
/// deterministic in-process ay the bridge uses.
fn unreachable_rows(name: &str) -> Vec<String> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            let mut rows = Vec::new();
            for vc in &vcs {
                if !matches!(vc.kind, VcKind::Unreachable) {
                    continue;
                }
                let verdict = match router
                    .verify_all(std::slice::from_ref(vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC")
                    .1
                {
                    VerificationResult::Proved { .. } => "PROVED".to_string(),
                    VerificationResult::Failed { .. } => "REFUTED".to_string(),
                    other => format!("{other:?}").chars().take(24).collect(),
                };
                rows.push(verdict);
            }
            rows
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

fn assert_not_refuted(name: &str) {
    let rows = unreachable_rows(name);
    assert!(
        !rows.is_empty(),
        "{name}: the fixture must actually produce an `[unreach]` row or this test proves nothing"
    );
    assert!(
        rows.iter().all(|v| v != "REFUTED"),
        "{name}: the shared `otherwise -> Unreachable` is dead on every execution (every \
         `discriminant(_5.1)` temp reads the same unwritten field); a refutation is a \
         counterexample over untied re-reads: {rows:?}"
    );
}

/// bit-vec 0.9.1's `Ord::cmp` shape: the discriminant re-reads follow the
/// `iter()`/`next()` calls, and the aggregate they read is owned and never
/// borrowed, so the calls cannot reach it.
#[test]
fn bit_vec_ord_cmp_shape_is_not_refuted_after_the_calls() {
    assert_not_refuted("cmp_slices");
}

/// The same match with no call before the reads: the shape the builder admitted
/// before this fix must keep proving.
#[test]
fn the_call_free_shape_still_proves() {
    assert_not_refuted("cmp_pair");
}
