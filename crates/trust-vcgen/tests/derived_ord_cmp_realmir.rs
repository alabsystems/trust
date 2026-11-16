//! REAL-MIR pin: a `#[derive(Ord)]` enum's `cmp` does not reach its
//! `_ => unreachable` arm (TRUST-09).
//!
//! # What was wrong
//!
//! Triaging the strict-lane failures of ordinary registry crates, regex-syntax
//! 0.8.10's `#[derive(Ord)] enum Utf8Sequence` (four data-carrying variants) was
//! reported under `-Ztrust-policy=advisory` as
//!
//! ```text
//! [unreach] FAILED (ay-in-process); counterexample: _10 = 1, _11 = 0, _12 = 0, _3 = 0, _4 = 0, …
//! ```
//!
//! The derive lowers `cmp` to
//!
//! ```text
//! bb0: _3 = discriminant((*_1)); _4 = discriminant((*_2));
//!      _5 = <isize as Ord>::cmp(&_3, &_4) -> bb1
//! bb3: _9 = (copy _1, copy _2); _17 = copy (_9.0); _12 = discriminant((*_17)); …
//!      … `otherwise -> bb4` on every arm; bb4: unreachable
//! ```
//!
//! and reaches bb3 only when the two discriminants compared `Equal`. Every
//! `discriminant((*_17))`-style re-read canonicalizes to `*self` / `*other`, and
//! `build_discriminant_cse_facts` ties such reads — but only BEFORE the first call,
//! and every re-read here follows `<isize as Ord>::cmp`. The counterexample has
//! `disc(*self)` read as 0 before the call and as 1 after it. `self` and `other`
//! are this function's own `&E` parameters: protected for the whole call, so no
//! write to a byte of `*self` outside an `UnsafeCell` is defined behaviour while
//! `cmp` runs. The counterexample is not an execution.
//!
//! # The matrix
//!
//! | fixture | expectation |
//! |---|---|
//! | `seq` (`enum Seq { One(Range), Two([Range; 2]) }`) | no `[unreach]` row REFUTED |
//! | `celled` (`enum Celled { A(Cell<u8>), B(u8) }`) | the `[unreach]` row stays REFUTED: an `UnsafeCell` inline in the pointee refuses the post-call tie |
//!
//! The other refusals — a `&mut` or reassigned parameter, a shared reference that
//! is a LOCAL rather than a parameter, a foreign / `unsafe` / atomic callee or an
//! `Opaque` barrier — are pinned on hand-built MIR in `src/tests.rs`
//! (`frozen_shared_param_discriminants_are_tied_after_a_call` and its
//! siblings), since the derive never emits them.
//!
//! # Fixtures
//!
//! `tests/fixtures/derived_ord_cmp_*_mir.json` are the compiler's own extraction
//! of the source below, captured with the installed `450403669` as
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> derived_ord_cmp.rs
//! ```
//!
//! ```text
//! use core::cell::Cell;
//! #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
//! pub struct Range { pub start: u8, pub end: u8 }
//! #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
//! pub enum Seq { One(Range), Two([Range; 2]) }
//! #[derive(PartialEq, Eq, PartialOrd, Ord)]
//! pub enum Celled { A(Cell<u8>), B(u8) }
//! ```
use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

/// Stack for the generation/solver thread; real extracted MIR carries deep
/// recursive `Formula` walks (the same allowance the other realmir files make).
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/derived_ord_cmp_");
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

/// regex-syntax's `Utf8Sequence` shape: both variants carry data, so the derive
/// re-reads the discriminants after the `<isize as Ord>::cmp` call.
#[test]
fn derived_ord_cmp_does_not_reach_its_unreachable_arm() {
    let rows = unreachable_rows("seq");
    assert!(
        !rows.is_empty(),
        "seq: the fixture must actually produce an `[unreach]` row or this test proves nothing"
    );
    assert!(
        rows.iter().all(|v| v != "REFUTED"),
        "seq: bb3 is reached only when `disc(*self)` and `disc(*other)` compared Equal, \
         and `*self`/`*other` are the pointees of this function's own protected `&Seq` \
         parameters; a refutation is a counterexample over a discriminant that changed \
         under a live shared reference: {rows:?}"
    );
}

/// The fail-closed half: `Cell<u8>` puts an `UnsafeCell` inline in the pointee, so
/// the protector does not make every byte of `*self` immutable and the post-call
/// re-reads are NOT tied — the row keeps the verdict it had before the fix.
#[test]
fn an_unsafe_cell_in_the_pointee_keeps_the_post_call_reads_untied() {
    let rows = unreachable_rows("celled");
    assert_eq!(
        rows,
        vec!["REFUTED".to_string()],
        "celled: an `UnsafeCell` inline in the pointee must refuse the post-call tie"
    );
}
