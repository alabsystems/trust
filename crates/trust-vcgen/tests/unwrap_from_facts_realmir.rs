//! Unwrap/expect panic-freedom from facts the body already established
//! (2026-10-03, unwrap-from-facts), on REAL extracted MIR.
//!
//! The obligation of a std `Option`/`Result` `unwrap`/`expect`/`unwrap_err`/
//! `expect_err` call is "the receiver's discriminant is not the panicking
//! variant". It is discharged only from facts over ONE shared tag term — a
//! std probe (`is_some`/`is_none`/`is_ok`/`is_err`), a discriminant read
//! (`match`, `if let`), a construction. These fixtures are the shapes that
//! still kept the fail-closed `Call::<m>::panic-freedom-unverified` row on
//! stage-1 aa965027e2 although the variant was established:
//!
//! ```text
//! fn ref_is_some(x: &Option<u32>)        if x.is_some() { x.unwrap() }       pointee of a `&` param
//! fn ref_match(x: &Option<u32>)          match *x { Some(_) => x.unwrap() }  read-pinned pointee
//! fn ref_if_let_expect(x: &Option<u32>)  if let Some(_) = x { x.expect(..) }
//! fn ref_as_ref(x: &Option<String>)      if x.is_some() { x.as_ref().unwrap() }
//! fn tuple_field(s: &(Option<u32>, u32)) if s.0.is_some() { s.0.unwrap() }
//! fn struct_field_ok(t: &T)              if t.r.is_ok() { t.r.unwrap() }
//! fn ok_or_result(x: Option<u32>)        let r = x.ok_or(()); if r.is_ok() { r.unwrap() }   call-pinned
//! fn parse_is_err(v: &str)               let r = v.parse::<u8>(); if r.is_err() {0} else { r.unwrap() }
//! fn ref_is_none_early(x: &Option<u32>)  if x.is_none() { return 0 } x.unwrap()
//! ```
//!
//! and the controls, every one of which must stay UNPROVED: an unchecked
//! unwrap, a check on a DIFFERENT variable, the wrong polarity, a mutation
//! between check and unwrap through `&mut`, a `&mut` alias handed to a callee,
//! a re-pointed `&` parameter, a call result redefined after its check, a
//! check that belongs to the previous loop iteration, an unchecked call result,
//! a `&raw const` borrow of the receiver cast to `*mut` and written through,
//! and a USER method named `unwrap` (resolved by item: not the std one, so it
//! carries no std obligation at its call site, while the std unwrap inside it
//! stays unproved).
//!
//! Source: the fixtures are `-Ztrust-dump=mir` captures of
//! `crates/trust-vcgen/tests/fixtures/unwrap_facts.rs.txt` (kept beside them),
//! compiled as `trustc -Ztrust-verify=on -Ztrust-dump=mir:<dir> --crate-type=lib
//! unwrap_facts.rs` by stage-1 aa965027e2.

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

/// Real extracted MIR carries deep recursive `Formula` walks.
const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/unwrap_facts_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

#[derive(Debug, Clone)]
struct Row {
    kind: VcKind,
    proved: bool,
    result: String,
}

/// Is `kind` the obligation of a std unwrap-family call — the solvable one or
/// the fail-closed `panic-freedom-unverified` row?
fn is_unwrap_family_row(kind: &VcKind) -> bool {
    trust_types::l0_refutation::is_unwrap_family_panic_freedom_assertion(kind)
        || trust_types::l0_refutation::is_known_panicking_call_unsupported_mir(kind)
}

/// Every unwrap-family row of fixture `name`, decided by the in-process ay
/// router (hardened profile ON, as the compiler runs it).
fn unwrap_rows(name: &str) -> Vec<Row> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
            let db = trust_vcgen::SummaryDatabase::new();
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func,
                    &db,
                    true,
                    &context,
                    &std::collections::HashSet::new(),
                );
            let router = trust_router::Router::deterministic_in_process_ay(
                30_000,
                trust_types::determinism::EffortScale::BUILTIN,
            );
            let decided = solver_vcs.into_iter().map(|vc| {
                let (_, result) = router
                    .verify_all(std::slice::from_ref(&vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC");
                (vc, result)
            });
            preclassified
                .into_iter()
                .chain(decided)
                .filter(|(vc, _)| is_unwrap_family_row(&vc.kind))
                .map(|(vc, result)| Row {
                    kind: vc.kind,
                    proved: matches!(result, VerificationResult::Proved { .. }),
                    result: format!("{result:?}"),
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

/// The variant is established before the call: exactly one obligation, the
/// SOLVABLE one, and it is proved.
fn assert_discharged(name: &str) {
    let rows = unwrap_rows(name);
    assert_eq!(rows.len(), 1, "`{name}`: one unwrap-family obligation per call: {rows:#?}");
    let row = &rows[0];
    assert!(
        trust_types::l0_refutation::is_unwrap_family_panic_freedom_assertion(&row.kind),
        "`{name}`: the solvable obligation replaces the fail-closed row: {row:#?}"
    );
    assert!(row.proved, "`{name}`: the established variant must discharge it: {}", row.result);
}

/// Nothing establishes the variant at the call: at least one obligation, none
/// proved, and every one a Level-0 refutation when unproved (so the published
/// row is `failed` whichever of the two kinds it is).
fn assert_stays_unproved(name: &str) {
    let rows = unwrap_rows(name);
    assert!(!rows.is_empty(), "`{name}`: the std unwrap keeps an obligation");
    for row in &rows {
        assert!(!row.proved, "`{name}`: FALSE PROOF — nothing pins the variant: {row:#?}");
        assert_eq!(
            trust_types::l0_refutation::L0RefutationClass::of_kind(&row.kind, |_| false),
            Some(trust_types::l0_refutation::L0RefutationClass::KnownPanickingCall),
            "`{name}`: an unproved unwrap obligation is published `failed`: {row:#?}"
        );
    }
}

#[test]
fn pointee_of_a_shared_param_checked_by_a_probe_is_discharged() {
    assert_discharged("ref_is_some");
    assert_discharged("ref_is_none_early");
}

#[test]
fn pointee_of_a_shared_param_checked_by_a_match_is_discharged() {
    assert_discharged("ref_match");
    assert_discharged("ref_if_let_expect");
}

#[test]
fn as_ref_view_of_a_checked_pointee_is_discharged() {
    assert_discharged("ref_as_ref");
}

#[test]
fn field_of_a_shared_param_checked_by_a_probe_is_discharged() {
    assert_discharged("tuple_field");
    assert_discharged("struct_field_ok");
}

#[test]
fn checked_call_result_is_discharged() {
    assert_discharged("ok_or_result");
    assert_discharged("parse_is_err");
}

#[test]
fn unchecked_and_wrongly_checked_unwraps_stay_unproved() {
    // `ref_match_other` matches on `*x` and unwraps `y`: a read of a DIFFERENT
    // subject is not this subject's term.
    for name in
        ["ref_unchecked", "ref_other", "ref_match_other", "ref_is_none_unwrap", "ok_or_unchecked"]
    {
        assert_stays_unproved(name);
    }
}

#[test]
fn a_write_between_check_and_unwrap_keeps_it_unproved() {
    // `*x = None` through the `&mut` parameter; `f(x)` hands the `&mut` to a
    // callee; `*y = None` through a reborrow `y = &mut *x`; `*p = None` through a
    // raw pointer `p = &raw mut *x` (the shape only the "base is a SHARED
    // reference" gate refuses: `x` itself is never reborrowed `&mut` or
    // written, so it reads as pinned); `x = y` re-points the
    // `&` parameter; `r = v.pop()` redefines the checked call result; the loop's
    // check belongs to the previous `r`.
    for name in [
        "mut_between",
        "mut_alias",
        "mut_reborrow",
        "mut_raw",
        "mut_ptr_read",
        "reseat",
        "call_redefined",
        "loop_stale",
    ] {
        assert_stays_unproved(name);
    }
}

#[test]
fn a_raw_const_borrow_of_the_receiver_keeps_it_unproved() {
    // `p = &raw const r as *mut _; if r.is_ok() { *p = Err(()); r.unwrap() }`:
    // a `*const` is a valid `*const -> *mut` cast root, and under Tree Borrows
    // the write to a `mut` local through it is defined, so the check no longer
    // describes `r`. Before 2026-10-03 `place_source_is_stable` admitted a
    // `&raw const` borrow: `raw_const_call` (shape (e)) was a FALSE PROOF on the
    // first UF-1 commit, and `raw_const_param` (the by-value parameter twin) was
    // already one on stage-1 aa965027e2.
    for name in ["raw_const_call", "raw_const_param"] {
        assert_stays_unproved(name);
    }
}

#[test]
fn a_user_method_named_unwrap_is_not_the_std_one() {
    // At the call site `w.unwrap()` resolves to `W::unwrap`, not std's: no
    // std unwrap-family obligation there at all.
    assert!(unwrap_rows("user_unwrap").is_empty(), "{:#?}", unwrap_rows("user_unwrap"));
    // Inside it, `self.0.unwrap()` is std's, and nothing checks `self.0`.
    assert_stays_unproved("w_unwrap");
}
