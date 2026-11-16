//! R18 soundness boundary for [`discharge_call_arm_admits`].
//!
//! EVERY string below was MEASURED on deployed driver
//! `sha256:48f2e7437873c1ee` from `.gatelogs/R18-frontA-fixture.rs`
//! (`TRUST_TLS_DISCHARGE_DEBUG=1`) — none is invented, so a rendering change in
//! the extractor makes these tests fail rather than silently pass.
//!
//! MUTANT WITNESS: replacing the `tls_try_with_total.contains(callee)` arm with
//! an unconditional `true` (or dropping the set lookup for a `try_with` name
//! test) turns `empty_record_admits_nothing`,
//! `grant_is_per_call_site_never_per_key_type` and
//! `local_key_with_is_never_admitted_by_the_record_arm` RED. That is the point
//! of pinning strings that differ only in the closure def-path.

use super::super::*;

/// The CONST-INIT `try_with` site of the fixture's `s7_mixed_keys`.
const CONST_TRY_WITH: &str = "std::thread::local::LocalKey::<core::cell::Cell<bool>>::\
    try_with::<{closure@lib.rs:59:29: 59:32}, bool>";
/// The LAZY `try_with` site of the SAME function. Identical but for the
/// closure def-path — this pair is exactly why the record is per-CALL.
const LAZY_TRY_WITH: &str = "std::thread::local::LocalKey::<core::cell::Cell<bool>>::\
    try_with::<{closure@lib.rs:60:28: 60:31}, bool>";
/// `LocalKey::with` on the same const key (fixture `s3_const_with`); `with`
/// adds its own `panic_access_error` and must never be admitted.
const CONST_WITH: &str = "std::thread::local::LocalKey::<core::cell::Cell<bool>>::\
    with::<{closure@lib.rs:39:46: 39:49}, bool>";

fn set(items: &[&str]) -> FxHashSet<String> {
    items.iter().map(|item| (*item).to_string()).collect()
}

fn empty() -> FxHashSet<String> {
    FxHashSet::default()
}

/// FALSE PROOF #12 at this seam. With no record for this caller the premise
/// set is EMPTY, and an empty premise set entails nothing — not even for a
/// callee string that is unmistakably a const-init-shaped `try_with`.
#[test]
fn empty_record_admits_nothing() {
    assert_eq!(
        discharge_call_arm_admits(&empty(), &empty(), &empty(), &empty(), &empty(), CONST_TRY_WITH),
        None,
        "an absent per-caller record must admit NOTHING (absence of evidence fails closed)"
    );
    assert_eq!(
        discharge_call_arm_admits(&empty(), &empty(), &empty(), &empty(), &empty(), LAZY_TRY_WITH),
        None
    );
    assert_eq!(
        discharge_call_arm_admits(
            &empty(),
            &empty(),
            &empty(),
            &empty(),
            &empty(),
            "R18::s5_always_panics"
        ),
        None,
        "an unregistered same-crate callee must block (false proof #11)"
    );
}

/// FALSE PROOF #13/#14 at this seam. The record is keyed per CALL SITE, so a
/// const-init key's grant can never license the LAZY sibling call in the same
/// function — even though the two callee strings differ only in the closure
/// def-path.
#[test]
fn grant_is_per_call_site_never_per_key_type() {
    let granted = set(&[CONST_TRY_WITH]);
    assert_eq!(
        discharge_call_arm_admits(&empty(), &empty(), &granted, &empty(), &empty(), CONST_TRY_WITH),
        Some("tls-const-init"),
    );
    assert_eq!(
        discharge_call_arm_admits(&empty(), &empty(), &granted, &empty(), &empty(), LAZY_TRY_WITH),
        None,
        "a LAZY key's call must stay charged even beside a granted const-init sibling"
    );
}

/// `LocalKey::with` is excluded because it is never PUT in the record —
/// not by a name test here, which is why granting its `try_with` sibling
/// changes nothing for it.
#[test]
fn local_key_with_is_never_admitted_by_the_record_arm() {
    let granted = set(&[CONST_TRY_WITH]);
    assert_eq!(
        discharge_call_arm_admits(&empty(), &empty(), &granted, &empty(), &empty(), CONST_WITH),
        None
    );
}

/// The pre-existing arms keep answering, and each answers for itself only —
/// so a later reader can see that R18 added an arm rather than widening one.
#[test]
fn preexisting_registry_arms_are_unchanged_and_disjoint() {
    let proven = set(&["R18::m1_poison"]);
    let abi = set(&["some::foreign::nonunwind_import"]);
    assert_eq!(
        discharge_call_arm_admits(&proven, &abi, &empty(), &empty(), &empty(), "R18::m1_poison"),
        Some("registry-proven"),
    );
    assert_eq!(
        discharge_call_arm_admits(
            &proven,
            &abi,
            &empty(),
            &empty(),
            &empty(),
            "some::foreign::nonunwind_import"
        ),
        Some("abi-total"),
    );
    assert_eq!(
        discharge_call_arm_admits(
            &proven,
            &abi,
            &empty(),
            &empty(),
            &empty(),
            "R18::s5_always_panics"
        ),
        None,
        "a callee in no registry and no record must fall through and fail closed"
    );
}

/// LEVER 3 — the MOVED-VALUE-ARGUMENT arm at this seam.
///
/// Every spelling below was MEASURED as `UNREGISTERED callee blocks discharge`
/// in ny `.gatelogs/R40.log` (`TRUST_PF_MATCH_TRACE=1`), so a rendering change
/// in the extractor makes these tests fail rather than silently pass.
///
/// THE RETIREMENT STAYS RETIRED. trust-recon `957f47a332` removed
/// `Option::{unwrap_or, ok_or}` / `Result::unwrap_or` / `bool::then_some` from
/// the NAME surface because each drops a by-value argument on the branch it does
/// not take, running the CALLER's `Drop::drop` — invisible in the string. The
/// first assertion of each pair is the pin that they did NOT come back: with an
/// EMPTY record the exact same spellings admit NOTHING, which is only possible
/// because `callee_is_recognized_total_no_panic` still declines them.
///
/// MUTANT WITNESS: replacing the `moved_value_total.contains(callee)` arm with
/// a name test on `"unwrap_or"` turns `moved_value_arm_needs_this_callers_typed_record`
/// and `moved_value_grant_is_per_call_site_never_per_method` RED.
#[test]
fn moved_value_arm_needs_this_callers_typed_record() {
    // The R40 blocker spellings, verbatim.
    for callee in [
        "core::option::Option::<ny_cert::rational::Rat>::unwrap_or",
        "core::option::Option::<usize>::unwrap_or",
        "core::option::Option::<&[u8]>::unwrap_or",
        "core::result::Result::<u8, core::num::error::TryFromIntError>::unwrap_or",
        "core::option::Option::<ny_cert::rational::Rat>::ok_or::<ny_cert::rational::RatError>",
        // The bare (un-monomorphized) renderings the retired name list carried.
        "core::option::Option::unwrap_or",
        "std::option::Option::unwrap_or",
        "core::result::Result::unwrap_or",
        "core::option::Option::ok_or",
        "core::bool::then_some",
    ] {
        assert_eq!(
            discharge_call_arm_admits(&empty(), &empty(), &empty(), &empty(), &empty(), callee),
            None,
            "with no typed record these must admit NOTHING — the retired name \
             grants must not have come back: {callee}"
        );
        assert!(
            !trust_ir_bridge::callee_is_recognized_total_no_panic(callee),
            "the moved-value family must stay off the NAME-ONLY surface: {callee}"
        );
    }
    // With THIS caller's typed record the named call — and only it — clears.
    let granted = set(&["core::option::Option::<ny_cert::rational::Rat>::unwrap_or"]);
    assert_eq!(
        discharge_call_arm_admits(
            &empty(),
            &empty(),
            &empty(),
            &granted,
            &empty(),
            "core::option::Option::<ny_cert::rational::Rat>::unwrap_or",
        ),
        Some("moved-value-nodrop"),
    );
}

/// LEVER 3 — the record is an EXACT call-key set, never a method/type pattern.
///
/// ADVERSARIAL: `Option::<Rat>::unwrap_or` is drop-glue-free (`Rat` is
/// `#[derive(Clone, Copy)]` over a `u32` + a `PhantomData`), while
/// `Option::<Box<D>>::unwrap_or` for a `D` with a panicking `Drop` is the
/// EXACT counterexample the retirement commit published. `needs_drop` separates
/// them at collection time, so the second spelling is poisoned rather than
/// granted; if this arm were ever re-expressed as a name predicate the
/// panicking payload would ride the safe one's grant.
#[test]
fn moved_value_grant_is_per_call_site_never_per_method() {
    let safe = "core::option::Option::<ny_cert::rational::Rat>::unwrap_or";
    let panicking = "core::option::Option::<alloc::boxed::Box<A::D>>::unwrap_or";
    let granted = set(&[safe]);
    assert_eq!(
        discharge_call_arm_admits(&empty(), &empty(), &empty(), &granted, &empty(), safe),
        Some("moved-value-nodrop"),
    );
    assert_eq!(
        discharge_call_arm_admits(&empty(), &empty(), &empty(), &granted, &empty(), panicking),
        None,
        "a grant for a drop-glue-free payload must NOT discharge a sibling \
         monomorphization whose payload owns a panicking Drop"
    );
    // ...nor an unrelated neighbour, nor the closure-driving siblings that were
    // NEVER in this family (`unwrap_or_else`/`unwrap_or_default`/`map_or` drive
    // caller-supplied code and are excluded by `item_name`).
    for other in [
        "core::option::Option::<ny_cert::rational::Rat>::unwrap",
        "core::option::Option::<ny_cert::rational::Rat>::expect",
        "core::option::Option::<ny_cert::rational::Rat>::unwrap_or_else::<{closure@a.rs:1:1}>",
        "core::option::Option::<ny_cert::rational::Rat>::unwrap_or_default",
        "core::panicking::panic",
        "ny_cert::rational::Rat::new",
    ] {
        assert_eq!(
            discharge_call_arm_admits(&empty(), &empty(), &empty(), &granted, &empty(), other),
            None,
            "`{other}` must keep blocking despite an unrelated moved-value grant"
        );
    }
}

/// R43 — `Result::<T, E>::ok` joins the MOVED-VALUE family at this seam.
///
/// Both spellings below were MEASURED as `arm=NONE (blocks registration)` in ny
/// `.gatelogs/R42.log`, and reproduced on the deployed driver
/// (`~/.trust-tc-recon`, 2026-08-22) as
/// `[PF_ZEROGATE] fn=FR::ok_nodrop arm=NONE … callee=core::result::Result::<u8,
/// core::num::error::TryFromIntError>::ok`, so a rendering change in the
/// extractor makes this test fail rather than silently pass.
///
/// `ok` is in the moved-value family and NOT the `Self`-typed one because the
/// property that decides it is `!needs_drop` on the `E` its `Err(_)` wildcard
/// arm drops — a fact about the caller's type argument, invisible in the name.
#[test]
fn result_ok_needs_this_callers_typed_record() {
    for callee in [
        // The R42 blocker spellings, verbatim.
        "core::result::Result::<u64, core::num::error::TryFromIntError>::ok",
        "core::result::Result::<i64, core::num::error::TryFromIntError>::ok",
        "core::result::Result::<(), ny_cert::rational::RatError>::ok",
        // The bare (un-monomorphized) renderings a name list would have carried.
        "core::result::Result::ok",
        "std::result::Result::ok",
    ] {
        assert_eq!(
            discharge_call_arm_admits(&empty(), &empty(), &empty(), &empty(), &empty(), callee),
            None,
            "with no typed record `{callee}` must admit NOTHING"
        );
        assert!(
            !trust_ir_bridge::callee_is_recognized_total_no_panic(callee),
            "`Result::ok` must stay off the NAME-ONLY surface — the `E` it drops \
             is a caller-chosen type the string does not carry: {callee}"
        );
    }
    // With THIS caller's typed record the named call — and only it — clears.
    let safe = "core::result::Result::<u64, core::num::error::TryFromIntError>::ok";
    let granted = set(&[safe]);
    assert_eq!(
        discharge_call_arm_admits(&empty(), &empty(), &empty(), &granted, &empty(), safe),
        Some("moved-value-nodrop"),
    );
    // ADVERSARIAL: the drop-glue-bearing sibling. `RatError` owns two `String`s
    // (`RatError::NotI64 { num, den }`, crates/ny-cert/src/rational.rs:59), so
    // `needs_drop` is TRUE for it and `moved_value_arg_call_operands_need_no_drop`
    // answers `Some(false)` — the key is poisoned at collection time, never
    // granted. A `Box<PanickingDrop>` payload is the same shape with a REACHABLE
    // panic. Neither may ride the grant minted for the drop-glue-free one.
    for panicking in [
        "core::result::Result::<(), ny_cert::rational::RatError>::ok",
        "core::result::Result::<u64, alloc::boxed::Box<A::D>>::ok",
    ] {
        assert_eq!(
            discharge_call_arm_admits(&empty(), &empty(), &empty(), &granted, &empty(), panicking),
            None,
            "a grant for a drop-glue-free `E` must NOT discharge a sibling \
             monomorphization whose `E` owns drop glue: {panicking}"
        );
    }
    // ...nor the neighbouring methods this reasoning never read. `Result::err`
    // is the mirror method (drops the `T`) and is DELIBERATELY not in the family;
    // `Option::ok` does not exist and must not be conjured by the item name.
    for other in [
        "core::result::Result::<u64, core::num::error::TryFromIntError>::err",
        "core::result::Result::<u64, core::num::error::TryFromIntError>::ok_or",
        "core::option::Option::<u64>::ok",
        "core::result::Result::<u64, core::num::error::TryFromIntError>::unwrap",
        "mycrate::Result::<u64, E>::ok",
    ] {
        assert_eq!(
            discharge_call_arm_admits(&empty(), &empty(), &empty(), &granted, &empty(), other),
            None,
            "`{other}` must keep blocking despite an unrelated `Result::ok` grant"
        );
        assert!(
            !trust_ir_bridge::callee_is_recognized_total_no_panic(other),
            "and must not be name-total either: {other}"
        );
    }
}
