// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **W5 increment 1 — the ENVIRONMENT half of Lean-calls-Rust, measured at
//! the real elaborator** (`docs/design/2026-09-13-lean-calls-rust-lane.md`).
//!
//! Every claim the design's ENVIRONMENT paragraph makes about a
//! compiler-declared kernel `Opaque` is pinned here against the same
//! `CleanIslandSession` the mint, the MIR gate and the verify pass build:
//!
//! 1. an island that applies a declared Rust callee ELABORATES (this is the
//!    "Unknown identifier: inc" the battery row r18 was red on);
//! 2. the dependent `def` is graded by the mint's own admission seam
//!    (`admit_certified_island_definition`), i.e. an `Opaque` with a hidden
//!    inhabitant does NOT make the closure `Trusted` the way an axiom would;
//! 3. the kernel can prove NOTHING about the callee beyond its type — the
//!    hidden inhabitant never unfolds, so `theorem t : inc 0 = 0 := rfl` is
//!    REJECTED;
//! 4. a callee at the wrong carrier is a type error at the application, not a
//!    silently coerced call;
//! 5. a name the environment already holds (a prelude constant) is refused
//!    with a named reason, and the refusal taints the session.

use trust_certify::clean_island::{CleanIslandSession, RustCallee, declare_rust_callees};
use trust_types::Ty;

fn inc() -> RustCallee {
    RustCallee { clean_name: "inc".to_owned(), params: vec![Ty::u64()], result: Ty::u64() }
}

#[test]
fn an_island_applies_a_declared_rust_callee_and_the_mint_seam_grades_it() {
    let mut session = CleanIslandSession::new();
    session.declare_rust_callees(&[inc()]).expect("`inc : UInt64 → UInt64` declares");
    let batch = session.check_all(&["def twice_inc (x : UInt64) : UInt64 := inc (inc x)"]);
    assert!(
        !batch.is_rejected(),
        "the island must elaborate against the declared callee; outcomes: {:?}",
        batch.outcomes.iter().map(|o| &o.errors).collect::<Vec<_>>()
    );
    let env = session.environment().expect("an accepted batch leaves the session untainted");

    // The mint's own admission seam: `twice_inc` must be KernelChecked with an
    // audited-empty axiom closure even though its body names an `Opaque`.
    let mut facets = trust_spec_elab::FacetTable::new();
    let admission = trust_certify::clean_island::admit_certified_island_definition(
        env,
        "twice_inc",
        &mut facets,
    )
    .expect("an Opaque callee with a hidden inhabitant must not make the closure Trusted");
    assert!(
        admission.status().require_kernel_check("twice_inc").is_ok(),
        "the status must be the kernel-checked one; got {:?}",
        admission.status()
    );

    // The body is exactly the application spine the planner reads: two
    // applications of the stuck constant `inc`.
    let constant =
        env.get_const(&clean_kernel::Name::from_string("twice_inc")).expect("registered");
    let body = constant.value.as_ref().expect("a def has a value");
    let rendered = format!("{body:?}");
    assert!(rendered.contains("inc"), "the body must apply `inc`; got {rendered}");
}

#[test]
fn the_kernel_proves_nothing_about_the_callee_beyond_its_type() {
    let mut session = CleanIslandSession::new();
    session.declare_rust_callees(&[inc()]).expect("declares");
    let batch = session.check_all(&["theorem t : inc (UInt64.ofNat 0) = UInt64.ofNat 0 := rfl"]);
    assert!(
        batch.is_rejected(),
        "the hidden inhabitant must never unfold: `rfl` against `inc 0 = 0` must be REJECTED, \
         or the environment would have minted authority about a Rust body the kernel never saw"
    );
}

#[test]
fn a_callee_applied_at_the_wrong_carrier_is_an_elaboration_error() {
    let mut session = CleanIslandSession::new();
    session
        .declare_rust_callees(&[RustCallee {
            clean_name: "inc".to_owned(),
            params: vec![Ty::u32()],
            result: Ty::u64(),
        }])
        .expect("`inc : UInt32 → UInt64` declares");
    let batch = session.check_all(&["def twice_inc (x : UInt64) : UInt64 := inc (inc x)"]);
    assert!(batch.is_rejected(), "applying `inc` at `UInt64` where it takes `UInt32` must refuse");
    let messages: Vec<String> =
        batch.outcomes.iter().flat_map(|o| o.errors.iter().map(|e| e.message.clone())).collect();
    assert!(!messages.is_empty(), "the refusal must carry the elaborator's message");
    println!("wrong-carrier elaboration error(s): {messages:?}");
}

#[test]
fn an_absent_callee_is_the_unknown_identifier_refusal() {
    let mut session = CleanIslandSession::new();
    let batch = session.check_all(&["def twice_inc (x : UInt64) : UInt64 := inc (inc x)"]);
    assert!(batch.is_rejected());
    let messages: Vec<String> =
        batch.outcomes.iter().flat_map(|o| o.errors.iter().map(|e| e.message.clone())).collect();
    assert!(
        messages.iter().any(|m| m.contains("Unknown identifier: inc")),
        "the pre-increment refusal spelling must be unchanged; got {messages:?}"
    );
}

#[test]
fn a_prelude_name_is_refused_and_taints_the_session() {
    let mut session = CleanIslandSession::new();
    let refusal = session
        .declare_rust_callees(&[RustCallee {
            // `Nat.succ` is not a bare name, so use one the prelude holds at
            // the root: `ite`.
            clean_name: "ite".to_owned(),
            params: vec![Ty::u64()],
            result: Ty::u64(),
        }])
        .expect_err("a name the prelude holds must refuse, never shadow");
    assert_eq!(refusal.callee, "ite");
    assert!(refusal.reason.contains("already holds"), "got {}", refusal.reason);
    assert!(
        session.environment().is_none(),
        "a refused declaration taints the session so nothing positive is minted from it"
    );

    // And the free helper refuses a carrier outside the vocabulary by name.
    let mut env = clean_kernel::Environment::with_prelude();
    let refusal = declare_rust_callees(
        &mut env,
        &[RustCallee {
            clean_name: "neg".to_owned(),
            params: vec![Ty::Int { width: 64, signed: true }],
            result: Ty::u64(),
        }],
    )
    .expect_err("`i64` is outside the vocabulary");
    assert!(refusal.reason.contains("parameter 0"), "got {}", refusal.reason);
}

#[test]
fn a_bool_and_a_two_parameter_callee_declare_and_apply() {
    let mut session = CleanIslandSession::new();
    session
        .declare_rust_callees(&[
            RustCallee {
                clean_name: "is_small".to_owned(),
                params: vec![Ty::u32()],
                result: Ty::Bool,
            },
            RustCallee {
                clean_name: "add2".to_owned(),
                params: vec![Ty::u64(), Ty::u64()],
                result: Ty::u64(),
            },
        ])
        .expect("declares");
    let batch = session.check_all(&["def small_or (x : UInt32) : Bool := is_small x\n\
         def sum3 (a b c : UInt64) : UInt64 := add2 (add2 a b) c"]);
    assert!(
        !batch.is_rejected(),
        "both callees must apply; outcomes: {:?}",
        batch.outcomes.iter().map(|o| &o.errors).collect::<Vec<_>>()
    );
}
