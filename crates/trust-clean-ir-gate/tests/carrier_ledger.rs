// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Plan step 3.4 (docs/design/2026-10-02-step3-lean-through-trust-ir.md §4): the published token
//! a session ledger holds. What it binds (§4.2: the environment the kernel decided in, the
//! kernel version, the carrier, the method, the final subject), the one licensing claim
//! publication may add (the `clean-carrier-gate` stamp, §4.1), and the authentication a consumer
//! runs against the Function it is about to honor. Each refusal below is a control: removing
//! the check it names makes its assertion fail.

use clean_kernel::{Environment, Name};
use trust_certify::clean_island::CleanIslandSession;
use trust_clean_ir_gate::{
    CLEAN_CARRIER_GATE_AUTHORITY, GateEnvironment, admit_wrapping_binop, clean_carrier_gate_stamp,
};
use trust_clean_origin::{CleanOriginPlan, plan_clean_origin_body};
use trust_ir::ty::FuncTy;
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir::{BinOp, BodyGate, Function, Inst, Producer};

fn environment(sources: &[&str]) -> Environment {
    let mut session = CleanIslandSession::new();
    for source in sources {
        let outcome = session.check(source);
        assert!(!outcome.is_rejected(), "fixture must kernel-check: {outcome:?}");
    }
    session.environment().expect("untainted session").clone()
}

fn emitted(env: &Environment, name: &str) -> (CleanOriginPlan, FuncTy, Function) {
    let plan = plan_clean_origin_body(env, name).expect("fixture plans");
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).expect("signature");
    let mut function =
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .expect("emitted SSA");
    // WS5.2: the crate lane's subject is named by the Rust item's link-time symbol.
    bind_fixture_link_symbol(&mut function);
    (plan, signature, function)
}

/// The collector's WS5.2 binding, over a deterministic fixture symbol: the crate lane's gate
/// (`admit_clean_origin`) binds the plan through `display_path` and requires a link-time symbol
/// as the name (`trust_thir_lower::link_symbol::bind_clean_origin_link_symbol` does this in the
/// collector; this crate has no `tcx`, and the gate does not compute the symbol).
fn bind_fixture_link_symbol(function: &mut Function) {
    assert!(function.display_path.is_none(), "the emitter leaves display_path to the binder");
    let symbol = format!("_RNvCs0_7fixture{}", function.name.len());
    let lean = std::mem::replace(&mut function.name, symbol);
    function.name.push_str(&lean.replace('.', "_"));
    function.display_path = Some(lean);
}

/// The join's publication of a targeted row: final id/type, the Clean producer, and the stamp.
fn published(function: &Function) -> Function {
    let mut published = function.clone();
    published.id = FuncId::new(5);
    published.ty = FuncTyId::new(2);
    published.producer = Some(Producer::Clean);
    published.body_gate = Some(clean_carrier_gate_stamp());
    published
}

fn with_binop(function: &Function, replacement: BinOp) -> Function {
    let mut changed = function.clone();
    for node in &mut changed.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            *op = replacement;
            return changed;
        }
    }
    panic!("fixture has no binop");
}

const WSUM: &str = "def cleanWsum (a b : UInt64) : UInt64 := a + b";

#[test]
fn the_token_binds_the_environment_the_kernel_decided_in() {
    let env = environment(&[WSUM]);
    let (plan, signature, function) = emitted(&env, "cleanWsum");
    let token = admit_wrapping_binop(&env, &plan, 4, "m::cleanWsum", &signature, &function)
        .expect("gate admits");
    let here = GateEnvironment::of(&env, &Name::from_string("cleanWsum")).expect("digest");
    assert_eq!(token.environment(), &here);
    assert_eq!(here.kernel_version(), trust_clean_origin::local_kernel_version());
    assert_eq!(here.environment_digest().len(), 64, "a lowercase-hex SHA-256");
    token.authenticate_environment(&here).expect("the minting environment authenticates");

    // Another environment: the same declaration over a different dependency closure (the
    // closure of `cleanWsum` here reaches a second declaration it calls).
    let other_env = environment(&[
        "def helperAdd (a b : UInt64) : UInt64 := a + b",
        "def cleanWsum (a b : UInt64) : UInt64 := helperAdd a b",
    ]);
    let other = GateEnvironment::of(&other_env, &Name::from_string("cleanWsum")).expect("digest");
    assert_ne!(other, here, "fixture: the two closures must digest differently");
    let refusal = token
        .authenticate_environment(&other)
        .expect_err("a token is never read against another environment");
    assert_eq!(refusal.stage(), "token-environment", "{}", refusal.note());
}

#[test]
fn publication_may_add_exactly_the_carrier_stamp() {
    let env = environment(&[WSUM]);
    let (plan, signature, function) = emitted(&env, "cleanWsum");
    let token = admit_wrapping_binop(&env, &plan, 4, "m::cleanWsum", &signature, &function)
        .expect("gate admits");
    let stamped = published(&function);
    let entry = token
        .authenticate_published("cleanWsum", 4, "m::cleanWsum", &signature, &function, &stamped)
        .expect("the stamped publication authenticates");
    assert_eq!(entry.source_def_index(), 4);
    assert_eq!(entry.rust_def_path(), "m::cleanWsum");
    assert_eq!(entry.environment(), token.environment());
    assert_eq!(entry.carrier_tag(), "UInt64");

    // The unstamped publication (the pre-3.4 spelling) still authenticates, and digests
    // differently: the stamp is part of the subject.
    let mut unstamped = stamped.clone();
    unstamped.body_gate = None;
    let bare = token
        .authenticate_published("cleanWsum", 4, "m::cleanWsum", &signature, &function, &unstamped)
        .expect("an unstamped publication authenticates");
    assert_ne!(bare.subject_digest(), entry.subject_digest());
    assert_ne!(bare.ledger_digest(), entry.ledger_digest());

    // Any other licensing claim is a field change.
    for forged in [
        Some(BodyGate::Ungated),
        Some(BodyGate::Gated {
            authority: "trust-direct-lane-structural".to_string(),
            evidence: None,
        }),
        Some(BodyGate::Gated { authority: "clean-kernel-tv".to_string(), evidence: None }),
        Some(BodyGate::Gated {
            authority: format!("{CLEAN_CARRIER_GATE_AUTHORITY} "),
            evidence: None,
        }),
    ] {
        let mut wrong = stamped.clone();
        wrong.body_gate = forged.clone();
        let refusal = token
            .authenticate_published("cleanWsum", 4, "m::cleanWsum", &signature, &function, &wrong)
            .expect_err("only the exact carrier stamp may be added");
        assert_eq!(refusal.stage(), "published-relocation", "{forged:?}: {}", refusal.note());
    }
}

#[test]
fn a_ledger_entry_authenticates_only_its_exact_stamped_function() {
    let env = environment(&[WSUM]);
    let (plan, signature, function) = emitted(&env, "cleanWsum");
    let token = admit_wrapping_binop(&env, &plan, 4, "m::cleanWsum", &signature, &function)
        .expect("gate admits");
    let stamped = published(&function);
    let entry = token
        .authenticate_published("cleanWsum", 4, "m::cleanWsum", &signature, &function, &stamped)
        .expect("publication");
    entry.authenticate_function(&signature, &stamped).expect("the exact Function authenticates");

    // Edited after the gate: `a + b` became `a - b`. Still a wrapping binop at UInt64, so only
    // the digest can tell.
    let edited = with_binop(&stamped, BinOp::Sub);
    let refusal = entry.authenticate_function(&signature, &edited).expect_err("Add -> Sub");
    assert_eq!(refusal.stage(), "ledger-digest", "{}", refusal.note());

    // No stamp, another authority, another producer.
    let mut unstamped = stamped.clone();
    unstamped.body_gate = None;
    let refusal = entry.authenticate_function(&signature, &unstamped).expect_err("no stamp");
    assert_eq!(refusal.stage(), "ledger-stamp", "{}", refusal.note());
    let mut foreign = stamped.clone();
    foreign.body_gate =
        Some(BodyGate::Gated { authority: "clean-kernel-tv".to_string(), evidence: None });
    let refusal = entry.authenticate_function(&signature, &foreign).expect_err("foreign stamp");
    assert_eq!(refusal.stage(), "ledger-stamp", "{}", refusal.note());
    let mut rust = stamped.clone();
    rust.producer = Some(Producer::TRust);
    let refusal = entry.authenticate_function(&signature, &rust).expect_err("not Clean");
    assert_eq!(refusal.stage(), "ledger-producer", "{}", refusal.note());

    // Relocated into another module (another FuncId): the third rebind's job (step 3.6), not
    // this check's.
    let mut moved = stamped.clone();
    moved.id = FuncId::new(9);
    let refusal = entry.authenticate_function(&signature, &moved).expect_err("relocated");
    assert_eq!(refusal.stage(), "ledger-digest", "{}", refusal.note());
}

#[test]
fn the_ledger_digest_is_deterministic_and_in_its_own_domain() {
    // Two independent mints of one subject in one environment: one ledger digest. The subject
    // digest recipe is unchanged (pinned byte for byte by `standalone_gate.rs`); the ledger
    // digest is a separate domain over it and the verdict fields.
    let env = environment(&[WSUM]);
    let entry = |def_index: u32| {
        let (plan, signature, function) = emitted(&env, "cleanWsum");
        let token =
            admit_wrapping_binop(&env, &plan, def_index, "m::cleanWsum", &signature, &function)
                .expect("gate admits");
        token
            .authenticate_published(
                "cleanWsum",
                def_index,
                "m::cleanWsum",
                &signature,
                &function,
                &published(&function),
            )
            .expect("publication")
    };
    let (a, b, other) = (entry(4), entry(4), entry(5));
    assert_eq!(a.ledger_digest(), b.ledger_digest());
    assert_eq!(a.subject_digest(), b.subject_digest());
    assert_ne!(a.ledger_digest(), a.subject_digest(), "its own domain");
    assert_ne!(a.ledger_digest(), other.ledger_digest(), "the source identity is bound");
}
