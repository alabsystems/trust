// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 22 — the width of an island-authored `BitVec n`, read off the
//! REAL elaborator.**
//!
//! # The defect this control exists for
//!
//! `trust_clean_carrier::recognize` accepted `BitVec w` only when `w` was a
//! bare `Lit(Nat)`. No island-authored signature ever is one: the elaborator
//! records a `Nat` numeral as `@OfNat.ofNat Nat n (instOfNatNat n)`. So the
//! mint refused **every** `BitVec n` declaration with
//! `UnmodeledCleanType { rendered: "BitVec .." }` while the refusal it printed
//! went on offering `BitVec 8/16/32/64` as one of "the modeled value types" —
//! the compiler telling the user to use a spelling it then refuses. Measured
//! before the fix, 6 of the 10 `NoTotalCarrier` refusals over the whole in-tree
//! island corpus were this one shape.
//!
//! # Why this control is in THIS crate and hand-built `Expr`s are not enough
//!
//! `trust-clean-carrier` deliberately depends on exactly three crates and has
//! no elaborator (its `Cargo.toml` header: *"Exactly three. See the header
//! before adding a fourth."*), so its own tests must build the width term by
//! hand — and a hand-built term is a statement about what the author BELIEVES
//! the elaborator emits. That belief is the thing that was wrong. This file
//! runs the real `CleanIslandSession`, so the spelling under test is whatever
//! the elaborator actually produces today; if that changes again, this fails
//! rather than going quietly green.
//!
//! # The three halves
//!
//! * **half_1 — the positive.** `BitVec 8/16/32/64` in argument and result
//!   position CARRIES, at exactly `u8`/`u16`/`u32`/`u64`. That is the whole of
//!   what the carrier map decides, and it is what every READER of a carrier —
//!   contract clauses, citations, the declared-carrier lane, and the refusal
//!   renderer — now gets right.
//! * **half_1c — the boundary the carrier does NOT cross.** A total carrier is
//!   not permission to emit. The faithfulness gate reflects the EMITTED MIR
//!   using only that body's own local types, and the Clean domain it reads off
//!   `u64` is `UInt64` — a STRUCTURE whose one field is a `BitVec 64`, not the
//!   `BitVec 64` itself — so the reflection could never be definitionally equal
//!   to a `BitVec`-typed declaration. `plan_clean_origin_body` therefore
//!   refuses on side A with a named capability refusal, which is what keeps the
//!   mint from granting a `DefId` that would die inside `clean_origin_mir`.
//!   Measured: without that guard the two-line island plus a Rust caller
//!   compiles to `error: internal: refusing to emit code for Clean declaration
//!   `bvid``.
//! * **half_2 — the close negative twin.** A width that is not a literal —
//!   a `def`-bound constant (definitionally 64, and deliberately still
//!   refused: this map does not reduce) and an arithmetic expression — must
//!   keep refusing, BY NAME, as `BitVec ..`.
//! * **half_3 — the spelling pin.** The recorded width really is the
//!   `OfNat.ofNat` wrapper and not a bare literal, so half_1 is measuring the
//!   thing it claims to measure rather than passing for the old reason.

use clean_kernel::{Environment, Expr, ExprKind, Name};
use trust_clean_carrier::{CarrierRefused, carrier_signature_for};
use trust_clean_origin::plan_clean_origin_body;
use trust_types::Ty;

fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn type_of(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("the island registered no constant `{name}`"))
        .type_
        .clone()
}

const POSITIVE: &str = r"
def bv8  (x : BitVec 8)  : BitVec 8  := x
def bv16 (x : BitVec 16) : BitVec 16 := x
def bv32 (x : BitVec 32) : BitVec 32 := x
def bv64 (x : BitVec 64) : BitVec 64 := x
def bvmix (a : BitVec 64) (b : BitVec 8) : BitVec 8 := b
";

/// half_1 — every modeled width carries, at the exact Rust type.
#[test]
fn half_1_each_modeled_bitvec_width_carries() {
    let env = island(&[POSITIVE]);
    for (name, width) in [("bv8", 8_u32), ("bv16", 16), ("bv32", 32), ("bv64", 64)] {
        let signature = carrier_signature_for(&type_of(&env, name)).unwrap_or_else(|refusal| {
            panic!("`{name} : BitVec {width} -> BitVec {width}` must carry, got: {refusal}")
        });
        assert_eq!(signature.arity(), 1, "`{name}` takes one argument");
        let exact = Ty::Int { width, signed: false };
        assert_eq!(
            *signature.arguments()[0].rust(),
            exact,
            "`{name}`'s argument must carry at u{width} exactly"
        );
        assert_eq!(
            *signature.result().rust(),
            exact,
            "`{name}`'s result must carry at u{width} exactly"
        );
    }
}

/// half_1c — and it stops there, by name. A carried-but-unreflectable position
/// is refused on SIDE A, so no `DefId` is minted for it; the refusal names the
/// carrier as granted, says which half is missing, and carries options (v7/D3).
#[test]
fn half_1c_a_carried_bitvec_is_refused_by_the_reflection_not_by_the_carrier() {
    let env = island(&[POSITIVE]);
    for name in ["bv8", "bv16", "bv32", "bv64", "bvmix"] {
        let refusal = plan_clean_origin_body(&env, name)
            .err()
            .unwrap_or_else(|| panic!("`{name}` must NOT plan while side B cannot reflect it"));
        assert!(
            matches!(refusal, trust_clean_origin::EmitRefusal::CarrierDomainNotReflectable { .. }),
            "`{name}` must be refused for the REFLECTION, not for the carrier: {refusal:?}"
        );
        // It is a capability refusal about the compiler, never a "please
        // report this" — the user's declaration is fine.
        assert!(!refusal.is_compiler_defect(), "{refusal:?}");
        let note = refusal.note();
        for expected in ["carries TOTALLY", "options:", "UInt64", "BitVec"] {
            assert!(note.contains(expected), "the note must mention `{expected}`: {note}");
        }
    }
}

/// half_1b — the widths are read PER POSITION, not once for the signature. A
/// reader that took one width and reused it would pass half_1 and fail here.
#[test]
fn half_1b_positions_keep_their_own_widths() {
    let env = island(&[POSITIVE]);
    let signature = carrier_signature_for(&type_of(&env, "bvmix"))
        .expect("`bvmix : BitVec 64 -> BitVec 8 -> BitVec 8` must carry");
    assert_eq!(signature.arity(), 2);
    assert_eq!(*signature.arguments()[0].rust(), Ty::Int { width: 64, signed: false });
    assert_eq!(*signature.arguments()[1].rust(), Ty::Int { width: 8, signed: false });
    assert_eq!(*signature.result().rust(), Ty::Int { width: 8, signed: false });
}

/// half_2 — the close negative twin. A width that is not a literal is refused,
/// and the refusal NAMES the type. `bvdef` is the sharp one: `w` is
/// definitionally `64`, and the carrier map still refuses it, because the map
/// does not reduce — reduction is what turns `UInt64.ofNat (2^64)` into `0`.
#[test]
fn half_2_a_non_literal_width_still_refuses_by_name() {
    let env = island(&[r"
def w : Nat := 64
def bvdef  (x : BitVec w)         : BitVec w         := x
def bvexpr (x : BitVec (32 + 32)) : BitVec (32 + 32) := x
"]);
    for name in ["bvdef", "bvexpr"] {
        let refusal = carrier_signature_for(&type_of(&env, name))
            .err()
            .unwrap_or_else(|| panic!("`{name}` has a non-literal width and must NOT carry"));
        let rendered = refusal.to_string();
        assert!(
            rendered.contains("BitVec .."),
            "`{name}`'s refusal must NAME the type it refused, got: {rendered}"
        );
        assert!(
            rendered.contains("options:"),
            "v7/D3: the refusal must carry the fix, got: {rendered}"
        );
        // And it is the unmodeled-type refusal specifically, not some other
        // one that happens to mention `BitVec`.
        let position = trust_clean_carrier::carrier_for(&match type_of(&env, name).kind() {
            ExprKind::Pi(_, domain, _) => (**domain).clone(),
            other => panic!("`{name}` must be a Pi, got {other:?}"),
        })
        .expect_err("the argument position must refuse");
        assert!(
            matches!(&position, CarrierRefused::UnmodeledCleanType { rendered } if rendered == "BitVec .."),
            "expected UnmodeledCleanType{{ \"BitVec ..\" }}, got {position:?}"
        );
        // A refused position means no plan, which is what keeps it uncallable
        // — and this refusal is the CARRIER's, not the reflection's, which is
        // what separates this fixture from `half_1c`.
        let plan_refusal = plan_clean_origin_body(&env, name).expect_err("must not plan");
        assert!(
            matches!(plan_refusal, trust_clean_origin::EmitRefusal::NoTotalCarrier { .. }),
            "`{name}` must be refused by the CARRIER: {plan_refusal:?}"
        );
    }
}

/// half_3 — the spelling pin. This is what makes half_1 a measurement rather
/// than a hope: the recorded width is the `OfNat.ofNat` wrapper, so the arm
/// added for it is the arm being exercised.
#[test]
fn half_3_the_recorded_width_is_the_ofnat_wrapper_not_a_literal() {
    let env = island(&[POSITIVE]);
    let ty = type_of(&env, "bv64");
    let ExprKind::Pi(_, domain, _) = ty.kind() else { panic!("`bv64` must be a Pi") };
    let ExprKind::App(head, width) = domain.kind() else { panic!("the domain must be `BitVec w`") };
    assert!(matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "BitVec"));
    assert!(
        !matches!(width.kind(), ExprKind::Lit(_)),
        "if the elaborator has started recording a BARE literal, half_1 no longer \
         exercises the OfNat arm and this control must be re-read"
    );
    // The exact shape: `@OfNat.ofNat Nat (lit n) (instOfNatNat (lit n))`.
    let ExprKind::App(f2, instance) = width.kind() else { panic!("expected a 3-arg application") };
    let ExprKind::App(f1, _index) = f2.kind() else { panic!("expected a 3-arg application") };
    let ExprKind::App(of_nat, carrier) = f1.kind() else { panic!("expected a 3-arg application") };
    assert!(matches!(of_nat.kind(), ExprKind::Const(n, _) if n.to_string() == "OfNat.ofNat"));
    assert!(matches!(carrier.kind(), ExprKind::Const(n, _) if n.to_string() == "Nat"));
    let ExprKind::App(inst_head, _) = instance.kind() else { panic!("expected `instOfNatNat n`") };
    assert!(matches!(inst_head.kind(), ExprKind::Const(n, _) if n.to_string() == "instOfNatNat"));
}
