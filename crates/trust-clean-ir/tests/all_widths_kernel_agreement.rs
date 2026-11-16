// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! THE ALL-WIDTHS kernel agreement gate.
//!
//! `kernel_agreement.rs` establishes that emitted TrustIR agrees with the CIC
//! kernel, but it does so almost entirely at `UInt64` — measured when this file
//! was written, its rows were `UInt8` ×3, `UInt16` ×1, `UInt64` ×1, and no
//! `UInt32` at all. That leaves untested the property this lane is most likely
//! to get wrong and least likely to notice: **the width itself**.
//!
//! A carrier bug does not look like a wrong answer. A body emitted at `u64` for
//! a `UInt8` declaration returns the right value for every input that does not
//! reach the boundary, and every structural check passes, because the emitted
//! TrustIR is well-formed — it is well-formed at the wrong type. The input that
//! separates them is the modulus, and only the modulus.
//!
//! So every row here is run at EVERY admitted width, and the decisive rows are
//! the ones at the carrier boundary:
//!
//! * `MAX + 1 == 0` holds only if the emitted add is at THIS width. A body at
//!   any wider carrier answers `MAX + 1` and the kernel rejects it.
//! * `0 - 1 == MAX` holds only if the borrow is at THIS width — a wider carrier
//!   answers that width's MAX, a different number.
//! * `min(MAX, 1) == 1` holds only if the comparison is UNSIGNED at THIS width.
//!   A signed predicate reads MAX as negative and answers MAX.
//!
//! The oracle is the kernel, not this file: `unfold_island_application`
//! type-checks the application against the declaration's Pi telescope and
//! reduces with the kernel's own WHNF, and `is_def_eq` decides agreement. This
//! file chooses the inputs; it does not decide what the answer is.
//!
//! # What "all widths" means, and why the set is closed
//!
//! [`WIDTHS`] is exactly the set the emitter admits, which is exactly
//! `trust-clean-origin::carrier_class_of`'s `UInt(8 | 16 | 32 | 64)` and exactly
//! `trust_spec_elab::MachineUIntWidth`. That agreement is what makes this gate a
//! completeness statement rather than a sample: there is no admitted width that
//! this file does not cover, and the sibling unit test
//! `unwitnessable_widths_are_refused_rather_than_emitted` holds the other
//! direction shut — a width the island cannot name is refused, not emitted.
//!
//! Before this gate, those two sets disagreed in BOTH directions: the emitter
//! admitted a 128-bit carrier that no island name, no `MachineUIntWidth`, and
//! therefore no kernel could ever witness, while `UInt32` was admitted and
//! never checked.
//!
//! This remains a POINTWISE agreement check, exactly as its sibling is: it
//! witnesses agreement at the inputs tried and does not quantify over all
//! inputs. It is not the faithfulness gate, and it does not make this lane
//! proof-carrying. See the crate's `GATING` section.

use clean_kernel::{Environment, Expr, Name, TypeChecker};
use trust_certify::clean_island::unfold_island_application;
use trust_clean_ir::emit_clean_origin_function;
use trust_clean_origin::plan_clean_origin_body;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, FuncTyId};

/// One admitted machine carrier: its Clean name and its width.
#[derive(Clone, Copy)]
struct Carrier {
    clean: &'static str,
    bits: u32,
}

/// Every width the emitter admits — see the module note on why this set is
/// closed rather than a sample.
const WIDTHS: [Carrier; 4] = [
    Carrier { clean: "UInt8", bits: 8 },
    Carrier { clean: "UInt16", bits: 16 },
    Carrier { clean: "UInt32", bits: 32 },
    Carrier { clean: "UInt64", bits: 64 },
];

impl Carrier {
    fn ty(self) -> Ty {
        match self.bits {
            8 => Ty::U8,
            16 => Ty::U16,
            32 => Ty::U32,
            64 => Ty::U64,
            w => unreachable!("{w} is not an admitted carrier width"),
        }
    }

    fn max(self) -> u128 {
        (1u128 << self.bits) - 1
    }

    /// `UIntW.ofNat n` — the carrier-typed Clean value at this width.
    fn of_nat(self, n: u128) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string(&format!("{}.ofNat", self.clean)), vec![]),
            Expr::nat_lit(
                u64::try_from(n).expect("every admitted carrier value fits in a u64 literal"),
            ),
        )
    }
}

fn env_with(decl: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[decl]);
    assert!(!batch.is_rejected(), "the island must kernel-check `{decl}`: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// Run the emitted TrustIR at `args` and require the KERNEL to agree, at
/// `carrier`'s width.
///
/// `decl_tpl` is a declaration with `{C}` standing for the carrier name, so one
/// template is instantiated at every width and the widths cannot silently drift
/// apart in the test source.
fn kernel_agrees_at(carrier: Carrier, decl_tpl: &str, name: &str, args: &[u128]) -> u128 {
    let decl = decl_tpl.replace("{C}", carrier.clean);
    let env = env_with(&decl);
    let plan = plan_clean_origin_body(&env, name)
        .unwrap_or_else(|e| panic!("{}: `{decl}` must plan: {e:?}", carrier.clean));
    let f = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
        .unwrap_or_else(|e| panic!("{}: `{decl}` must emit: {e}", carrier.clean));

    // ── side 1: what the emitted TrustIR computes, AT THIS CARRIER ─────────
    let interp = Interpreter::new();
    let values: Vec<_> = args
        .iter()
        .map(|a| {
            InterpretValue::int(
                carrier.ty(),
                i128::try_from(*a).expect("an admitted carrier value fits an i128"),
            )
            .unwrap_or_else(|e| panic!("{a} must be a valid {} argument: {e:?}", carrier.clean))
        })
        .collect();
    let outcome = interp
        .execute_function(&f, values)
        .unwrap_or_else(|e| panic!("{}: the emitted TrustIR must execute: {e:?}", carrier.clean));
    let produced = outcome.returns[0].as_int().expect("an integer result").as_unsigned();

    // A result outside the carrier is a width bug even before the kernel is
    // asked — the interpreter would have had to carry it at something wider.
    assert!(
        produced <= carrier.max(),
        "{}: the emitted body produced {produced}, which does not fit the carrier (max {}). \
         The body was emitted at the wrong width.",
        carrier.clean,
        carrier.max(),
    );

    // ── side 2: what the KERNEL says the declaration is at those inputs ────
    let kernel_args: Vec<Expr> = args.iter().copied().map(|a| carrier.of_nat(a)).collect();
    let reduced = unfold_island_application(&env, name, &kernel_args).unwrap_or_else(|| {
        panic!("{}: the application must type-check and unfold in the island", carrier.clean)
    });

    // ── the agreement, decided by the kernel ───────────────────────────────
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&reduced, &carrier.of_nat(produced)),
        "KERNEL DISAGREEMENT for `{name}` at {} on {args:?}: the emitted TrustIR computed \
         {produced}, but the kernel reduced the Clean application to a term not definitionally \
         equal to `{}.ofNat {produced}`. This is a wrong binary, not a failed proof — the \
         emitted body and the Clean `def` denote different functions at this width.\n  \
         reduced: {reduced:?}",
        carrier.clean,
        carrier.clean,
    );
    produced
}

#[test]
fn every_admitted_width_projects_and_holds_its_constant() {
    for c in WIDTHS {
        assert_eq!(
            kernel_agrees_at(c, "def pick (a : {C}) (b : {C}) : {C} := a", "pick", &[7, 9]),
            7
        );
        assert_eq!(
            kernel_agrees_at(c, "def snd (a : {C}) (b : {C}) : {C} := b", "snd", &[7, 9]),
            9
        );
        assert_eq!(kernel_agrees_at(c, "def seven (a : {C}) : {C} := 7", "seven", &[3]), 7);
        // The projection at the boundary: a value the NEXT width down cannot
        // hold must survive being projected at this one.
        assert_eq!(
            kernel_agrees_at(c, "def pick (a : {C}) (b : {C}) : {C} := a", "pick", &[c.max(), 0]),
            c.max()
        );
    }
}

/// **The decisive width row.** `MAX + 1 == 0` at this width and nowhere else.
#[test]
fn every_admitted_width_wraps_addition_at_its_own_modulus() {
    let add = "def sum (a : {C}) (b : {C}) : {C} := a + b";
    for c in WIDTHS {
        assert_eq!(kernel_agrees_at(c, add, "sum", &[2, 3]), 5);
        assert_eq!(
            kernel_agrees_at(c, add, "sum", &[c.max(), 1]),
            0,
            "{} addition must wrap at 2^{}; a body emitted at a wider carrier answers {} here",
            c.clean,
            c.bits,
            c.max() + 1,
        );
        assert_eq!(kernel_agrees_at(c, add, "sum", &[c.max(), c.max()]), c.max() - 1);
    }
}

/// The borrow direction of the same property.
#[test]
fn every_admitted_width_borrows_subtraction_at_its_own_modulus() {
    let sub = "def diff (a : {C}) (b : {C}) : {C} := a - b";
    for c in WIDTHS {
        assert_eq!(kernel_agrees_at(c, sub, "diff", &[9, 4]), 5);
        assert_eq!(
            kernel_agrees_at(c, sub, "diff", &[0, 1]),
            c.max(),
            "{} subtraction must borrow to this width's MAX",
            c.clean,
        );
    }
}

#[test]
fn every_admitted_width_wraps_multiplication_at_its_own_modulus() {
    let mul = "def prod (a : {C}) (b : {C}) : {C} := a * b";
    for c in WIDTHS {
        assert_eq!(kernel_agrees_at(c, mul, "prod", &[3, 4]), 12);
        assert_eq!(kernel_agrees_at(c, mul, "prod", &[c.max(), 0]), 0);
        // MAX * 2 wraps to MAX - 1 at every width; a wider carrier does not.
        assert_eq!(kernel_agrees_at(c, mul, "prod", &[c.max(), 2]), c.max() - 1);
    }
}

/// The signedness row, at every width: `MAX` must read as the LARGEST value,
/// not as `-1`.
#[test]
fn every_admitted_width_compares_unsigned() {
    let minu = "def minu (a : {C}) (b : {C}) : {C} := if a < b then a else b";
    for c in WIDTHS {
        assert_eq!(kernel_agrees_at(c, minu, "minu", &[3, 9]), 3);
        assert_eq!(kernel_agrees_at(c, minu, "minu", &[9, 3]), 3);
        assert_eq!(kernel_agrees_at(c, minu, "minu", &[5, 5]), 5);
        assert_eq!(
            kernel_agrees_at(c, minu, "minu", &[c.max(), 1]),
            1,
            "{} `<` is UNSIGNED, so the minimum of (MAX, 1) is 1; an emitted `Slt` answers MAX",
            c.clean,
        );
    }
}

#[test]
fn every_admitted_width_composes() {
    let comp = "def comp (a : {C}) (b : {C}) : {C} := (a + b) * a";
    for c in WIDTHS {
        assert_eq!(kernel_agrees_at(c, comp, "comp", &[3, 4]), 21);
        assert_eq!(kernel_agrees_at(c, comp, "comp", &[0, 5]), 0);
    }
}

/// **The gate is not vacuous, and the ORACLE is what has to be shown non-vacuous.**
///
/// Every row above passes. That is only evidence if the kernel would have
/// REJECTED a wrong answer at these very inputs — a `is_def_eq` that said yes to
/// everything would produce exactly the same green.
///
/// So this asks the kernel the same question with a deliberately wrong value at
/// every width, and requires a NO. The wrong value is chosen to be inside the
/// carrier, so it cannot be rejected merely for not fitting: it is rejected
/// because the kernel computed something else.
#[test]
fn the_kernel_oracle_rejects_a_wrong_answer_at_every_width() {
    for c in WIDTHS {
        let decl = "def sum (a : {C}) (b : {C}) : {C} := a + b".replace("{C}", c.clean);
        let env = env_with(&decl);
        let args = [c.max(), 1];
        let kernel_args: Vec<Expr> = args.iter().copied().map(|a| c.of_nat(a)).collect();
        let reduced = unfold_island_application(&env, "sum", &kernel_args)
            .expect("the application must unfold");
        let tc = TypeChecker::new(&env);

        // The right answer, which the rows above rely on being accepted.
        assert!(tc.is_def_eq(&reduced, &c.of_nat(0)), "{}: MAX + 1 must reduce to 0", c.clean,);
        // The answer a body emitted one width too wide would give, reduced into
        // this carrier so the rejection cannot be about representability.
        assert!(
            !tc.is_def_eq(&reduced, &c.of_nat(1)),
            "{}: the kernel accepted 1 for MAX + 1 -- the oracle does not discriminate, so \
             every agreement row in this file is vacuous",
            c.clean,
        );
        assert!(
            !tc.is_def_eq(&reduced, &c.of_nat(c.max())),
            "{}: the kernel accepted MAX for MAX + 1 -- the oracle does not discriminate",
            c.clean,
        );
    }
}
