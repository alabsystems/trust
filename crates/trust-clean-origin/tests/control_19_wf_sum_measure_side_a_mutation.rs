// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 19 — the PHASE-3 SIDE-A mutation battery (R3e).**
//!
//! # The coverage gap this file closes
//!
//! Every phase-3 row that existed before it mutates the EMITTED BODY or SIDE B:
//! `control_18` exchanges the self-call's operands, moves the guard, reads the
//! wrong threaded parameter, transposes a leg's operands, swaps an operator, and
//! renders side B at phase 2's telescope; `phase3_spine_reader_probes` c2/c3 put
//! a wrong-layout and a mutated side B to the gate. **Not one of them changes
//! SIDE A.**
//!
//! That is the whole shape of the hole a three-lens review found. The phase-3
//! borrow takes four things from side A that MIR contains no trace of — every
//! self-call's decrease proof and MAJOR PREMISE, and the types of the `rec` and
//! `hm` binders. After the borrow both functionals hold side A's term at each of
//! those positions **by construction**, so neither the type check (step 7) nor
//! the defeq (step 8) can see anything about them. Whatever the gate has not
//! itself established about side A at a borrowed position, it never establishes
//! at all.
//!
//! And it had not established much: `check_faithful_wf_functional` read side A's
//! seed and its proof, and nothing else. `α = Nat`, `r = Nat.lt`, the motive's
//! shape and its hypothesis, both borrowed binder types, every major premise, and
//! THE ORDER of the spine's parameter arguments were read only by the plan lane's
//! `read_wf_sum_measure_anatomy`. The gate's reading of side A was a strict
//! SUBSET of the plan's at exactly the borrowed positions — which makes the plan
//! lane the sole enforcement of properties the gate's admission rests on, the
//! thing `parse_wf_fix_spine`'s own doc forbids ("the gate must rest on its own
//! reading of side A, never on the plan lane's") and `docs/TCB.md` denies.
//!
//! # EACH ROW MUTATES SIDE A AND NOTHING ELSE
//!
//! Every row registers a side A that **kernel-checks** (asserted, row by row —
//! a side A the kernel rejects would be refused by the gate's provenance step
//! and would measure nothing), builds side B from that declaration's own
//! functional by blanking the four borrowed positions, and calls
//! `check_faithful_wf_functional` **directly** — never `plan_clean_origin_body`,
//! never `admit_lowering`. The plan lane is not in the picture: what is being
//! measured is what the GATE ALONE will refuse.
//!
//! **Side B is byte-identical in every row, including the admit** (asserted in
//! `control_19_side_b_is_the_same_term_in_every_row`). Every side-A difference
//! here lives in the spine, the motive, or a position side B blanks, so the term
//! handed to the gate never changes. A row that refuses therefore refuses
//! because of side A, and for no other reason.
//!
//! # The fixture
//!
//! ```text
//! def cnt3 (a b c : Nat) : Nat := if h : 0 < a then cnt3 (a - 1) b c else b
//! termination_by a
//! ```
//!
//! hand-built in the sum-measure (phase-3) encoding and in RAW kernel spellings,
//! for the reason `phase3_spine_reader_probes` states: a hand-built term
//! registered with `add_decl` fails LOUDLY as a kernel error rather than
//! silently teaching a reader a shape nothing produces.
//!
//! `cnt3 a b c = b` for every input. That is deliberate: the function ignores
//! its third parameter's VALUE while binding it, so exchanging the spine's last
//! two arguments — row (a) — yields a declaration that denotes `cnt3 a c b`,
//! i.e. `c`. The kernel separates the two at `(2, 7, 9)`: 7 against 9, asserted
//! by `Eq.refl` in row (a). Arity THREE is required for that row to exist at
//! all: at arity 2 the only permutation of a spine's parameter arguments moves
//! the measure, and a permutation that moves the measure is a different measure
//! rather than a permuted one.
//!
//! # NOTHING HERE MAY BE REPAIRED BY EDITING A PRODUCER
//!
//! A row that stops refusing is a capability regression. In particular, none of
//! these rows can be fixed by changing what side B writes: side B is the same
//! term in all of them.

#![allow(clippy::doc_markdown)]

use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, FVarId, Level, Name, TypeChecker,
};
use trust_clean_origin::{
    DECREASE_SLOT_SENTINEL, MEASURE_SLOT_SENTINEL, ReflectedWfFunctional, WfLowering,
    check_faithful_wf_functional,
};

// ═══════════════════════════════════════════════════════════════════════════
// harness
// ═══════════════════════════════════════════════════════════════════════════

/// The declaration's arity. Three, and the file's doc says why.
const ARITY: usize = 3;

/// Constants the hand-built encoding names.
const REQUIRED: &[&str] = &[
    "Nat",
    "Nat.lt",
    "Nat.le.refl",
    "Nat.succ",
    "Nat.zero",
    "Nat.sub",
    "Nat.sub_lt",
    "Nat.zero_lt_succ",
    "Nat.accNatLt",
    "Nat.decLt",
    "Not",
    "dite",
    "WellFounded",
    "WellFounded.intro",
    "WellFounded.fix",
];

/// A monotone source of free variables; `abstract_fvar` only needs them
/// distinct.
struct Fresh(u64);

impl Fresh {
    fn next(&mut self) -> FVarId {
        self.0 += 1;
        FVarId::new(self.0)
    }
}

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn c_at(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

fn nat() -> Expr {
    c("Nat")
}

fn lt(x: Expr, y: Expr) -> Expr {
    Expr::apps(c("Nat.lt"), [x, y])
}

/// `(fun (t : Nat) => t) X` — definitionally `X` by beta, and a DIFFERENT term.
///
/// This is how rows (c) and (d) state "the same measure, spelled otherwise".
/// A beta redex is used rather than an arithmetic identity like `Nat.add x 0`
/// because it needs nothing from the prelude to be defeq: the row must isolate
/// the gate's on-the-nose comparison, not a reduction behaviour.
fn beta_wrapped(inner: Expr) -> Expr {
    Expr::app(Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)), inner)
}

fn prelude() -> Environment {
    let env = Environment::with_prelude();
    let missing: Vec<&str> = REQUIRED
        .iter()
        .copied()
        .filter(|name| env.get_const(&Name::from_string(name)).is_none())
        .collect();
    assert!(
        missing.is_empty(),
        "the builtin prelude must provide the encoding; missing {missing:?}"
    );
    env
}

fn nat_carrier() -> trust_clean_carrier::Carrier {
    trust_clean_carrier::carrier_for(&nat()).expect("I6: Nat carries at trust_bignum::Nat")
}

fn body_of(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .and_then(|constant| constant.value.clone())
        .unwrap_or_else(|| panic!("`{name}` must be a definition with a value"))
}

// ═══════════════════════════════════════════════════════════════════════════
// THE HAND-BUILT PHASE-3 SIDE A, and the ONE thing each row changes about it
// ═══════════════════════════════════════════════════════════════════════════

/// Which component of SIDE A to mutate. Every variant changes exactly one
/// thing, and every variant still KERNEL-CHECKS — that is what makes the row a
/// question for the gate rather than for the kernel.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mutation {
    /// Nothing — the real course-of-values encoding.
    None,
    /// (a) The spine passes the declaration's own parameters PERMUTED: `a c b`
    /// where the definition binds `a b c`. The functional is byte-identical;
    /// the declaration denotes `cnt3 a c b`.
    PermutedSpine,
    /// (b) The relation is eta-expanded `fun x y => Nat.lt x y` rather than the
    /// bare constant the sum-measure lowering cites. Kernel-legal (eta), and a
    /// term the lowering does not produce.
    EtaRelation,
    /// (c) The motive's hypothesis is stated at a beta-wrapped spelling of the
    /// measure the seed carries. Defeq, so it kernel-checks; a different term,
    /// so the three measure sites no longer name ONE measure.
    MotiveHypothesis,
    /// (d) The self-call's MAJOR PREMISE — a borrowed position — is a
    /// beta-wrapped spelling of the measure at the enclosing parameters.
    MajorPremise,
}

/// Build `(type, value)` for
///
/// ```text
/// cnt3 a b c = if h : 0 < a then cnt3 (a - 1) b c else b   termination_by a
/// ```
///
/// in the course-of-values-on-the-MEASURE encoding, exactly as
/// `first-party/clean`'s `sum_measure.rs` builds it, and in the RAW kernel
/// spellings.
fn build_cnt3(mutation: Mutation) -> (Expr, Expr) {
    let mut f = Fresh(0);
    let l1 = Level::succ(Level::zero());
    let succ = c("Nat.succ");
    let zero = c("Nat.zero");
    let one = Expr::app(succ.clone(), zero.clone());

    let type_ = Expr::arrow(nat(), Expr::arrow(nat(), Expr::arrow(nat(), nat())));

    // C := fun (n : Nat) => (x y z : Nat) → Nat.lt x n → Nat
    //
    // The measure is the FIRST parameter, so the motive's hypothesis names `x`.
    let (n_c, x_c, y_c, z_c) = (f.next(), f.next(), f.next(), f.next());
    let motive_measure = if mutation == Mutation::MotiveHypothesis {
        beta_wrapped(Expr::fvar(x_c))
    } else {
        Expr::fvar(x_c)
    };
    let motive = {
        let inner = Expr::arrow(lt(motive_measure, Expr::fvar(n_c)), nat());
        let inner = Expr::pi(BinderInfo::Default, nat(), inner.abstract_fvar(z_c));
        let inner = Expr::pi(BinderInfo::Default, nat(), inner.abstract_fvar(y_c));
        let inner = Expr::pi(BinderInfo::Default, nat(), inner.abstract_fvar(x_c));
        Expr::lam(BinderInfo::Default, nat(), inner.abstract_fvar(n_c))
    };

    let relation = if mutation == Mutation::EtaRelation {
        let (p, q) = (f.next(), f.next());
        let inner = lt(Expr::fvar(p), Expr::fvar(q));
        let inner = Expr::lam(BinderInfo::Default, nat(), inner.abstract_fvar(q));
        Expr::lam(BinderInfo::Default, nat(), inner.abstract_fvar(p))
    } else {
        c("Nat.lt")
    };

    // hwf := @WellFounded.intro.{1} Nat r Nat.accNatLt
    let hwf = Expr::apps(
        c_at("WellFounded.intro", vec![l1.clone()]),
        [nat(), relation.clone(), c("Nat.accNatLt")],
    );

    // F := fun (n) (rec) (x y z) (hm) => dite (0 < x) …
    let n = f.next();
    let rec_ty = {
        let k = f.next();
        let inner =
            Expr::arrow(lt(Expr::fvar(k), Expr::fvar(n)), Expr::app(motive.clone(), Expr::fvar(k)));
        Expr::pi(BinderInfo::Default, nat(), inner.abstract_fvar(k))
    };
    let rec = f.next();
    let (x, y, z, hm) = (f.next(), f.next(), f.next(), f.next());
    let hm_ty = lt(Expr::fvar(x), Expr::fvar(n));
    let cond = lt(zero.clone(), Expr::fvar(x));
    let x_minus_1 = Expr::apps(c("Nat.sub"), [Expr::fvar(x), one.clone()]);

    let h = f.next();
    // `Nat.sub_lt x 1 h (Nat.zero_lt_succ Nat.zero) : Nat.lt (Nat.sub x 1) x`
    let decrease = Expr::apps(
        c("Nat.sub_lt"),
        [Expr::fvar(x), one.clone(), Expr::fvar(h), Expr::app(c("Nat.zero_lt_succ"), zero.clone())],
    );

    // `rec m hm x' y' z' prf` — arity + 3 = SIX arguments, the decrease LAST.
    let major = if mutation == Mutation::MajorPremise {
        beta_wrapped(Expr::fvar(x))
    } else {
        Expr::fvar(x)
    };
    let call = Expr::apps(
        Expr::fvar(rec),
        [major, Expr::fvar(hm), x_minus_1, Expr::fvar(y), Expr::fvar(z), decrease],
    );

    let then_lam = Expr::lam(BinderInfo::Default, cond.clone(), call.abstract_fvar(h));
    let h_neg = f.next();
    let else_lam = Expr::lam(
        BinderInfo::Default,
        Expr::app(c("Not"), cond.clone()),
        // The ZERO arm returns the SECOND parameter — the asymmetry row (a)
        // needs, and the reason `cnt3 a b c` and `cnt3 a c b` are different
        // functions rather than the same one twice.
        Expr::fvar(y).abstract_fvar(h_neg),
    );
    let dite_app = Expr::apps(
        c_at("dite", vec![l1.clone()]),
        [
            nat(),
            cond.clone(),
            Expr::apps(c("Nat.decLt"), [zero.clone(), Expr::fvar(x)]),
            then_lam,
            else_lam,
        ],
    );

    let functional = {
        let t = Expr::lam(BinderInfo::Default, hm_ty, dite_app.abstract_fvar(hm));
        let t = Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(z));
        let t = Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(y));
        let t = Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(x));
        let t = Expr::lam(BinderInfo::Default, rec_ty, t.abstract_fvar(rec));
        Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(n))
    };

    // value := fun a b c => fix … (Nat.succ a) a b c (Nat.le.refl (Nat.succ a))
    let (a_o, b_o, c_o) = (f.next(), f.next(), f.next());
    let succ_m = Expr::app(succ.clone(), Expr::fvar(a_o));
    let fix = Expr::apps(
        c_at("WellFounded.fix", vec![l1.clone(), l1]),
        [nat(), motive, relation, hwf, functional, succ_m.clone()],
    );
    // THE PERMUTATION, and the only thing row (a) changes: the last two
    // parameter arguments are exchanged. The seed and its proof are untouched,
    // because the measure is parameter 0 and the permutation does not move it —
    // which is exactly why the term still kernel-checks.
    let parameters = if mutation == Mutation::PermutedSpine {
        [Expr::fvar(a_o), Expr::fvar(c_o), Expr::fvar(b_o)]
    } else {
        [Expr::fvar(a_o), Expr::fvar(b_o), Expr::fvar(c_o)]
    };
    let seed_proof = Expr::app(c("Nat.le.refl"), succ_m);
    let applied = Expr::apps(
        fix,
        [parameters[0].clone(), parameters[1].clone(), parameters[2].clone(), seed_proof],
    );
    let value = {
        let t = Expr::lam(BinderInfo::Default, nat(), applied.abstract_fvar(c_o));
        let t = Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(b_o));
        Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(a_o))
    };

    (type_, value)
}

/// Register a mutated side A under `name`, and REQUIRE the kernel to accept it.
///
/// The assertion is the row's premise: a side A the kernel rejects is refused
/// by the gate's provenance step for a reason that has nothing to do with what
/// this file measures.
fn register(env: &mut Environment, name: &str, mutation: Mutation) {
    let (type_, value) = build_cnt3(mutation);
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|error| {
        panic!(
            "the {mutation:?} side A must KERNEL-CHECK — a row whose declaration the kernel \
             rejects measures the kernel, not the gate: {error:?}"
        )
    });
}

/// A one-declaration environment holding a mutated side A.
fn env_with(mutation: Mutation) -> Environment {
    let mut env = prelude();
    register(&mut env, "cnt3", mutation);
    env
}

// ═══════════════════════════════════════════════════════════════════════════
// SIDE B — built from SIDE A's own functional, identically in every row
// ═══════════════════════════════════════════════════════════════════════════

fn decrease_sentinel() -> Expr {
    Expr::const_(Name::from_string(DECREASE_SLOT_SENTINEL), vec![])
}

fn measure_sentinel() -> Expr {
    Expr::const_(Name::from_string(MEASURE_SLOT_SENTINEL), vec![])
}

/// Peel the spine off side A's value and hand back the functional (argument 4).
fn functional_of(env: &Environment, name: &str) -> Expr {
    let mut cursor = body_of(env, name);
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        cursor = (**inner).clone();
    }
    let mut args: Vec<Expr> = Vec::new();
    let mut head = cursor;
    while let ExprKind::App(function, argument) = head.kind() {
        args.push((**argument).clone());
        head = (**function).clone();
    }
    args.reverse();
    assert_eq!(
        args.len(),
        WfLowering::OnMeasureValue.spine_arguments(ARITY),
        "the fixture is a sum-measure spine at arity {ARITY}"
    );
    args[4].clone()
}

/// Replace the arguments of the single self-call inside a phase-3 functional's
/// body, at the `rec` binder's own depth.
fn rewrite_call(expr: &Expr, depth: u32, edit: &dyn Fn(usize, &Expr) -> Expr) -> Expr {
    match expr.kind() {
        ExprKind::App(..) => {
            let mut args: Vec<&Expr> = Vec::new();
            let mut head = expr;
            while let ExprKind::App(function, argument) = head.kind() {
                args.push(argument);
                head = function;
            }
            args.reverse();
            if matches!(head.kind(), &ExprKind::BVar(index) if index == depth) {
                let mut rebuilt = head.clone();
                for (position, argument) in args.iter().enumerate() {
                    rebuilt = Expr::app(rebuilt, edit(position, argument));
                }
                return rebuilt;
            }
            let ExprKind::App(function, argument) = expr.kind() else { unreachable!() };
            Expr::app(rewrite_call(function, depth, edit), rewrite_call(argument, depth, edit))
        }
        ExprKind::Lam(binder, ty, body) => {
            Expr::lam(*binder, rewrite_call(ty, depth, edit), rewrite_call(body, depth + 1, edit))
        }
        ExprKind::Pi(binder, ty, body) => {
            Expr::pi(*binder, rewrite_call(ty, depth, edit), rewrite_call(body, depth + 1, edit))
        }
        _ => expr.clone(),
    }
}

/// **THE HONEST SIDE B**: side A's functional with the FOUR positions a
/// MIR-derived term could never hold blanked to their sentinels — the two
/// binder types stated in terms of the measure, the self-call's major premise,
/// and its decrease proof.
///
/// This is the same construction `phase3_spine_reader_probes` q4 uses, and it
/// is the ONLY side B this file ever hands the gate.
fn honest_side_b(functional: &Expr) -> Expr {
    let lowering = WfLowering::OnMeasureValue;
    let slot = lowering.decrease_slot_position(ARITY);
    let mut telescope: Vec<(clean_kernel::BinderData, Expr)> = Vec::new();
    let mut cursor = functional.clone();
    for position in 0..lowering.functional_binders(ARITY) {
        let ExprKind::Lam(binder, ty, inner) = cursor.kind() else {
            panic!("side A's functional binds what this lowering binds");
        };
        let ty = if position == 1 || position == ARITY + 2 {
            measure_sentinel()
        } else {
            (**ty).clone()
        };
        telescope.push((*binder, ty));
        cursor = (**inner).clone();
    }
    let mut rebuilt =
        rewrite_call(&cursor, lowering.rec_binder_depth(ARITY), &move |position, argument| {
            match position {
                0 => measure_sentinel(),
                _ if position == slot => decrease_sentinel(),
                _ => argument.clone(),
            }
        });
    for (binder, ty) in telescope.into_iter().rev() {
        rebuilt = Expr::lam(binder, ty, rebuilt);
    }
    rebuilt
}

/// Put a mutated side A to **the gate alone** — never `plan_clean_origin_body`,
/// never `admit_lowering` — with the honest side B built from that
/// declaration's own functional.
fn gate(mutation: Mutation) -> Result<(), String> {
    let env = env_with(mutation);
    let reflected =
        ReflectedWfFunctional { functional: honest_side_b(&functional_of(&env, "cnt3")) };
    check_faithful_wf_functional(&env, "cnt3", &reflected, &nat_carrier())
        .map(|_| ())
        .map_err(|refusal| format!("{refusal:?}"))
}

// ═══════════════════════════════════════════════════════════════════════════
// THE ADMIT — the anchor every row below is a sibling of
// ═══════════════════════════════════════════════════════════════════════════

/// The unmutated side A ADMITS, and the borrow is not vacuous.
#[test]
fn control_19_the_unmutated_side_a_admits() {
    let env = env_with(Mutation::None);
    let functional = functional_of(&env, "cnt3");
    let side_b = honest_side_b(&functional);

    // Non-vacuity, exactly as q4 states it: side B really is DIFFERENT from
    // side A before the borrow, and does not even type-check on its own.
    assert!(side_b != functional, "side B must differ from side A at the borrowed positions");
    for sentinel in [DECREASE_SLOT_SENTINEL, MEASURE_SLOT_SENTINEL] {
        assert!(
            env.get_const(&Name::from_string(sentinel)).is_none(),
            "`{sentinel}` must not resolve, or the gate refuses the borrow outright"
        );
    }
    let checker = TypeChecker::new(&env);
    assert!(
        checker.infer_type(&side_b).is_err(),
        "before the borrow side B does not type-check — the borrow is what makes it a term the \
         kernel can be asked about"
    );
    drop(checker);

    gate(Mutation::None).expect("the honest sum-measure side A must admit at the gate");
}

/// **Side B is the SAME TERM in every row**, so nothing but side A varies.
///
/// Without this, a refusal below could be a statement about side B — and the
/// file would be measuring its own producer instead of the gate's reading of
/// the declaration.
#[test]
fn control_19_side_b_is_the_same_term_in_every_row() {
    let honest = honest_side_b(&functional_of(&env_with(Mutation::None), "cnt3"));
    for mutation in [
        Mutation::PermutedSpine,
        Mutation::EtaRelation,
        Mutation::MotiveHypothesis,
        Mutation::MajorPremise,
    ] {
        let side_b = honest_side_b(&functional_of(&env_with(mutation), "cnt3"));
        assert_eq!(
            side_b, honest,
            "{mutation:?} must change SIDE A only — every difference it makes to the functional \
             sits at a position side B blanks, so the term handed to the gate is unchanged"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (a) THE PERMUTED SPINE — the refuted safety argument's own counterexample
// ═══════════════════════════════════════════════════════════════════════════

/// A side A whose spine applies the declaration to its own parameters PERMUTED
/// is REFUSED, and the kernel says the two declarations are different functions.
///
/// Before R3e the gate marked a `seen` slot per argument and refused only a
/// REPEAT or a non-parameter, so this passed — with a BYTE-IDENTICAL functional,
/// therefore an identical type check, an identical closure audit and an
/// identical defeq. The permutation lives entirely in the spine's argument list,
/// which the F-layer comparison never reads.
#[test]
fn control_19_a_a_permuted_spine_is_refused_by_the_gate_alone() {
    // The two functionals are the same bytes: nothing the F layer looks at
    // differs, which is why nothing but a spine-order check can catch this.
    assert_eq!(
        functional_of(&env_with(Mutation::PermutedSpine), "cnt3"),
        functional_of(&env_with(Mutation::None), "cnt3"),
        "the permutation must live in the SPINE, or this row is measuring something else"
    );

    // THE KERNEL SEPARATES THE TWO DECLARATIONS. `cnt3 a b c = b`, so the
    // permuted spine denotes `c`. Both reduce; the values differ.
    let mut env = prelude();
    register(&mut env, "cnt3", Mutation::None);
    register(&mut env, "cnt3Permuted", Mutation::PermutedSpine);
    let l1 = Level::succ(Level::zero());
    let eq_at = |lhs: Expr, rhs: Expr| Expr::apps(c_at("Eq", vec![l1.clone()]), [nat(), lhs, rhs]);
    let value_of = |callee: &str, want: u64| {
        let applied = Expr::apps(c(callee), [Expr::nat_lit(2), Expr::nat_lit(7), Expr::nat_lit(9)]);
        Declaration::Theorem {
            name: Name::from_string(&format!("{callee}_2_7_9")),
            level_params: vec![],
            type_: eq_at(applied, Expr::nat_lit(want)),
            value: Expr::apps(c_at("Eq.refl", vec![l1.clone()]), [nat(), Expr::nat_lit(want)]),
        }
    };
    env.add_decl(value_of("cnt3", 7)).expect("`cnt3 2 7 9` must COMPUTE to 7");
    env.add_decl(value_of("cnt3Permuted", 9))
        .expect("the permuted declaration must COMPUTE to 9 — a DIFFERENT function");
    // …and the two values are a decision, not a coincidence of the encoding.
    assert!(
        env.add_decl(value_of("cnt3Permuted", 7)).is_err(),
        "if the permuted declaration also computed to 7 this row would be vacuous"
    );

    // THE GATE, ALONE, REFUSES IT.
    let refusal = gate(Mutation::PermutedSpine).expect_err(
        "a permuted spine must never admit: the emitted body would compute `b` for a \
                     declaration that denotes `c`",
    );
    assert!(
        refusal.contains("PERMUTED") && refusal.contains("NotWellFoundedRecursor"),
        "the refusal must name the permutation, from the gate's OWN spine parse: {refusal}"
    );
    eprintln!("ROW 19(a) | {}", refusal.chars().take(200).collect::<String>());
}

// ═══════════════════════════════════════════════════════════════════════════
// (b) THE WRONG RELATION
// ═══════════════════════════════════════════════════════════════════════════

/// A side A whose `r` is the eta-expanded `fun x y => Nat.lt x y` is REFUSED.
///
/// This is a FRAGMENT boundary and is stated as one: the term is perfectly
/// kernel-legal (eta is definitional here, and `phase3_spine_reader_probes` c1
/// measures that it registers), and it denotes the same function. It is refused
/// because `sum_measure.rs` cites the bare constant and the gate's borrow is
/// measured against the lowering that lowering produces — a fix at a relation
/// nothing in the pin emits is a shape whose borrowed positions this lane has
/// no measurement for. The plan lane has always read this; until R3e the gate
/// did not, and that asymmetry is the defect, not the strictness.
#[test]
fn control_19_b_a_relation_the_lowering_does_not_produce_is_refused() {
    let refusal = gate(Mutation::EtaRelation)
        .expect_err("a relation other than the bare `Nat.lt` must not admit at this lane");
    assert!(
        refusal.contains("bare constant `Nat.lt`"),
        "the refusal must name the relation: {refusal}"
    );
    eprintln!("ROW 19(b) | {}", refusal.chars().take(200).collect::<String>());
}

// ═══════════════════════════════════════════════════════════════════════════
// (c) THE WRONG MOTIVE HYPOTHESIS
// ═══════════════════════════════════════════════════════════════════════════

/// A side A whose motive states its hypothesis at a DEFEQ-but-different
/// spelling of the measure is REFUSED.
///
/// The typing rules leave exactly this much room and no more: the seed proof
/// `Nat.le.refl (Nat.succ m)` forces the motive's hypothesis at the passed
/// arguments to be **definitionally** `m`, never syntactically, so a beta
/// wrapper passes the kernel while breaking the identification the borrow rests
/// on. The gate reads the motive against the seed's measure ON THE NOSE, and
/// this row is why: the borrow copies TERMS out of `hm` and out of every major
/// premise, and "these sites name one measure" is what makes the copied terms
/// the measure at all.
#[test]
fn control_19_c_a_motive_hypothesis_at_another_spelling_is_refused() {
    let refusal = gate(Mutation::MotiveHypothesis)
        .expect_err("a motive whose hypothesis is not at the seed's own measure must not admit");
    assert!(
        refusal.contains("motive's hypothesis") && refusal.contains("SAME measure"),
        "the refusal must name the motive and the measure: {refusal}"
    );
    eprintln!("ROW 19(c) | {}", refusal.chars().take(200).collect::<String>());
}

// ═══════════════════════════════════════════════════════════════════════════
// (d) THE WRONG MAJOR PREMISE — a BORROWED position
// ═══════════════════════════════════════════════════════════════════════════

/// A side A whose self-call's MAJOR PREMISE is not the measure at the enclosing
/// parameters is REFUSED.
///
/// This is the sharpest row in the file, because the major premise is a position
/// the gate **borrows**: side B writes the measure sentinel there and receives
/// side A's term. After the borrow both functionals hold that term, so the type
/// check and the defeq are blind to it by construction — whatever the gate does
/// not decide about this position here, nothing downstream decides at all. Before
/// R3e the gate decided nothing about it.
#[test]
fn control_19_d_a_major_premise_that_is_not_the_measure_is_refused() {
    let refusal = gate(Mutation::MajorPremise).expect_err(
        "a major premise other than the measure at the enclosing parameters must not \
                     admit — it is BORROWED into side B unexamined",
    );
    assert!(
        refusal.contains("MAJOR PREMISE"),
        "the refusal must name the major premise: {refusal}"
    );
    eprintln!("ROW 19(d) | {}", refusal.chars().take(200).collect::<String>());
}
