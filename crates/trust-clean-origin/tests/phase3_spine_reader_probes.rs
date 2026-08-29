// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **PHASE-3 SPINE READERS — the sum-measure lowering, read.**
//!
//! `first-party/clean`'s `wf_recursion::sum_measure` lowers a `termination_by`
//! measure that mentions SEVERAL parameters as a course-of-values recursion on
//! the measure's **value**:
//!
//! ```text
//! C     := fun (n : Nat) => Π (p⃗), Nat.lt m n → ret
//! F     := fun (n : Nat) (rec : (k : Nat) → Nat.lt k n → C k) (p⃗)
//!              (hm : Nat.lt m n) => body[ f a⃗ ↦ rec m hm a⃗ prf ]
//! value := fun (p⃗) => @WellFounded.fix.{1,v} Nat C Nat.lt hwf F
//!              (Nat.succ m) p⃗ (Nat.le.refl (Nat.succ m))
//! ```
//!
//! Every reader in this crate was written against **phase 2**, where the fix
//! runs on a PARAMETER: the motive is a constant `Nat` arrow tower, the spine
//! carries `5 + N` arguments, the functional binds `N + 1` binders, and a
//! self-call carries `N + 1` arguments with the decrease proof SECOND. Phase 3
//! moves all four at once — an `n`-DEPENDENT Pi motive, `7 + N` spine
//! arguments seeded `(Nat.succ m) p⃗ (Nat.le.refl (Nat.succ m))`, `N + 3`
//! functional binders because of the extra hypothesis binder, and an
//! `N + 3`-argument `rec` (FIVE at arity 2) with the decrease proof LAST.
//!
//! This file measures that the readers learned that shape **alongside** phase 2
//! and not instead of it.
//!
//! # What each probe decides
//!
//! | probe | decides |
//! |---|---|
//! | q1 | the hand-built spine is a term the KERNEL accepts, and it COMPUTES |
//! | q2 | the reader reads every component of the hand-built spine |
//! | q3 | the reader reads the REAL elaborated body the same way |
//! | q4 | the GATE parses phase-3 side A and borrows its decrease slots |
//! | c1 | a malformed phase-3 spine is REFUSED by the reader, component by component |
//! | c2 | a side B at the wrong phase-3 layout is REFUSED by the gate |
//! | c3 | a mutated side B is REFUSED even at the right layout |
//! | p2 | **PHASE 2 IS BYTE-IDENTICAL** — the plan, the layout numbers, and the gate's verdict |
//!
//! # Why a HAND-BUILT spine and a REAL one, and why the hand-built one comes first
//!
//! The task this file discharges was written when the superproject pin did not
//! carry the sum-measure lowering, so the only way to reach a phase-3 body was
//! to build one. Measured 2026-08-27, the pin DOES carry it (`first-party/clean`
//! `6adb7beeb`), so q3 drives the reader from the elaborator's own output.
//!
//! Both are kept, and the hand-built one is the PRIMARY. It is built in the RAW
//! kernel spellings (`Nat.lt`, `Nat.decLt`, `Nat.sub`, `Nat.add`) where the
//! elaborator emits SURFACE ones (`LT.lt`/`instLTNat`, `instDecidableNatLt`,
//! `HSub.hSub`, `HAdd.hAdd`) — the exact class of gap that made the R2 lane
//! unreachable for every program a user could write while its own suite stayed
//! green (`r2_session_probes` p1). A reader that passes q2 and q3 has been put
//! to both spellings. And the hand-built term is registered with `add_decl`, so
//! a malformed construction fails LOUDLY as a kernel error rather than
//! silently teaching the reader a shape nothing produces.
//!
//! # HONESTY RULE
//!
//! Every ADMIT here is paired with a refusal at the same layer. Nothing in this
//! file may be repaired by editing a side-B producer.

#![allow(clippy::doc_markdown)]

use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, FVarId, Level, Name, TypeChecker,
};
use trust_clean_origin::{
    DECREASE_SLOT_SENTINEL, MEASURE_SLOT_SENTINEL, ReflectedWfFunctional, WfLowering,
    check_faithful_wf_functional, plan_clean_origin_body, read_wf_sum_measure_anatomy,
};

// ═══════════════════════════════════════════════════════════════════════════
// harness
// ═══════════════════════════════════════════════════════════════════════════

/// Constants the hand-built encoding names. Checked up front so a missing
/// prelude piece fails with its own name rather than deep inside a term.
const REQUIRED: &[&str] = &[
    "Nat",
    "Nat.lt",
    "Nat.le.refl",
    "Nat.succ",
    "Nat.zero",
    "Nat.add",
    "Nat.sub",
    "Nat.sub_lt",
    "Nat.zero_lt_succ",
    "Nat.add_lt_add_left",
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

fn add(x: Expr, y: Expr) -> Expr {
    Expr::apps(c("Nat.add"), [x, y])
}

fn lt(x: Expr, y: Expr) -> Expr {
    Expr::apps(c("Nat.lt"), [x, y])
}

fn prelude() -> Environment {
    let env = Environment::with_prelude();
    let missing: Vec<&str> = REQUIRED
        .iter()
        .copied()
        .filter(|name| env.get_const(&Name::from_string(name)).is_none())
        .collect();
    assert!(missing.is_empty(), "the builtin prelude must provide the encoding; missing {missing:?}");
    env
}

fn island(source: &str) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    if batch.is_rejected() {
        let mut msgs: Vec<String> = batch
            .outcomes
            .iter()
            .flat_map(|outcome| outcome.errors.iter().map(|error| error.message.clone()))
            .collect();
        msgs.extend(batch.cycles.iter().map(|cycle| cycle.message.clone()));
        return Err(msgs.join(" | "));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
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
// THE HAND-BUILT PHASE-3 SPINE
// ═══════════════════════════════════════════════════════════════════════════

/// Which component of the encoding to break. `Faithful` is the real one; every
/// other variant changes EXACTLY one thing, so a refusal names one cause.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Break {
    /// Nothing — the real course-of-values encoding.
    None,
    /// The seed proof is `Nat.le.refl m` where the seed is `Nat.succ m`.
    Seed,
    /// The functional drops its `hm` binder (and the call passes `Nat.le.refl`
    /// in its place), so the telescope is `arity + 2` instead of `arity + 3`.
    BinderCount,
    /// The self-call drops its trailing decrease proof: `arity + 2` arguments
    /// where the slot takes `arity + 3`.
    RecArity,
    /// The motive is phase 2's constant `Nat` arrow tower.
    ConstantMotive,
    /// The relation is eta-expanded (`fun a b => Nat.lt a b`) rather than the
    /// bare constant the sum-measure lowering cites.
    EtaRelation,
}

/// Build `(type, value)` for
/// `probeSumRaw a b = if 0 < b then Nat.succ (probeSumRaw a (b - 1)) else a`
/// with `termination_by a + b`, in the course-of-values-on-the-MEASURE
/// encoding, exactly as `sum_measure.rs` builds it — and in the RAW kernel
/// spellings, which is the half the elaborated fixture does not cover.
fn build_probe_sum(broken: Break) -> (Expr, Expr) {
    let mut f = Fresh(0);
    let l1 = Level::succ(Level::zero());
    let nat_lt = c("Nat.lt");
    let succ = c("Nat.succ");
    let zero = c("Nat.zero");
    let one = Expr::app(succ.clone(), zero.clone());
    let arity = 2usize;

    let type_ = Expr::arrow(nat(), Expr::arrow(nat(), nat()));

    // C := fun (n : Nat) => (a b : Nat) → Nat.lt (Nat.add a b) n → Nat
    let (n_c, a_c, b_c) = (f.next(), f.next(), f.next());
    let motive = if broken == Break::ConstantMotive {
        // Phase 2's spelling: `fun _ => Nat -> Nat`, constant in the bound.
        Expr::lam(BinderInfo::Default, nat(), Expr::arrow(nat(), Expr::arrow(nat(), nat())))
    } else {
        let inner = Expr::arrow(lt(add(Expr::fvar(a_c), Expr::fvar(b_c)), Expr::fvar(n_c)), nat());
        let inner = Expr::pi(BinderInfo::Default, nat(), inner.abstract_fvar(b_c));
        let inner = Expr::pi(BinderInfo::Default, nat(), inner.abstract_fvar(a_c));
        Expr::lam(BinderInfo::Default, nat(), inner.abstract_fvar(n_c))
    };

    let relation = if broken == Break::EtaRelation {
        let (x, y) = (f.next(), f.next());
        let inner = lt(Expr::fvar(x), Expr::fvar(y));
        let inner = Expr::lam(BinderInfo::Default, nat(), inner.abstract_fvar(y));
        Expr::lam(BinderInfo::Default, nat(), inner.abstract_fvar(x))
    } else {
        nat_lt.clone()
    };

    // hwf := @WellFounded.intro.{1} Nat Nat.lt Nat.accNatLt
    let hwf = Expr::apps(
        c_at("WellFounded.intro", vec![l1.clone()]),
        [nat(), relation.clone(), c("Nat.accNatLt")],
    );

    // F := fun (n) (rec) (a b) (hm) => dite (0 < b) …
    let n = f.next();
    let rec_ty = {
        let k = f.next();
        let inner = Expr::arrow(
            lt(Expr::fvar(k), Expr::fvar(n)),
            Expr::app(motive.clone(), Expr::fvar(k)),
        );
        Expr::pi(BinderInfo::Default, nat(), inner.abstract_fvar(k))
    };
    let rec = f.next();
    let (a, b, hm) = (f.next(), f.next(), f.next());
    let hm_ty = lt(add(Expr::fvar(a), Expr::fvar(b)), Expr::fvar(n));
    let cond = lt(zero.clone(), Expr::fvar(b));
    let b_minus_1 = Expr::apps(c("Nat.sub"), [Expr::fvar(b), one.clone()]);

    let h = f.next();
    // `Nat.sub_lt b 1 h (Nat.zero_lt_succ Nat.zero) : Nat.lt (Nat.sub b 1) b`
    let sub_lt = Expr::apps(
        c("Nat.sub_lt"),
        [
            Expr::fvar(b),
            one.clone(),
            Expr::fvar(h),
            Expr::app(c("Nat.zero_lt_succ"), zero.clone()),
        ],
    );
    // `Nat.add_lt_add_left (b-1) b sub_lt a : Nat.lt (a + (b-1)) (a + b)` — the
    // real obligation: the SUM decreases although neither summand is inspected
    // by the relation.
    let decrease = Expr::apps(
        c("Nat.add_lt_add_left"),
        [b_minus_1.clone(), Expr::fvar(b), sub_lt, Expr::fvar(a)],
    );

    // `rec (a + b) hm a (b - 1) prf` — arity + 3 = FIVE arguments.
    let mut call_args = vec![
        add(Expr::fvar(a), Expr::fvar(b)),
        if broken == Break::BinderCount {
            // No `hm` binder to pass: the seed identity in its place. The term
            // does not kernel-check and is never registered; it exists only to
            // put a telescope of the wrong length in front of the reader.
            Expr::app(c("Nat.le.refl"), Expr::app(succ.clone(), add(Expr::fvar(a), Expr::fvar(b))))
        } else {
            Expr::fvar(hm)
        },
        Expr::fvar(a),
        b_minus_1.clone(),
    ];
    if broken != Break::RecArity {
        call_args.push(decrease);
    }
    let call = Expr::apps(Expr::fvar(rec), call_args);

    let then_body = Expr::app(succ.clone(), call);
    let then_lam = Expr::lam(BinderInfo::Default, cond.clone(), then_body.abstract_fvar(h));
    let h_neg = f.next();
    let else_lam = Expr::lam(
        BinderInfo::Default,
        Expr::app(c("Not"), cond.clone()),
        Expr::fvar(a).abstract_fvar(h_neg),
    );
    let dite_app = Expr::apps(
        c_at("dite", vec![l1.clone()]),
        [
            nat(),
            cond.clone(),
            Expr::apps(c("Nat.decLt"), [zero.clone(), Expr::fvar(b)]),
            then_lam,
            else_lam,
        ],
    );

    let fix_body = {
        let mut t = dite_app;
        if broken != Break::BinderCount {
            t = Expr::lam(BinderInfo::Default, hm_ty, t.abstract_fvar(hm));
        }
        let t = Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(b));
        let t = Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(a));
        let t = Expr::lam(BinderInfo::Default, rec_ty, t.abstract_fvar(rec));
        Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(n))
    };

    // value := fun a b => fix … (Nat.succ (a+b)) a b (Nat.le.refl (Nat.succ (a+b)))
    let (a_o, b_o) = (f.next(), f.next());
    let m_o = add(Expr::fvar(a_o), Expr::fvar(b_o));
    let succ_m = Expr::app(succ.clone(), m_o.clone());
    let fix = Expr::apps(
        c_at("WellFounded.fix", vec![l1.clone(), l1]),
        [nat(), motive, relation, hwf, fix_body, succ_m.clone()],
    );
    let seed_proof = Expr::app(
        c("Nat.le.refl"),
        if broken == Break::Seed { m_o } else { succ_m },
    );
    let applied = Expr::apps(fix, [Expr::fvar(a_o), Expr::fvar(b_o), seed_proof]);
    let value = {
        let t = Expr::lam(BinderInfo::Default, nat(), applied.abstract_fvar(b_o));
        Expr::lam(BinderInfo::Default, nat(), t.abstract_fvar(a_o))
    };

    assert_eq!(arity, 2, "the fixture is arity 2 by construction");
    (type_, value)
}

fn register(env: &mut Environment, name: &str, broken: Break) -> Result<(), String> {
    let (type_, value) = build_probe_sum(broken);
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .map_err(|error| format!("{error:?}"))
}

// ═══════════════════════════════════════════════════════════════════════════
// (q1) THE KERNEL PROBE — run BEFORE the reader is asked anything
// ═══════════════════════════════════════════════════════════════════════════

/// The hand-built phase-3 spine is a term the kernel ACCEPTS, and it COMPUTES.
///
/// Without this, q2 would only measure that a reader agrees with a Rust
/// function that built a tree — the shape could be one nothing produces. The
/// computation half is the part a typing check alone does not make: the fix has
/// to grind through `Acc.rec` and `Nat.accNatLt` to reduce.
#[test]
fn q1_the_hand_built_phase3_spine_kernel_checks_and_computes() {
    let mut env = prelude();
    register(&mut env, "probeSumRaw", Break::None)
        .expect("the course-of-values sum-measure encoding must kernel-check as written");

    let value = body_of(&env, "probeSumRaw");
    assert!(!value.has_sorry(), "the fixture must be sorry-free");

    // `probeSumRaw a b = a + b`, so `probeSumRaw 12 18` reduces to 30.
    let l1 = Level::succ(Level::zero());
    let eq_at = |lhs: Expr, rhs: Expr| Expr::apps(c_at("Eq", vec![l1.clone()]), [nat(), lhs, rhs]);
    let applied = Expr::apps(c("probeSumRaw"), [Expr::nat_lit(12), Expr::nat_lit(18)]);
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("probeSumRaw_12_18"),
        level_params: vec![],
        type_: eq_at(applied.clone(), Expr::nat_lit(30)),
        value: Expr::apps(c_at("Eq.refl", vec![l1.clone()]), [nat(), Expr::nat_lit(30)]),
    })
    .expect("`probeSumRaw 12 18` must COMPUTE to 30 by kernel reduction");

    // MUTATION CONTROL at the same layer: the computation is a decision.
    assert!(
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("probeSumRaw_12_18_bad"),
            level_params: vec![],
            type_: eq_at(applied, Expr::nat_lit(29)),
            value: Expr::apps(c_at("Eq.refl", vec![l1]), [nat(), Expr::nat_lit(29)]),
        })
        .is_err(),
        "`probeSumRaw 12 18 = 29` must be refused — otherwise the evidence above is vacuous"
    );

    // The one thing a hand-built decrease must not buy: the encoding admits no
    // axiom of its own.
    let foundational = ["propext", "Quot.sound", "Classical.choice"];
    let offending: Vec<String> = env
        .axiom_deps(&Name::from_string("probeSumRaw"))
        .expect("the fixture has an axiom closure")
        .iter()
        .map(ToString::to_string)
        .filter(|axiom| !foundational.contains(&axiom.as_str()))
        .collect();
    assert!(offending.is_empty(), "the encoding must admit no axiom, got {offending:?}");
}

// ═══════════════════════════════════════════════════════════════════════════
// (q2) THE READ — every component of the hand-built spine
// ═══════════════════════════════════════════════════════════════════════════

/// The reader reads the hand-built phase-3 spine, component by component.
#[test]
fn q2_the_reader_reads_the_hand_built_phase3_spine() {
    let mut env = prelude();
    register(&mut env, "probeSumRaw", Break::None).expect("the fixture registers");
    let body = body_of(&env, "probeSumRaw");

    let anatomy = read_wf_sum_measure_anatomy(&body)
        .unwrap_or_else(|why| panic!("the phase-3 reader must read its own fixture: {why}"));

    assert_eq!(anatomy.arity(), 2, "two parameters");

    // THE MEASURE, spelled as the SEED carries it: source parameter `i` is
    // `BVar(arity - 1 - i)`, so `a + b` is `Nat.add #1 #0`.
    assert_eq!(
        *anatomy.measure(),
        add(Expr::bvar(1), Expr::bvar(0)),
        "the measure is read out of the seed in the declaration's own parameter spelling"
    );
    // …and the MOTIVE and the `hm` binder had to agree with it on the nose, or
    // the reader would have refused. That is asserted negatively in c1.

    // The motive is n-DEPENDENT: `fun n => Nat -> Nat -> (Nat.lt (a+b) n -> Nat)`.
    let ExprKind::Lam(_, motive_binder, motive_body) = anatomy.motive().kind() else {
        panic!("the motive is a lambda over the course-of-values bound");
    };
    assert_eq!(**motive_binder, nat());
    assert!(
        motive_body.has_loose_bvar(0),
        "phase 3's motive DEPENDS on the recursion variable; phase 2's mentions no variable at \
         all, and that is what tells the two lowerings apart at the motive"
    );
    assert_eq!(*anatomy.return_ty(), nat());

    // THE SELF-CALL. One site, at depth 1 (under the `dite`'s positive-branch
    // binder), carrying its arguments in SOURCE order.
    assert_eq!(anatomy.calls().len(), 1, "exactly one self-call");
    let call = &anatomy.calls()[0];
    assert_eq!(call.depth(), 1, "the call sits under the guard's own hypothesis binder");
    // The MAJOR premise is the measure at the call site's own parameters — the
    // seed spelling lifted by `depth + 1`.
    assert_eq!(
        *call.major(),
        add(Expr::bvar(3), Expr::bvar(2)),
        "`rec`'s major premise is `m` at the enclosing parameters, which is what makes `hm` the \
         hypothesis the slot demands"
    );
    assert_eq!(call.arguments().len(), 2, "one argument per source parameter");
    assert_eq!(call.arguments()[0], Expr::bvar(3), "`a` unchanged");
    assert_eq!(
        call.arguments()[1],
        Expr::apps(c("Nat.sub"), [Expr::bvar(2), Expr::app(c("Nat.succ"), c("Nat.zero"))]),
        "`b - 1`"
    );
    // The decrease proof is READ, never authored: it is side A's own term.
    let (proof_head, proof_args) = {
        let mut args: Vec<&Expr> = Vec::new();
        let mut head = call.decrease_proof();
        while let ExprKind::App(function, argument) = head.kind() {
            args.push(argument);
            head = function;
        }
        args.reverse();
        (head.clone(), args.len())
    };
    assert_eq!(
        proof_head,
        c("Nat.add_lt_add_left"),
        "the decrease slot holds side A's real sum-congruence proof"
    );
    assert_eq!(proof_args, 4);

    // THE FOUR LAYOUT NUMBERS phase 3 moves, asserted against LITERALS rather
    // than against the functions that compute them.
    let phase3 = WfLowering::OnMeasureValue;
    assert_eq!(phase3.spine_arguments(2), 9, "α C r hwf F, the seed, 2 params, the seed proof");
    assert_eq!(phase3.functional_binders(2), 5, "n, rec, a, b, hm — the EXTRA hypothesis binder");
    assert_eq!(phase3.rec_binder_depth(2), 3, "`rec` at the functional body");
    assert_eq!(phase3.rec_call_arity(2), 5, "the FIVE-argument `rec`");
    assert_eq!(phase3.decrease_slot_position(2), 4, "the decrease proof is LAST");
}

// ═══════════════════════════════════════════════════════════════════════════
// (q3) THE SAME READ, on the elaborator's OWN output
// ═══════════════════════════════════════════════════════════════════════════

/// The `def` whose measure mentions both parameters and whose decrease the
/// elaborator's own cascade discharges. Its `+`, `-`, `<` and numerals all
/// arrive in SURFACE spellings, which is the half q2 cannot cover.
const PROBE_SUM_SOURCE: &str = "def probeSum (a b : Nat) : Nat := \
                                if h : 0 < b then Nat.succ (probeSum a (b - 1)) else a\n\
                                termination_by a + b";

/// The reader reads the body the ELABORATOR produces, and agrees with q2 about
/// the layout.
///
/// **This is the row that will move if the pin moves.** If `probeSum` stops
/// elaborating, the sum-measure lowering left the pin and this file's premise
/// is gone; if it elaborates to a DIFFERENT shape, the reader must be
/// re-measured, not patched.
#[test]
fn q3_the_reader_reads_the_elaborated_phase3_body() {
    let env = island(PROBE_SUM_SOURCE).unwrap_or_else(|why| {
        panic!(
            "the pin must still carry the sum-measure lowering — this whole lane is about the \
             shape it emits: {why}"
        )
    });
    let body = body_of(&env, "probeSum");
    let anatomy = read_wf_sum_measure_anatomy(&body).unwrap_or_else(|why| {
        panic!("the phase-3 reader must read the elaborator's own sum-measure body: {why}")
    });

    assert_eq!(anatomy.arity(), 2);
    assert_eq!(anatomy.calls().len(), 1);
    assert_eq!(anatomy.calls()[0].depth(), 1);
    assert_eq!(anatomy.calls()[0].arguments().len(), 2);
    assert_eq!(*anatomy.return_ty(), nat());
    // The measure arrives in the SURFACE spelling — `HAdd.hAdd` through
    // `instHAddNat`, not the raw `Nat.add` q2 built. The reader does not care,
    // and must not: it compares the measure to ITSELF across the seed, the
    // motive and the hypothesis binder, so any spelling is admitted as long as
    // the three agree.
    assert!(
        anatomy.measure().collect_constants().contains(&Name::from_string("HAdd.hAdd")),
        "the elaborated fixture is the SURFACE-spelling half of this measurement; if it has \
         become raw, the spelling gap this probe covers has moved"
    );
    // …and the raw fixture really is the other half.
    let mut raw_env = prelude();
    register(&mut raw_env, "probeSumRaw", Break::None).expect("the fixture registers");
    let raw = read_wf_sum_measure_anatomy(&body_of(&raw_env, "probeSumRaw")).expect("reads");
    assert!(raw.measure().collect_constants().contains(&Name::from_string("Nat.add")));

    // **THE DISPOSITION HERE FLIPPED IN R3d, and the old one is written out
    // because it is what a reader would search for.** R3c left this as: the call
    // lane refuses phase 3 outright, with a refusal naming the lowering ("it is
    // `first-party/clean`'s SUM-MEASURE lowering (WF phase 3) … READS that shape
    // … but does not yet EMIT it"). Phase 3 is EMITTED now
    // (`gcd_phase3_probes` p5), so that refusal is retired and this fixture
    // refuses for an ORDINARY reason instead: `Nat.succ (probeSum a (b - 1))`
    // applies `Nat.succ` to the self-call's result, and `Nat.succ` is not in the
    // branch-value vocabulary at either lowering.
    //
    // That is the honest state — the shape is emittable, this particular BODY is
    // not — and it is asserted rather than described so the two cannot drift.
    let refusal = plan_clean_origin_body(&env, "probeSum")
        .err()
        .expect("`Nat.succ` at a branch value is outside the fragment, at BOTH lowerings");
    let note = refusal.note();
    assert!(
        note.contains("outside this fragment's vocabulary"),
        "the refusal must be about the VALUE, which is what is actually wrong with this body — \
         not about the lowering, which is emittable: {note}"
    );
    assert!(
        !note.contains("does not yet EMIT it"),
        "R3d retired the not-yet-emitted refusal; a refusal that still says phase 3 cannot be \
         emitted is false of the compiler: {note}"
    );

    // …and the same body with `Nat.succ` written as `+ 1` — inside the
    // vocabulary — PLANS, which is what makes the row above a statement about
    // the value and not about the lowering.
    let plus_one = island(
        "def probeSumPlus (a b : Nat) : Nat := \
         if h : 0 < b then probeSumPlus a (b - 1) + 1 else a\n\
         termination_by a + b",
    )
    .expect("the `+ 1` spelling elaborates");
    let plan = plan_clean_origin_body(&plus_one, "probeSumPlus")
        .unwrap_or_else(|refusal| panic!("the phase-3 lane must PLAN this body: {}", refusal.note()));
    assert_eq!(
        format!("{:?}", plan.shape()),
        "WellFoundedNatRec { zero_value: Param(0), nonzero_value: Add(Rec, NatConst(1)), \
         rec_args: [Param(0), Pred], measure_index: 1, \
         lowering: OnMeasureValue }"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (q4) THE GATE — a phase-3 side A, and the borrow at its layout
// ═══════════════════════════════════════════════════════════════════════════

/// Replace the `position`-th argument of the single self-call in a phase-3
/// functional. Used to build side B (sentinel in the decrease slot) and every
/// adversarial variant of it, from SIDE A's own term — which is what makes the
/// controls differ from the admit in exactly one place.
fn rewrite_call_argument(expr: &Expr, rec_depth: u32, edit: &dyn Fn(usize, &Expr) -> Expr) -> Expr {
    fn go(expr: &Expr, depth: u32, edit: &dyn Fn(usize, &Expr) -> Expr) -> Expr {
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
                Expr::app(go(function, depth, edit), go(argument, depth, edit))
            }
            ExprKind::Lam(binder, ty, body) => {
                Expr::lam(*binder, go(ty, depth, edit), go(body, depth + 1, edit))
            }
            ExprKind::Pi(binder, ty, body) => {
                Expr::pi(*binder, go(ty, depth, edit), go(body, depth + 1, edit))
            }
            _ => expr.clone(),
        }
    }
    go(expr, rec_depth, edit)
}

/// Side A's functional with every binder kept and only the decrease slot
/// replaced, using `edit` on the call's arguments.
fn side_b_from(functional: &Expr, arity: usize, edit: &dyn Fn(usize, &Expr) -> Expr) -> Expr {
    let mut telescope: Vec<(clean_kernel::BinderData, Expr)> = Vec::new();
    let mut cursor = functional.clone();
    for _ in 0..WfLowering::OnMeasureValue.functional_binders(arity) {
        let ExprKind::Lam(binder, ty, inner) = cursor.kind() else {
            panic!("side A's functional binds what the lowering binds");
        };
        telescope.push((*binder, (**ty).clone()));
        cursor = (**inner).clone();
    }
    let mut rebuilt =
        rewrite_call_argument(&cursor, WfLowering::OnMeasureValue.rec_binder_depth(arity), edit);
    for (binder, ty) in telescope.into_iter().rev() {
        rebuilt = Expr::lam(binder, ty, rebuilt);
    }
    rebuilt
}

fn sentinel() -> Expr {
    Expr::const_(Name::from_string(DECREASE_SLOT_SENTINEL), vec![])
}

fn measure_sentinel() -> Expr {
    Expr::const_(Name::from_string(MEASURE_SLOT_SENTINEL), vec![])
}

/// The honest side B at phase 3: side A's functional with the FOUR positions a
/// MIR-derived term could never hold blanked to their sentinels.
///
/// **R3d added three of them.** R3c blanked the decrease proof alone, which was
/// enough while nothing emitted phase 3 and side B was built here out of side
/// A's own term. A real MIR-derived side B additionally cannot author the
/// MEASURE, which occupies the `rec` binder's type, the `hm` binder's type and
/// the self-call's major premise — see `gate::MEASURE_SLOT_SENTINEL`.
fn honest_side_b(functional: &Expr, arity: usize) -> Expr {
    let slot = WfLowering::OnMeasureValue.decrease_slot_position(arity);
    let blanked = side_b_from(functional, arity, &move |position, argument| match position {
        0 => measure_sentinel(),
        _ if position == slot => sentinel(),
        _ => argument.clone(),
    });
    blank_measure_binders(&blanked, arity)
}

/// Replace the two telescope binder TYPES the sum-measure lowering states in
/// terms of the measure — `rec` (position 1) and `hm` (position `arity + 2`) —
/// with the measure sentinel.
fn blank_measure_binders(functional: &Expr, arity: usize) -> Expr {
    let mut telescope: Vec<(clean_kernel::BinderData, Expr)> = Vec::new();
    let mut cursor = functional.clone();
    for position in 0..WfLowering::OnMeasureValue.functional_binders(arity) {
        let ExprKind::Lam(binder, ty, inner) = cursor.kind() else {
            panic!("the functional binds what the lowering binds");
        };
        let ty = if position == 1 || position == arity + 2 {
            measure_sentinel()
        } else {
            (**ty).clone()
        };
        telescope.push((*binder, ty));
        cursor = (**inner).clone();
    }
    let mut rebuilt = cursor;
    for (binder, ty) in telescope.into_iter().rev() {
        rebuilt = Expr::lam(binder, ty, rebuilt);
    }
    rebuilt
}

/// **THE GATE, AT PHASE 3.** Side A's spine parses, its decrease slots are
/// located at the sum-measure layout, and side B's sentinel is borrowed into
/// the LAST argument position rather than the second.
#[test]
fn q4_the_gate_parses_a_phase3_side_a_and_borrows_its_decrease_slots() {
    let env = island(PROBE_SUM_SOURCE).expect("the elaborated fixture is this probe's side A");
    let anatomy = read_wf_sum_measure_anatomy(&body_of(&env, "probeSum")).expect("reads");
    let reflected = ReflectedWfFunctional {
        functional: honest_side_b(anatomy.functional(), anatomy.arity()),
    };

    // Non-vacuity first: side B really is DIFFERENT from side A before the
    // borrow — it holds a constant the environment does not even declare.
    assert!(
        reflected.functional != *anatomy.functional(),
        "side B must differ from side A in the decrease slot, or the borrow is measuring nothing"
    );
    assert!(
        env.get_const(&Name::from_string(DECREASE_SLOT_SENTINEL)).is_none(),
        "the sentinel must not resolve, or the gate refuses the borrow outright"
    );
    let checker = TypeChecker::new(&env);
    assert!(
        checker.infer_type(&reflected.functional).is_err(),
        "before the borrow, side B does not even type-check — the borrow is what makes it a term \
         the kernel can be asked about"
    );
    drop(checker);

    let faithful = check_faithful_wf_functional(&env, "probeSum", &reflected, &nat_carrier())
        .unwrap_or_else(|refusal| {
            panic!("the gate must read a phase-3 side A and borrow its slots: {refusal:?}")
        });
    assert_eq!(faithful.name(), "probeSum");
}

// ═══════════════════════════════════════════════════════════════════════════
// (c1) THE READER'S CONTROLS — one broken component each
// ═══════════════════════════════════════════════════════════════════════════

/// A malformed phase-3 spine is REFUSED, and the refusal names the component.
///
/// Each row changes exactly one thing about the term q1 registered. Three of
/// them are the ones the lane was written to catch — **wrong seed, wrong binder
/// count, wrong `rec` arity** — and two more guard the classification itself
/// (a constant motive is PHASE 2 wearing phase 3's argument count; an
/// eta-expanded relation is not what `sum_measure.rs` cites).
#[test]
fn c1_a_malformed_phase3_spine_is_refused_component_by_component() {
    for (broken, expect) in [
        (Break::Seed, "DIFFERENT bound than the seed"),
        (Break::BinderCount, "binder(s) where the sum-measure lowering at arity 2 binds 5"),
        (Break::RecArity, "argument(s) where the sum-measure slot at arity 2 takes 5"),
        (Break::ConstantMotive, "does not end in the measure hypothesis"),
        (Break::EtaRelation, "not the bare constant `Nat.lt`"),
    ] {
        let (_, value) = build_probe_sum(broken);
        let why = read_wf_sum_measure_anatomy(&value)
            .err()
            .expect("a malformed sum-measure spine must be REFUSED, never read at some layout");
        assert!(
            why.contains(expect),
            "the refusal must name the component that broke; expected {expect:?}, got: {why}"
        );
    }

    // …and the kernel agrees about the three that are type errors rather than
    // shape choices, which is what keeps the controls from being a reader
    // talking to itself. (`ConstantMotive` and `EtaRelation` are not in this
    // list: a constant motive with a hypothesis-free `C` is ill-typed against
    // this functional, but an eta-expanded relation is a term the kernel is
    // perfectly happy with — it is refused because the sum-measure lowering
    // does not produce it, and that is a READER boundary, stated as one.)
    for broken in [Break::Seed, Break::BinderCount, Break::RecArity] {
        let mut env = prelude();
        assert!(
            register(&mut env, "probeSumBroken", broken).is_err(),
            "a spine the reader refuses for a TYPING reason must also be refused by the kernel"
        );
    }
    let mut env = prelude();
    assert!(
        register(&mut env, "probeSumEtaRel", Break::EtaRelation).is_ok(),
        "the eta-expanded relation is a KERNEL-legal term; the reader refuses it because the \
         sum-measure lowering does not emit it, and that boundary must be visible as a reader's"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (c2/c3) THE GATE'S CONTROLS
// ═══════════════════════════════════════════════════════════════════════════

/// A side B that writes its sentinel at PHASE 2's slot, or applies its
/// recursive slot at phase 2's arity, is REFUSED.
///
/// This is the control the whole lane rests on: if the gate had been taught
/// phase 3 by widening a count rather than by moving the decrease slot, this
/// row would ADMIT a functional whose termination evidence sits in the wrong
/// argument.
#[test]
fn c2_a_side_b_at_the_wrong_phase3_layout_is_refused() {
    let env = island(PROBE_SUM_SOURCE).expect("side A elaborates");
    let anatomy = read_wf_sum_measure_anatomy(&body_of(&env, "probeSum")).expect("reads");
    let arity = anatomy.arity();

    // (a) the sentinel at PHASE 2's position (the second argument, which
    //     phase 3 uses for the course-of-values hypothesis).
    let phase2_slot = WfLowering::OnParameter.decrease_slot_position(arity);
    // The measure plumbing is blanked honestly; ONLY the decrease slot sits at
    // phase 2's position (the second argument, which phase 3 uses for the
    // course-of-values hypothesis).
    let wrong_slot = side_b_from(anatomy.functional(), arity, &move |position, argument| {
        match position {
            0 => measure_sentinel(),
            _ if position == phase2_slot => sentinel(),
            _ => argument.clone(),
        }
    });
    let wrong_slot = blank_measure_binders(&wrong_slot, arity);
    let refusal = check_faithful_wf_functional(
        &env,
        "probeSum",
        &ReflectedWfFunctional { functional: wrong_slot },
        &nat_carrier(),
    )
    .err()
    .expect("a sentinel in phase 2's slot must be REFUSED at a phase-3 declaration");
    assert!(
        format!("{refusal:?}").contains("may not author a decrease proof"),
        "the refusal must be the borrow's, naming the slot: {refusal:?}"
    );

    // (b) a self-call at phase 2's ARITY — one argument short.
    let short = drop_last_call_argument(&honest_side_b(anatomy.functional(), arity), arity);
    let refusal = check_faithful_wf_functional(
        &env,
        "probeSum",
        &ReflectedWfFunctional { functional: short },
        &nat_carrier(),
    )
    .err()
    .expect("a self-call one argument short must be REFUSED");
    assert!(
        format!("{refusal:?}").contains("argument(s) where a self-call at this arity and \
                                         lowering carries 5"),
        "the refusal must name the lowering's own call arity: {refusal:?}"
    );

    // (c) a functional one binder short — the telescope disagrees with the
    //     spine the gate parsed for itself.
    let honest = honest_side_b(anatomy.functional(), arity);
    let ExprKind::Lam(_, _, inner) = honest.kind() else { panic!("side B is a lambda") };
    let refusal = check_faithful_wf_functional(
        &env,
        "probeSum",
        &ReflectedWfFunctional { functional: (**inner).clone() },
        &nat_carrier(),
    )
    .err()
    .expect("a functional one binder short must be REFUSED");
    assert!(
        format!("{refusal:?}").contains("binder(s) where this lowering binds 5")
            || format!("{refusal:?}").contains("recursive slot"),
        "the refusal must be about the telescope: {refusal:?}"
    );
}

/// Drop the LAST argument of the single self-call, giving a `rec` applied at
/// phase 2's arity inside a phase-3 functional.
fn drop_last_call_argument(functional: &Expr, arity: usize) -> Expr {
    let keep = WfLowering::OnMeasureValue.rec_call_arity(arity) - 1;
    fn go(expr: &Expr, depth: u32, keep: usize) -> Expr {
        match expr.kind() {
            ExprKind::App(function, argument) => {
                let mut args: Vec<&Expr> = Vec::new();
                let mut head = expr;
                while let ExprKind::App(f, a) = head.kind() {
                    args.push(a);
                    head = f;
                }
                args.reverse();
                if matches!(head.kind(), &ExprKind::BVar(index) if index == depth) {
                    let mut rebuilt = head.clone();
                    for argument in args.iter().take(keep) {
                        rebuilt = Expr::app(rebuilt, (*argument).clone());
                    }
                    return rebuilt;
                }
                Expr::app(go(function, depth, keep), go(argument, depth, keep))
            }
            ExprKind::Lam(binder, ty, body) => {
                Expr::lam(*binder, go(ty, depth, keep), go(body, depth + 1, keep))
            }
            ExprKind::Pi(binder, ty, body) => {
                Expr::pi(*binder, go(ty, depth, keep), go(body, depth + 1, keep))
            }
            _ => expr.clone(),
        }
    }
    let mut telescope: Vec<(clean_kernel::BinderData, Expr)> = Vec::new();
    let mut cursor = functional.clone();
    for _ in 0..WfLowering::OnMeasureValue.functional_binders(arity) {
        let ExprKind::Lam(binder, ty, inner) = cursor.kind() else { panic!("telescope") };
        telescope.push((*binder, (**ty).clone()));
        cursor = (**inner).clone();
    }
    let mut rebuilt = go(&cursor, WfLowering::OnMeasureValue.rec_binder_depth(arity), keep);
    for (binder, ty) in telescope.into_iter().rev() {
        rebuilt = Expr::lam(binder, ty, rebuilt);
    }
    rebuilt
}

/// A side B at the RIGHT layout but with a mutated self-call ARGUMENT is
/// refused — so q4's admit is a decision about the body, not about the shape.
#[test]
fn c3_a_mutated_phase3_side_b_is_refused_at_the_right_layout() {
    let env = island(PROBE_SUM_SOURCE).expect("side A elaborates");
    let anatomy = read_wf_sum_measure_anatomy(&body_of(&env, "probeSum")).expect("reads");
    let arity = anatomy.arity();
    let slot = WfLowering::OnMeasureValue.decrease_slot_position(arity);

    // `probeSum a (b - 1)` mutated to `probeSum a a` — well-typed, differently
    // valued, and the decrease slot is still the honest sentinel.
    let mutated = side_b_from(anatomy.functional(), arity, &move |position, argument| {
        match position {
            0 => measure_sentinel(),
            _ if position == slot => sentinel(),
            // the SECOND source argument (0: major, 1: hm, 2: a, 3: b)
            3 => Expr::bvar(3),
            _ => argument.clone(),
        }
    });
    let mutated = blank_measure_binders(&mutated, arity);
    let refusal = check_faithful_wf_functional(
        &env,
        "probeSum",
        &ReflectedWfFunctional { functional: mutated },
        &nat_carrier(),
    )
    .err()
    .expect("a mutated self-call argument must be REFUSED even with the honest sentinel");
    let rendered = format!("{refusal:?}");
    assert!(
        rendered.contains("DecreaseSlotBorrowRefused")
            || rendered.contains("FunctionalDisagreement"),
        "the mutation must die at the type check or the defeq, not somewhere else: {rendered}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (p2) PHASE 2 IS UNCHANGED
// ═══════════════════════════════════════════════════════════════════════════

/// The phase-2 fixture `addAcc` — arity 2, ONE-parameter measure, which is
/// exactly the shape R3a widened the lane to and the shape phase 3 must not
/// disturb.
const ADD_ACC_SOURCE: &str = "def addAcc (n acc : Nat) : Nat := \
                              if h : 0 < n then addAcc (n - 1) (acc + 1) else acc\n\
                              termination_by n";

/// **THE PHASE-2-UNCHANGED TEST.** An existing phase-2 body's plan is
/// byte-identical to the literal this file pins, its layout numbers are the
/// literals R2/R3a shipped, and the phase-3 reader refuses it outright.
///
/// The plan is compared as its `Debug` rendering against a string written out
/// here rather than recomputed: a comparison against something derived from the
/// same code path would move whenever the code path moved, which is the one
/// thing this test exists to notice.
#[test]
fn p2_a_phase2_body_still_plans_byte_identically() {
    let env = island(ADD_ACC_SOURCE)
        .unwrap_or_else(|why| panic!("the phase-2 fixture must still elaborate: {why}"));
    let plan = plan_clean_origin_body(&env, "addAcc")
        .unwrap_or_else(|refusal| panic!("the phase-2 fixture must still PLAN: {}", refusal.note()));

    assert_eq!(
        format!("{:?}", plan.shape()),
        "WellFoundedNatRec { zero_value: Param(1), nonzero_value: Rec, \
         rec_args: [Pred, Add(Param(1), NatConst(1))], measure_index: 0, \
         lowering: OnParameter }",
        "R3a's plan for `addAcc` must be UNCHANGED by the phase-3 readers"
    );

    // The phase-2 layout numbers, as literals.
    let phase2 = WfLowering::OnParameter;
    assert_eq!(phase2.spine_arguments(1), 6);
    assert_eq!(phase2.spine_arguments(2), 7);
    assert_eq!(phase2.functional_binders(1), 2, "R2's `x`, `rec`");
    assert_eq!(phase2.functional_binders(2), 3, "`r7` q1's three-binder functional");
    assert_eq!(phase2.rec_binder_depth(1), 0, "the literal R2 shipped");
    assert_eq!(phase2.rec_binder_depth(2), 1);
    assert_eq!(phase2.rec_call_arity(1), 2, "the literal R2 shipped");
    assert_eq!(phase2.rec_call_arity(2), 3, "`r7` q1 measured 3 at arity 2");
    assert_eq!(phase2.decrease_slot_position(1), 1, "phase 2 puts the proof SECOND, always");
    assert_eq!(phase2.decrease_slot_position(2), 1);

    // The phase-3 reader must not read a phase-2 body at all: the argument
    // counts differ by two at every arity, so this is a decision.
    let why = read_wf_sum_measure_anatomy(&body_of(&env, "addAcc"))
        .err()
        .expect("a phase-2 body is NOT the sum-measure lowering");
    assert!(
        why.contains("its spine carries 7 argument(s) under 2 binder(s)"),
        "the phase-3 reader must refuse a phase-2 body on the spine count: {why}"
    );

    // …and the arity-1 fixture the R2 batteries pin still plans too, so the
    // eta-contracted spelling did not move either.
    let env = island(
        "def countdown (n : Nat) : Nat := if h : 0 < n then n + countdown (n - 1) else 0\n\
         termination_by n",
    )
    .expect("the arity-1 fixture elaborates");
    assert_eq!(
        format!("{:?}", plan_clean_origin_body(&env, "countdown").expect("plans").shape()),
        "WellFoundedNatRec { zero_value: NatConst(0), \
         nonzero_value: Add(Decreasing, Rec), rec_args: [Pred], measure_index: 0, \
         lowering: OnParameter }",
        "R2's arity-1 plan must be UNCHANGED"
    );
}
