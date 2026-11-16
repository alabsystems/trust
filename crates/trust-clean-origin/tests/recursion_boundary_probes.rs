// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **RECURSION-BOUNDARY PROBES — the exact structural case now admitted, and
//! why general `gcd` recursion remains outside the fragment.**
//!
//! `docs/design/2026-08-04-two-language-compiler-architecture.md` §6c records
//! *"`gcd` is unreachable at every slice — recursion is outside all five
//! recognizer arms"*. That sentence is a slogan until each side has a pinned
//! verdict. This file measures the boundary the same way
//! `fragment_widening_probes.rs` measured the binop widening — at the kernel,
//! against the FROZEN side-B producers, before any rustc work — so the
//! increment that closes it is designed against measurements, not guesses.
//!
//! # The measured boundary (2026-08-20, this file's assertions ARE the record)
//!
//! | # | seam | verdict |
//! |---|---|---|
//! | r1 | kernel `add_decl`, direct self-reference | REFUSED — `UnknownConst`; a `Definition`'s value is checked BEFORE its name exists (`clean-kernel/src/env/decl_add.rs` Phase 1 `check_type`, Phase 2 insert), and `Declaration` has exactly four variants (Definition/Axiom/Theorem/Opaque — `env/mod.rs`, `add_staged_header`'s match), none a fixpoint |
//! | r2 | prelude machinery | `Nat.rec`, `Acc`, `Acc.rec`, `WellFounded`, `WellFounded.fix`/`fixF`, `Nat.lt_wf` ALL present in `with_prelude` (the island session's env); `Nat.brecOn`/`Nat.strongRecOn` do NOT exist (Clean is not Lean 4 here) |
//! | r3 | kernel holds STRUCTURAL recursion | ADMIT — as a plain `Nat.rec` application (`fun n => @Nat.rec.{1} (fun _ => Nat) Nat.zero (fun k ih => ih) n`), and it COMPUTES under defeq (`tozero 1 ≡ 0`); planner: **the constant-zero fold PLANS `StructuralNatRec` — pin FLIPPED 2026-08-21 with the R1 arm** (was `NotEmittable`; the flip lands in the same change as the plan/recognise arms and the per-equation gate, per the no-silent-ratchet rule), while the succ-ih identity fold (outside the R1 case vocabulary) falls through to the inductive-projection fallback, plans `InductiveProjection`, and its emitted bignum projection re-earns a structural-induction verdict |
//! | r4 | kernel holds WF recursion | ADMIT — as a `WellFounded.fix` application over `Nat.lt`/`Nat.lt_wf`; its defeq reduction behaviour on a closed argument is pinned below (load-bearing for any future gate); planner: `NotEmittable`, now with the R2-seam reason (kernel-checked equation lemmas are the prerequisite) |
//! | r5 | recursion at a CARRIER-friendly signature | ADMIT (`UInt64 → UInt64` via `Nat.rec` on `toNat`) — total carriers exist, so the planner refusal isolates RECURSION, not the carrier, as the boundary; planner: `NotEmittable`, now naming the MEASURED e2 boundary (open u64-carrier equations are not definitional — `Nat.mod` sticks) with the restate-at-Nat option |
//! | r6 | side B: recognizer on self-call MIR | `None` — no `recognize_admissible_body` arm accepts a `Call` to a non-marker callee, so a self-call (minimal or full gcd shape) never recognizes there — **still true after R1**, by design: the structural-recursion recognizer is the SEPARATE entry point `recognize_structural_rec` (E6 import stays blind to recursion), and it refuses both these shapes too (no zero-test contract, wrong carrier, `Rem`) |
//! | r7 | side B: the four mint paths | `p0 % 7` MINTS but `p0 % p1` — gcd's own remainder — is REFUSED (variable divisor needs a nonzero side-condition, not yet wired), a call has no spelling, and no `admit_*` takes a fixpoint — neither gcd's recursion NOR its arithmetic has a side-B spelling today (R1's recursion lane reflects through `trust_clean_origin::reflect_rec`, not through these paths) |
//! | r8 | induction discovery resources | a nine-parameter Nat identity fold has nine eligible projection candidates and is REFUSED as one declaration before proof search; the lane never truncates to eight or multiplies a timeout by arity |
//!
//! # What the ISLAND lane does with `gcd` (measured 2026-08-20, via
//! `trust_certify::clean_island::CleanIslandSession` — the exact compiler
//! path; harness outside this file because trust-certify is not a dependency)
//!
//! **R0 diagnostic flip — landed in the sibling and now AT THE PIN.**
//! Written on `alabsystems/clean` branch `recursion-refusal-r0`, commit
//! **`f391bd4664a9bd95eae814e449db8a941bd66dce`** (2026-08-22). When this
//! header was first written the superproject still pinned `315d9a41c`, so the
//! rows below carry a "was" column (what the compiler printed then) and a
//! "now" column (what the R0 commit prints). Measured 2026-09-21: the
//! `first-party/clean` gitlink (`faf434b73`) contains `f391bd4664`, so the
//! "now" column is what THIS tree compiles; "was" is history.
//!
//! What it changes: the five gcd-shaped REJECTED rows below surfaced as
//! `UnknownIdentWithSuggestions`/`UnknownIdent`, and the suggestion machinery
//! offered `Quotient.ind` for `gcd` — a name-distance guess, actively
//! misleading for a self-reference. Per v7/D3 the elaborator recognizes that
//! the unknown identifier IS the name being defined and refuses with
//! `ElabError::RecursionOutsideFragment`, verbatim:
//!
//! > `gcd` is the name being defined: a self-reference in a def body is a
//! > recursive definition, not a missing name. Recursive definitions are
//! > supported for structural recursion (match/equation form on a
//! > structurally decreasing parameter) and for single-parameter
//! > well-founded recursion with `termination_by`; the form of `gcd` (2
//! > parameter(s); neither lowering applied) is outside today's fragment.
//! >   help: ways forward, in order of preference — (1) restate `gcd`
//! >   structurally: match on one parameter and recurse on its immediate
//! >   sub-term, which lowers through that type's recursor and needs no
//! >   termination argument at all; (2) reduce `gcd` to ONE recursing
//! >   parameter and give it `termination_by <that parameter>` — a
//! >   multi-parameter measure is not lowered yet, so thread the others
//! >   through an inner single-parameter helper; (3) if `gcd` is only needed
//! >   to STATE something, write it in proof position — a signature plus the
//! >   equations you rely on, each disclosed by name — where no emitted body
//! >   is required.
//!
//! The adjacent batch case — an identifier matching a same-batch declaration
//! whose header failed collection — refuses with
//! `ElabError::SameBatchHeaderUnavailable`, which names the sibling, says why
//! it staged no header, and points at repairing IT rather than at the use
//! site. EVERY verdict below is unchanged (still REJECTED / ADMITTED exactly
//! as measured): the refusal is raised where resolution has already failed,
//! so only the text moved, and the two ADMITTING rows still register the same
//! values. Measured in the sibling:
//! `clean-elab/tests/recursion_refusal_diagnostic_e2e.rs` (9 probes, every
//! refusal paired with an admit/typo/no-leak control) plus 5 in
//! `clean-elab/tests/name_resolution_e2e.rs` pinning that the three
//! unknown-identifier diagnostics stay sorted.
//!
//! | island source | verdict |
//! |---|---|
//! | `def gcd (a b : Nat) : Nat := if b == 0 then a else gcd b (a % b)` (§1 demo, verbatim shape) | REJECTED — at the pin `UnknownIdentWithSuggestions { name: "gcd" }` (offering `Quotient.ind`); on the R0 branch `RecursionOutsideFragment { name: "gcd", decl: "gcd", params: 2 }` |
//! | same at `UInt64` | REJECTED — at the pin `UnknownIdentWithSuggestions { name: "gcd64" }` (also offering `Quotient.ind`); on the R0 branch `RecursionOutsideFragment` (params 2) |
//! | same + `termination_by b` | at the pin `UnknownIdentWithSuggestions { name: "gcd2" }`; on the R0 branch `RecursionOutsideFragment` (params 2, sibling-tested); **on branch `gcd-bool-spelling` ADMITTED, and `gcd 12 18` computes to `6` by `rfl`** — see the R4 amendment below |
//! | `if h : 0 < b then gcd4 b (a % b) else a` + `termination_by b` (the passing class's spelling, 2 params) | REJECTED — at the pin `UnknownIdentWithSuggestions { name: "gcd4" }`; on the R0 branch `RecursionOutsideFragment` (params 2) |
//! | equation form `\| a, 0 => a \| a, b => gcd3 b (a % b)` | REJECTED — at the pin `UnknownIdentWithSuggestions { name: "gcd3" }`; on the R0 branch `RecursionOutsideFragment` with the NORMALIZED param count (2 — the surface decl writes no binders at all; sibling-tested) |
//! | `def tozero : Nat -> Nat \| 0 => 0 \| n + 1 => tozero n` | ADMITTED — value IS `fun n => @Nat.rec.{1} (fun _ => Nat) (OfNat.ofNat Nat 0 …) (fun n ih => ih) n` |
//! | `def fib : Nat -> Nat \| 0 => 0 \| 1 => 1 \| n + 2 => fib (n+1) + fib n` | ADMITTED as TWO defs — `fib.cov : Nat → Prod Nat Nat` (pair-threaded `Nat.rec`) + `fib = fun n => Prod.fst (fib.cov n)` |
//! | `def down (n : Nat) : Nat := if n == 0 then 0 else down (n - 1)` + `termination_by n` | at the pin REJECTED fail-closed in the WF path: *"no decreasing proof was found for a recursive call site (tried: hypothesis lookup, Nat.sub_lt, omega, simp_arith)"*; **on branch `gcd-bool-spelling` ADMITTED and computing** — the same Bool-test lane as `gcd2`, discharged through `Nat.sub_lt` instead of `Nat.mod_lt` |
//! | `def countdownSum (n : Nat) : Nat := if h : 0 < n then n + countdownSum (n - 1) else 0` + `termination_by n` | **ADMITTED** — value IS `@WellFounded.fix.{1,1} Nat (fun _ => Nat) (fun a b => Nat.lt a b) (WellFounded.intro … Acc.rec … Nat.accNatLt …) (fun x rec => dite …)` — the elaborator's WF lowering (`clean-elab/src/infer/wf_recursion/mod.rs:20-26`), phase-1 limits at `mod.rs:45-59`: ONE parameter, Nat measure, cascade-dischargeable decreases |
//!
//! # R4 amendment (2026-08-22) — the Bool-test spelling now ADMITS on a branch
//!
//! **Originally a BRANCH measurement.** When written, the gitlink still named
//! R3 (`27a46804e`) and the rows marked *"on branch `gcd-bool-spelling`"* were
//! measured in `first-party/clean` on that branch. Measured 2026-09-21: the
//! pin (`faf434b73`) contains both `27a46804e` and the R4 commit, so those rows
//! now describe what this repo compiles.
//!
//! What changed there, and what it cost:
//!
//! * **`ite` → `dite` inside the well-founded lowering only.** A non-dependent
//!   `ite` binds no hypothesis, so `if b == 0 then …`'s else branch knew
//!   nothing about `b` and `a % b < b` was underivable — not hard, underivable.
//!   The rewrite is DEFINITIONAL (`ite` and `dite` are both reducible and
//!   δ-unfold to the same `Decidable.casesOn`), kernel-confirmed by an `rfl`
//!   fixture, which is why `gcd 12 18` still reduces to `6`.
//! * **Two prelude theorems, PROVED, foundational-only closure:**
//!   `Nat.pos_of_ne_zero : ∀ n, ¬(n = 0) → 0 < n` and
//!   `of_not_decide_eq_true : ¬(decide p = true) → ¬p`. No axiom was added —
//!   this is the trust root, and an axiom here is precisely the escape the
//!   closure audits look for.
//!
//! Two things did NOT change and are worth not misreading: `gcd` with **no**
//! `termination_by` is still REJECTED (R4 extends what a DECLARED measure can
//! discharge; it adds no measure inference), and a genuinely two-parameter
//! (lexicographic) measure is still REJECTED. Sibling evidence:
//! `clean-elab/tests/r4_gcd_bool_spelling_e2e.rs` (12 probes) and
//! `clean-elab/tests/r4_bool_test_bridge_probes.rs`.
//!
//! So the island elaborator holds recursion in exactly two kernel forms —
//! `T.rec` applications (structural, incl. the fib/mutual/projection
//! desugars) and `WellFounded.fix` applications (phase-1 WF). At the pin `gcd`
//! fits neither: its recursion is non-structural AND two-parameter (the WF path
//! was single-parameter), so every spelling is rejected. On the branches above
//! that is no longer the shape of the boundary — R3 widened the SIGNATURE while
//! keeping the measure single-parameter, and R4 discharged the Bool-test
//! decrease. Termination
//! evidence is kernel-grade BY CONSTRUCTION for anything that does enter: the
//! only route into the island environment is `Environment::add_decl`'s full
//! check (`clean-kernel/src/env/decl_add.rs`, `check_declaration_core` —
//! `tc.check_type(value, type_)` before Phase-2 insertion), where a recursor
//! application terminates by iota reduction over per-constructor
//! `RecursorRule`s (`clean-kernel/src/inductive/mod.rs:129-137`, strict
//! positivity `:394-488`; reduction in `tc/whnf.rs`, `beta_or_iota_step`
//! `:616`) and a `WellFounded.fix` term bottoms out in the constructive
//! `Acc`/`Nat.lt_wf` witnesses (`env/algebra_advanced/well_founded.rs:27`,
//! `env/nat_lt_wf_proof.rs:75` — sorry-free, with no non-foundational
//! domain/trust assumptions). There is
//! no partial/unsafe/meta escape on the island lane.
//!
//! # The corpus fact
//!
//! No probe in `tests/e6-fragment-probe/probes/` (d01–d14, f01–f24) ever
//! exercised a recursive def: every island `def` in the corpus (`fst_isl`,
//! `min_isl`, `winc_isl`, `composed_isl`, `const42`, …) is non-recursive, and
//! the only `.rec` any probe mentions is `Bool.rec` as the ELABORATION of
//! if-then-else (d06/f01) — not user recursion. This file is the first
//! measurement of the recursion seam anywhere in the tree.
//!
//! # HONESTY RULES (same as the controls and the widening probes)
//!
//! * A probe that REFUSES asserts the refusal and its kind. A probe that
//!   ADMITS asserts admission. No probe passes vacuously.
//! * Admitting probes carry a paired MUTATION control.
//! * Side B's producers are FROZEN against this lane: if a verdict here is
//!   not the one you want, the fix is a new emitter shape or kernel/prelude
//!   work — never an edit to `recognize_admissible_body`, `admit_*_function`,
//!   or this fixture's assertions.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker};
use trust_clean_origin::{
    CleanOriginShape, EmitRefusal, FaithfulnessMethod, admit_lowering, plan_clean_origin_body,
};
use trust_spec_elab::{Domain, MachineUIntWidth};
use trust_types::admissible_body::{
    RecBodyExpr, recognize_admissible_body, recognize_structural_rec,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ───────────────────────────── side A helpers ─────────────────────────────

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn uint64() -> Expr {
    Expr::const_(Name::from_string("UInt64"), vec![])
}

fn cnst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn lvl1() -> Level {
    Level::succ(Level::zero())
}

/// Insert `def name : type_ := value` through the FULL kernel check, panicking
/// on refusal — the widening probes' `define` convention.
fn define(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    try_define(env, name, type_, value)
        .unwrap_or_else(|e| panic!("`{name}` must kernel-check as written: {e}"));
}

/// The same insertion, refusal returned as data (probe r1 measures it).
fn try_define(env: &mut Environment, name: &str, type_: Expr, value: Expr) -> Result<(), String> {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .map_err(|e| format!("{e:?}"))
}

/// `fun (n : Nat) => @Nat.rec.{1} (fun _ => Nat) Nat.zero step n` — the exact
/// kernel form the island elaborator produces for a structural equation-form
/// def (measured 2026-08-20; the elaborated `tozero` differs only in spelling
/// its base numeral through `OfNat.ofNat`).
fn nat_rec_body(step: Expr) -> Expr {
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![lvl1()]),
        [
            Expr::lam(BinderInfo::Default, nat(), nat()), // motive: fun _ => Nat
            cnst("Nat.zero"),                             // base
            step,                                         // fun k ih => ...
            Expr::bvar(0),                                // scrutinee n
        ],
    );
    Expr::lam(BinderInfo::Default, nat(), rec_app)
}

/// Identity fold over an already-bound Nat scrutinee.
fn nat_identity_rec(scrutinee: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![lvl1()]),
        [
            Expr::lam(BinderInfo::Default, nat(), nat()),
            cnst("Nat.zero"),
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(BinderInfo::Default, nat(), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
            ),
            scrutinee,
        ],
    )
}

/// `fun (n : Nat) => @WellFounded.fix.{1,1} Nat (fun _ => Nat) Nat.lt
/// Nat.lt_wf F n` with `F = fun x rec => body` — the raw-kernel spelling of
/// the form the WF elaboration path produces (binder order per
/// `clean-kernel/src/env/algebra_advanced/well_founded.rs`, fix type: α, C,
/// r, hwf, F, x; level params `[u, v]`).
fn wf_fix_body(f_body: Expr) -> Expr {
    // rec : (y : Nat) → Nat.lt y x → Nat, under binder x (bvar 1 inside).
    let rec_ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::arrow(Expr::apps(cnst("Nat.lt"), [Expr::bvar(0), Expr::bvar(1)]), nat()),
    );
    let f = Expr::lam(BinderInfo::Default, nat(), Expr::lam(BinderInfo::Default, rec_ty, f_body));
    let fix_app = Expr::apps(
        Expr::const_(Name::from_string("WellFounded.fix"), vec![lvl1(), lvl1()]),
        [
            nat(),                                        // α
            Expr::lam(BinderInfo::Default, nat(), nat()), // C: fun _ => Nat
            cnst("Nat.lt"),                               // r
            cnst("Nat.lt_wf"),                            // hwf
            f,                                            // F
            Expr::bvar(0),                                // x = n
        ],
    );
    Expr::lam(BinderInfo::Default, nat(), fix_app)
}

// ─────────────── the self-call MIR a future emitter would face ───────────────

fn u64_locals(n: usize) -> Vec<LocalDecl> {
    (0..n).map(|index| LocalDecl { index, ty: Ty::u64(), name: None }).collect()
}

fn vf(
    name: &str,
    arg_count: usize,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    let return_ty = locals[0].ty.clone();
    VerifiableFunction {
        name: name.into(),
        def_path: format!("probe::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn call(callee: &str, args: Vec<Operand>, dest: Place, target: BlockId) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest,
        target: Some(target),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        unwind: UnwindEdge::Unreachable,
    }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// `fn spin(a: u64) -> u64 { spin(a) }` — the MINIMAL self-call body: one call
/// block whose callee is the function's own def_path.
fn emitted_minimal_self_call() -> VerifiableFunction {
    vf(
        "spin",
        1,
        u64_locals(2),
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: call(
                    "probe::spin",
                    vec![Operand::Copy(Place::local(1))],
                    Place::local(0),
                    BlockId(1),
                ),
            },
            BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
        ],
    )
}

/// `fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }`
/// as MIR — the body a future recursive emitter would most plausibly produce
/// for the §1 demo (same construction discipline as the widening probes'
/// `emitted_lt_bool`): compare, branch, one arm projecting, one arm computing
/// the remainder and SELF-CALLING.
fn emitted_gcd_self_call() -> VerifiableFunction {
    let mut locals = u64_locals(5);
    locals[3].ty = Ty::Bool; // _3 = (b == 0)
    vf(
        "gcd",
        2,
        locals,
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    Place::local(3),
                    Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Uint(0, 64)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(3)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            // b == 0 ⇒ return a
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1))))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            // else ⇒ _4 = a % b; _0 = gcd(b, _4)
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(
                    Place::local(4),
                    Rvalue::BinaryOp(
                        BinOp::Rem,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                )],
                terminator: call(
                    "probe::gcd",
                    vec![Operand::Copy(Place::local(2)), Operand::Copy(Place::local(4))],
                    Place::local(0),
                    BlockId(3),
                ),
            },
            BasicBlock { id: BlockId(3), stmts: Vec::new(), terminator: Terminator::Return },
        ],
    )
}

// ════════════ (r1) the kernel refuses a DIRECT self-reference ════════════

/// A `Declaration::Definition` whose value names itself cannot enter the
/// environment: `add_decl` type-checks the value BEFORE inserting the name
/// (decl_add.rs Phase 1 → Phase 2), so the self-reference is an unknown
/// constant. The CONTROL half shows the same body referring to an EXISTING
/// name admits — isolating the self-reference as the refusal cause. There is
/// no other declaration form to reach for: `Declaration` is
/// Definition/Axiom/Theorem/Opaque, with no fixpoint variant.
#[test]
fn probe_r1_direct_self_reference_refused_at_add_decl() {
    let mut env = Environment::with_prelude();

    // CONTROL: the same two-parameter application body over an existing
    // constant kernel-checks (so r1's refusal below is about SELF-reference,
    // not about the body shape).
    define(
        &mut env,
        "ctrl",
        Expr::arrow(uint64(), Expr::arrow(uint64(), uint64())),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                Expr::apps(cnst("UInt64.add"), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        ),
    );

    // MEASURED REFUSAL: `def selfref (a b : UInt64) : UInt64 := selfref a b`.
    let err = try_define(
        &mut env,
        "selfref",
        Expr::arrow(uint64(), Expr::arrow(uint64(), uint64())),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                Expr::apps(cnst("selfref"), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        ),
    )
    .expect_err("a self-referential Definition must be refused at add_decl");
    assert!(
        err.contains("UnknownConst"),
        "the refusal must be the unknown self-constant (the name does not \
         exist during its own value's check), got: {err}"
    );
    eprintln!("PROBE-ROW | r1 direct self-reference     | kernel: REFUSE UnknownConst");
}

// ═══════════ (r2) which recursion machinery the environments hold ═══════════

/// The island session's environment (`with_prelude`) carries the FULL
/// termination substrate — `Nat.rec`, `Acc`/`Acc.rec`, `WellFounded.fix` —
/// but NOT Lean 4's `brecOn`/`strongRecOn` towers. The widening probes' lean
/// `init_uint_arith` environment carries none of the Nat-side machinery; a
/// recursion increment therefore measures against `with_prelude`, not against
/// the env the binop probes used.
#[test]
fn probe_r2_recursion_machinery_presence() {
    let prelude = Environment::with_prelude();
    let has = |env: &Environment, n: &str| env.get_const(&Name::from_string(n)).is_some();

    for name in [
        "Nat.rec",
        "Acc",
        "Acc.intro",
        "Acc.rec",
        "WellFounded",
        "WellFounded.fix",
        "WellFounded.fixF",
        "Nat.lt_wf",
        "Nat.lt",
        "Nat.zero",
        "UInt64.toNat",
        "UInt64.ofNat",
    ] {
        assert!(has(&prelude, name), "with_prelude must carry `{name}`");
    }
    // Lean 4 compiles structural recursion through brecOn; Clean does NOT
    // build that tower — a recognizer written against Lean 4's term shapes
    // would be looking for machinery that does not exist here.
    for name in ["Nat.brecOn", "Nat.strongRecOn"] {
        assert!(
            !has(&prelude, name),
            "measured 2026-08-20: `{name}` is NOT in the prelude; if this \
             flips, the structural-recursion term shape may have changed — \
             re-measure r3 before trusting any recognizer built on it"
        );
    }

    let mut uint_env = Environment::new();
    uint_env.init_uint_arith().expect("the widening probes' env must init");
    // MEASURED 2026-08-20: the lean binop env DOES carry `Nat.rec` (the UInt
    // carriers are built over Nat) but NONE of the WF machinery. A structural
    // recursion increment could in principle measure on env_uint; a WF one
    // cannot — it needs `with_prelude`, the island session's actual env.
    assert!(has(&uint_env, "Nat.rec"), "measured: init_uint_arith carries Nat.rec");
    for name in ["Acc", "Acc.rec", "WellFounded", "WellFounded.fix", "Nat.lt_wf"] {
        assert!(
            !has(&uint_env, name),
            "measured 2026-08-20: `{name}` was absent from init_uint_arith; \
             it has appeared — re-measure which env a recursion gate runs in"
        );
    }
    eprintln!(
        "PROBE-ROW | r2 machinery presence        | with_prelude: Nat.rec + Acc.rec + \
         WellFounded.fix + Nat.lt_wf, brecOn ABSENT | init_uint_arith: Nat.rec only"
    );
}

// ══════ (r3) structural recursion IS kernel-holdable, as a recursor app ══════

/// `def tozero : Nat -> Nat := fun n => @Nat.rec.{1} (fun _ => Nat) Nat.zero
/// (fun k ih => ih) n` — the raw-kernel spelling of what the island
/// elaborator produced for the equation-form `tozero` (measured 2026-08-20).
/// The kernel ADMITS it, it COMPUTES under defeq (kernel-grade termination in
/// action: iota reduction over the recursor rules), and TODAY's planner
/// refuses it as a capability boundary.
#[test]
fn probe_r3_structural_identity_fold_plans_and_readmits_by_induction() {
    let mut env = Environment::with_prelude();
    define(
        &mut env,
        "tozero",
        Expr::arrow(nat(), nat()),
        nat_rec_body(Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)), // fun k ih => ih
        )),
    );
    // MUTATION-CONTROL sibling: step `fun k ih => Nat.succ ih` (the identity
    // function on Nat) — used below to show the kernel evidence distinguishes.
    define(
        &mut env,
        "tozero_mut",
        Expr::arrow(nat(), nat()),
        nat_rec_body(Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::lam(BinderInfo::Default, nat(), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
        )),
    );

    let one = Expr::app(cnst("Nat.succ"), cnst("Nat.zero"));
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&Expr::app(cnst("tozero"), one.clone()), &cnst("Nat.zero")),
        "MEASURED: `tozero 1 ≡ 0` — the recursor application COMPUTES by iota \
         reduction; this is what kernel-grade termination evidence buys"
    );
    // The mutation: `tozero_mut 1 ≡ 1`, and NOT ≡ 0 — the kernel evidence
    // above is a decision, not a rubber stamp.
    assert!(tc.is_def_eq(&Expr::app(cnst("tozero_mut"), one.clone()), &one));
    assert!(!tc.is_def_eq(&Expr::app(cnst("tozero_mut"), one), &cnst("Nat.zero")));

    // PIN FLIPPED (2026-08-21, EXPLICITLY, in the same change as the R1
    // plan/recognise arms + the per-equation gate + control_7): the planner
    // now PLANS this def as `StructuralNatRec` — base `NatConst(0)` (the
    // `Nat.zero` spelling reads as the numeral), step `Rec` (`fun k ih =>
    // ih`), recursion argument `Pred` by construction of the class.
    let plan = plan_clean_origin_body(&env, "tozero")
        .expect("R1: the structural tozero class is now plannable");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::StructuralNatRec {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        },
        "the planned vocabulary must be exactly the r3 spelling's reading"
    );

    // MERGED PIN (2026-08-21): `tozero_mut` — the identity fold, step
    // `fun k ih => Nat.succ ih` — is outside the R1 case vocabulary (no
    // `Succ` node), so the STRUCTURAL recogniser still refuses it exactly as
    // the R1 change pinned. But that refusal no longer ends the plan: the
    // inductive-projection fallback fires on recognition refusal, and defeq
    // cannot identify the fold with the projection at a symbolic `n` while a
    // genuine Nat.rec induction can. The plan is therefore the distinct
    // InductiveProjection shape — the R1-era "stays NotEmittable" control was
    // refuting a lane that now exists, and the two folds planning DIFFERENT
    // shapes is the sharper mutation control.
    let plan = plan_clean_origin_body(&env, "tozero_mut")
        .expect("the axiom-free induction proof must unpause the identity fold");
    assert_eq!(plan.shape(), &CleanOriginShape::InductiveProjection { projected: 0 });

    // Run the complete side-B round trip over the body the compiler emits:
    // `_0 = move _1; return`. The final permission must be freshly re-earned
    // by induction, not reused from planning.
    let emitted = vf(
        "tozero_mut",
        1,
        vec![
            LocalDecl { index: 0, ty: Ty::BignumNat, name: None },
            LocalDecl { index: 1, ty: Ty::BignumNat, name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(1))))],
            terminator: Terminator::Return,
        }],
    );
    let faithful = admit_lowering(&env, &plan, &emitted)
        .expect("the emitted projection must re-earn the inductive verdict");
    assert_eq!(faithful.method(), FaithfulnessMethod::StructuralInduction);
    eprintln!(
        "PROBE-ROW | r3 Nat.rec structural def    | kernel: ADMIT + computes | constant fold: \
         StructuralNatRec (pin FLIPPED 2026-08-21) | identity fold: InductiveProjection"
    );
}

#[test]
fn probe_r3_nine_inductive_projection_candidates_refuse_as_one_bounded_declaration() {
    const ARITY: usize = 9;
    let mut env = Environment::with_prelude();

    let mut type_ = nat();
    for _ in 0..ARITY {
        type_ = Expr::arrow(nat(), type_);
    }
    // Under nine binders, bvar(0) is the last source parameter. The recursor
    // computes that projection extensionally, so all nine same-carrier
    // parameters are eligible candidates. Discovery must refuse the WHOLE
    // declaration at the arity/candidate rail; it must not test eight and
    // silently truncate the ninth. (Since the merge with R1, the refusal
    // this leaves in force is the structural recogniser's multi-parameter
    // boundary — still a capability refusal, still not a defect.)
    let mut value = nat_identity_rec(Expr::bvar(0));
    for _ in 0..ARITY {
        value = Expr::lam(BinderInfo::Default, nat(), value);
    }
    define(&mut env, "wide_identity", type_, value);

    let refusal = plan_clean_origin_body(&env, "wide_identity")
        .expect_err("nine eligible induction candidates are outside the bounded fragment");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }));
    assert!(!refusal.is_compiler_defect());
}

// ═══════ (r4) WF recursion IS kernel-holdable, as a WellFounded.fix app ═══════

/// `def wfz : Nat -> Nat := fun n => @WellFounded.fix.{1,1} Nat (fun _ => Nat)
/// Nat.lt Nat.lt_wf (fun x rec => Nat.zero) n` — the raw-kernel spelling of
/// the form the WF elaboration path produces (measured on `countdownSum`,
/// 2026-08-20). Pins THREE things: the kernel ADMITS a fix-applied def; the
/// planner refuses it; and — load-bearing for any future faithfulness gate —
/// whether a CLOSED application reduces under defeq (`wfz 0 ≡ 0`?), i.e.
/// whether `Acc.rec` grinds through `Nat.lt_wf`'s constructive witness or
/// sticks. Whichever way that measures, an architecture that needs defeq
/// against fix applications inherits it.
#[test]
fn probe_r4_wellfounded_fix_def_admits_and_plans_notemittable() {
    let mut env = Environment::with_prelude();
    define(&mut env, "wfz", Expr::arrow(nat(), nat()), wf_fix_body(cnst("Nat.zero")));
    // Mutation sibling: F returns 1 instead of 0.
    define(
        &mut env,
        "wfz_mut",
        Expr::arrow(nat(), nat()),
        wf_fix_body(Expr::app(cnst("Nat.succ"), cnst("Nat.zero"))),
    );

    let zero = cnst("Nat.zero");
    let one = Expr::app(cnst("Nat.succ"), zero.clone());
    let tc = TypeChecker::new(&env);
    let reduces = tc.is_def_eq(&Expr::app(cnst("wfz"), zero.clone()), &zero);
    let mut_reduces = tc.is_def_eq(&Expr::app(cnst("wfz_mut"), zero.clone()), &one);
    eprintln!(
        "PROBE-ROW | r4 WellFounded.fix def       | kernel: ADMIT | closed app reduces: {reduces} (mutation: {mut_reduces}) | plan: NotEmittable"
    );
    // MEASURED 2026-08-20: the closed application DOES reduce — WellFounded.fix
    // and fixF are REDUCIBLE definitions (well_founded.rs:380 "Clean seeds
    // WellFounded.fixF/fix as REDUCIBLE"), and Acc.rec iota-reduces through
    // the constructive `Nat.lt_wf` witness. If this pin flips, defeq-based
    // checking of fix applications has changed; re-measure before designing on
    // it.
    assert!(reduces, "measured 2026-08-20: `wfz 0 ≡ 0` reduced; it no longer does");
    assert!(mut_reduces, "the mutation sibling must reduce to ITS value");
    assert!(
        !tc.is_def_eq(&Expr::app(cnst("wfz_mut"), zero.clone()), &zero),
        "`wfz_mut 0 ≡ 0` must refuse — otherwise the reduction evidence is vacuous"
    );

    let refusal = plan_clean_origin_body(&env, "wfz")
        .expect_err("no CleanOriginShape covers a WellFounded.fix application");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect());
    // R1 (v7/D3): the refusal now NAMES the well-founded boundary and R2's
    // prerequisite rather than falling through to the generic fragment text.
    assert!(
        refusal.note().contains("WELL-FOUNDED"),
        "the wfz refusal must name the WF boundary; got: {}",
        refusal.note()
    );
    assert!(
        refusal.note().contains("equation lemmas"),
        "the wfz refusal must name R2's prerequisite; got: {}",
        refusal.note()
    );
}

// ══ (r5) recursion at a CARRIER-friendly signature still plans NotEmittable ══

/// `def spin64 (a : UInt64) : UInt64 := UInt64.ofNat (@Nat.rec.{1}
/// (fun _ => Nat) Nat.zero (fun k ih => ih) (UInt64.toNat a))` — a
/// recursor-computed body at a signature whose EVERY position has a total
/// fixed-width carrier. The planner still refuses: this isolates RECURSION,
/// not the carrier, as the boundary (contrast r3, where `Nat` positions ride
/// the bignum carrier).
#[test]
fn probe_r5_recursor_body_at_uint64_signature_plans_notemittable() {
    let mut env = Environment::with_prelude();
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![lvl1()]),
        [
            Expr::lam(BinderInfo::Default, nat(), nat()),
            cnst("Nat.zero"),
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
            ),
            Expr::app(cnst("UInt64.toNat"), Expr::bvar(0)),
        ],
    );
    define(
        &mut env,
        "spin64",
        Expr::arrow(uint64(), uint64()),
        Expr::lam(BinderInfo::Default, uint64(), Expr::app(cnst("UInt64.ofNat"), rec_app)),
    );

    let refusal = plan_clean_origin_body(&env, "spin64")
        .expect_err("a recursor-computed body at the u64 carrier stays refused (e2 boundary)");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect());
    // R1: THE PIN STAYS — the u64-carrier structural lane is OUT of the R1
    // slice — and the refusal now carries the MEASURED reason (v7/D3): the
    // OPEN equations at the u64 carrier are not definitional
    // (`r1_equation_probes` e2 — `Nat.mod` sticks at an open argument), so
    // no per-equation gate can be stated there; the named option is to
    // restate at `Nat -> Nat`, which IS emittable since this same change.
    assert!(
        refusal.note().contains("Nat.mod"),
        "the r5 refusal must cite the measured e2 stick; got: {}",
        refusal.note()
    );
    assert!(
        refusal.note().contains("restate the recursion at"),
        "the r5 refusal must carry the restate-at-Nat option; got: {}",
        refusal.note()
    );
    eprintln!(
        "PROBE-ROW | r5 recursion at u64 carriers | kernel: ADMIT | plan: NotEmittable \
         (e2 boundary named: open u64 equations are not definitional)"
    );
}

// ═════════ (r6) side B: no recognizer arm accepts a self-call body ═════════

/// The five arms of `recognize_admissible_body`
/// (`trust-types/src/admissible_body.rs:149-155`) are `recognize_single_block`
/// (ConstantUint/Projection), `recognize_arithmetic`, `recognize_select`,
/// `recognize_use_chain`, `recognize_call_chain` — the call-accepting arms
/// admit ONLY marker-authenticated `core::num` wrapping primitives
/// (`arith_method` / `RustcTotalPrimitiveMethod::classify`), so a call whose
/// callee is the function's OWN def_path never recognizes, in the minimal
/// form or the full gcd form.
#[test]
fn probe_r6_recognizer_refuses_self_call_bodies() {
    // REWRITTEN (not flipped) with the R1 arm, per this probe's own
    // instruction: the recursion arm landed as the SEPARATE entry point
    // `recognize_structural_rec` — deliberately NOT an `AdmissibleBody`
    // variant, so the E6 kernel-import direction
    // (`trust_certify::clean_island::admit_function_into`, which consumes
    // ONLY `recognize_admissible_body`) stays blind to recursive bodies BY
    // CONSTRUCTION until trust-mc's `Termination` facet is Certified for
    // them. Both pins below therefore still hold on the original chain —
    // and the NEW entry point refuses these two shapes as well: `spin` has
    // no zero-test contract and a u64 carrier; `gcd` is two-parameter,
    // carries a `Rem` rvalue, and self-calls with a non-predecessor
    // argument.
    assert_eq!(
        recognize_admissible_body(&emitted_minimal_self_call()),
        None,
        "no AdmissibleBody variant covers a self-call — R1 deliberately did \
         not add one; if this recognizes, the E6 import direction has been \
         opened to recursion and that is a soundness incident, not a test \
         update"
    );
    assert_eq!(
        recognize_admissible_body(&emitted_gcd_self_call()),
        None,
        "the full gcd shape (compare, branch, Rem, self-call) must not \
         recognize either"
    );
    assert_eq!(
        recognize_structural_rec(&emitted_minimal_self_call()),
        None,
        "the R1 structural entry point refuses the minimal self-call too \
         (no zero-test contract, u64 carrier)"
    );
    assert_eq!(
        recognize_structural_rec(&emitted_gcd_self_call()),
        None,
        "and the full gcd shape (arity 2, Rem, non-predecessor self-call)"
    );
    eprintln!(
        "PROBE-ROW | r6 self-call MIR             | recognize_admissible_body: None (both) | \
         recognize_structural_rec: None (both)"
    );
}

// ═══════ (r7) side B: no admit path can mint a recursive side B ═══════

/// The four E6 mint paths are `admit_constant_function`,
/// `admit_projection_function`, `admit_expr_function`, `admit_select_function`
/// (`trust-spec-elab/src/lib.rs:2130/2169/2223/2277`) — none takes a fixpoint
/// or a call. TWO measured refusals stack against gcd here:
///
/// * `p0 % p1` — gcd's own remainder, VARIABLE divisor — is refused: the
///   machine fragment's `%` requires a positive integer LITERAL divisor
///   ("a variable or zero divisor needs a nonzero side-condition, not yet
///   wired"). `p0 % 7` mints. So even gcd's non-recursive arithmetic is
///   outside today's mintable fragment.
/// * A call — self or otherwise — has no spelling in the expr grammar at all.
#[test]
fn probe_r7_no_admit_path_for_recursion_and_rem_needs_literal_divisor() {
    // `p0 % 7` mints — remainder itself is in the fragment…
    let mut env = Environment::new();
    env.init_uint_arith().expect("machine domain env");
    trust_spec_elab::admit_expr_function(
        &mut env,
        "rem_lit_probe",
        "p0 % 7",
        &["p0"],
        &Domain::Machine(MachineUIntWidth::U64),
    )
    .expect("MEASURED: `%` with a positive literal divisor is in the machine expr fragment");

    // …but `p0 % p1` — the divisor gcd actually needs — is refused.
    let mut scratch = Environment::new();
    scratch.init_uint_arith().expect("machine domain env");
    let rem_err = trust_spec_elab::admit_expr_function(
        &mut scratch,
        "rem_probe",
        "p0 % p1",
        &["p0", "p1"],
        &Domain::Machine(MachineUIntWidth::U64),
    )
    .expect_err("MEASURED 2026-08-20: a variable divisor is refused");
    assert!(
        rem_err.contains("divisor"),
        "the refusal must name the divisor side-condition boundary, got: {rem_err}"
    );

    // And a self-call has no spelling: the expr grammar has no call syntax.
    let mut scratch2 = Environment::new();
    scratch2.init_uint_arith().expect("machine domain env");
    let call_err = trust_spec_elab::admit_expr_function(
        &mut scratch2,
        "gcd_probe",
        "gcd_probe(p1, p0 % p1)",
        &["p0", "p1"],
        &Domain::Machine(MachineUIntWidth::U64),
    )
    .expect_err("a call — self or otherwise — must be outside the expr fragment");
    eprintln!(
        "PROBE-ROW | r7 admit paths               | `p0 % 7`: MINTS | `p0 % p1`: REFUSED \
         (variable divisor) | self-call spelling: REFUSED ({call_err})"
    );
    assert!(
        !call_err.is_empty(),
        "the refusal must carry a message (v7/D3: a refusal names the boundary)"
    );
}
