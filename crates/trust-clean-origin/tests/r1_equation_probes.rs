// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **R1 EQUATION PROBES — the §6e probes-first battery for structural
//! recursion, measured BEFORE any emitter arm exists.**
//!
//! §6e (2026-08-21) rules that [`Faithful`] for a recursive shape is kernel
//! defeq against EVERY defining equation, case by case, at the carrier —
//! never against the whole fixpoint term. That ruling stands on three
//! measurable claims, and this file measures each one against the frozen
//! kernel, in the same discipline as `recursion_boundary_probes.rs`:
//!
//! 1. the defining equations of an admitted structural def can be STATED and
//!    KERNEL-CHECKED as propositions in the session env (probe e1/e2);
//! 2. per-case agreement — side-B-like case terms, with the self-reference
//!    as the already-defined CONSTANT — is decidable by kernel defeq, and a
//!    family satisfying a STRICT SUBSET of the equations is REFUSED (e3)
//!    — **measured true, and SUPERSEDED as a gate spelling: see the s-series
//!    below**;
//! 3. the fib `.cov` pair-threading and closed-value computation behave the
//!    way the gate needs (e4/e5).
//!
//! # THE §6e IMPLEMENTATION AMENDMENT, and what this file's e-rows now mean
//!
//! The §6e IMPLEMENTATION AMENDMENT (2026-08-21, design doc
//! `docs/design/2026-08-04-two-language-compiler-architecture.md`, just above
//! §6f) records that the CONSTANT-CITING spelling this file's e1/e3 succ rows
//! measured — reflect the emitted self-call as the defined constant `f` and
//! put whole equations to defeq — is **VACUOUS as a gate**: CIC equations are
//! denotational, defeq unfolds `f`, and `tozero (succ k) ≡ tozero k` is
//! kernel-TRUE, so an emitted binary with an off-by-one recursive argument —
//! a DIVERGING loop — passes. Probe **s2** below constructs that
//! wrong-argument family and PINS THE ADMISSION: the vacuity is a measured
//! fact of this kernel, not an argument. The judgment §6e actually denotes is
//! the amendment's ABSTRACT-IH form, whose three components the s-series
//! measures: per-minor-premise defeq with the recursive result held abstract
//! (s3), the kernel-checked recursive-argument identity — the divergence
//! catch (s4), and equation-set completeness against the kernel's own
//! minor-premise count (s5).
//!
//! The e-rows are NOT deleted: every one is a true measurement, and e1's
//! rfl-definitionality of the succ equation is precisely the INGREDIENT of
//! the vacuity — because the defining equation is kernel-true, no defeq check
//! that cites the constant on both sides can distinguish the right recursive
//! argument from a wrong one. The table below says, per row, what is now
//! known to be measured.
//!
//! # The measured table (2026-08-21, this file's assertions ARE the record)
//!
//! | # | equation | rfl-definitional? | what the row measures (post-amendment) |
//! |---|---|---|---|
//! | e1 | `tozero 0 = 0` (kernel `Nat.zero` spelling) | YES — `Declaration::Theorem` with an `Eq.refl` value kernel-checks | side-A fact about the admitted def; still load-bearing |
//! | e1 | `∀ n, tozero (n+1) = tozero n` (OPEN n) | YES — iota fires on the constructor-headed scrutinee; rfl closes | side-A fact — AND the vacuity ingredient: this kernel-truth is what admits s2's diverging candidate |
//! | e1 | same two, stated about `tozero_mut` (identity) | zero: ADMIT (subset!), succ: REFUSED — the uniqueness control at the theorem layer | the constant-citing spelling catches wrong VALUES; s2 shows it cannot catch wrong ARGUMENTS |
//! | e2 | `tz64 (UInt64.ofNat 0) = UInt64.ofNat 0` (closed, u64 carrier) | YES | carrier fact; unaffected by the amendment |
//! | e2 | `tz64 (UInt64.ofNat 3) = UInt64.ofNat 0` (closed) | YES | carrier fact; unaffected |
//! | e2 | `∀ n, tz64 (ofNat (n+1)) = tz64 (ofNat n)` (OPEN n) | **NO — REFUSED**: `toNat (ofNat (succ n))` sticks on `Nat.mod` at open `n`; the u64-carrier equations are definitional CLOSED but not OPEN | carrier boundary; unaffected |
//! | e3 | per-case defeq, `double` succ-case candidate vs `fun n => double (n+1)` | YES (nontrivial: delta+iota through the recursor) | **the VACUOUS constant-citing spelling** — a true defeq, superseded as a gate; see s2 and the amendment |
//! | e3 | impostor (identity) zero-case | ADMIT — the subset is real | still real: a base-only check is insufficient in ANY spelling |
//! | e3 | impostor succ-case | REFUSED | wrong-VALUE refusal under the vacuous spelling; §6e's soundness now rests on s3+s4+s5, NOT here |
//! | e4 | `fib 0 = 0`, `fib 1 = 1` vs the `.cov`-backed constant | YES — rfl | side-A fact about the `.cov` compile; unaffected |
//! | e4 | `∀ n, fib (n+2) = fib (n+1) + fib n` (OPEN n) | YES — rfl; iota grinds `fst/snd` through the pair-threaded recursor with NO struct-eta needed, and the elaborator's `b + a` rewrite preserves the user's addend order | side-A fact; unaffected |
//! | e4 | flipped addend order `∀ n, fib (n+2) = fib n + fib (n+1)` | REFUSED — defeq is not arithmetic | still real; structure-sensitivity of defeq on stuck terms |
//! | e5 | `tozero 3 ≡ 0`, `fib 10 ≡ 55` — succ-tree AND `Nat` literal lanes | YES, all four; mutations refuse | closed-value run-pass pins; unaffected |
//! | s2 | wrong-ARGUMENT succ candidate `fun k => tozero (succ k)` vs the equation RHS `fun k => tozero k` | **ADMITTED — as the amendment predicts** | THE VACUITY: kernel defeq identifies a diverging binary's reflection with the right one under the constant-citing spelling |
//! | s2 | `double`'s off-by-one `fun n => succ (succ (double (succ n)))` vs its equation | REFUSED | the vacuity is DENOTATION-DEPENDENT — spot-checks look alive while tozero's divergence passes; that is what makes it insidious |
//! | s3 | reflected base `Nat.zero` vs b_A; reflected step `fun k ih => ih` vs s_A | ADMIT (both) | abstract-ih component 1: the defined constant appears NOWHERE — vacuity impossible by construction |
//! | s3 | wrong base `succ zero` vs b_A; wrong-value step `fun k ih => succ ih` vs s_A | REFUSED (both) | the identity family caught at the minor-premise layer, nothing to unfold |
//! | s4 | `fun k => Nat.pred (Nat.succ k)` vs `fun k => k` | ADMIT — iota | abstract-ih component 2: the argument identity accepts defeq-equal spellings |
//! | s4 | `fun k => Nat.succ k` vs `fun k => k` | **REFUSED — the divergence catch** | the SAME off-by-one that s2 shows passing the vacuous spelling is refused here, at the kernel layer |
//! | s5 | Nat's minor-premise count from the kernel env | == 2, from `get_inductive`/`get_recursor` | abstract-ih component 3: completeness reads the KERNEL's declaration, never the emission |
//! | s6 | `fun k => Nat.sub (Nat.succ k) 1` vs `fun k => k` | ADMIT — both numeral lanes | the MIR-faithful predecessor spelling (`trust_bignum::Nat::sub(&n, &1)` read dumbly) closes the rec-arg identity; `Nat.sub k 1 ≢ k` refuses |
//! | s7 | `OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)` | kernel-checks; ≡ `lit 0` ≡ `Nat.zero` | the island's surface numeral spelling identifies with side B's literal rendering; `≡ lit 1` refuses |
//! | s8 | `HAdd.hAdd.{0,0,0} Nat Nat Nat instHAddNat` vs `Nat.add` (open, under binders) | ADMIT | the surface `+` spelling identifies with the reflection's `Nat.add`; the arg-swap refuses (structure-sensitivity) |
//!
//! # THE EQUATION-MODE WORLD VERDICT (load-bearing for the whole R1 design)
//!
//! **We are in the PURE-DEFEQ world for the R1 structural slice.** Every
//! defining equation of a direct-recursor structural def — base AND inductive
//! case, closed AND open — closes by `Eq.refl` against the real kernel, so
//! the §6e gate's equation mode needs NO unfolding lemmas and NO
//! `equation_lemmas` machinery (none exists to productionize: grep of
//! clean-kernel + clean-elab finds no equation-lemma generator for `def`s;
//! the only mention is `inductive_builder.rs:483` REJECTING Lean-elaborated
//! equation lemmas on import). The measured boundary of that world:
//! **OPEN equations at the UInt64 carrier are NOT definitional** (e2) —
//! `Nat.mod` sticks on an open argument inside `toNat (ofNat (succ n))` —
//! so a gate for u64-carrier structural defs must either check the
//! equations at Nat and cross the carrier via I4's representation
//! obligation, or state the u64 equations CLOSED only. That is a
//! measurement, not a design choice made here.
//!
//! **Amendment note (2026-08-21):** "pure-defeq world" survives the §6e
//! IMPLEMENTATION AMENDMENT unchanged — but the defeq questions the GATE asks
//! are NOT the constant-citing equations above (vacuous as a gate, s2). They
//! are the abstract-ih components: minor-premise defeq (s3), the
//! recursive-argument identity (s4), and a structural count read from the
//! kernel's inductive declaration (s5). All three are still plain kernel
//! defeq / kernel reads — no unfolding lemmas, no equation-lemma machinery —
//! so the no-new-machinery conclusion carries over to the amended judgment.
//!
//! # fib: R1's first slice COVERS it
//!
//! The user-level equations (`fib 0 = 0`, `fib 1 = 1`,
//! `fib (n+2) = fib (n+1) + fib n`) are ALL rfl-checkable against the
//! `.cov`-backed constant (e4) — the pair-threading is transparent to
//! kernel defeq because `Prod.fst`/`Prod.snd` iota-reduce through the
//! explicit `Prod.mk` the step builds, and the `course_of_values.rs`
//! rewrite (`fib (n+1) → b`, `fib n → a`, minor `(a,b) => (b, b+a)`)
//! preserves the user's addend order in the reduct. R1's equation gate
//! therefore covers `.cov`-compiled two-back recurrences exactly as it
//! covers direct-recursor defs — no special case needed.
//!
//! # HONESTY RULES (same as `recursion_boundary_probes.rs`)
//!
//! * A probe that REFUSES asserts the refusal. A probe that ADMITS asserts
//!   admission. No probe passes vacuously; every ADMIT is paired with a
//!   refused mutation at the same layer. (s2 inverts the polarity of the
//!   pairing — its ADMIT is the ADVERSE finding, and its paired refusal
//!   (`double`'s off-by-one) shows the admission is a property of the
//!   spelling meeting tozero's denotation, not of a kernel that admits
//!   everything.)
//! * The kernel terms here are the RAW-KERNEL mirrors of the measured island
//!   elaborator output (`recursion_boundary_probes.rs` fib/tozero rows;
//!   `clean-elab/src/infer/course_of_values.rs` for the `.cov` shape),
//!   built by hand because trust-clean-origin does not (and must not)
//!   depend on the elaborator. Numerals are spelled `Nat.zero`/`Nat.succ`
//!   where the island spells `OfNat.ofNat` — the same deviation the prior
//!   file's `nat_rec_body` records; the pair minor is spelled with
//!   `Prod.fst`/`Prod.snd` projections (the prelude defines both AS
//!   `Expr::proj`, `clean-kernel/src/env/core.rs:101/136`).
//! * Side B's producers are FROZEN against this lane: if a verdict here is
//!   not the one the emitter design wants, the fix is kernel/prelude work or
//!   a different gate design — never an edit to this fixture's assertions.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker};

// ───────────────────────────── helpers (prior file's conventions) ──────────

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

/// Succ-tree numeral `Nat.succ^k Nat.zero` — the raw constructor spelling.
fn nat_num(k: u64) -> Expr {
    let mut e = cnst("Nat.zero");
    for _ in 0..k {
        e = Expr::app(cnst("Nat.succ"), e);
    }
    e
}

/// `@Eq.{1} Nat lhs rhs` — the defining-equation proposition at Nat.
fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![lvl1()]), [nat(), lhs, rhs])
}

/// `@Eq.refl.{1} Nat x` — the rfl proof candidate at Nat.
fn refl_nat(x: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![lvl1()]), [nat(), x])
}

/// `@Eq.{1} UInt64 lhs rhs` / `@Eq.refl.{1} UInt64 x` — at the u64 carrier.
fn eq_u64(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![lvl1()]), [uint64(), lhs, rhs])
}

fn refl_u64(x: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![lvl1()]), [uint64(), x])
}

/// Insert `def name : type_ := value` through the FULL kernel check, panicking
/// on refusal — the prior files' `define` convention.
fn define(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("`{name}` must kernel-check as written: {e:?}"));
}

/// State `theorem name : prop := proof` through the FULL kernel check —
/// "can the defining equation be stated and kernel-checked as a proposition
/// in the session env" is EXACTLY this call. Refusal returned as data.
fn try_theorem(env: &mut Environment, name: &str, prop: Expr, proof: Expr) -> Result<(), String> {
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: prop,
        value: proof,
    })
    .map_err(|e| format!("{e:?}"))
}

/// `fun (n : Nat) => @Nat.rec.{1} (fun _ => Nat) Nat.zero step n` — verbatim
/// from `recursion_boundary_probes.rs` (the measured raw-kernel mirror of the
/// island's structural equation-form output).
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

/// `tozero`'s step `fun k ih => ih`.
fn tozero_step() -> Expr {
    Expr::lam(BinderInfo::Default, nat(), Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)))
}

/// The mutation sibling's step `fun k ih => Nat.succ ih` (yields the identity
/// function — RIGHT on the zero equation, WRONG on the succ equation, which
/// is exactly the strict-subset family §6e's soundness argument must refuse).
fn succ_step() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
    )
}

/// `double`'s step `fun k ih => Nat.succ (Nat.succ ih)` — a def whose succ
/// RHS is NOT syntactically its own IH, so the per-case defeq in e3 is a
/// real reduction question rather than a syntactic identity.
fn double_step() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::app(cnst("Nat.succ"), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
        ),
    )
}

// ── Prod at Nat: `Prod.{0,0} Nat Nat` (Nat : Sort 1 = Type 0 ⇒ u = v = 0;
//    same instantiation `algebra_nat_div2_lt_self_proof.rs:132` uses) ──

fn prod_nat() -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Prod"), vec![Level::zero(), Level::zero()]),
        [nat(), nat()],
    )
}

fn pmk(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Prod.mk"), vec![Level::zero(), Level::zero()]),
        [nat(), nat(), a, b],
    )
}

fn pfst(p: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Prod.fst"), vec![Level::zero(), Level::zero()]),
        [nat(), nat(), p],
    )
}

fn psnd(p: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Prod.snd"), vec![Level::zero(), Level::zero()]),
        [nat(), nat(), p],
    )
}

fn add(a: Expr, b: Expr) -> Expr {
    Expr::apps(cnst("Nat.add"), [a, b])
}

/// Install the raw-kernel mirror of the island's `.cov` output for fib
/// (`recursion_boundary_probes.rs` fib row; shape per
/// `clean-elab/src/infer/course_of_values.rs`):
///
/// * `fib.cov : Nat → Prod Nat Nat`
///   `:= fun x => Nat.rec (fun _ => Prod Nat Nat) (0, 1)
///        (fun k ih => (ih.snd, ih.snd + ih.fst)) x`
///   — base `(base0, base1) = (0, 1)`; minor `(a, b) => (b, b + a)`, where
///   `b + a` is the `course_of_values.rs` rewrite of the user's
///   `fib (n+1) + fib n` (`f (n+1) → b`, `f n → a`), so the USER'S addend
///   order is what the compiled step carries.
/// * `fib : Nat → Nat := fun n => Prod.fst (fib.cov n)`.
fn install_fib(env: &mut Environment) {
    let ih = Expr::bvar(0);
    let step = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            prod_nat(),
            pmk(psnd(ih.clone()), add(psnd(ih.clone()), pfst(ih))),
        ),
    );
    let cov_val = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![lvl1()]),
            [
                Expr::lam(BinderInfo::Default, nat(), prod_nat()),
                pmk(nat_num(0), nat_num(1)),
                step,
                Expr::bvar(0),
            ],
        ),
    );
    define(env, "fib.cov", Expr::arrow(nat(), prod_nat()), cov_val);
    define(
        env,
        "fib",
        Expr::arrow(nat(), nat()),
        Expr::lam(BinderInfo::Default, nat(), pfst(Expr::app(cnst("fib.cov"), Expr::bvar(0)))),
    );
}

/// `tz64 : UInt64 → UInt64` — the UInt64-carrier structural variant, exactly
/// probe r5's `spin64` construction (recursor over `toNat`, admitted there).
fn install_tz64(env: &mut Environment, name: &str, step: Expr) {
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![lvl1()]),
        [
            Expr::lam(BinderInfo::Default, nat(), nat()),
            cnst("Nat.zero"),
            step,
            Expr::app(cnst("UInt64.toNat"), Expr::bvar(0)),
        ],
    );
    define(
        env,
        name,
        Expr::arrow(uint64(), uint64()),
        Expr::lam(BinderInfo::Default, uint64(), Expr::app(cnst("UInt64.ofNat"), rec_app)),
    );
}

/// `UInt64.ofNat k` with a succ-tree argument.
fn u64_of(k: u64) -> Expr {
    Expr::app(cnst("UInt64.ofNat"), nat_num(k))
}

// ═══════ (e1) tozero's defining equations: STATED, KERNEL-CHECKED, rfl ═══════

/// Both defining equations of the admitted structural `tozero` enter the
/// session env as `Declaration::Theorem`s whose value is bare `Eq.refl` —
/// i.e. they are DEFINITIONAL, full stop. The succ equation is checked at an
/// OPEN variable (`∀ n`): iota fires because the scrutinee `Nat.succ n` is
/// constructor-headed even when `n` is a bound variable. The mutation half
/// states the SAME equations about the identity-valued sibling: its zero
/// equation ADMITS (the subset is real) and its succ equation is REFUSED at
/// the kernel layer.
///
/// **What this measures, post-amendment:** side-A facts about the admitted
/// def — the defining equations ARE definitional, and that remains
/// load-bearing (it is why the gate needs no equation lemmas). What it does
/// NOT measure is a usable gate spelling: the rfl-truth of
/// `∀ n, tozero (succ n) = tozero n` is exactly the VACUITY INGREDIENT the
/// §6e IMPLEMENTATION AMENDMENT records — because that equation is
/// kernel-true, any constant-citing defeq check admits a candidate whose
/// self-call argument is off by one (measured: probe s2). The subset
/// refusal below shows the constant-citing spelling catches wrong VALUES;
/// s2 shows it cannot catch wrong ARGUMENTS.
#[test]
fn probe_e1_tozero_equations_are_rfl_definitional() {
    let mut env = Environment::with_prelude();
    define(&mut env, "tozero", Expr::arrow(nat(), nat()), nat_rec_body(tozero_step()));
    define(&mut env, "tozero_mut", Expr::arrow(nat(), nat()), nat_rec_body(succ_step()));

    // Equation 1 — zero case: `tozero 0 = 0`, proof `rfl`.
    try_theorem(
        &mut env,
        "tozero.eq_zero",
        eq_nat(Expr::app(cnst("tozero"), nat_num(0)), nat_num(0)),
        refl_nat(nat_num(0)),
    )
    .expect("MEASURED: `tozero 0 = 0` must kernel-check with a bare Eq.refl value");

    // Equation 2 — succ case at an OPEN variable:
    // `∀ (n : Nat), tozero (Nat.succ n) = tozero n`, proof `fun n => rfl`.
    let succ_eq = |f: &str| {
        Expr::pi(
            BinderInfo::Default,
            nat(),
            eq_nat(
                Expr::app(cnst(f), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
                Expr::app(cnst(f), Expr::bvar(0)),
            ),
        )
    };
    let succ_rfl = |f: &str| {
        Expr::lam(
            BinderInfo::Default,
            nat(),
            refl_nat(Expr::app(cnst(f), Expr::app(cnst("Nat.succ"), Expr::bvar(0)))),
        )
    };
    try_theorem(&mut env, "tozero.eq_succ", succ_eq("tozero"), succ_rfl("tozero"))
        .expect("MEASURED: the OPEN succ equation must close by rfl (iota on a constructor-headed scrutinee)");

    // UNIQUENESS CONTROL at the theorem layer. `tozero_mut` is the identity
    // function: RIGHT on the zero equation — this ADMIT is what makes it a
    // STRICT-subset family rather than a garbage term —
    try_theorem(
        &mut env,
        "tozero_mut.eq_zero",
        eq_nat(Expr::app(cnst("tozero_mut"), nat_num(0)), nat_num(0)),
        refl_nat(nat_num(0)),
    )
    .expect("MEASURED: the subset family's ZERO equation admits (it is right on zero)");
    // — and WRONG on the succ equation, which the kernel must REFUSE.
    let err =
        try_theorem(&mut env, "tozero_mut.eq_succ", succ_eq("tozero_mut"), succ_rfl("tozero_mut"))
            .expect_err(
                "SOUNDNESS PIN (recontextualized by the §6e amendment): a family \
         satisfying a strict subset of the defining equations is REFUSED on \
         the equation it violates — a true wrong-VALUE refusal. The gate's \
         soundness does NOT rest here anymore: this spelling cites the \
         constant, and s2 measures it admitting a wrong-ARGUMENT (diverging) \
         family. The amended judgment's refusals live in s3/s4",
            );
    // The refusal must be the DEFEQ mismatch at the agreement question — an
    // `UnknownConst` here would mean the probe never reached it. MEASURED:
    // `TypeCheckFailed { source: TypeMismatch { expected: ∀ n, tozero_mut
    // (succ n) = tozero_mut n, inferred: ∀ n, tozero_mut (succ n) =
    // tozero_mut (succ n) } }` — the kernel names exactly the equation the
    // subset family violates.
    assert!(err.contains("TypeMismatch"), "the refusal must be the defeq TypeMismatch, got: {err}");
    eprintln!(
        "REFUSAL-DATA | e1 subset succ    | TypeMismatch (kernel defeq) at tozero_mut.eq_succ"
    );
    eprintln!(
        "PROBE-ROW | e1 tozero equations          | zero: rfl ADMIT | succ (open n): rfl ADMIT | \
         subset family: zero ADMIT, succ REFUSED"
    );
}

// ═══ (e2) the UInt64-carrier structural variant: which equations survive ═══

/// r5 measured that a recursor-over-`toNat` def at `UInt64 → UInt64` ADMITS.
/// This probe measures which of ITS defining equations are definitional at
/// the carrier: the CLOSED instances compute (`toNat`/`ofNat`/`Nat.mod`
/// reduce on closed values — the same machinery I4's control B measured),
/// but the OPEN succ-style equation is REFUSED — `UInt64.toNat
/// (UInt64.ofNat (Nat.succ n))` sticks on `Nat.mod` at an open `n`, so no
/// iota can fire. **The u64-carrier equation lane is CLOSED-ONLY today**;
/// an open-equation gate for u64 structural defs has to go through Nat plus
/// the carrier obligation.
#[test]
fn probe_e2_uint64_carrier_equations_closed_yes_open_no() {
    let mut env = Environment::with_prelude();
    install_tz64(&mut env, "tz64", tozero_step());
    install_tz64(&mut env, "tz64_mut", succ_step());

    // Closed zero equation: `tz64 (UInt64.ofNat 0) = UInt64.ofNat 0`.
    try_theorem(
        &mut env,
        "tz64.eq_zero",
        eq_u64(Expr::app(cnst("tz64"), u64_of(0)), u64_of(0)),
        refl_u64(u64_of(0)),
    )
    .expect("MEASURED: the closed zero equation at the u64 carrier is rfl");

    // Closed computed instance: `tz64 (UInt64.ofNat 3) = UInt64.ofNat 0`.
    try_theorem(
        &mut env,
        "tz64.eq_three",
        eq_u64(Expr::app(cnst("tz64"), u64_of(3)), u64_of(0)),
        refl_u64(Expr::app(cnst("tz64"), u64_of(3))),
    )
    .expect("MEASURED: a closed application at the u64 carrier computes to the base");

    // Mutation pair for the closed lane: the identity-valued sibling computes
    // to ITS value and its wrong-value statement is refused.
    try_theorem(
        &mut env,
        "tz64_mut.eq_three",
        eq_u64(Expr::app(cnst("tz64_mut"), u64_of(3)), u64_of(3)),
        refl_u64(Expr::app(cnst("tz64_mut"), u64_of(3))),
    )
    .expect("the mutation sibling must compute to ITS value");
    try_theorem(
        &mut env,
        "tz64_mut.eq_three_wrong",
        eq_u64(Expr::app(cnst("tz64_mut"), u64_of(3)), u64_of(0)),
        refl_u64(Expr::app(cnst("tz64_mut"), u64_of(3))),
    )
    .expect_err("`tz64_mut 3 = 0` must refuse — otherwise the closed lane is vacuous");

    // THE OPEN succ-style equation at the carrier:
    // `∀ (n : Nat), tz64 (ofNat (succ n)) = tz64 (ofNat n)`.
    let open_prop = Expr::pi(
        BinderInfo::Default,
        nat(),
        eq_u64(
            Expr::app(
                cnst("tz64"),
                Expr::app(cnst("UInt64.ofNat"), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
            ),
            Expr::app(cnst("tz64"), Expr::app(cnst("UInt64.ofNat"), Expr::bvar(0))),
        ),
    );
    let open_rfl = Expr::lam(
        BinderInfo::Default,
        nat(),
        refl_u64(Expr::app(
            cnst("tz64"),
            Expr::app(cnst("UInt64.ofNat"), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
        )),
    );
    let err = try_theorem(&mut env, "tz64.eq_succ_open", open_prop, open_rfl).expect_err(
        "MEASURED BOUNDARY: the OPEN succ equation at the u64 carrier is NOT \
         definitional — `toNat (ofNat (succ n))` sticks on Nat.mod at open n. \
         If this ever ADMITS, the u64 reduction machinery has changed: \
         re-measure e2 before extending the R1 gate to open u64 equations",
    );
    // MEASURED: a defeq `TypeMismatch` whose `inferred` side is the stuck
    // `tz64 (ofNat (succ n)) = tz64 (ofNat (succ n))` — the reduction never
    // crossed `toNat (ofNat (succ n))`, confirming the open-argument stick.
    assert!(err.contains("TypeMismatch"), "the refusal must be the defeq TypeMismatch, got: {err}");
    eprintln!(
        "REFUSAL-DATA | e2 open u64 succ  | TypeMismatch (kernel defeq) at tz64.eq_succ_open"
    );
    eprintln!(
        "PROBE-ROW | e2 u64-carrier equations     | closed zero/3: rfl ADMIT | \
         OPEN succ: REFUSED (Nat.mod sticks) | mutation pair: distinguishes"
    );
}

// ═══ (e3) per-case agreement under the CONSTANT-CITING spelling — MEASURED
//     TRUE, SUPERSEDED AS A GATE (§6e amendment; see s2) ═══

/// **Post-amendment recontextualization.** This probe was written as "the
/// §6e gate's exact shape". Its measurements stand — every ADMIT and REFUSE
/// below is real — but what it measures is the CONSTANT-CITING spelling of
/// the per-equation check, which the §6e IMPLEMENTATION AMENDMENT records as
/// VACUOUS for gating: because defeq unfolds the defined constant, a
/// candidate whose self-call ARGUMENT is wrong can be identified with the
/// right one whenever the defining equation makes the two denotationally
/// equal — probe s2 measures exactly that admission for `tozero`. The
/// refusals below are wrong-VALUE refusals; they never test a wrong
/// ARGUMENT. The amended judgment (abstract-ih: s3/s4/s5) is the gate.
///
/// The original measurement, still true, still worth keeping pinned:
/// side-B-like case terms, checked by kernel defeq at the carrier:
/// * zero case — a CONSTANT (`Nat.zero` for tozero, `Nat.zero` for double);
/// * succ case — a term containing THE FUNCTION CONSTANT ITSELF applied to
///   the predecessor (the self-reference-as-constant treatment): the
///   already-admitted `double`/`tozero` constant is legal in any term put to
///   the kernel AFTER admission, which is why per-equation checking escapes
///   probe r1's phase-1 `UnknownConst` refusal — the equations are checked
///   against the DEFINED constant, not inside its own definition.
///
/// The candidate agrees with BOTH sides of its equation (RHS syntactically
/// or near-syntactically; LHS through delta+iota). THE UNIQUENESS CONTROL:
/// the identity family, which satisfies the zero equation only, must pass
/// the zero-case check AND fail the succ-case check — pinned hard in both
/// directions. That control is necessary but NOT sufficient for a gate: it
/// varies the case VALUE while holding the recursive argument right, so it
/// cannot see the vacuity s2 pins.
#[test]
fn probe_e3_per_case_agreement_and_uniqueness_control() {
    let mut env = Environment::with_prelude();
    define(&mut env, "tozero", Expr::arrow(nat(), nat()), nat_rec_body(tozero_step()));
    define(&mut env, "double", Expr::arrow(nat(), nat()), nat_rec_body(double_step()));
    // The impostor: a NON-recursive def, `fun n => n`. Not a mutated recursor
    // — a genuinely different family that happens to satisfy the zero
    // equation. This is the shape a wrong emitted body would take.
    define(
        &mut env,
        "impostor",
        Expr::arrow(nat(), nat()),
        Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)),
    );
    let tc = TypeChecker::new(&env);

    // — zero cases: candidate constant vs the function at zero —
    assert!(
        tc.is_def_eq(&Expr::app(cnst("tozero"), nat_num(0)), &nat_num(0)),
        "MEASURED: tozero's zero case agrees with the constant candidate"
    );
    assert!(
        tc.is_def_eq(&Expr::app(cnst("double"), nat_num(0)), &nat_num(0)),
        "MEASURED: double's zero case agrees with the constant candidate"
    );

    // — succ case, the self-reference-as-constant treatment —
    // candidate: `fun n => Nat.succ (Nat.succ (double n))` — side B's succ
    // case with the recursive call spelled as the CONSTANT `double` applied
    // to the predecessor.
    let candidate_succ = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app(
            cnst("Nat.succ"),
            Expr::app(cnst("Nat.succ"), Expr::app(cnst("double"), Expr::bvar(0))),
        ),
    );
    // Against the equation's LHS family `fun n => double (Nat.succ n)` — the
    // NONTRIVIAL direction (delta on `double`, iota on the recursor):
    let lhs_family = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app(cnst("double"), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
    );
    assert!(
        tc.is_def_eq(&candidate_succ, &lhs_family),
        "MEASURED: the succ-case candidate (self-reference as constant) is \
         kernel-defeq to `fun n => double (n+1)`. Post-amendment reading: a \
         true defeq of the VACUOUS constant-citing spelling — decidable, but \
         not a gate, because the same mechanism (delta through the defined \
         constant) is what admits s2's wrong-argument family"
    );

    // — THE UNIQUENESS CONTROL, pinned in both directions —
    // (a) the impostor PASSES the zero-case check (the subset is real; a
    //     gate that checked only the base case would ADMIT it):
    assert!(
        tc.is_def_eq(&Expr::app(cnst("impostor"), nat_num(0)), &nat_num(0)),
        "MEASURED: the impostor satisfies the zero equation — this ADMIT is \
         what makes the succ-case refusal below load-bearing"
    );
    // (b) and is REFUSED at the succ case, for BOTH defs' equations:
    let impostor_at_succ = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app(cnst("impostor"), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
    );
    let impostor_as_tozero_rhs =
        Expr::lam(BinderInfo::Default, nat(), Expr::app(cnst("impostor"), Expr::bvar(0)));
    assert!(
        !tc.is_def_eq(&impostor_at_succ, &impostor_as_tozero_rhs),
        "WRONG-VALUE PIN (was: SOUNDNESS PIN — recontextualized by the §6e \
         amendment): `fun n => impostor (n+1)` ≢ `fun n => impostor n` — the \
         kernel refuses the strict-subset family at tozero's succ equation. \
         Real, but a refusal of the vacuous spelling; gate soundness rests \
         on s3/s4/s5"
    );
    let impostor_as_double_rhs = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app(
            cnst("Nat.succ"),
            Expr::app(cnst("Nat.succ"), Expr::app(cnst("impostor"), Expr::bvar(0))),
        ),
    );
    assert!(
        !tc.is_def_eq(&impostor_at_succ, &impostor_as_double_rhs),
        "WRONG-VALUE PIN: the impostor is refused at double's succ equation too"
    );
    eprintln!(
        "PROBE-ROW | e3 constant-citing spelling  | zero: defeq ADMIT | succ (self-ref as \
         constant): defeq ADMIT | impostor: zero ADMIT + succ REFUSED (both defs) | \
         VACUOUS AS GATE — see s2"
    );
}

// ═══════ (e4) fib: the user's equations vs the `.cov`-backed constant ═══════

/// The `.cov` pair-threading compiles fib into a DIFFERENT recursor than the
/// user's equations mention — so whether the USER-level equations are
/// kernel-checkable against the compiled constant decides whether R1's first
/// slice covers fib. MEASURED: they are, all three, by bare rfl — including
/// the two-back equation at an OPEN `n`. No struct-eta is needed: the minor
/// builds an EXPLICIT `Prod.mk`, so `Prod.fst`/`Prod.snd` (which are
/// `Expr::proj` under the hood) iota-reduce through it, and both sides
/// normalize to `Nat.add (snd (fib.cov n)) (fst (fib.cov n))`, stuck only at
/// the open `fib.cov n`. The FLIPPED-addend control is REFUSED — kernel
/// defeq does not commute `Nat.add` over stuck arguments — which pins that
/// the open-equation check is structure-sensitive, not an over-reducing
/// rubber stamp.
#[test]
fn probe_e4_fib_user_equations_rfl_check_against_cov_constant() {
    let mut env = Environment::with_prelude();
    install_fib(&mut env);

    // `fib 0 = 0` and `fib 1 = 1` — the two base equations, by rfl.
    try_theorem(
        &mut env,
        "fib.eq_zero",
        eq_nat(Expr::app(cnst("fib"), nat_num(0)), nat_num(0)),
        refl_nat(Expr::app(cnst("fib"), nat_num(0))),
    )
    .expect("MEASURED: `fib 0 = 0` is rfl against the .cov-backed constant");
    try_theorem(
        &mut env,
        "fib.eq_one",
        eq_nat(Expr::app(cnst("fib"), nat_num(1)), nat_num(1)),
        refl_nat(Expr::app(cnst("fib"), nat_num(1))),
    )
    .expect("MEASURED: `fib 1 = 1` is rfl against the .cov-backed constant");

    // THE two-back user equation at an OPEN n:
    // `∀ (n : Nat), fib (succ (succ n)) = fib (succ n) + fib n`.
    let n = || Expr::bvar(0);
    let fib_at = |x: Expr| Expr::app(cnst("fib"), x);
    let succ = |x: Expr| Expr::app(cnst("Nat.succ"), x);
    let two_back = Expr::pi(
        BinderInfo::Default,
        nat(),
        eq_nat(fib_at(succ(succ(n()))), add(fib_at(succ(n())), fib_at(n()))),
    );
    let two_back_rfl = Expr::lam(BinderInfo::Default, nat(), refl_nat(fib_at(succ(succ(n())))));
    try_theorem(&mut env, "fib.eq_two_back", two_back, two_back_rfl).expect(
        "MEASURED, load-bearing for R1 scope: the user's two-back equation IS \
         rfl-checkable against the compiled .cov constant at OPEN n — R1's \
         first slice covers fib, not just direct-recursor defs. If this \
         refuses, the .cov minor's shape has changed: re-measure before \
         narrowing the R1 slice",
    );

    // FLIPPED-ADDEND CONTROL: `∀ n, fib (n+2) = fib n + fib (n+1)` — the
    // propositionally-true (add-comm) but definitionally-distinct order.
    let flipped = Expr::pi(
        BinderInfo::Default,
        nat(),
        eq_nat(fib_at(succ(succ(n()))), add(fib_at(n()), fib_at(succ(n())))),
    );
    let flipped_rfl = Expr::lam(BinderInfo::Default, nat(), refl_nat(fib_at(succ(succ(n())))));
    let err = try_theorem(&mut env, "fib.eq_two_back_flipped", flipped, flipped_rfl).expect_err(
        "CONTROL: the flipped addend order must REFUSE — defeq is not \
         arithmetic; if this admits, the open-equation check has gone vacuous",
    );
    // MEASURED: a defeq `TypeMismatch` — `Nat.add (fib n) (fib (succ n))`
    // (expected) vs the straight-order reduct (inferred); the kernel did not
    // commute the stuck addition.
    assert!(err.contains("TypeMismatch"), "the refusal must be the defeq TypeMismatch, got: {err}");
    eprintln!(
        "REFUSAL-DATA | e4 flipped addends | TypeMismatch (kernel defeq) at fib.eq_two_back_flipped"
    );
    eprintln!(
        "PROBE-ROW | e4 fib vs .cov constant      | fib 0/fib 1: rfl ADMIT | two-back (open n): \
         rfl ADMIT | flipped addends: REFUSED"
    );
}

// ═══════ (e5) closed-value computation at the carrier — the run-pass pins ═══════

/// `tozero 3 ≡ 0` and `fib 10 ≡ 55`, in BOTH numeral lanes (raw succ-trees
/// and the kernel's `Nat` literals) — these are the expected values the R1
/// run-pass fixtures will assert, so they are pinned here first, each with a
/// refusing mutation. The literal lane matters because side B's reflected
/// constants arrive as literals; the succ-tree lane matters because iota
/// works on constructors — the kernel bridges the two (literal↔constructor
/// conversion in whnf) and BOTH lanes are measured green.
#[test]
fn probe_e5_closed_value_computation_both_numeral_lanes() {
    let mut env = Environment::with_prelude();
    define(&mut env, "tozero", Expr::arrow(nat(), nat()), nat_rec_body(tozero_step()));
    define(&mut env, "tozero_mut", Expr::arrow(nat(), nat()), nat_rec_body(succ_step()));
    install_fib(&mut env);
    let tc = TypeChecker::new(&env);

    // tozero 3 ≡ 0 — succ-tree lane, then literal lane.
    assert!(
        tc.is_def_eq(&Expr::app(cnst("tozero"), nat_num(3)), &nat_num(0)),
        "MEASURED: `tozero 3 ≡ 0` (succ-tree lane)"
    );
    assert!(
        tc.is_def_eq(&Expr::app(cnst("tozero"), Expr::nat_lit(3)), &Expr::nat_lit(0)),
        "MEASURED: `tozero 3 ≡ 0` (literal lane — literal→constructor bridging feeds iota)"
    );
    // Mutation: the identity-valued sibling computes to ITS value, not 0.
    assert!(
        tc.is_def_eq(&Expr::app(cnst("tozero_mut"), nat_num(3)), &nat_num(3)),
        "the mutation sibling must compute to ITS value"
    );
    assert!(
        !tc.is_def_eq(&Expr::app(cnst("tozero_mut"), nat_num(3)), &nat_num(0)),
        "`tozero_mut 3 ≡ 0` must refuse — otherwise the closed lane is vacuous"
    );

    // fib 10 ≡ 55 — the Nat-lane run-pass pin, both numeral spellings.
    // This exercises Nat.add on closed arguments through ten iota steps of
    // the pair-threaded recursor.
    assert!(
        tc.is_def_eq(&Expr::app(cnst("fib"), nat_num(10)), &nat_num(55)),
        "MEASURED: `fib 10 ≡ 55` (succ-tree lane) — the kernel computes the \
         .cov tower AND Nat.add on closed values"
    );
    assert!(
        tc.is_def_eq(&Expr::app(cnst("fib"), Expr::nat_lit(10)), &Expr::nat_lit(55)),
        "MEASURED: `fib 10 ≡ 55` (literal lane)"
    );
    assert!(
        !tc.is_def_eq(&Expr::app(cnst("fib"), nat_num(10)), &nat_num(54)),
        "`fib 10 ≡ 54` must refuse — the computation pin is a decision, not a \
         rubber stamp"
    );
    eprintln!(
        "PROBE-ROW | e5 closed values             | tozero 3 ≡ 0: both lanes | fib 10 ≡ 55: \
         both lanes | mutations refuse"
    );
}

// ═════════════════════════════════════════════════════════════════════════
//   THE §6e IMPLEMENTATION AMENDMENT SERIES (s2–s5, 2026-08-21)
//
//   s2 pins the VACUITY of the constant-citing spelling the e-rows measured;
//   s3/s4/s5 measure the three components of the abstract-ih judgment the
//   amendment records as what §6e's ruling actually denotes. Design doc:
//   docs/design/2026-08-04-two-language-compiler-architecture.md, the
//   "§6e IMPLEMENTATION AMENDMENT" block just above §6f.
// ═════════════════════════════════════════════════════════════════════════

// ═══════ (s2) THE VACUITY COUNTEREXAMPLE — the load-bearing adverse pin ═══════

/// **THE MEASURED PROOF THAT THE CONSTANT-CITING SPELLING CANNOT BE THE
/// GATE.** Take the wrong-argument family: an emitted succ case whose
/// recursive call goes to `succ k` instead of `k` — under the
/// constant-citing reflection that is `fun k => tozero (Nat.succ k)`.
/// Operationally that binary DIVERGES on every nonzero input (each step
/// grows its argument). The old probes' check would put it to kernel defeq
/// against the defining equation's RHS spelling, `fun k => tozero k` — and
/// the kernel ADMITS it: defeq delta-unfolds `tozero`, iota fires on the
/// constructor-headed `succ k`, and both sides normalize to the same
/// `Nat.rec … k` reduct, because `tozero (succ k) ≡ tozero k` is exactly the
/// (kernel-true, e1-measured) defining equation. CIC equations are
/// denotational; defeq cannot see operational divergence through a defined
/// constant. (Against the equation's LHS spelling `fun k => tozero (succ
/// k)`, the wrong family is SYNTACTICALLY IDENTICAL — there the admission
/// is not even a kernel question.)
///
/// **This ADMIT is the adverse finding, not good news** — the honesty-rule
/// polarity is inverted on purpose. Its paired control: `double`'s
/// off-by-one family IS refused under the same spelling (`double (succ n)`
/// carries two extra `succ`s that never cancel), which pins that the
/// vacuity is DENOTATION-DEPENDENT — the constant-citing check catches the
/// off-by-one for some functions and admits it for others, so a test suite
/// of spot-checks can look alive while a diverging `tozero` binary walks
/// through. A gate whose refusal depends on which function the user wrote,
/// rather than on the recursion structure, is not a faithfulness gate.
///
/// s4 measures the SAME off-by-one argument refused at the kernel layer
/// once the defined constant is out of the terms — which is why the
/// amendment's abstract-ih form is the judgment.
#[test]
fn probe_s2_constant_citing_spelling_admits_offbyone_divergence() {
    let mut env = Environment::with_prelude();
    define(&mut env, "tozero", Expr::arrow(nat(), nat()), nat_rec_body(tozero_step()));
    define(&mut env, "double", Expr::arrow(nat(), nat()), nat_rec_body(double_step()));
    let tc = TypeChecker::new(&env);

    // The RIGHT succ-case reflection under the constant-citing spelling —
    // the defining equation's RHS as e1/e3 spelled it:
    let right = Expr::lam(BinderInfo::Default, nat(), Expr::app(cnst("tozero"), Expr::bvar(0)));
    // The WRONG-ARGUMENT family: self-call at `succ k` — off by one,
    // operationally a diverging binary:
    let wrong = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app(cnst("tozero"), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
    );
    assert!(
        tc.is_def_eq(&wrong, &right),
        "VACUITY PIN (§6e amendment, s2): the kernel was EXPECTED to ADMIT \
         the diverging wrong-argument family under the constant-citing \
         spelling — `fun k => tozero (succ k)` ≡ `fun k => tozero k` by \
         delta+iota, because the defining equation is kernel-true. If this \
         REFUSED, the amendment's premise is WRONG: re-read the amendment \
         before touching the gate design, and re-measure e1's open succ \
         equation — the two verdicts cannot diverge"
    );

    // PAIRED CONTROL — the same off-by-one shape at `double` REFUSES under
    // the same spelling: `double (succ n)` ≡ `succ (succ (double n))`, so
    // the wrong candidate `fun n => succ (succ (double (succ n)))` reduces
    // to four `succ`s against the equation's two. The vacuity is
    // denotation-dependent, which is what makes it insidious: spot-checking
    // the spelling on `double` would have reported a working gate.
    let double_wrong = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app(
            cnst("Nat.succ"),
            Expr::app(
                cnst("Nat.succ"),
                Expr::app(cnst("double"), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
            ),
        ),
    );
    let double_lhs_family = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app(cnst("double"), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
    );
    assert!(
        !tc.is_def_eq(&double_wrong, &double_lhs_family),
        "CONTROL: double's off-by-one family must REFUSE under the \
         constant-citing spelling — if this admits, the kernel is equating \
         succ-towers of different height and everything upstream is suspect"
    );
    eprintln!(
        "PROBE-ROW | s2 VACUITY COUNTEREXAMPLE    | tozero off-by-one (diverging) vs equation \
         RHS: defeq ADMITTED — as the amendment predicts | double off-by-one: REFUSED \
         (denotation-dependent, not a gate)"
    );
}

// ═══════ (s3) abstract-ih component 1: per-minor-premise defeq ═══════

/// The amended judgment's first component: each emitted case reflects with
/// the recursive RESULT abstracted as the recursor's own `ih` binder, and is
/// identified against side A's corresponding minor premise. For `tozero`,
/// side A's minors are `b_A = Nat.zero` and `s_A = fun k ih => ih`. **The
/// defined constant appears NOWHERE in either side** — no `define` is even
/// needed in this probe's env — so the delta-unfolding route that produced
/// s2's vacuity is closed by construction, and circularity (citing `tozero`
/// inside the check of `tozero`) is impossible for the same reason.
///
/// The wrong-VALUE family (`fun k ih => succ ih`, the identity-function
/// sibling e1/e3 caught at the theorem/equation layer) is refused HERE at
/// the minor-premise layer directly: `succ ih ≢ ih` at an open `ih`, with
/// nothing to unfold.
///
/// **Deliberate scope note:** the off-by-one family of s2 reflects its case
/// VALUE to this same `fun k ih => ih` — under abstract-ih reflection the
/// self-call's RESULT becomes `ih` regardless of what argument the call
/// passed — so component 1 alone ADMITS it. That is by design: the wrong
/// ARGUMENT is component 2's question (s4), and the judgment is the
/// CONJUNCTION of s3+s4+s5.
#[test]
fn probe_s3_abstract_ih_minor_premise_defeq() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);

    // Side A's minor premises for tozero.
    let b_a = cnst("Nat.zero");
    let s_a = tozero_step(); // fun k ih => ih

    // (a) the CORRECT reflections admit. Built here independently rather
    // than by sharing the helper, so the check is a defeq question about
    // two constructions, not one expression compared with itself.
    let reflected_base = cnst("Nat.zero");
    let reflected_step =
        Expr::lam(BinderInfo::Default, nat(), Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)));
    assert!(
        tc.is_def_eq(&reflected_base, &b_a),
        "MEASURED: the reflected base case admits against b_A"
    );
    assert!(
        tc.is_def_eq(&reflected_step, &s_a),
        "MEASURED: the reflected succ case `fun k ih => ih` admits against s_A"
    );

    // (b) the WRONG-VALUE reflections refuse — at the minor-premise layer,
    // with no constant anywhere to unfold.
    assert!(
        !tc.is_def_eq(&nat_num(1), &b_a),
        "SOUNDNESS PIN: a wrong base value (`succ zero`) refuses against b_A"
    );
    assert!(
        !tc.is_def_eq(&succ_step(), &s_a),
        "SOUNDNESS PIN: the wrong-value step `fun k ih => succ ih` (the \
         identity-function family) refuses against s_A — the subset family \
         e1/e3 caught downstream is caught HERE, at the minor premise, \
         under the amended judgment"
    );
    eprintln!(
        "PROBE-ROW | s3 abstract-ih minors        | base: ADMIT | step `fun k ih => ih`: ADMIT | \
         wrong base: REFUSED | wrong-value step: REFUSED (no constant in scope)"
    );
}

// ═══════ (s4) abstract-ih component 2: the recursive-argument identity ═══════

/// The amended judgment's second component — THE DIVERGENCE CATCH. The
/// reflected self-call ARGUMENT (under the case substitution) must be
/// definitionally the case binder. Both directions measured:
///
/// * `fun k => Nat.pred (Nat.succ k)` ADMITS against `fun k => k` — iota
///   closes it (`Nat.pred` is the prelude's recursor-built predecessor, so
///   `pred (succ k)` reduces to `k` even at open `k`). The identity check
///   accepts defeq-equal spellings of the right argument, not just the
///   syntactic binder — an emitted body whose MIR reflects the argument as
///   a computed predecessor is not spuriously refused.
/// * `fun k => Nat.succ k` REFUSES against `fun k => k` — the SAME
///   off-by-one argument s2 measured PASSING the constant-citing spelling
///   is refused here, because with the defined constant out of the terms
///   the kernel is asked the structural question directly, and `succ k ≢ k`.
///
/// This is the component that lets side A's kernel termination evidence
/// transfer: the emitted body recurses on exactly the structurally-smaller
/// binder the recursor supplies.
#[test]
fn probe_s4_recursive_argument_identity_divergence_catch() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);

    let case_binder = Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)); // fun k => k

    // Defeq-equal spelling of the right argument: iota through Nat.pred.
    let pred_succ = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app(cnst("Nat.pred"), Expr::app(cnst("Nat.succ"), Expr::bvar(0))),
    );
    assert!(
        tc.is_def_eq(&pred_succ, &case_binder),
        "MEASURED: `fun k => Nat.pred (Nat.succ k)` ≡ `fun k => k` — the \
         argument identity closes by iota, so it is a defeq question, not a \
         syntax match"
    );

    // THE DIVERGENCE CATCH: the off-by-one argument refuses.
    let off_by_one =
        Expr::lam(BinderInfo::Default, nat(), Expr::app(cnst("Nat.succ"), Expr::bvar(0)));
    assert!(
        !tc.is_def_eq(&off_by_one, &case_binder),
        "SOUNDNESS PIN (the amendment's divergence catch): `fun k => succ k` \
         ≢ `fun k => k` — the off-by-one recursive argument that the \
         constant-citing spelling ADMITS (s2) is REFUSED at the kernel layer \
         once the defined constant is out of the terms. If this ever admits, \
         the kernel is unsound about Nat and NOTHING downstream matters"
    );
    eprintln!(
        "PROBE-ROW | s4 recursive-arg identity    | pred (succ k) vs k: ADMIT (iota) | \
         succ k vs k: REFUSED — the divergence catch"
    );
}

// ═══════ (s5) abstract-ih component 3: completeness reads the KERNEL ═══════

/// The amended judgment's third component needs the number of cases the
/// emitted body must supply — one reflected case per minor premise, no
/// more, no fewer. This probe pins that the count is OBTAINABLE FROM THE
/// KERNEL'S OWN DECLARATIONS (never from any emission): the prelude env
/// hands back Nat's inductive declaration with exactly two constructors, in
/// declaration order, and `Nat.rec` with `num_minors == 2` and one recursor
/// rule per constructor, paired in the same order. The completeness check
/// reads THESE; an emission that omitted a case (the impostor family) or
/// invented one has nothing to say about the target count.
#[test]
fn probe_s5_minor_premise_count_read_from_kernel() {
    let env = Environment::with_prelude();

    // The inductive declaration, from the kernel env.
    let nat_ind = env
        .get_inductive(&Name::from_string("Nat"))
        .expect("MEASURED: Nat's inductive declaration is readable from the kernel env");
    assert_eq!(
        nat_ind.constructor_names.len(),
        2,
        "MEASURED: the minor-premise COUNT for Nat is 2, read from the \
         kernel's inductive declaration"
    );
    assert_eq!(nat_ind.constructor_names[0], Name::from_string("Nat.zero"));
    assert_eq!(nat_ind.constructor_names[1], Name::from_string("Nat.succ"));

    // The recursor agrees — num_minors and one rule per constructor, in
    // the same order (the pairing the per-minor-premise check indexes by).
    let nat_rec = env
        .get_recursor(&Name::from_string("Nat.rec"))
        .expect("MEASURED: Nat.rec is readable from the kernel env");
    assert_eq!(nat_rec.inductive_name, Name::from_string("Nat"));
    assert_eq!(
        nat_rec.num_minors, 2,
        "MEASURED: Nat.rec carries num_minors == 2 — the recursor's own case count"
    );
    assert_eq!(nat_rec.rules.len(), 2, "MEASURED: one recursor rule per constructor");
    for (rule, ctor) in nat_rec.rules.iter().zip(nat_ind.constructor_names.iter()) {
        assert_eq!(
            &rule.constructor_name, ctor,
            "MEASURED: recursor rules pair 1:1, in order, with the inductive's \
             constructors — the pairing the completeness check indexes by"
        );
    }
    eprintln!(
        "PROBE-ROW | s5 completeness groundwork   | Nat constructors: 2 (zero, succ) | \
         Nat.rec num_minors: 2, rules: 2, paired in order | source: KERNEL env, not emission"
    );
}

// ═══════ (s6) the MIR-faithful predecessor spelling of the rec-arg ═══════

/// The emitted body computes the predecessor as `trust_bignum::Nat::sub(&n,
/// &1)` — the runtime twin of Lean's truncated `Nat.sub` (the bignum TCB
/// row's differential pins the pairing) — so the DUMB reflection of the
/// self-call argument under the succ-case substitution is
/// `fun k => Nat.sub (Nat.succ k) 1`, not the `Nat.pred` spelling s4
/// measured. This probe pins that the sub spelling ALSO closes the
/// recursive-argument identity by kernel computation, in BOTH numeral lanes
/// (`Nat.sub` recurses on its second argument; literal→constructor bridging
/// feeds the iota, the e5 machinery), and that the WRONG-OPERAND reading
/// `fun k => Nat.sub k 1` refuses at open `k` — so the identity cannot be
/// satisfied by a body that subtracts from the wrong value.
///
/// (The off-by-one divergence catch itself — `fun k => succ k ≢ fun k => k`
/// — is s4's pin; a `rec_arg: Decreasing` reflection renders exactly that.)
#[test]
fn probe_s6_sub_spelling_closes_rec_arg_identity() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);

    let case_binder = Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)); // fun k => k
    let sub_lit = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(cnst("Nat.sub"), [Expr::app(cnst("Nat.succ"), Expr::bvar(0)), Expr::nat_lit(1)]),
    );
    assert!(
        tc.is_def_eq(&sub_lit, &case_binder),
        "MEASURED: `fun k => Nat.sub (succ k) (lit 1)` ≡ `fun k => k` — the \
         MIR-faithful predecessor spelling closes by kernel computation; if \
         this refuses, the reflection's rendering must be re-measured before \
         any gate trusts it"
    );
    let sub_tree = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(cnst("Nat.sub"), [Expr::app(cnst("Nat.succ"), Expr::bvar(0)), nat_num(1)]),
    );
    assert!(
        tc.is_def_eq(&sub_tree, &case_binder),
        "MEASURED: the succ-tree subtrahend lane closes too"
    );

    // WRONG-OPERAND CONTROL: subtracting from the case binder itself (what a
    // body that computed `pred(k)` instead of `pred(n)` would reflect to)
    // must refuse — `Nat.sub k 1` is stuck at open `k`.
    let sub_wrong = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(cnst("Nat.sub"), [Expr::bvar(0), Expr::nat_lit(1)]),
    );
    assert!(
        !tc.is_def_eq(&sub_wrong, &case_binder),
        "SOUNDNESS PIN: `fun k => Nat.sub k 1` ≢ `fun k => k` — the identity \
         is not satisfiable by subtracting from the wrong operand"
    );
    eprintln!(
        "PROBE-ROW | s6 sub-spelled rec-arg       | sub (succ k) 1 vs k: ADMIT (both numeral \
         lanes) | sub k 1 vs k: REFUSED"
    );
}

// ═══════ (s7) the island's surface numeral spelling vs the reflection's ═══════

/// The island elaborator spells the equation-form base numeral as
/// `OfNat.ofNat Nat 0 …` (`recursion_boundary_probes` module-docs, tozero
/// row), while side B's reflection renders numerals as kernel literals. This
/// probe pins the bridge the gate rides: the surface spelling KERNEL-CHECKS
/// as built here (`OfNat.ofNat.{0}` + `instOfNatNat`, the prelude's
/// instance), and identifies with BOTH the literal and the constructor
/// spellings — with the wrong-value control refused, so the identification
/// is a decision, not a collapse.
#[test]
fn probe_s7_surface_numeral_identifies_with_literal() {
    let mut env = Environment::with_prelude();
    let of_nat_zero = Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [nat(), Expr::nat_lit(0), Expr::app(cnst("instOfNatNat"), Expr::nat_lit(0))],
    );
    define(&mut env, "probe_s7_ofnat_zero", nat(), of_nat_zero.clone());

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&of_nat_zero, &Expr::nat_lit(0)),
        "MEASURED: the island's surface numeral identifies with the literal \
         rendering side B mints — the gate's base-case comparison rests on \
         this bridge"
    );
    assert!(
        tc.is_def_eq(&of_nat_zero, &cnst("Nat.zero")),
        "MEASURED: and with the constructor spelling"
    );
    assert!(
        !tc.is_def_eq(&of_nat_zero, &Expr::nat_lit(1)),
        "CONTROL: the surface numeral does not identify with a DIFFERENT \
         value — otherwise the bridge is a collapse, not a decision"
    );
    eprintln!(
        "PROBE-ROW | s7 surface numeral           | OfNat.ofNat.{{0}} Nat 0 (instOfNatNat 0): \
         kernel-checks | ≡ lit 0 ≡ Nat.zero | ≢ lit 1"
    );
}

// ═══════ (s8) the surface `+` spelling vs the reflection's `Nat.add` ═══════

/// An island step that writes `… + …` at `Nat` elaborates through the
/// surface `HAdd.hAdd` with the prelude's `instHAddNat`; side B's reflection
/// renders addition as `Nat.add`. This probe pins the two spellings
/// kernel-identical at OPEN arguments under binders (delta through the
/// instance projection), and pins the ARG-SWAP refused — kernel defeq does
/// not commute a stuck `Nat.add` (e4's flipped-addend precedent), so the
/// identification cannot silently bless a swapped emission.
#[test]
fn probe_s8_surface_add_identifies_with_nat_add() {
    let mut env = Environment::with_prelude();
    let hadd = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            nat(),
            Expr::apps(
                Expr::const_(
                    Name::from_string("HAdd.hAdd"),
                    vec![Level::zero(), Level::zero(), Level::zero()],
                ),
                [nat(), nat(), nat(), cnst("instHAddNat"), Expr::bvar(1), Expr::bvar(0)],
            ),
        ),
    );
    // Kernel-check the construction (level and instance shape), then compare.
    define(&mut env, "probe_s8_hadd", Expr::arrow(nat(), Expr::arrow(nat(), nat())), hadd.clone());

    let nat_add = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), add(Expr::bvar(1), Expr::bvar(0))),
    );
    let nat_add_swapped = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), add(Expr::bvar(0), Expr::bvar(1))),
    );
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&hadd, &nat_add),
        "MEASURED: the surface `+` spelling identifies with `Nat.add` at open \
         arguments — the reflection's rendering is the same function"
    );
    assert!(
        !tc.is_def_eq(&hadd, &nat_add_swapped),
        "CONTROL: the argument swap refuses — stuck additions do not commute \
         under defeq, so the identification is structure-sensitive"
    );
    eprintln!(
        "PROBE-ROW | s8 surface add               | HAdd.hAdd.{{0,0,0}} instHAddNat ≡ Nat.add \
         (open) | arg swap: REFUSED"
    );
}
