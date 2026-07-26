// trust-certify: CHECKER-CORE STRUCTURAL-POSTCONDITION discharge lane (`is_whnf`).
//
// This is the DISCHARGE half of Gap-A. The STATE + EMIT half already landed
// (`trust-integration-tests/tests/checker_core_recursive_spec.rs`): the
// checker-core structural postcondition `is_whnf(result)` — "the kernel
// expression returned by a WHNF-producing kernel operation is in weak-head
// normal form" — is parsed from an `#[ensures]` clause and EMITTED by the
// standard vcgen pipeline as an OPAQUE `VcKind::Postcondition` VC
// (`Formula::Pred("is_whnf", [_0])`). Opaque, its negation is not refutable, so
// the arithmetic `certify_violation` correctly FAILS CLOSED on it (no false
// PROVE), verified sound.
//
// The `is_whnf` predicate's semantics is bound to clean-verify's REAL inductive
// (core_spec/whnf_reduction.rs):
//
//   inductive is_whnf : KExpr -> Type
//   | sort : forall (n : Level), is_whnf (KExpr.sort n)
//   | lam  : forall (ty : KExpr) (body : KExpr), is_whnf (KExpr.lam ty body)
//   | pi   : forall (ty : KExpr) (body : KExpr), is_whnf (KExpr.pi ty body)
//   | neutral : forall (e : KExpr), is_neutral e -> is_whnf e
//
// BLOCKER-A (from the synthesis): the emitted VC's `_0` is an OPAQUE handle with
// no link to a concrete `KExpr`, so the `is_whnf.*` ctors cannot be instantiated.
// This lane closes that for the STATICALLY-KNOWN-HEAD fragment — the first
// KERNEL-DISCHARGED checker-core structural postcondition:
//
//   1. LINK (`link_whnf`): when the return value's `KExpr` head is STATICALLY a
//      `sort` / `lam` / `pi` constructor, a `const` candidate, or a const-headed
//      neutral application spine, bind
//      `is_whnf(_0)` to that concrete `KExpr` and DERIVE the matching
//      `is_whnf.*` ctor term FROM THE KExpr's OWN constructor arguments (not a
//      hand-supplied ctor). A `const` candidate derives
//      `is_whnf.neutral ... (is_neutral.const ... (Eq.refl ... none))`; the
//      kernel accepts it only when the const has no delta reduct. A neutral app
//      derives the complete recursive `is_neutral.app` spine down to that same
//      delta-dead const base. FAIL CLOSED for a bvar/fvar-headed application,
//      a lambda-headed beta redex, `KExpr.let_`, or wrong arity.
//
//   2. DISCHARGE: build the CIC proof term = the matching
//      `is_whnf.sort/lam/pi` ctor or the derived `is_whnf.neutral` proof
//      (a const base, optionally wrapped by `is_neutral.app` nodes) applied to
//      the concrete `KExpr`, and run the clean kernel
//      `TypeChecker::check_type(proof, is_whnf(that KExpr))`. For a const, this
//      check unfolds reducible `const_whnf` and computes `delta_reduct = none`;
//      a delta-reducing const is rejected. Mint a `CleanCic` only on kernel
//      acceptance; serialize + round-trip re-check.
//
// NO MASQUERADE (this lane produces `CleanCic` = TCB-adjacent, highest
// masquerade risk — the negative controls are LOAD-BEARING and MANDATORY):
//   * the discharge is a REAL `clean_kernel::check_type` of a REAL `is_whnf` ctor
//     term against the `is_whnf(concrete-KExpr)` goal — nothing is rubber-stamped;
//   * the BVAR-headed STUCK-APP negative control
//     (`KExpr.app (KExpr.bvar 0) (KExpr.sort 0)`) MUST fail closed at LINK: this
//     fragment has no `is_neutral` base for a bvar. A lambda-headed application
//     (a beta redex) fails independently. These witness that the recursive app
//     arm does not merely rubber-stamp `is_whnf`;
//   * a TAMPERED / wrong ctor (`is_whnf.sort n` against an `is_whnf(KExpr.lam ..)`
//     goal) MUST be kernel-REJECTED — `KExpr.sort n` is not def-equal to
//     `KExpr.lam ..`, so the kernel refuses the mismatch;
//   * the known delta-reducing const `kcre_name_116` MUST link as a
//     `NeutralConst` candidate but be kernel-REJECTED, proving that const-head
//     classification alone cannot mint evidence;
//   * minting is GATED on all three controls failing as required — each mint
//     returns `None` unless the stuck-app link fails, the wrong ctor is rejected,
//     AND the reducing-const candidate is rejected.
//
// GROUNDING CAVEAT (stated honestly): this is a MODEL-LEVEL discharge over
// clean-verify's 7-constructor `KExpr` abstraction of the kernel's ~20-ctor Rust
// `Expr`, the same honest scope as the sibling `checker_core` lanes. The `_0`
// -> concrete-`KExpr` link for the const-head fixture is grounded on its DECLARED
// return literal, NOT extracted from a literal Rust kernel fn's MIR. The
// MIR-grounded lane below deliberately still maps Rust `ExprKind::Const` and
// `ExprKind::App` to `None`: it does not derive the concrete const name/universe
// list, bind the application spine, or prove the head absent from `the_red_env`.
// That literal-Rust binding still needs the recursive-spec + functional-VC path.
// What IS airtight here: the model-level discharge kernel-check and the
// fail-closed link/negative controls.
// The clean CIC kernel (`TypeChecker::check_type`) is the proof-checking TCB; the
// semantic claim remains relative to clean-verify's model and foundational
// premises.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::{Environment, Expr, ExprKind, Name};
use clean_verify::spec::Specification;
use sha2::{Digest, Sha256};
use trust_types::{
    AggregateKind, BasicBlock, BlockId, Operand, Place, Projection, Rvalue, Statement, Terminator,
    VerifiableFunction, WriteEffect,
};

use crate::checker_core::{elaborate_full, kernel_checks_goal, run_on_large_stack};

/// Lineage domain tag for the `is_whnf` structural-postcondition discharge.
/// Distinct from every other lane so certificates never alias.
const IS_WHNF_LINEAGE_DOMAIN: &str = "trust-certify.cleancic.checker-core.is-whnf-discharge.v1";

/// The canonical STUCK-APP negative control: a stuck application whose head is a
/// bound variable. `is_whnf` has NO `app` ctor (and this cannot be `neutral` —
/// its head is a bvar, not a `const`), so it is genuinely NOT in WHNF. The LINK
/// step MUST fail closed on it.
const STUCK_APP_KEXPR_SRC: &str = "KExpr.app (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)";

/// A definition present in `the_red_env`. It therefore has a delta reduct and
/// MUST NOT inhabit `const_whnf`; this is the discriminating const-head control.
const DELTA_REDUCING_CONST_KEXPR_SRC: &str = "KExpr.const kcre_name_116 (ListType.nil Level)";

/// The statically-classified WHNF head of a concrete `KExpr` `_0`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WhnfHead {
    /// `KExpr.sort n` -> discharged by `is_whnf.sort n`.
    Sort,
    /// `KExpr.lam ty body` -> discharged by `is_whnf.lam ty body`.
    Lam,
    /// `KExpr.pi ty body` -> discharged by `is_whnf.pi ty body`.
    Pi,
    /// `KExpr.const n us` with NO delta-reduct -> discharged by
    /// `is_whnf.neutral (KExpr.const n us) (is_neutral.const n us hw)`, where
    /// `hw : const_whnf n us` is the `Eq.refl (OptionType KExpr) (OptionType.none
    /// KExpr)` proof the clean kernel accepts by UNFOLDING the (now reducible)
    /// `const_whnf` and REDUCING `delta_reduct (red_def the_red_env) (KExpr.const n
    /// us)` to `none`. A const that DOES delta-reduce makes that reduction non-`none`,
    /// so the kernel REJECTS the proof and the lane fails closed — the kernel's
    /// `delta_reduct = none` computation is the soundness gate.
    NeutralConst,
    /// `KExpr.app f a` whose spine bottoms out in a no-delta-reduct const — a STUCK
    /// application, a weak-head normal form. Discharged by `is_whnf.neutral` over the
    /// recursive `is_neutral.app … (is_neutral.const n us hw)` spine proof. Fails
    /// closed on bvar-headed spines (the STUCK_APP control) and lam-headed spines
    /// (beta redexes — not normal forms).
    NeutralApp,
}

impl WhnfHead {
    /// Stable tag folded into the lineage digest so a certificate for one head
    /// cannot be replayed against a differently-classified obligation.
    fn tag(self) -> &'static str {
        match self {
            WhnfHead::Sort => "is_whnf.sort",
            WhnfHead::Lam => "is_whnf.lam",
            WhnfHead::Pi => "is_whnf.pi",
            WhnfHead::NeutralConst => "is_whnf.neutral(const)",
            WhnfHead::NeutralApp => "is_whnf.neutral(app-spine)",
        }
    }
}

/// A concrete-WHNF-returning kernel-operation fixture. Models a literal Rust
/// kernel fn whose return slot `_0` is a `KExpr` with a statically-known WHNF
/// head. The `kexpr_src` is the concrete `KExpr` the operation returns; the LINK
/// step classifies its head and DERIVES the ctor from the KExpr itself — the
/// fixture never supplies the ctor, so a mislabelled fixture cannot masquerade.
#[derive(Clone, Copy)]
pub struct WhnfFixture {
    /// Description of the conceptual WHNF-producing kernel operation.
    label: &'static str,
    /// The concrete `KExpr` returned in `_0` (source form).
    kexpr_src: &'static str,
}

/// A WHNF operation that returns a `sort` head — e.g. the kernel computing the
/// type of a universe / `whnf` on an already-sort term. `Sort 0` is always WHNF.
pub static WHNF_SORT: WhnfFixture = WhnfFixture {
    label: "whnf-produces-Sort0 (universe head is already WHNF)",
    kexpr_src: "KExpr.sort Level.zero",
};

/// A WHNF operation that returns a `lam` head — e.g. `whnf` on a lambda, which
/// is already a weak-head normal form (reduction does not enter the binder).
pub static WHNF_LAM: WhnfFixture = WhnfFixture {
    label: "whnf-produces-Lam (lambda head is already WHNF)",
    kexpr_src: "KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)",
};

/// A WHNF operation that returns a `pi` head — e.g. the kernel inferring a
/// function type / `whnf` on a Pi. A Pi head is a weak-head normal form.
pub static WHNF_PI: WhnfFixture = WhnfFixture {
    label: "whnf-produces-Pi (function-type head is already WHNF)",
    kexpr_src: "KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)",
};

/// A WHNF operation that returns a NEUTRAL `const` head with NO delta-reduct — e.g.
/// `whnf` on an opaque/undefined constant, which is stuck (a weak-head normal form).
/// The synthetic name `Name.str Name.anonymous 8` is absent from `the_red_env`, so
/// the clean kernel reduces `delta_reduct (red_def the_red_env) (KExpr.const n [])`
/// to `none`, which (with `const_whnf` now reducible) discharges `const_whnf n []`.
/// A const that DID delta-reduce would make that reduct non-`none` and be REJECTED.
pub static WHNF_NEUTRAL_CONST: WhnfFixture = WhnfFixture {
    label: "whnf-produces-neutral-const (opaque constant head is already WHNF)",
    kexpr_src: "KExpr.const (Name.str Name.anonymous (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))) (ListType.nil Level)",
};

/// A WHNF operation that returns a NEUTRAL application SPINE — a stuck TWO-deep
/// application `(c s0) s0` of the same opaque constant (`Name.str Name.anonymous 8`,
/// proven absent from `the_red_env` by the neutral-const fixture). This is exactly
/// the shape the real whnf reducer returns for a stuck application; the two nested
/// `KExpr.app` nodes exercise the RECURSIVE `is_neutral.app` spine proof.
pub static WHNF_NEUTRAL_APP: WhnfFixture = WhnfFixture {
    label: "whnf-produces-neutral-app-spine (stuck application spine over an opaque constant)",
    kexpr_src: "KExpr.app (KExpr.app (KExpr.const (Name.str Name.anonymous (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))) (ListType.nil Level)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)",
};

/// The `const_whnf n us` witness: the same `Eq.refl (OptionType KExpr) (OptionType.none
/// KExpr)` clean-verify uses. Built as an `Expr` (never elaborated against the field
/// type) and kernel-checked; the kernel unfolds the (reducible) `const_whnf` and reduces
/// `delta_reduct (red_def the_red_env) (KExpr.const n us)` to `none` to accept it
/// (fail-closed if the const reduces).
const CONST_WHNF_REFL_SRC: &str = "Eq.refl (OptionType KExpr) (OptionType.none KExpr)";

/// Public fixture certification is sealed to the audited static instances.
/// Pointer identity prevents a caller from constructing an arbitrary source
/// string and asking the fixture lane to mint evidence for it.
fn fixture_is_sealed(fixture: &'static WhnfFixture) -> bool {
    std::ptr::eq(fixture, &WHNF_SORT)
        || std::ptr::eq(fixture, &WHNF_LAM)
        || std::ptr::eq(fixture, &WHNF_PI)
        || std::ptr::eq(fixture, &WHNF_NEUTRAL_CONST)
        || std::ptr::eq(fixture, &WHNF_NEUTRAL_APP)
}

/// The result of LINKing an opaque `is_whnf(_0)` VC to a concrete `KExpr`.
struct LinkedWhnf {
    /// The statically-classified head.
    head: WhnfHead,
    /// The derived proof term: `is_whnf.<head>` applied to `_0`'s ctor args.
    proof: Expr,
    /// The goal `is_whnf (_0)` for the concrete `KExpr`.
    goal: Expr,
}

/// Get the head constant `Name` of an application spine, stripping metadata.
/// `None` if the head is not a constant.
fn head_const(e: &Expr) -> Option<Name> {
    match e.get_app_fn().strip_mdata().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// LINK step (the Gap-A "Lever-A datatype sort" sketch, statically-known-head
/// case): elaborate the concrete `KExpr` `_0` from source, classify its head
/// constructor, and — for `sort`/`lam`/`pi`, a `const` candidate, or a
/// const-headed application spine — DERIVE the matching `is_whnf.*` proof term
/// from `_0`'s OWN constructor arguments and build the `is_whnf(_0)` goal. A
/// const is only a candidate at LINK: the kernel DISCHARGE decides whether its
/// `delta_reduct` is actually `none`.
///
/// FAIL CLOSED (`None`) for an unsupported head — a bvar/fvar-headed application,
/// a lambda-headed beta redex, a non-constant neutral head, or a wrong arity.
/// The proof ctor is NEVER supplied by the caller: it is
/// reconstructed here from the classified head applied to `_0`'s own arguments,
/// so a mislabelled or hostile fixture cannot smuggle in a mismatched ctor.
fn link_whnf(env: &Environment, kexpr_src: &str) -> Option<LinkedWhnf> {
    let k0 = elaborate_full(env, kexpr_src)?;
    let k0 = k0.strip_mdata().clone();

    let head_name = head_const(&k0)?;
    // `get_app_args` yields the explicit ctor arguments in source order. KExpr's
    // sort/lam/pi ctors carry no implicit args, so these are exactly the ctor
    // arguments the matching `is_whnf.*` ctor must be applied to.
    let args: Vec<Expr> = k0.get_app_args().iter().map(|a| (**a).clone()).collect();

    let sort_c = Name::from_string("KExpr.sort");
    let lam_c = Name::from_string("KExpr.lam");
    let pi_c = Name::from_string("KExpr.pi");
    let const_c = Name::from_string("KExpr.const");
    let app_c = Name::from_string("KExpr.app");

    let (head, proof) = if head_name == sort_c && args.len() == 1 {
        (WhnfHead::Sort, Expr::app(Expr::const_str("is_whnf.sort"), args[0].clone()))
    } else if head_name == lam_c && args.len() == 2 {
        (
            WhnfHead::Lam,
            Expr::apps(Expr::const_str("is_whnf.lam"), [args[0].clone(), args[1].clone()]),
        )
    } else if head_name == pi_c && args.len() == 2 {
        (
            WhnfHead::Pi,
            Expr::apps(Expr::const_str("is_whnf.pi"), [args[0].clone(), args[1].clone()]),
        )
    } else if head_name == const_c && args.len() == 2 {
        // NEUTRAL const head: derive `is_whnf.neutral (KExpr.const n us) (is_neutral.const
        // n us hw)` where `n, us` are `_0`'s OWN ctor args (never caller-supplied) and
        // `hw : const_whnf n us` is the fixed `Eq.refl (OptionType KExpr) (OptionType.none
        // KExpr)`. Built as an `Expr` and checked by the DISCHARGE step's pure kernel,
        // which unfolds the (now reducible) `const_whnf` and reduces `delta_reduct
        // (red_def the_red_env) (KExpr.const n us)` to `none`. A const that DOES
        // delta-reduce fails that kernel check => fail closed (the `delta_reduct = none`
        // computation is the discriminating soundness gate).
        let neutral = neutral_spine_proof(env, &k0)?;
        (
            WhnfHead::NeutralConst,
            Expr::apps(Expr::const_str("is_whnf.neutral"), [k0.clone(), neutral]),
        )
    } else if head_name == app_c && args.len() == 2 {
        // NEUTRAL application SPINE: `KExpr.app f a` whose spine bottoms out in a
        // no-delta-reduct const — a STUCK application, which IS a weak-head normal
        // form (`is_neutral.app` recursion down the spine to `is_neutral.const`).
        // This is exactly the shape the real whnf reducer returns for stuck
        // applications. FAILS CLOSED on any non-const spine head: a bvar-headed
        // spine (the STUCK_APP control) or a lam-headed spine (a beta REDEX — not
        // a normal form!) makes `neutral_spine_proof` return `None`.
        let neutral = neutral_spine_proof(env, &k0)?;
        (
            WhnfHead::NeutralApp,
            Expr::apps(Expr::const_str("is_whnf.neutral"), [k0.clone(), neutral]),
        )
    } else {
        // Not a statically-known WHNF constructor head (`bvar`, `lam`-headed redex
        // via the app arm's fail-closed spine walk, or wrong arity): fail closed.
        // NEVER link a non-WHNF head.
        return None;
    };

    let goal = Expr::app(Expr::const_str("is_whnf"), k0);
    Some(LinkedWhnf { head, proof, goal })
}

/// Recursively derive the `is_neutral` proof for a const-headed application SPINE:
/// `is_neutral.const n us (Eq.refl ..none..)` at the spine head (kernel-checked by
/// unfolding the reducible `const_whnf` and reducing `delta_reduct` to `none`),
/// wrapped by one `is_neutral.app f a <ih>` per application node. FAILS CLOSED
/// (`None`) on any non-const spine head — a `bvar`/`fvar` (not neutral-dischargeable
/// in this fragment) or a `lam` (a beta REDEX, not a normal form at all). The proof
/// is derived from the KExpr's OWN structure, never caller-supplied.
fn neutral_spine_proof(env: &Environment, k: &Expr) -> Option<Expr> {
    let head_name = head_const(k)?;
    let args: Vec<Expr> = k.get_app_args().iter().map(|a| (**a).clone()).collect();
    if head_name == Name::from_string("KExpr.const") && args.len() == 2 {
        let cw_proof = elaborate_full(env, CONST_WHNF_REFL_SRC)?;
        Some(Expr::apps(
            Expr::const_str("is_neutral.const"),
            [args[0].clone(), args[1].clone(), cw_proof],
        ))
    } else if head_name == Name::from_string("KExpr.app") && args.len() == 2 {
        let ih = neutral_spine_proof(env, &args[0])?;
        Some(Expr::apps(Expr::const_str("is_neutral.app"), [args[0].clone(), args[1].clone(), ih]))
    } else {
        None
    }
}

/// NO-MASQUERADE control 1 (LOAD-BEARING): the stuck-app result must FAIL CLOSED
/// at the LINK step. The `STUCK_APP` control is a BVAR-headed application spine —
/// `is_neutral` has no bvar base, so `neutral_spine_proof` (and hence `link_whnf`)
/// must return `None` — no proof can even be built for a non-neutral stuck result.
fn stuck_app_link_fails_closed(env: &Environment) -> bool {
    link_whnf(env, STUCK_APP_KEXPR_SRC).is_none()
}

/// NO-MASQUERADE control 1b (redex): a LAM-headed application — a genuine beta
/// REDEX, i.e. NOT a weak-head normal form — must also FAIL CLOSED at the LINK
/// step (the spine walk hits the `lam` head and refuses).
fn redex_app_link_fails_closed(env: &Environment) -> bool {
    link_whnf(
        env,
        "KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)",
    )
    .is_none()
}

/// NO-MASQUERADE control 2: a tampered / wrong ctor must be kernel-REJECTED. We
/// take the `sort` proof (`is_whnf.sort Level.zero : is_whnf (KExpr.sort 0)`) and
/// check it against the `lam` goal (`is_whnf (KExpr.lam ..)`). `KExpr.sort 0` is
/// NOT def-equal to `KExpr.lam ..`, so the clean kernel MUST reject it — the
/// witness that the discharge kernel-check is discriminating.
fn wrong_ctor_kernel_rejected(env: &Environment) -> bool {
    let (Some(sort_linked), Some(lam_linked)) =
        (link_whnf(env, WHNF_SORT.kexpr_src), link_whnf(env, WHNF_LAM.kexpr_src))
    else {
        // Cannot construct the discriminating attempt -> cannot demonstrate the
        // rejection -> fail closed.
        return false;
    };
    // The `sort` proof must NOT type-check against the `lam` goal.
    !kernel_checks_goal(env, &sort_linked.proof, &lam_linked.goal)
}

/// NO-MASQUERADE control 3 (LOAD-BEARING): a const known to occur in
/// `the_red_env` must LINK as a `NeutralConst` candidate but MUST be rejected by
/// the kernel because its delta reduct is not `none`. This pins the distinction
/// between syntactic const-head classification and a valid `const_whnf` witness.
fn delta_reducing_const_kernel_rejected(env: &Environment) -> bool {
    let Some(linked) = link_whnf(env, DELTA_REDUCING_CONST_KEXPR_SRC) else {
        return false;
    };
    linked.head == WhnfHead::NeutralConst && !kernel_checks_goal(env, &linked.proof, &linked.goal)
}

/// SHA-256 lineage digest binding the proof term, the empty closed context, the
/// obligation label, the pinned domain, and the fixture's concrete `KExpr`
/// source. Position-tagged + length-prefixed => injective; a certificate cannot
/// be replayed against another obligation or KExpr.
fn lineage_digest(
    fixture: &WhnfFixture,
    head: WhnfHead,
    term_bytes: &[u8],
    context_bytes: &[u8],
) -> trust_ir::ProofDigest {
    let mut hasher = Sha256::new();
    hasher.update(IS_WHNF_LINEAGE_DOMAIN.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"label:".as_slice(), fixture.label.as_bytes()),
        (b"kexpr:".as_slice(), fixture.kexpr_src.as_bytes()),
        (b"head:".as_slice(), head.tag().as_bytes()),
    ] {
        hasher.update(tag);
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    let digest = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&digest);
    trust_ir::ProofDigest::sha256(bytes)
}

/// The heavy body of the mint against an already-built spec. Kept separate so a
/// test can amortize a single (expensive) `Specification::new()` across all
/// fixtures + controls.
fn certify_with_spec(
    spec: &Specification,
    fixture: &WhnfFixture,
) -> Option<trust_ir::ProofEvidence> {
    let env = spec.env();

    // 1. LINK `_0` -> concrete KExpr; fail closed if the head is outside the
    //    statically-known supported fragment.
    let linked = link_whnf(env, fixture.kexpr_src)?;

    // 2. DISCHARGE: the clean kernel must accept the DERIVED `is_whnf.*` ctor
    //    term against the `is_whnf(_0)` goal.
    if !kernel_checks_goal(env, &linked.proof, &linked.goal) {
        return None;
    }

    // 3. NO MASQUERADE (mandatory, minting is GATED on all four controls): the
    //    bvar-headed stuck-app and lam-headed redex links must fail closed, a
    //    wrong ctor must be kernel-rejected, and a known delta-reducing const
    //    must be kernel-rejected.
    if !stuck_app_link_fails_closed(env)
        || !redex_app_link_fails_closed(env)
        || !wrong_ctor_kernel_rejected(env)
        || !delta_reducing_const_kernel_rejected(env)
    {
        return None;
    }

    // 4. Serialize term + empty closed context, then re-check the DESERIALIZED
    //    payload round-trips to a kernel-valid term.
    let term_bytes = serialize_term(&linked.proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let roundtrip = deserialize_term(&term_bytes).ok()?;
    if !kernel_checks_goal(env, &roundtrip, &linked.goal) {
        return None;
    }
    let lineage = lineage_digest(fixture, linked.head, &term_bytes, &context_bytes);

    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Mint a kernel-CHECKED `CleanCic` certificate that the checker-core structural
/// postcondition `is_whnf(_0)` holds for `fixture`'s concrete WHNF-returning
/// result, by DISCHARGING it with the matching `is_whnf.*` ctor term the clean
/// kernel accepts against the `is_whnf(_0)` goal. Fail-closed (`None`) on any
/// spec-build, LINK (non-WHNF head), kernel-check, negative-control,
/// serialization, or round-trip failure.
#[must_use]
pub fn certify_is_whnf(fixture: &'static WhnfFixture) -> Option<trust_ir::ProofEvidence> {
    if !fixture_is_sealed(fixture) {
        return None;
    }
    run_on_large_stack(move || {
        let spec = Specification::new().ok()?;
        certify_with_spec(&spec, fixture)
    })
    .flatten()
}

/// The heavy body of the consumer-side re-check against an already-built spec.
fn recheck_with_spec(
    spec: &Specification,
    fixture: &WhnfFixture,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    let env = spec.env();
    // Rebuild the goal INDEPENDENTLY from the fixture's KExpr source.
    let Some(linked) = link_whnf(env, fixture.kexpr_src) else {
        return false;
    };
    if !crate::is_canonical_term(term_bytes, &linked.proof) {
        return false;
    }
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(env, &term, &linked.goal) {
        return false;
    }
    &lineage_digest(fixture, linked.head, term_bytes, context_bytes) == lineage
}

/// Consumer-side re-check of an `is_whnf` discharge certificate: independently
/// rebuild the spec + goal, deserialize the term, re-run the clean-kernel
/// `check_type`, and re-bind the lineage digest. Returns `true` ONLY if the
/// kernel accepts the deserialized term against the freshly-rebuilt goal AND the
/// lineage matches — a tampered term or a swapped lineage fails closed.
#[must_use]
pub fn recheck_is_whnf(
    fixture: &'static WhnfFixture,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if !fixture_is_sealed(fixture) || !crate::is_canonical_empty_context(context_bytes) {
        return false;
    }
    let term = term_bytes.to_vec();
    let context = context_bytes.to_vec();
    let lineage = *lineage;
    run_on_large_stack(move || {
        let Some(spec) = Specification::new().ok() else {
            return false;
        };
        recheck_with_spec(&spec, fixture, &term, &context, &lineage)
    })
    .unwrap_or(false)
}

// ════════════════════════════════════════════════════════════════════════════
// MIR-GROUNDED head extraction (the Blocker-A crux).
//
// The fixture lane above links `_0` to a KExpr via a DECLARED source string
// (`WhnfFixture::kexpr_src`). This lane instead DERIVES the WHNF head from the
// REAL, fork-extracted MIR (`trust_types::VerifiableFunction`) of a literal
// clean-kernel constructor fn — the `_0 -> KExpr` head now comes from the MIR's
// own return-value construction, NOT a hand-supplied string.
//
// The extracted MIR of e.g. `Expr::prop` (clean-kernel/src/expr/constructors.rs)
// is (fork-dumped, verbatim):
//
//   bb0: _1 = Aggregate(Adt { name: "…ExprKind", variant: 2 }, [const 0])   // Sort
//        Call "…Expr::from_kind"(Move _1) -> _0
//   bb1: return
//
// and `Expr::from_kind` itself (validated kind-preserving):
//
//   _0 = Aggregate(Adt { name: "…Expr", variant: 0 }, [Copy _1, const 0])   // { kind:_1, meta }
//   return
//
// so the head of the returned `Expr` IS the variant of the `ExprKind` aggregate
// (`from_kind` copies its `kind` argument into field 0 unchanged). We read that
// MIR variant, map it to the KExpr head, and discharge exactly as the fixture
// lane. NO MASQUERADE: a literal fn returning a non-WHNF head (`Expr::app` builds
// `ExprKind::App`, variant 4) FAILS CLOSED at the MIR-extraction step — the
// witness that the grounding is real, not rubber-stamped.
// ════════════════════════════════════════════════════════════════════════════

/// Lineage domain for the MIR-GROUNDED `is_whnf` discharge. Distinct from the
/// fixture-string domain so a MIR certificate can never alias a fixture one.
const IS_WHNF_MIR_LINEAGE_DOMAIN: &str =
    "trust-certify.cleancic.checker-core.is-whnf-mir-discharge.v2";

// Certificate authority is intentionally narrower than the public structural
// analyzers below.  The analyzers remain useful advisory diagnostics, but they
// do not prove reachability/dominance for arbitrary caller-authored MIR.  Mint
// and recheck therefore accept only these exact, build-embedded fork extracts.
const MIR_PROP_JSON: &str =
    include_str!("../fixtures/checker_core_is_whnf_mir/clean_kernel.expr.Expr.prop.json");
const MIR_SORT_JSON: &str =
    include_str!("../fixtures/checker_core_is_whnf_mir/clean_kernel.expr.Expr.sort.json");
const MIR_ARROW_JSON: &str =
    include_str!("../fixtures/checker_core_is_whnf_mir/clean_kernel.expr.Expr.arrow.json");
const MIR_FROM_KIND_JSON: &str =
    include_str!("../fixtures/checker_core_is_whnf_mir/clean_kernel.expr.Expr.from_kind.json");

/// The rustc return slot is always local `_0`.
const RETURN_LOCAL: usize = 0;

/// Map an `ExprKind` enum VARIANT INDEX (as extracted from the MIR aggregate's
/// `variant` field) to the WHNF head it constructs. `ExprKind` carries NO
/// explicit `= N` discriminants, so the rustc `VariantIdx` in the MIR aggregate
/// equals the DECLARATION POSITION; the full order (clean-kernel
/// `crates/clean-kernel/src/expr/kind.rs`, recorded submodule `f9f8024d`) is:
///
///   0  BVar            NON-WHNF (loose bvar — neutral; needs is_neutral proof)
///   1  FVar            NON-WHNF (free var  — neutral; needs is_neutral proof)
///   2  Sort            WHNF  -> is_whnf.sort   ✓ discharge
///   3  Const           NON-WHNF (δ-reducible def OR neutral)
///   4  App             NON-WHNF (β-redex or neutral spine)
///   5  Lam             WHNF  -> is_whnf.lam    ✓ discharge
///   6  Pi              WHNF  -> is_whnf.pi     ✓ discharge
///   7  Let             NON-WHNF (ζ-reducible)
///   8  Lit             NON-WHNF (value, but no is_whnf.lit ctor in the KExpr model)
///   9  Proj            NON-WHNF (projection reduces on a ctor)
///   10 MData           NON-WHNF (transparent wrapper -> reduces to inner)
///   11 SProp           NON-WHNF-dischargeable (sort-like, but NOT KExpr.sort)
///   12 Squash          NON-WHNF-dischargeable
///   13 CubicalInterval / 14 CubicalI0 / 15 CubicalI1        NON-WHNF-dischargeable
///   16 CubicalPath / 17 CubicalPathLam / 18 CubicalPathApp  NON-WHNF(-dischargeable)
///   19 CubicalHComp / 20 CubicalTransp                      NON-WHNF-dischargeable
///   21 ZFCSet / 22 ZFCMem / 23 ZFCComprehension             NON-WHNF-dischargeable
///
/// (Working-tree `97950495` inserts `CubicalCoe` at index 21, shifting the ZFC
/// tail to 22/23/24; this does NOT touch the WHNF heads 2/5/6 nor the fail-closed
/// result of the shifted variants — every non-WHNF index maps to `None` either
/// way.)
///
/// SOUNDNESS + COMPLETENESS: ONLY the three genuine WHNF heads `Sort(2)` /
/// `Lam(5)` / `Pi(6)` — head constructors that are not further reducible —
/// discharge (to `is_whnf.sort/lam/pi`). EVERY other index is NON-WHNF and maps
/// to `None` (FAIL CLOSED) via the `_` arm — including the neutral-but-not-
/// dischargeable-here variants (BVar/FVar/Const, whose WHNF-ness would need an
/// `is_neutral` proof this lane does not build: failing closed is the SAFE
/// direction, never a false certificate), the genuinely-reducible ones
/// (App/Let/Proj/MData), and any FUTURE variant (a new ctor added to the enum is
/// non-WHNF by default here — soundness is preserved by construction; the worst
/// a future WHNF ctor causes is a missed discharge, never a false one). This is
/// the ONLY place the enum layout is consulted; that a given fn RETURNS a given
/// index is MIR-derived (the aggregate's `variant` field), not hand-supplied, and
/// the index<->head correspondence is PINNED by the real fork-extracted fixtures
/// (`Expr::sort` -> variant 2, `Expr::arrow` -> variant 6, `Expr::app` ->
/// variant 4, …). The exhaustive completeness + fail-closed table lives in
/// `tests::full_exprkind_classification_is_complete_and_fails_closed`.
fn exprkind_variant_to_whnf_head(variant: usize) -> Option<WhnfHead> {
    match variant {
        2 => Some(WhnfHead::Sort),
        5 => Some(WhnfHead::Lam),
        6 => Some(WhnfHead::Pi),
        _ => None,
    }
}

/// Final `::`-separated segment of a def-path string (robust to the module
/// prefix rustc emits, e.g. `clean_kernel::expr::Expr::from_kind`).
fn final_segment(path: &str) -> &str {
    path.rsplit("::").next().unwrap_or(path)
}

/// The (unprojected) local an operand copies/moves from, if any.
fn operand_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// The UNIQUE rvalue assigned to `local` (unprojected), or `None` if the local
/// has zero OR more than one such assignment. Ambiguity -> `None` keeps the
/// analysis fail-closed (a re-assigned local is not soundly traceable here).
fn unique_assign(func: &VerifiableFunction, local: usize) -> Option<&Rvalue> {
    let mut it = func.body.blocks.iter().flat_map(|bb| bb.stmts.iter()).filter_map(|st| match st {
        Statement::Assign { place, rvalue, .. }
            if place.local == local && place.projections.is_empty() =>
        {
            Some(rvalue)
        }
        _ => None,
    });
    let first = it.next()?;
    if it.next().is_some() {
        return None;
    }
    Some(first)
}

/// Follow unique `_x = Use(Move/Copy _y)` copy chains to the source local
/// (rustc routinely inserts such moves, e.g. `from_kind` moves its `kind` arg
/// `_1` into `_4` before the struct aggregate). Bounded; stops at the first local
/// that is not a lone plain copy (an aggregate, a call dest, an arg, or an
/// ambiguously-assigned local), returning that local.
fn resolve_copy_source(func: &VerifiableFunction, mut local: usize) -> usize {
    for _ in 0..16 {
        match unique_assign(func, local) {
            Some(Rvalue::Use(op)) => match operand_local(op) {
                Some(src) => local = src,
                None => return local,
            },
            _ => return local,
        }
    }
    local
}

/// MIR-GROUNDED head extraction (the Blocker-A crux). Given a REAL fork-extracted
/// `VerifiableFunction` (NOT a hand-authored MIR), determine the statically-known
/// WHNF head of the returned `Expr` by tracing the return slot `_0` back through
/// the kind-preserving `Expr::from_kind` constructor to the `ExprKind` aggregate
/// the fn builds, and reading THAT aggregate's MIR `variant`.
///
/// FAIL CLOSED (`None`) unless:
///   * some block returns via a `Call` to `*::from_kind` whose `dest` is `_0`,
///   * that call's first arg is an unprojected local `_k`,
///   * `_k` is assigned by EXACTLY ONE `Aggregate(Adt { name: `*::ExprKind`,
///     variant }, _)` (any other/extra write to `_k` -> `None`), and
///   * `variant` is a WHNF ctor (Sort/Lam/Pi).
///
/// The head is DERIVED FROM THE MIR aggregate's `variant` field — not from a
/// hand-supplied source string. A non-WHNF head (App/BVar/Const/…) yields
/// `None`: `_0` is never linked to a WHNF KExpr unless the MIR shows a WHNF ctor.
///
/// This is an advisory structural recognizer, not certificate authority for
/// arbitrary MIR: it does not prove CFG reachability or dominance. The public
/// CleanCic mint/recheck APIs additionally require exact equality with an
/// embedded audited fixture via [`sealed_constructor_material`].
#[must_use]
pub fn extract_whnf_head_from_mir(func: &VerifiableFunction) -> Option<WhnfHead> {
    // 1. Find the `from_kind` constructor call that writes the return slot `_0`,
    //    and take its `kind` argument's local.
    let mut kind_local: Option<usize> = None;
    for bb in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &bb.terminator
            && dest.local == RETURN_LOCAL
            && dest.projections.is_empty()
            && final_segment(callee) == "from_kind"
        {
            kind_local = args.first().and_then(operand_local);
            break;
        }
    }
    let kind_local = kind_local?;

    // 2. Resolve the kind arg through any copy chain, then read the UNIQUE
    //    `ExprKind` aggregate assigned to it. Any non-aggregate / non-ExprKind /
    //    ambiguous write -> fail closed.
    let root = resolve_copy_source(func, kind_local);
    match unique_assign(func, root) {
        Some(Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, _))
            if final_segment(name) == "ExprKind" =>
        {
            exprkind_variant_to_whnf_head(*variant)
        }
        _ => None,
    }
}

/// VALIDATE (closes the trace's trust gap): confirm, FROM THE REAL MIR of
/// `Expr::from_kind` ITSELF, that it is STRUCTURALLY kind-preserving — it returns
/// `Aggregate(Adt { name: `*::Expr`, variant 0 }, [<kind arg>, <meta>])` whose
/// FIRST field (the `kind`) is exactly the function's `kind` argument `_1`. This
/// turns "`from_kind` preserves the head" from a modeling ASSUMPTION into a
/// MIR-CHECKED fact, so the [`extract_whnf_head_from_mir`] trace THROUGH the
/// `from_kind` call is grounded, not merely trusted.
#[must_use]
pub fn mir_from_kind_is_kind_preserving(from_kind_fn: &VerifiableFunction) -> bool {
    if from_kind_fn.body.arg_count != 1 {
        return false;
    }
    // The single `kind` argument is local `_1` (the return slot is `_0`).
    let kind_arg_local = 1usize;
    let Some(Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, ops)) =
        unique_assign(from_kind_fn, RETURN_LOCAL)
    else {
        return false;
    };
    // `Expr { kind: <field 0>, meta: <field 1> }`, and field 0 must trace (through
    // rustc's move copies) back to the `kind` argument `_1`.
    final_segment(name) == "Expr"
        && *variant == 0
        && ops.first().and_then(operand_local).map(|l| resolve_copy_source(from_kind_fn, l))
            == Some(kind_arg_local)
}

fn embedded_mir(json: &str) -> Option<(VerifiableFunction, Vec<u8>)> {
    let func = serde_json::from_str(json).ok()?;
    let bytes = bincode::serialize(&func).ok()?;
    Some((func, bytes))
}

/// Seal certificate authority to the three audited literal constructors and
/// the separately audited, kind-preserving `Expr::from_kind` implementation.
/// Exact bincode equality covers def-path, callee paths, CFG, statements,
/// contracts, and all other serialized MIR fields.
fn sealed_constructor_material(func: &VerifiableFunction) -> Option<(WhnfHead, Vec<u8>)> {
    let (from_kind, _) = embedded_mir(MIR_FROM_KIND_JSON)?;
    if !mir_from_kind_is_kind_preserving(&from_kind) {
        return None;
    }

    let presented = bincode::serialize(func).ok()?;
    for json in [MIR_PROP_JSON, MIR_SORT_JSON, MIR_ARROW_JSON] {
        let (canonical, canonical_bytes) = embedded_mir(json)?;
        if presented == canonical_bytes {
            return Some((extract_whnf_head_from_mir(&canonical)?, canonical_bytes));
        }
    }
    None
}

/// The canonical KExpr source for a MIR-derived head. The specific ctor arguments
/// are WHNF-irrelevant (`is_whnf.<head>` holds for ALL args); only the HEAD — the
/// MIR-derived fact — is load-bearing. These are exactly the fixture lane's
/// `kexpr_src`, so the kernel discharge is byte-identical; ONLY head SELECTION is
/// now MIR-grounded rather than fixture-declared.
fn canonical_kexpr_src(head: WhnfHead) -> &'static str {
    match head {
        WhnfHead::Sort => WHNF_SORT.kexpr_src,
        WhnfHead::Lam => WHNF_LAM.kexpr_src,
        WhnfHead::Pi => WHNF_PI.kexpr_src,
        WhnfHead::NeutralConst => WHNF_NEUTRAL_CONST.kexpr_src,
        WhnfHead::NeutralApp => WHNF_NEUTRAL_APP.kexpr_src,
    }
}

/// SHA-256 lineage for a MIR-grounded discharge, binding the term, the empty
/// closed context, every serialized field of the exact canonical MIR fixture,
/// and the MIR-derived head. Position-tagged + length-prefixed => injective; a
/// certificate for one body/head cannot be replayed against another.
fn mir_lineage_digest(
    func: &VerifiableFunction,
    head: WhnfHead,
    term_bytes: &[u8],
    context_bytes: &[u8],
) -> Option<trust_ir::ProofDigest> {
    let (sealed_head, canonical_mir) = sealed_constructor_material(func)?;
    if sealed_head != head {
        return None;
    }
    let mut hasher = Sha256::new();
    hasher.update(IS_WHNF_MIR_LINEAGE_DOMAIN.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"mir:".as_slice(), canonical_mir.as_slice()),
        (b"head:".as_slice(), head.tag().as_bytes()),
    ] {
        hasher.update(tag);
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    let digest = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&digest);
    Some(trust_ir::ProofDigest::sha256(bytes))
}

/// Heavy body of the MIR-grounded mint against an already-built spec.
fn certify_from_mir_with_spec(
    spec: &Specification,
    func: &VerifiableFunction,
) -> Option<trust_ir::ProofEvidence> {
    let env = spec.env();

    // 1. MIR-GROUND: require an exact audited constructor fixture and the exact
    //    audited kind-preserving `from_kind` fixture. The loose structural
    //    analyzer remains advisory and cannot authorize arbitrary MIR.
    let (head, _) = sealed_constructor_material(func)?;

    // 2. Build the canonical KExpr for that MIR-derived head and LINK (the
    //    is_whnf.* ctor is re-derived from the KExpr's OWN args, not supplied).
    let linked = link_whnf(env, canonical_kexpr_src(head))?;

    // 3. DISCHARGE: the clean kernel must accept the derived ctor term against
    //    the is_whnf(_0) goal.
    if !kernel_checks_goal(env, &linked.proof, &linked.goal) {
        return None;
    }

    // 4. NO MASQUERADE (mandatory, minting is GATED): the stuck-app link must
    //    fail closed, a wrong ctor must be kernel-rejected, and a known
    //    delta-reducing const must be kernel-rejected.
    if !stuck_app_link_fails_closed(env)
        || !wrong_ctor_kernel_rejected(env)
        || !delta_reducing_const_kernel_rejected(env)
    {
        return None;
    }

    // 5. Serialize + round-trip re-check.
    let term_bytes = serialize_term(&linked.proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let roundtrip = deserialize_term(&term_bytes).ok()?;
    if !kernel_checks_goal(env, &roundtrip, &linked.goal) {
        return None;
    }
    let lineage = mir_lineage_digest(func, head, &term_bytes, &context_bytes)?;

    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Mint a kernel-CHECKED `CleanCic` certificate that `is_whnf(_0)` holds for the
/// value returned by one of the three exact build-embedded, audited clean-kernel
/// constructor fixtures (`prop`, `sort`, or `arrow`). The separately embedded
/// `from_kind` fixture must also validate as kind-preserving. Arbitrary MIR is
/// advisory-only and cannot mint. Fail-closed (`None`) on any fixture mismatch,
/// spec-build, MIR-extraction (non-WHNF head),
/// kernel-check, negative-control, serialization, or round-trip failure.
#[must_use]
pub fn certify_is_whnf_from_mir(func: &VerifiableFunction) -> Option<trust_ir::ProofEvidence> {
    sealed_constructor_material(func)?;
    let func = func.clone();
    run_on_large_stack(move || {
        let spec = Specification::new().ok()?;
        certify_from_mir_with_spec(&spec, &func)
    })
    .flatten()
}

/// Heavy body of the consumer-side MIR-grounded re-check against a built spec.
fn recheck_from_mir_with_spec(
    spec: &Specification,
    func: &VerifiableFunction,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    let env = spec.env();
    // Independently re-establish exact fixture membership and rebuild the goal.
    let Some((head, _)) = sealed_constructor_material(func) else {
        return false;
    };
    let Some(linked) = link_whnf(env, canonical_kexpr_src(head)) else {
        return false;
    };
    if !crate::is_canonical_term(term_bytes, &linked.proof) {
        return false;
    }
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(env, &term, &linked.goal) {
        return false;
    }
    mir_lineage_digest(func, head, term_bytes, context_bytes).as_ref() == Some(lineage)
}

/// Consumer-side re-check of a MIR-grounded `is_whnf` certificate: independently
/// require exact membership in the embedded audited fixture allowlist, rebuild
/// the spec and goal,
/// deserialize the term, re-run the clean-kernel `check_type`, and re-bind the
/// lineage. `true` ONLY if the kernel accepts the deserialized term against the
/// freshly-rebuilt goal AND the lineage matches — a tampered term, swapped
/// lineage, or non-WHNF `func` fails closed.
#[must_use]
pub fn recheck_is_whnf_from_mir(
    func: &VerifiableFunction,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if sealed_constructor_material(func).is_none()
        || !crate::is_canonical_empty_context(context_bytes)
    {
        return false;
    }
    let func = func.clone();
    let term = term_bytes.to_vec();
    let context = context_bytes.to_vec();
    let lineage = *lineage;
    run_on_large_stack(move || {
        let Some(spec) = Specification::new().ok() else {
            return false;
        };
        recheck_from_mir_with_spec(&spec, &func, &term, &context, &lineage)
    })
    .unwrap_or(false)
}

// ════════════════════════════════════════════════════════════════════════════
// LITERAL-`whnf` identity-path brick — the FIRST property about the real REDUCER.
//
// The MIR lane ABOVE proves a property about clean-kernel CONSTRUCTORS
// (`Expr::prop`/`arrow`/… return a WHNF head). This lane proves the first property
// about the literal `whnf` FUNCTION: the early-return match at
// `clean-kernel/src/tc/whnf.rs:145-165`
//
//   match &e.kind {
//       ExprKind::Sort(_) | Pi(..) | Lam(..) | Lit(_) | BVar(_) => return e.clone(),
//       ExprKind::FVar(id) => { ...conditional... }
//       _ => {}   // App/Const/Let/Proj/MData/… fall through to the recursive core
//   }
//
// is the IDENTITY on its Sort/Pi/Lam/Lit/BVar heads — it returns its argument
// UNCHANGED. This is NON-RECURSIVE (a single match + `return e.clone()`), so it
// dodges the blockers that make full recursive `whnf` research-scale (heartbeat-
// fuel termination, the `Arc`/`RefCell` cache, un-monomorphized generic callees).
// The extracted `whnf_impl` MIR (the fn `whnf` delegates to) is (verbatim):
//
//   bb0:  _3 = &((*e).kind)                         // e = arg local _2
//         _4 = Discriminant((*_3))                  // discriminant of (*e).kind
//         SwitchInt(move _4) -> [0: bb2, 1: bb1, 2: bb2, 5: bb2, 6: bb2, 8: bb2],
//                               otherwise: bb11
//   bb2:  _0 = <Expr as Clone>::clone(Copy _2) -> bb16   // return e.clone()
//   bb16: return
//
// The analyzer confirms, PER INPUT VARIANT, that the SwitchInt routes the variant
// to a block returning `_0 = clone(e)` where the clone argument is the SAME
// argument `e` the discriminant was read from. Sort/Lam/Pi (variants 2/5/6) then
// discharge `is_whnf` through the SAME kernel lane as the constructor brick;
// Lit/BVar (8/0) prove identity from MIR but FAIL CLOSED at discharge (the KExpr
// model has no `is_whnf.lit`/`is_whnf.bvar` ctor) — the honest partial result.
//
// NO MASQUERADE (this lane mints `CleanCic` = TCB-adjacent; the negative controls
// are LOAD-BEARING and gate minting):
//   * the FVar arm (variant 1) is CONDITIONAL — its block borrows `self.ctx` and
//     only sometimes returns `e.clone()`; the analyzer MUST reject it (its block
//     does something other than unconditionally return the argument);
//   * an App-headed input (variant 4) FALLS THROUGH the early return into the
//     recursive core (`otherwise` -> bb11 -> `inc_heartbeat`/`whnf_inner`); it has
//     NO explicit SwitchInt target, so the analyzer MUST fail closed — the witness
//     that this brick claims NOTHING about the recursive `whnf`.
// The identity is READ FROM the real MIR (SwitchInt + copy-trace-to-argument),
// never assumed. Provenance + regen: the fixture directory's `PROVENANCE.md`.
// ════════════════════════════════════════════════════════════════════════════

/// Lineage domain for the LITERAL-`whnf` identity-path discharge. Distinct from
/// both the fixture-string and the constructor-MIR domains so a whnf-identity
/// certificate can never alias a constructor-lane certificate.
const WHNF_IDENTITY_LINEAGE_DOMAIN: &str =
    "trust-certify.cleancic.checker-core.whnf-identity-path-discharge.v2";

const MIR_WHNF_IMPL_JSON: &str =
    include_str!("../fixtures/checker_core_is_whnf_mir/clean_kernel.tc.whnf.whnf_impl.json");

/// `ExprKind::App` — the head that FALLS THROUGH `whnf`'s early return into the
/// recursive core (whnf.rs `_ => {}`). The identity analyzer MUST reject it.
const APP_INPUT_VARIANT: usize = 4;

/// `ExprKind::FVar` — `whnf`'s CONDITIONAL arm (returns `e.clone()` only for a
/// non-let FVar). NOT an unconditional identity; the analyzer MUST reject it.
const FVAR_INPUT_VARIANT: usize = 1;

/// Is `local` one of the function's arguments (`_1..=_arg_count`; `_0` is the
/// return slot)?
fn is_argument_local(func: &VerifiableFunction, local: usize) -> bool {
    local >= 1 && local <= func.body.arg_count
}

/// The block with id `id`, or `None`.
fn block_by_id(func: &VerifiableFunction, id: BlockId) -> Option<&BasicBlock> {
    func.body.blocks.iter().find(|bb| bb.id == id)
}

/// `[Deref, Field(_)]` — the place reads a struct FIELD of a DEREFERENCED
/// reference, i.e. `(*e).<field>` (here `(*e).kind`). This binds the discriminant
/// to the `.kind` field so the variant index maps to the right `ExprKind` head.
fn projections_are_deref_then_field(projs: &[Projection]) -> bool {
    matches!(projs, [Projection::Deref, Projection::Field(_)])
}

/// Peel `local` to the ROOT local it ultimately denotes, following unique `Use`
/// copies AND single reborrows (`Ref` / `AddressOf` / `CopyForDeref`). Bounded.
/// Lets the analyzer prove the discriminant place and the clone argument denote
/// the SAME underlying argument even when rustc routes one through a `&(*e).kind`
/// reborrow and the other through a plain `Copy` of `e`.
fn resolve_to_root_local(func: &VerifiableFunction, mut local: usize) -> usize {
    for _ in 0..32 {
        match unique_assign(func, local) {
            Some(Rvalue::Use(op)) => match operand_local(op) {
                Some(src) => local = src,
                None => return local,
            },
            Some(Rvalue::Ref { place, .. })
            | Some(Rvalue::AddressOf(_, place))
            | Some(Rvalue::CopyForDeref(place)) => local = place.local,
            _ => return local,
        }
    }
    local
}

/// Given the `discriminant(...)` place a SwitchInt reads, confirm it is the
/// discriminant of a FIELD of a DEREFERENCED argument (`(*e).kind`) and return
/// that argument's local. Handles both the direct place `(*e).kind` and rustc's
/// `_r = &((*e).kind); discriminant(*_r)` reborrow (the shape `whnf` emits). Fail
/// closed otherwise.
fn discriminant_arg_of_deref_field(func: &VerifiableFunction, disc_place: &Place) -> Option<usize> {
    // Case A: discriminant directly on `(*arg).<field>`.
    if is_argument_local(func, disc_place.local)
        && projections_are_deref_then_field(&disc_place.projections)
    {
        return Some(disc_place.local);
    }
    // Case B: discriminant on `*_r` where `_r = &((*arg).<field>)`.
    if disc_place.projections == [Projection::Deref] {
        return match unique_assign(func, disc_place.local) {
            Some(Rvalue::Ref { place, .. })
            | Some(Rvalue::AddressOf(_, place))
            | Some(Rvalue::CopyForDeref(place))
                if is_argument_local(func, place.local)
                    && projections_are_deref_then_field(&place.projections) =>
            {
                Some(place.local)
            }
            _ => None,
        };
    }
    None
}

/// `(arg_local, targets, otherwise)` of `whnf`'s discriminant-on-`(*e).kind`
/// SwitchInt: the argument matched on, its `(discriminant value, block)` arms,
/// and the fall-through block (the recursive core).
type WhnfKindSwitch = (usize, Vec<(u128, BlockId)>, BlockId);

/// Find the SwitchInt that head-matches on `discriminant((*e).kind)` for an
/// argument `e`, returning `(arg_local, targets, otherwise)`. Fail closed if no
/// block ends in such a SwitchInt (the fn does not match on an argument's
/// `ExprKind` head at all).
pub(crate) fn whnf_kind_switch_public(
    func: &VerifiableFunction,
) -> Option<(usize, Vec<(u128, BlockId)>, BlockId)> {
    whnf_kind_switch(func)
}

fn whnf_kind_switch(func: &VerifiableFunction) -> Option<WhnfKindSwitch> {
    for bb in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &bb.terminator else {
            continue;
        };
        let Some(d) = operand_local(discr) else {
            continue;
        };
        let Some(Rvalue::Discriminant(disc_place)) =
            unique_assign(func, resolve_copy_source(func, d))
        else {
            continue;
        };
        if let Some(arg_local) = discriminant_arg_of_deref_field(func, disc_place) {
            return Some((arg_local, targets.clone(), *otherwise));
        }
    }
    None
}

/// Follow a bounded chain of `Goto`-terminated blocks whose statements are all
/// value-preserving ([`WriteEffect::NoValueWrite`]), returning the first
/// non-`Goto` block. `None` if a block on the path carries a value-writing
/// statement (a value change that would break the identity claim) or the chain
/// exceeds the bound.
fn skip_noop_gotos(func: &VerifiableFunction, start: BlockId) -> Option<&BasicBlock> {
    let mut id = start;
    for _ in 0..16 {
        let bb = block_by_id(func, id)?;
        match &bb.terminator {
            Terminator::Goto(next) => {
                if !bb.stmts.iter().all(|s| s.write_effect() == WriteEffect::NoValueWrite) {
                    return None;
                }
                id = *next;
            }
            _ => return Some(bb),
        }
    }
    None
}

/// Does the SwitchInt target `target` return `_0 = e.clone()` — call
/// `Clone::clone` on the SAME argument `arg_local`, write the RETURN slot `_0`,
/// then reach `return` — with NO intervening value-writing statement? This is the
/// structural read of `return e.clone()` (the identity). Fail closed on any other
/// shape (the FVar conditional arm's `RefCell::borrow`, the fall-through's
/// `inc_heartbeat`, or a block that clones a DIFFERENT local).
pub(crate) fn block_returns_clone_of_arg_public(
    func: &VerifiableFunction,
    target: BlockId,
    arg_local: usize,
) -> bool {
    block_returns_clone_of_arg(func, target, arg_local)
}

fn block_returns_clone_of_arg(
    func: &VerifiableFunction,
    target: BlockId,
    arg_local: usize,
) -> bool {
    let Some(bb) = skip_noop_gotos(func, target) else {
        return false;
    };
    // The arm block must carry ONLY value-preserving statements (nothing mangles
    // `_0` or the argument before the clone).
    if !bb.stmts.iter().all(|s| s.write_effect() == WriteEffect::NoValueWrite) {
        return false;
    }
    // ... and terminate in `_0 = Clone::clone(<arg>)`.
    let Terminator::Call { func: callee, args, dest, target: ret, .. } = &bb.terminator else {
        return false;
    };
    if dest.local != RETURN_LOCAL || !dest.projections.is_empty() {
        return false;
    }
    if final_segment(callee) != "clone" {
        return false;
    }
    // The clone's argument must trace back to the SAME argument the discriminant
    // was read from — that is what makes this the identity `return e.clone()`.
    let Some(clone_arg) = args.first().and_then(operand_local) else {
        return false;
    };
    if resolve_to_root_local(func, clone_arg) != arg_local {
        return false;
    }
    // The clone's continuation must reach `return` with `_0` untouched.
    let Some(ret) = ret else {
        return false;
    };
    let Some(ret_bb) = skip_noop_gotos(func, *ret) else {
        return false;
    };
    ret_bb.stmts.iter().all(|s| s.write_effect() == WriteEffect::NoValueWrite)
        && matches!(ret_bb.terminator, Terminator::Return)
}

/// Confirm, FROM THE REAL fork-extracted MIR, that `whnf`'s early-return match
/// returns its argument UNCHANGED (`return e.clone()`) for `variant`: the
/// `discriminant((*e).kind)` SwitchInt routes `variant` to a block that returns
/// `_0 = e.clone()` on the SAME argument `e`.
///
/// TRUE for the unconditional early-return heads (Sort/Pi/Lam/Lit/BVar). FALSE
/// (fail closed) for the CONDITIONAL FVar arm, for App/Const/Let/Proj/MData which
/// FALL THROUGH into the recursive core (no explicit SwitchInt target), and for
/// any fn that does not head-match an argument's `ExprKind` at all.
/// Advisory only for arbitrary MIR: certificate APIs additionally require exact
/// equality with the embedded audited `whnf_impl` fixture.
#[must_use]
pub fn whnf_returns_arg_identity_for_variant(func: &VerifiableFunction, variant: usize) -> bool {
    let Some((arg_local, targets, _otherwise)) = whnf_kind_switch(func) else {
        return false;
    };
    // `variant` must have an EXPLICIT SwitchInt target — a value routed to
    // `otherwise` (the recursive core) is NOT an identity path.
    let Some((_, target)) = targets.iter().copied().find(|(v, _)| *v == variant as u128) else {
        return false;
    };
    block_returns_clone_of_arg(func, target, arg_local)
}

// Diagnostic-only structural lane. These recognizers and their crate-visible
// landmarks do not mint, recheck, or authorize `ProofEvidence`; in particular,
// they are not composed into a universal reducer certificate. Certificate
// authority remains sealed to the exact-fixture lanes below.

/// The number of `ExprKind` variants — the FULL 25-variant enum
/// (`clean-kernel/src/expr/kind.rs`): the 11 core forms (BVar 0 … MData 10) PLUS
/// SProp(11), Squash(12), the six cubical forms CubicalInterval(13)/I0(14)/I1(15)/
/// Path(16)/PathLam(17)/PathApp(18), CubicalHComp(19)/Transp(20)/Coe(21), and the
/// three ZFC forms ZFCSet(22)/ZFCMem(23)/ZFCComprehension(24). The dispatch-totality
/// analysis classifies EVERY variant in `0..EXPRKIND_VARIANTS`; a variant landing
/// in no class (or a class landing outside this range) fails the partition.
///
/// CORRECTION (2026-07-17): this was first landed as 11, silently truncating the
/// range — the totality then only covered the core forms while variants 11..=24
/// (which also route through `otherwise` into the recursive core; `whnf_core_inner`'s
/// kind switch has explicit arms at 18..=21 = PathApp/HComp/Transp/Coe) were outside
/// the claimed partition. The witness logic was sound; the RANGE was wrong.
const EXPRKIND_VARIANTS: usize = 25;

/// The TOTAL dispatch partition of the real outer `whnf_impl` MIR, read from its
/// `discriminant((*e).kind)` SwitchInt: every `ExprKind` variant `0..=24` is
/// classified into exactly one of four classes. This is the OUTER half of the
/// reducer branch analysis (the model-level twin is the attested
/// `whnf_progress_bd`/`whnf_normalizes_bd` case split): the identity-WHNF class is
/// dischargeable by the `is_whnf.{sort,lam,pi}` heads, the identity-residual class
/// is the narrow-`is_whnf` `stuck` residual clean-verify itself discloses, and the
/// recursive-core class is exactly the complement routed to the `stack_safe`
/// closure (the INNER half, analyzed against the closure body's MIR).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhnfDispatchPartition {
    /// Identity return of an already-WHNF ctor head: Sort(2), Lam(5), Pi(6).
    pub identity_whnf: Vec<usize>,
    /// Identity return the narrow `is_whnf` cannot classify: BVar(0), Lit(8).
    pub identity_residual: Vec<usize>,
    /// The conditional local-context lookup arm: FVar(1).
    pub fvar_lookup: Vec<usize>,
    /// The `otherwise` complement routed to the recursive core (`stack_safe`
    /// closure): Const(3), App(4), Let(7), Proj(9), MData(10), plus every extended
    /// form SProp(11)..ZFCComprehension(24) — the reducible/deferred forms all go
    /// through the recursive core (whose own kind switch handles e.g. the cubical
    /// computation forms PathApp(18)/HComp(19)/Transp(20)/Coe(21) explicitly).
    pub recursive_core: Vec<usize>,
}

/// Bounded BFS from `start`: does some reachable block terminate in a `Call` to
/// `stack_safe` writing the RETURN slot `_0`? This is the structural witness that
/// the `otherwise` complement genuinely routes into the recursive core (the
/// reduction loop lives inside the `stack_safe` closure) rather than, say,
/// silently returning the unreduced input. Fail closed beyond the block bound.
fn reaches_stack_safe_writing_ret(func: &VerifiableFunction, start: BlockId) -> bool {
    let mut seen = vec![start];
    let mut queue = vec![start];
    let mut steps = 0usize;
    while let Some(id) = queue.pop() {
        steps += 1;
        if steps > 64 {
            return false;
        }
        let Some(bb) = block_by_id(func, id) else {
            return false;
        };
        let push = |b: BlockId, seen: &mut Vec<BlockId>, queue: &mut Vec<BlockId>| {
            if !seen.contains(&b) {
                seen.push(b);
                queue.push(b);
            }
        };
        match &bb.terminator {
            Terminator::Call { func: callee, dest, target, .. } => {
                if final_segment(callee) == "stack_safe"
                    && dest.local == RETURN_LOCAL
                    && dest.projections.is_empty()
                {
                    return true;
                }
                if let Some(t) = target {
                    push(*t, &mut seen, &mut queue);
                }
            }
            Terminator::Goto(t) => push(*t, &mut seen, &mut queue),
            Terminator::SwitchInt { targets, otherwise, .. } => {
                for (_, t) in targets {
                    push(*t, &mut seen, &mut queue);
                }
                push(*otherwise, &mut seen, &mut queue);
            }
            Terminator::Drop { target, .. } => push(*target, &mut seen, &mut queue),
            _ => {}
        }
    }
    false
}

/// Read the TOTAL dispatch partition off the real outer `whnf_impl` MIR. Fails
/// closed (`None`) unless EVERY invariant holds:
///
///   * the fn head-matches `discriminant((*e).kind)` (via [`whnf_kind_switch`]);
///   * every EXPLICIT switch value is in `0..EXPRKIND_VARIANTS` and appears once;
///   * every explicit value classifies as identity (`_0 = e.clone()`, the
///     [`block_returns_clone_of_arg`] read) or as the single non-identity
///     FVar-lookup arm — nothing else;
///   * the identity values split exactly into the WHNF ctor heads
///     (Sort/Lam/Pi = `{2,5,6}`) and the narrow-`is_whnf` residual
///     (BVar/Lit = `{0,8}`), per [`exprkind_variant_to_whnf_head`]'s mapping;
///   * the `otherwise` complement (every variant with NO explicit target) routes
///     into the recursive core — [`reaches_stack_safe_writing_ret`];
///   * the four classes together cover ALL `EXPRKIND_VARIANTS` variants exactly
///     once (the TOTALITY witness).
#[must_use]
pub fn whnf_dispatch_partition(func: &VerifiableFunction) -> Option<WhnfDispatchPartition> {
    let (arg_local, targets, otherwise) = whnf_kind_switch(func)?;

    let mut identity_whnf = Vec::new();
    let mut identity_residual = Vec::new();
    let mut fvar_lookup = Vec::new();
    let mut explicit = Vec::new();

    for (value, target) in &targets {
        let variant = usize::try_from(*value).ok()?;
        if variant >= EXPRKIND_VARIANTS || explicit.contains(&variant) {
            return None; // out-of-range or duplicate switch value
        }
        explicit.push(variant);
        if block_returns_clone_of_arg(func, *target, arg_local) {
            // Identity arm: classify by whether the returned head is a WHNF ctor.
            if exprkind_variant_to_whnf_head(variant).is_some() {
                identity_whnf.push(variant);
            } else {
                identity_residual.push(variant);
            }
        } else if variant == 1 {
            // The single conditional (FVar local-context lookup) arm.
            fvar_lookup.push(variant);
        } else {
            return None; // an explicit non-identity, non-FVar arm — unknown shape
        }
    }

    // The otherwise complement must genuinely route into the recursive core.
    if !reaches_stack_safe_writing_ret(func, otherwise) {
        return None;
    }
    let recursive_core: Vec<usize> =
        (0..EXPRKIND_VARIANTS).filter(|v| !explicit.contains(v)).collect();

    // TOTALITY: the four classes cover 0..EXPRKIND_VARIANTS exactly once.
    let mut all: Vec<usize> = identity_whnf
        .iter()
        .chain(&identity_residual)
        .chain(&fvar_lookup)
        .chain(&recursive_core)
        .copied()
        .collect();
    all.sort_unstable();
    if all != (0..EXPRKIND_VARIANTS).collect::<Vec<_>>() {
        return None;
    }

    identity_whnf.sort_unstable();
    identity_residual.sort_unstable();
    Some(WhnfDispatchPartition { identity_whnf, identity_residual, fvar_lookup, recursive_core })
}

/// The stack_safe PAYLOAD witness — the link from the dispatch partition's
/// recursive-core class to the actual reduction entry point. The real
/// `whnf_impl::{closure#1}` (the closure `whnf_impl` hands to `expr::stack_safe`
/// in its recursive-core branch) is a PURE `whnf_inner(self, e)` PASSTHROUGH,
/// read fail-closed off its real fork-extracted MIR:
///
///   * exactly two blocks: `[capture-unpack + the call]`, `[bare Return]`;
///   * every statement in block 0 only UNPACKS closure captures — an `Assign`
///     whose rvalue is `Use(Copy/Move)` of a `Field` projection of local `_1`
///     (the closure environment), writing a non-return temp;
///   * NO statement anywhere writes the return place `_0`, so the closure's sole
///     call is the ONLY possible writer of `_0` (well-formed MIR must write the
///     return place before `Return`) — the closure returns EXACTLY that call's
///     result;
///   * the terminator is the fork's `Opaque`-encoded unwind-carrying call whose
///     `kind` names `tc::whnf::…::whnf_inner` (the fork lowers
///     `Call::…::UnsupportedUnwind(..)` opaquely but preserves the callee path in
///     `kind`), continuing to the Return block.
///
/// Together with [`whnf_dispatch_partition`] this grounds, on the literal MIR:
/// recursive-core variants -> `stack_safe(closure#1)` -> `whnf_inner` — the
/// entry of the reduction loop (`whnf_core_inner`), the INNER half's root.
#[must_use]
pub fn whnf_stack_safe_payload_is_whnf_inner(closure: &VerifiableFunction) -> bool {
    if closure.body.blocks.len() != 2 {
        return false;
    }
    let b0 = &closure.body.blocks[0];
    let b1 = &closure.body.blocks[1];
    // Block 1: a bare `Return`.
    if !b1.stmts.is_empty() || !matches!(b1.terminator, Terminator::Return) {
        return false;
    }
    // No statement anywhere writes `_0`.
    for bb in &closure.body.blocks {
        for s in &bb.stmts {
            if let Statement::Assign { place, .. } = s
                && place.local == RETURN_LOCAL
            {
                return false;
            }
        }
    }
    // Block 0: capture unpacking only — `_n = copy (_1.<field>)`.
    for s in &b0.stmts {
        let Statement::Assign { place, rvalue, .. } = s else {
            return false;
        };
        if place.local == RETURN_LOCAL {
            return false;
        }
        let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue else {
            return false;
        };
        if src.local != 1 || !matches!(src.projections.first(), Some(Projection::Field(_))) {
            return false;
        }
    }
    // The sole call: the Opaque-encoded `whnf_inner`, continuing to block 1.
    let Terminator::Opaque { kind, targets, .. } = &b0.terminator else {
        return false;
    };
    kind.starts_with("Call::tc::whnf")
        && kind.contains("::whnf_inner::")
        && targets.as_slice() == [BlockId(1)]
}

/// Bounded BFS: the set of blocks reachable from `start` (inclusive) following
/// every successor edge (Goto/Call/Opaque/SwitchInt/Drop). Fail-closed: returns
/// `None` if the walk exceeds the bound (the caller must treat that as "unknown").
fn reachable_blocks(func: &VerifiableFunction, start: BlockId) -> Option<Vec<BlockId>> {
    let mut seen = vec![start];
    let mut queue = vec![start];
    let mut steps = 0usize;
    while let Some(id) = queue.pop() {
        steps += 1;
        if steps > 256 {
            return None;
        }
        let bb = block_by_id(func, id)?;
        let succs: Vec<BlockId> = match &bb.terminator {
            Terminator::Goto(t) => vec![*t],
            Terminator::Call { target, .. } => target.iter().copied().collect(),
            Terminator::Opaque { targets, .. } => targets.clone(),
            Terminator::SwitchInt { targets, otherwise, .. } => {
                targets.iter().map(|(_, t)| *t).chain([*otherwise]).collect()
            }
            Terminator::Drop { target, .. } => vec![*target],
            _ => vec![],
        };
        for s in succs {
            if !seen.contains(&s) {
                seen.push(s);
                queue.push(s);
            }
        }
    }
    Some(seen)
}

/// The block whose terminator's Opaque `kind` contains `needle` — the way the
/// fork-extracted MIR names unwind-carrying callees. Fails closed unless EXACTLY
/// one block matches (ambiguity would make a shape witness unsound).
fn unique_opaque_call_block(func: &VerifiableFunction, needle: &str) -> Option<BlockId> {
    let mut found = None;
    for bb in &func.body.blocks {
        if let Terminator::Opaque { kind, .. } = &bb.terminator
            && kind.starts_with("Call::")
            && kind.contains(needle)
        {
            if found.is_some() {
                return None;
            }
            found = Some(bb.id);
        }
    }
    found
}

/// The CACHED-REDUCER witness for the real `whnf_inner` MIR — the next literal
/// link after the stack_safe payload. `whnf_inner` is a cache wrapper around the
/// reduction loop, read fail-closed off its real fork-extracted MIR:
///
///   * exactly ONE reduction call — the Opaque-encoded
///     `tc::whnf_proj::…::whnf_outer_loop` (the reduction loop's entry);
///   * exactly ONE cache lookup (`SlidingCache::…::get`) and ONE cache insert
///     (`SlidingCache::…::insert`);
///   * the lookup's continuation reaches a `SwitchInt` (the `Option`
///     discriminant) from which the reducer call is reachable via EXACTLY ONE
///     arm (the miss arm) — the hit arm returns the cached value WITHOUT
///     reducing and WITHOUT inserting;
///   * the cache INSERT is reachable from the REDUCER's continuation — the only
///     value ever inserted is the reducer's result (the cache-coherence
///     invariant: the cache stores nothing but `whnf_outer_loop` outputs).
///
/// Together with the dispatch partition and the payload witness this grounds:
/// recursive-core -> stack_safe(closure#1) -> whnf_inner -> {cache hit |
/// whnf_outer_loop + insert} on the literal MIR. (The remaining inner links —
/// `whnf_outer_loop` -> `whnf_core*`/`beta_or_iota_step` returning WHNF heads —
/// are the committed fixtures' next analyses.)
#[must_use]
pub fn whnf_inner_is_cached_reducer(func: &VerifiableFunction) -> bool {
    let Some(lm) = cached_reducer_landmarks(func) else {
        return false;
    };
    // The hit arm reaches NEITHER the reducer (enforced by the landmark
    // classification) NOR the insert; the insert sits on the reducer's
    // continuation (the miss path stores exactly the reducer's result).
    let Some(hit_reach) = reachable_blocks(func, lm.hit_arm) else {
        return false;
    };
    if hit_reach.contains(&lm.insert) {
        return false;
    }
    match reachable_blocks(func, lm.after_reducer) {
        Some(reach) => reach.contains(&lm.insert),
        None => false,
    }
}

/// The semantic LANDMARKS of the cached-reducer wrapper, derived fail-closed
/// from the real MIR: the unique reducer call, the unique cache get/insert, the
/// get switch's hit/miss arms (miss = the ONE arm from which the reducer is
/// reachable), and the reducer's continuation block. Retained for the
/// diagnostic Rust witness; no certificate-authority path consumes it.
#[derive(Debug, Clone, Copy)]
pub(crate) struct CachedReducerLandmarks {
    pub reducer: BlockId,
    pub insert: BlockId,
    pub hit_arm: BlockId,
    pub miss_arm: BlockId,
    pub after_reducer: BlockId,
}

/// Derive [`CachedReducerLandmarks`] — every identification fail-closed
/// (ambiguous calls, a non-2-arm switch, zero or two reducer-reaching arms all
/// yield `None`).
pub(crate) fn cached_reducer_landmarks(
    func: &VerifiableFunction,
) -> Option<CachedReducerLandmarks> {
    let reducer = unique_opaque_call_block(func, "::whnf_outer_loop::")?;
    let get = unique_opaque_call_block(func, ">::get::")?;
    let insert = unique_opaque_call_block(func, ">::insert::")?;

    // The lookup flows into an Option-discriminant SwitchInt with two arms.
    let get_bb = block_by_id(func, get)?;
    let Terminator::Opaque { targets: get_targets, .. } = &get_bb.terminator else {
        return None;
    };
    let switch = get_targets.first().and_then(|t| block_by_id(func, *t))?;
    let Terminator::SwitchInt { targets: arms, .. } = &switch.terminator else {
        return None;
    };
    if arms.len() != 2 {
        return None;
    }
    // miss = the ONE arm from which the reducer is reachable; hit = the other.
    let mut miss = None;
    let mut hit = None;
    for (_, arm) in arms {
        if reachable_blocks(func, *arm)?.contains(&reducer) {
            if miss.is_some() {
                return None; // both arms reduce: no genuine hit path
            }
            miss = Some(*arm);
        } else {
            hit = Some(*arm);
        }
    }
    let (miss_arm, hit_arm) = (miss?, hit?);

    let reducer_bb = block_by_id(func, reducer)?;
    let Terminator::Opaque { targets: red_targets, .. } = &reducer_bb.terminator else {
        return None;
    };
    let after_reducer = *red_targets.first()?;

    Some(CachedReducerLandmarks { reducer, insert, hit_arm, miss_arm, after_reducer })
}

/// [`reachable_blocks`] with one CFG edge cut (`cut_from -> cut_to` removed) —
/// the loop-analysis primitive: cutting a loop's backedge separates "exits this
/// iteration" from "re-loops".
fn reachable_blocks_with_cut(
    func: &VerifiableFunction,
    start: BlockId,
    cut_from: BlockId,
    cut_to: BlockId,
) -> Option<Vec<BlockId>> {
    let mut seen = vec![start];
    let mut queue = vec![start];
    let mut steps = 0usize;
    while let Some(id) = queue.pop() {
        steps += 1;
        if steps > 256 {
            return None;
        }
        let bb = block_by_id(func, id)?;
        let succs: Vec<BlockId> = match &bb.terminator {
            Terminator::Goto(t) => vec![*t],
            Terminator::Call { target, .. } => target.iter().copied().collect(),
            Terminator::Opaque { targets, .. } => targets.clone(),
            Terminator::SwitchInt { targets, otherwise, .. } => {
                targets.iter().map(|(_, t)| *t).chain([*otherwise]).collect()
            }
            Terminator::Drop { target, .. } => vec![*target],
            _ => vec![],
        };
        for s in succs {
            if id == cut_from && s == cut_to {
                continue; // the cut edge
            }
            if !seen.contains(&s) {
                seen.push(s);
                queue.push(s);
            }
        }
    }
    Some(seen)
}

/// The FIXPOINT-EXIT witness for the real `whnf_outer_loop` MIR — the reduction
/// loop returns ONLY through one of its three legitimate exits, read fail-closed
/// off the real fork-extracted MIR by CUTTING the loop backedge and checking
/// which arms can still reach `Return`:
///
///   1. the FIXPOINT exit — the `Expr::eq(old, new)` check's TRUE arm (the
///      iteration changed nothing: the result is a fixpoint of the reduction
///      step — the literal-MIR content of "whnf returns an unreducible term");
///   2. the CACHE-HIT exit — after a change, the reduced term's whnf is already
///      cached (`SlidingCache::get` -> `Some`); sound by the cache-coherence
///      invariant ([`whnf_inner_is_cached_reducer`]: the cache stores nothing
///      but reducer outputs);
///   3. the HEARTBEAT bail — the budget-exhaustion arm (the kernel's honest
///      incompleteness disclosure, the literal analog of the model's `stuck`).
///
/// The load-bearing negative: the CHANGED + CACHE-MISS arm CANNOT reach `Return`
/// with the backedge cut — a freshly-reduced, uncached term ALWAYS re-loops
/// (through the heartbeat check) until one of the three exits fires. No path
/// returns a term that just changed without either finding its cached whnf or
/// re-entering the loop.
#[must_use]
pub fn whnf_outer_loop_exits_only_at_fixpoint_cache_or_heartbeat(
    func: &VerifiableFunction,
) -> bool {
    let Some(lm) = fixpoint_exit_landmarks(func) else {
        return false;
    };
    let reach_cut = |start: BlockId| -> Option<Vec<BlockId>> {
        reachable_blocks_with_cut(func, start, lm.backedge_from, lm.heartbeat)
    };
    // 1. The heartbeat bail exits; 2. the fixpoint arm exits; 3. the cache-hit
    //    arm exits; 4. THE LOAD-BEARING NEGATIVE: the changed + cache-miss arm
    //    CANNOT exit — it must re-loop (reach the backedge source), never
    //    Return, with the cut.
    if !reach_cut(lm.hb_bail).is_some_and(|r| r.contains(&lm.ret)) {
        return false;
    }
    if !reach_cut(lm.fixpoint_arm).is_some_and(|r| r.contains(&lm.ret)) {
        return false;
    }
    if !reach_cut(lm.hit_arm).is_some_and(|r| r.contains(&lm.ret)) {
        return false;
    }
    match reach_cut(lm.miss_arm) {
        Some(r) => !r.contains(&lm.ret) && r.contains(&lm.backedge_from),
        None => false,
    }
}

/// The semantic LANDMARKS of the reduce-until-fixpoint loop, derived fail-closed
/// from the real MIR: the heartbeat block (loop head), the unique Goto backedge
/// into it, the sole Return, the heartbeat bail arm, the eq fixpoint/changed
/// arms, and the changed path's cache hit/miss arms. Retained for the diagnostic
/// Rust witness; no certificate-authority path consumes it.
#[derive(Debug, Clone, Copy)]
pub(crate) struct FixpointLandmarks {
    pub heartbeat: BlockId,
    pub backedge_from: BlockId,
    pub ret: BlockId,
    pub hb_bail: BlockId,
    pub fixpoint_arm: BlockId,
    pub hit_arm: BlockId,
    pub miss_arm: BlockId,
}

/// Derive [`FixpointLandmarks`] from the real MIR — every identification step
/// fail-closed (ambiguity, missing shapes, or a broken continue-path all yield
/// `None`). Includes the derivation-time sanity conditions (the heartbeat
/// continue arm reaches the eq check; the cache lookup on the changed path is
/// unique).
pub(crate) fn fixpoint_exit_landmarks(func: &VerifiableFunction) -> Option<FixpointLandmarks> {
    // The heartbeat block (loop head) and the unique Goto backedge into it.
    let heartbeat = unique_opaque_call_block(func, "::heartbeat_exhausted::")?;
    let mut backedge_from = None;
    for bb in &func.body.blocks {
        if let Terminator::Goto(t) = &bb.terminator
            && *t == heartbeat
        {
            if backedge_from.is_some() {
                return None; // ambiguous backedge
            }
            backedge_from = Some(bb.id);
        }
    }
    let backedge_from = backedge_from?;

    // The sole Return block.
    let mut returns =
        func.body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let (Some(ret), None) = (returns.next(), returns.next()) else {
        return None;
    };
    let ret = ret.id;

    let reach_cut = |start: BlockId| -> Option<Vec<BlockId>> {
        reachable_blocks_with_cut(func, start, backedge_from, heartbeat)
    };

    // The heartbeat switch: bail = otherwise; continue = value-0 arm.
    let hb_bb = block_by_id(func, heartbeat)?;
    let Terminator::Opaque { targets: hb_targets, .. } = &hb_bb.terminator else {
        return None;
    };
    let hb_switch = hb_targets.first().and_then(|t| block_by_id(func, *t))?;
    let Terminator::SwitchInt { targets: hb_arms, otherwise: hb_bail, .. } = &hb_switch.terminator
    else {
        return None;
    };
    let (_, hb_continue) = hb_arms.iter().find(|(v, _)| *v == 0)?;

    // The eq (fixpoint) check on the continue path.
    let eq = unique_opaque_call_block(func, "PartialEq>::eq::")?;
    if !reach_cut(*hb_continue).is_some_and(|r| r.contains(&eq)) {
        return None;
    }
    let eq_bb = block_by_id(func, eq)?;
    let Terminator::Opaque { targets: eq_targets, .. } = &eq_bb.terminator else {
        return None;
    };
    let eq_switch = eq_targets.first().and_then(|t| block_by_id(func, *t))?;
    let Terminator::SwitchInt { targets: eq_arms, otherwise: fixpoint_arm, .. } =
        &eq_switch.terminator
    else {
        return None;
    };
    let (_, changed_arm) = eq_arms.iter().find(|(v, _)| *v == 0)?;

    // The changed path's UNIQUE cache lookup and its Option switch.
    let changed_reach = reach_cut(*changed_arm)?;
    let mut get_in_changed = None;
    for bb in &func.body.blocks {
        if let Terminator::Opaque { kind, .. } = &bb.terminator
            && kind.starts_with("Call::")
            && kind.contains(">::get::")
            && changed_reach.contains(&bb.id)
        {
            if get_in_changed.is_some() {
                return None; // ambiguous: two lookups on the changed path
            }
            get_in_changed = Some(bb.id);
        }
    }
    let get = get_in_changed?;
    let get_bb = block_by_id(func, get)?;
    let Terminator::Opaque { targets: get_targets, .. } = &get_bb.terminator else {
        return None;
    };
    let get_switch = get_targets.first().and_then(|t| block_by_id(func, *t))?;
    let Terminator::SwitchInt { targets: get_arms, .. } = &get_switch.terminator else {
        return None;
    };
    let (_, hit_arm) = get_arms.iter().find(|(v, _)| *v == 1)?;
    let (_, miss_arm) = get_arms.iter().find(|(v, _)| *v == 0)?;

    Some(FixpointLandmarks {
        heartbeat,
        backedge_from,
        ret,
        hb_bail: *hb_bail,
        fixpoint_arm: *fixpoint_arm,
        hit_arm: *hit_arm,
        miss_arm: *miss_arm,
    })
}

/// The successor ids of block `id` (the SAME edge relation the reachability
/// witnesses walk) — shared with the kernel-side graph encoder.
pub(crate) fn block_successors(func: &VerifiableFunction, id: BlockId) -> Option<Vec<BlockId>> {
    let bb = block_by_id(func, id)?;
    Some(match &bb.terminator {
        Terminator::Goto(t) => vec![*t],
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Opaque { targets, .. } => targets.clone(),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            targets.iter().map(|(_, t)| *t).chain([*otherwise]).collect()
        }
        Terminator::Drop { target, .. } => vec![*target],
        _ => vec![],
    })
}

/// The WHNF discharge head for a `whnf` input variant whose identity path is
/// MIR-CONFIRMED. `Some(Sort/Lam/Pi)` for variants 2/5/6 (dischargeable to
/// `is_whnf.sort/lam/pi`); `None` for Lit/BVar (identity is PROVEN from MIR, but
/// the KExpr model has no `is_whnf.lit`/`is_whnf.bvar` ctor — the honest partial
/// result, so discharge fails closed) and for any non-identity variant.
#[must_use]
pub fn whnf_identity_path_head(func: &VerifiableFunction, variant: usize) -> Option<WhnfHead> {
    if whnf_returns_arg_identity_for_variant(func, variant) {
        exprkind_variant_to_whnf_head(variant)
    } else {
        None
    }
}

/// Seal certificate authority to the exact build-embedded `whnf_impl` extract.
/// The structural identity analyzer remains public for diagnostics, but only an
/// exact match of every serialized MIR field may authorize CleanCic evidence.
fn sealed_whnf_identity_material(
    func: &VerifiableFunction,
    variant: usize,
) -> Option<(WhnfHead, Vec<u8>)> {
    let (canonical, canonical_bytes) = embedded_mir(MIR_WHNF_IMPL_JSON)?;
    if bincode::serialize(func).ok()? != canonical_bytes {
        return None;
    }
    Some((whnf_identity_path_head(&canonical, variant)?, canonical_bytes))
}

/// SHA-256 lineage for a whnf-identity discharge, binding the term, the empty
/// closed context, every serialized field of the exact canonical `whnf_impl`
/// fixture, the matched input variant, and the MIR-derived head. Position-tagged
/// + length-prefixed => injective; a certificate for one body/variant/head cannot
/// be replayed against another.
fn whnf_identity_lineage_digest(
    func: &VerifiableFunction,
    variant: usize,
    head: WhnfHead,
    term_bytes: &[u8],
    context_bytes: &[u8],
) -> Option<trust_ir::ProofDigest> {
    let (sealed_head, canonical_mir) = sealed_whnf_identity_material(func, variant)?;
    if sealed_head != head {
        return None;
    }
    let variant_bytes = (variant as u64).to_le_bytes();
    let mut hasher = Sha256::new();
    hasher.update(WHNF_IDENTITY_LINEAGE_DOMAIN.as_bytes());
    for (tag, field) in [
        (b"term:".as_slice(), term_bytes),
        (b"ctx:".as_slice(), context_bytes),
        (b"mir:".as_slice(), canonical_mir.as_slice()),
        (b"variant:".as_slice(), variant_bytes.as_slice()),
        (b"head:".as_slice(), head.tag().as_bytes()),
    ] {
        hasher.update(tag);
        hasher.update((field.len() as u64).to_le_bytes());
        hasher.update(field);
    }
    let digest = hasher.finalize();
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(&digest);
    Some(trust_ir::ProofDigest::sha256(bytes))
}

/// Heavy body of the whnf-identity mint against an already-built spec.
fn certify_whnf_identity_with_spec(
    spec: &Specification,
    func: &VerifiableFunction,
    variant: usize,
) -> Option<trust_ir::ProofEvidence> {
    let env = spec.env();

    // 1. LITERAL-MIR: require the exact audited `whnf_impl` fixture, then
    //    confirm its identity path for `variant`. The loose CFG recognizer is
    //    advisory and cannot authorize arbitrary caller-authored MIR.
    let (head, _) = sealed_whnf_identity_material(func, variant)?;

    // 2. LINK the canonical KExpr for that head (the is_whnf.* ctor is re-derived
    //    from the KExpr's OWN args, never supplied).
    let linked = link_whnf(env, canonical_kexpr_src(head))?;

    // 3. DISCHARGE: the clean kernel must accept the derived ctor term.
    if !kernel_checks_goal(env, &linked.proof, &linked.goal) {
        return None;
    }

    // 4. NO MASQUERADE (mandatory, minting GATED): the shared is_whnf controls
    //    (stuck-app link fails; wrong ctor and delta-reducing const are
    //    kernel-rejected) AND the whnf-SPECIFIC literal-MIR controls — the
    //    App-headed input FALLS THROUGH into the recursive core and the FVar arm
    //    is CONDITIONAL, so BOTH must FAIL the identity check on this very MIR.
    //    This witnesses that the brick claims only the non-recursive identity
    //    slice, never the recursive core.
    if !stuck_app_link_fails_closed(env)
        || !wrong_ctor_kernel_rejected(env)
        || !delta_reducing_const_kernel_rejected(env)
    {
        return None;
    }
    if whnf_returns_arg_identity_for_variant(func, APP_INPUT_VARIANT)
        || whnf_returns_arg_identity_for_variant(func, FVAR_INPUT_VARIANT)
    {
        return None;
    }

    // 5. Serialize + round-trip re-check.
    let term_bytes = serialize_term(&linked.proof).ok()?;
    let context_bytes = crate::canonical_empty_context_bytes()?;
    let roundtrip = deserialize_term(&term_bytes).ok()?;
    if !kernel_checks_goal(env, &roundtrip, &linked.goal) {
        return None;
    }
    let lineage = whnf_identity_lineage_digest(func, variant, head, &term_bytes, &context_bytes)?;

    Some(trust_ir::ProofEvidence::CleanCic {
        term: term_bytes,
        context: context_bytes,
        lineage,
        kernel_recheck: None,
    })
}

/// Mint a kernel-CHECKED `CleanCic` certificate that the literal `whnf` reducer is
/// the IDENTITY on its `variant` early-return head (`return e.clone()`), provided
/// `func` exactly matches the build-embedded audited `whnf_impl` MIR, AND that
/// the returned head is in WHNF (`is_whnf`). Only the
/// discharge heads Sort/Lam/Pi (variants 2/5/6) mint; Lit/BVar prove identity but
/// fail closed at discharge; App/FVar (and any non-identity variant) fail closed
/// at the identity analyzer. Fail-closed (`None`) on any spec-build, identity,
/// kernel-check, negative-control, serialization, or round-trip failure.
#[must_use]
pub fn certify_whnf_identity_from_mir(
    func: &VerifiableFunction,
    variant: usize,
) -> Option<trust_ir::ProofEvidence> {
    sealed_whnf_identity_material(func, variant)?;
    let func = func.clone();
    run_on_large_stack(move || {
        let spec = Specification::new().ok()?;
        certify_whnf_identity_with_spec(&spec, &func, variant)
    })
    .flatten()
}

/// Heavy body of the consumer-side whnf-identity re-check against a built spec.
fn recheck_whnf_identity_with_spec(
    spec: &Specification,
    func: &VerifiableFunction,
    variant: usize,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    let env = spec.env();
    // Independently re-establish exact fixture membership and rebuild the goal.
    let Some((head, _)) = sealed_whnf_identity_material(func, variant) else {
        return false;
    };
    let Some(linked) = link_whnf(env, canonical_kexpr_src(head)) else {
        return false;
    };
    if !crate::is_canonical_term(term_bytes, &linked.proof) {
        return false;
    }
    let Ok(term) = deserialize_term(term_bytes) else {
        return false;
    };
    if !kernel_checks_goal(env, &term, &linked.goal) {
        return false;
    }
    whnf_identity_lineage_digest(func, variant, head, term_bytes, context_bytes).as_ref()
        == Some(lineage)
}

/// Consumer-side re-check of a whnf-identity certificate: independently require
/// exact equality with the embedded audited `whnf_impl` fixture, rebuild the
/// spec and goal,
/// deserialize the term, re-run the clean-kernel `check_type`, and re-bind the
/// lineage. `true` ONLY if the kernel accepts the deserialized term against the
/// freshly-rebuilt goal AND the lineage matches — a tampered term, swapped
/// lineage, or non-identity `(func, variant)` fails closed.
#[must_use]
pub fn recheck_whnf_identity_from_mir(
    func: &VerifiableFunction,
    variant: usize,
    term_bytes: &[u8],
    context_bytes: &[u8],
    lineage: &trust_ir::ProofDigest,
) -> bool {
    if sealed_whnf_identity_material(func, variant).is_none()
        || !crate::is_canonical_empty_context(context_bytes)
    {
        return false;
    }
    let func = func.clone();
    let term = term_bytes.to_vec();
    let context = context_bytes.to_vec();
    let lineage = *lineage;
    run_on_large_stack(move || {
        let Some(spec) = Specification::new().ok() else {
            return false;
        };
        recheck_whnf_identity_with_spec(&spec, &func, variant, &term, &context, &lineage)
    })
    .unwrap_or(false)
}

// ────────────────────────────────────────────────────────────────────────────
// INNER REDUCTION CORE step routing — `whnf_core_inner`'s kind dispatch.
//
// `whnf_core_inner` is the loop where the actual REDUCTION STEPS live: its root
// ExprKind switch routes each kind to its step family — δ (definition
// unfolding) from Const, β/ι (`beta_or_iota_step`, plus the native/nat
// accelerators and Glue elimination) from App, ι-proj from Proj, path-β from
// PathApp, and each kan reduction (HComp/Transp/Coe) from exactly its own
// cubical kind; FVar/Let/MData route to NO step call (inline handling). The
// loop re-enters the dispatch head through a SINGLE backedge, so cutting that
// one edge yields sound PER-ITERATION routing facts.
// ────────────────────────────────────────────────────────────────────────────

/// The semantic LANDMARKS of the inner core's kind dispatch, derived
/// fail-closed from the literal MIR: the root ExprKind switch (the unique
/// SwitchInt with ≥ 8 arms all < 25), its single loop backedge, the sorted
/// (variant, arm target) list, and the twelve tracked step-callee blocks.
/// Shared by the Rust witness and the KERNEL-side reflection.
#[derive(Debug, Clone)]
pub(crate) struct CoreRoutingLandmarks {
    pub head: BlockId,
    pub backedge_from: BlockId,
    /// `(variant, arm target)`, sorted by variant.
    pub arms: Vec<(usize, BlockId)>,
    pub delta_unfold: BlockId,
    pub delta_env: BlockId,
    /// `beta_or_iota_step` has exactly two call sites (app spine / cached path).
    pub beta_iota: [BlockId; 2],
    pub iota_proj: BlockId,
    pub path_beta: BlockId,
    pub kan_hcomp: BlockId,
    pub kan_transp: BlockId,
    pub kan_coe: BlockId,
    pub kan_glue: BlockId,
    pub native: BlockId,
    pub nat_native: BlockId,
}

/// Derive [`CoreRoutingLandmarks`] — every identification step fail-closed
/// (ambiguity, missing shapes, unexpected predecessors all yield `None`).
pub(crate) fn core_routing_landmarks(func: &VerifiableFunction) -> Option<CoreRoutingLandmarks> {
    // The root kind switch: the UNIQUE SwitchInt with ≥ 8 arms, all < 25.
    let mut head = None;
    for bb in &func.body.blocks {
        if let Terminator::SwitchInt { targets, .. } = &bb.terminator
            && targets.len() >= 8
            && targets.iter().all(|(v, _)| *v < 25)
        {
            if head.is_some() {
                return None;
            }
            head = Some(bb.id);
        }
    }
    let head = head?;

    // Exactly two predecessors: the entry block and the single loop backedge.
    let mut preds = Vec::new();
    for bb in &func.body.blocks {
        if block_successors(func, bb.id)?.contains(&head) {
            preds.push(bb.id);
        }
    }
    preds.sort_unstable_by_key(|b| b.0);
    let [entry, backedge_from] = preds.as_slice() else {
        return None;
    };
    if *entry != BlockId(0) {
        return None;
    }
    let backedge_from = *backedge_from;

    let head_bb = block_by_id(func, head)?;
    let Terminator::SwitchInt { targets, .. } = &head_bb.terminator else {
        return None;
    };
    let mut arms = Vec::with_capacity(targets.len());
    for (v, t) in targets {
        arms.push((usize::try_from(*v).ok()?, *t));
    }
    arms.sort_unstable_by_key(|(v, _)| *v);

    let mut beta_iota = Vec::new();
    for bb in &func.body.blocks {
        if let Terminator::Opaque { kind, .. } = &bb.terminator
            && kind.contains("::beta_or_iota_step::")
        {
            beta_iota.push(bb.id);
        }
    }
    beta_iota.sort_unstable_by_key(|b| b.0);
    let [bi0, bi1] = beta_iota.as_slice() else {
        return None;
    };

    Some(CoreRoutingLandmarks {
        head,
        backedge_from,
        arms,
        delta_unfold: unique_opaque_call_block(func, "::unfold_definition_cached::")?,
        delta_env: unique_opaque_call_block(func, "::unfold_with_transparency::")?,
        beta_iota: [*bi0, *bi1],
        iota_proj: unique_opaque_call_block(func, "::whnf_reduce_proj::")?,
        path_beta: unique_opaque_call_block(func, "::try_path_beta_step::")?,
        kan_hcomp: unique_opaque_call_block(func, "::try_hcomp_reduction::")?,
        kan_transp: unique_opaque_call_block(func, "::try_transp_reduction::")?,
        kan_coe: unique_opaque_call_block(func, "::try_coe_reduction::")?,
        kan_glue: unique_opaque_call_block(func, "::try_glue_reduction::")?,
        native: unique_opaque_call_block(func, "::reduce_native::")?,
        nat_native: unique_opaque_call_block(func, "::native_nat_binop_grind_stuck::")?,
    })
}

/// THE STEP-ROUTING WITNESS: with the single backedge cut, EVERY kind arm's
/// per-iteration reachable set hits EXACTLY its expected step-callee family
/// over all twelve tracked call sites:
///
///   FVar(1) / Let(7) / MData(10)  →  ∅ (inline handling, no step call)
///   Const(3)                      →  {δ unfold-cached, δ env-unfold} only
///   App(4)                        →  {β/ι both sites, Glue elim, native, nat}
///   Proj(9)                       →  {ι-proj} only
///   PathApp(18)                   →  {path-β} only
///   HComp(19)/Transp(20)/Coe(21)  →  exactly its own kan reduction
///
/// This is the literal-MIR grounding that δ fires ONLY from Const, β/ι ONLY
/// from the App spine, and the kan steps sit ONLY under the cubical kinds
/// (which the F-scope gate proves dead in the default mode). Fail-closed.
#[must_use]
pub fn whnf_core_inner_routes_steps_by_kind(func: &VerifiableFunction) -> bool {
    let Some(lm) = core_routing_landmarks(func) else {
        return false;
    };
    let variants: Vec<usize> = lm.arms.iter().map(|(v, _)| *v).collect();
    if variants != [1, 3, 4, 7, 9, 10, 18, 19, 20, 21] {
        return false;
    }
    let tracked = [
        lm.delta_unfold,
        lm.delta_env,
        lm.beta_iota[0],
        lm.beta_iota[1],
        lm.iota_proj,
        lm.path_beta,
        lm.kan_hcomp,
        lm.kan_transp,
        lm.kan_coe,
        lm.kan_glue,
        lm.native,
        lm.nat_native,
    ];
    let expected = |v: usize| -> Vec<BlockId> {
        match v {
            3 => vec![lm.delta_unfold, lm.delta_env],
            4 => vec![lm.beta_iota[0], lm.beta_iota[1], lm.kan_glue, lm.native, lm.nat_native],
            9 => vec![lm.iota_proj],
            18 => vec![lm.path_beta],
            19 => vec![lm.kan_hcomp],
            20 => vec![lm.kan_transp],
            21 => vec![lm.kan_coe],
            _ => Vec::new(),
        }
    };
    for (v, target) in &lm.arms {
        let Some(r) = reachable_blocks_with_cut(func, *target, lm.backedge_from, lm.head) else {
            return false;
        };
        let want = expected(*v);
        for c in tracked {
            if r.contains(&c) != want.contains(&c) {
                return false;
            }
        }
    }
    true
}

// ────────────────────────────────────────────────────────────────────────────
// STEP FUNCTION: `beta_or_iota_step` — the β+ι head-contraction the App case
// rests on. FIRST property about what a step FUNCTION DOES (not just where
// dispatch routes it). The head is pre-normalized by `whnf_recurse`, its result
// classified by ONE `is_lam` switch, and the two contraction families are
// DISJOINTLY partitioned by that redex test: β (`instantiate_rev`) fires ONLY
// when the whnf'd head is a lambda; the ι/quot/nat/int/native reducer family
// fires ONLY when it is not. This is the "only fires on a genuine redex" half of
// the reduction-universal, grounded on the literal MIR.
// ────────────────────────────────────────────────────────────────────────────

/// Landmarks of `beta_or_iota_step`, derived fail-closed from the literal MIR:
/// the two arms of the `is_lam` partition switch (β = is_lam TRUE, ι = FALSE),
/// the β substitution primitive, the native-nat stuck guard, and the five
/// ι-family reducer call sites. Shared by the Rust witness and the KERNEL-side
/// reflection.
#[derive(Debug, Clone, Copy)]
pub(crate) struct BetaIotaLandmarks {
    /// is_lam = TRUE arm (β / lambda contraction).
    pub beta_arm: BlockId,
    /// is_lam = FALSE arm (ι / non-lambda reduction).
    pub iota_arm: BlockId,
    pub instantiate_rev: BlockId,
    pub guard: BlockId,
    /// try_iota / try_quot / reduce_nat / reduce_int / reduce_native.
    pub iota_reducers: [BlockId; 5],
}

/// Derive [`BetaIotaLandmarks`] — every step fail-closed (ambiguity, missing
/// shapes, a non-unique callee all yield `None`).
pub(crate) fn beta_iota_landmarks(func: &VerifiableFunction) -> Option<BetaIotaLandmarks> {
    // The is_lam call → its unique continuation → the partition SwitchInt on the
    // Bool result: value-0 = FALSE (ι arm), otherwise = TRUE (β arm).
    let is_lam = unique_opaque_call_block(func, "::is_lam::")?;
    let is_lam_bb = block_by_id(func, is_lam)?;
    let Terminator::Opaque { targets, .. } = &is_lam_bb.terminator else {
        return None;
    };
    let switch = targets.first().and_then(|t| block_by_id(func, *t))?;
    let Terminator::SwitchInt { targets: arms, otherwise: beta_arm, .. } = &switch.terminator
    else {
        return None;
    };
    let (_, iota_arm) = arms.iter().find(|(v, _)| *v == 0)?;

    Some(BetaIotaLandmarks {
        beta_arm: *beta_arm,
        iota_arm: *iota_arm,
        instantiate_rev: unique_opaque_call_block(func, "::instantiate_rev::")?,
        guard: unique_opaque_call_block(func, "::native_nat_grind_recursor_stuck::")?,
        iota_reducers: [
            unique_opaque_call_block(func, "::try_iota_reduction::")?,
            unique_opaque_call_block(func, "::try_quot_reduction::")?,
            unique_opaque_call_block(func, "::reduce_nat::")?,
            unique_opaque_call_block(func, "::reduce_int::")?,
            unique_opaque_call_block(func, "::reduce_native::")?,
        ],
    })
}

/// THE REDEX-GATED CONTRACTION WITNESS: the pre-normalized head's `is_lam` test
/// EXCLUSIVELY partitions the contraction on the literal MIR —
///
///   is_lam TRUE  →  reaches {instantiate_rev, stuck guard}, NO ι reducer
///   is_lam FALSE →  reaches every ι reducer, NEITHER instantiate_rev nor guard
///
/// i.e. β fires iff the whnf'd head is a lambda (a genuine redex); the
/// ι/quot/nat/int/native family fires iff it is not. Fail-closed. (The graph is
/// cyclic — four internal loops — but bounded BFS with a visited set saturates
/// in ≤ node-count pops, so the exclusion negatives are sound.)
#[must_use]
pub fn beta_or_iota_step_gates_contraction_by_redex(func: &VerifiableFunction) -> bool {
    let Some(lm) = beta_iota_landmarks(func) else {
        return false;
    };
    let (Some(beta_r), Some(iota_r)) =
        (reachable_blocks(func, lm.beta_arm), reachable_blocks(func, lm.iota_arm))
    else {
        return false;
    };
    // β arm: reaches the substitution + the stuck guard, NO ι reducer.
    if !beta_r.contains(&lm.instantiate_rev) || !beta_r.contains(&lm.guard) {
        return false;
    }
    if lm.iota_reducers.iter().any(|c| beta_r.contains(c)) {
        return false;
    }
    // ι arm: reaches every ι reducer, NEITHER the substitution nor the guard.
    if !lm.iota_reducers.iter().all(|c| iota_r.contains(c)) {
        return false;
    }
    if iota_r.contains(&lm.instantiate_rev) || iota_r.contains(&lm.guard) {
        return false;
    }
    true
}

// ────────────────────────────────────────────────────────────────────────────
// RECURSION BOUNDARY: `whnf_recurse` — the mode router on the production spine
// (`reduce_proj_with_mode` → `whnf_recurse`). Its root `WhnfMode` switch is
// EXHAUSTIVE (otherwise → Unreachable) and routes each mode to a DISJOINT
// reducer: Full → the δ-enabled `whnf_impl`; the two NoDelta modes → the
// cached `stack_safe(whnf_core_inner)` path; Transparency → its own
// `stack_safe` reducer. The load-bearing δ-DISCIPLINE fact: a NoDelta
// re-entry can NEVER route into the δ-enabled `whnf_impl` — the projection
// recursion cannot smuggle δ into a no-δ descent.
// ────────────────────────────────────────────────────────────────────────────

/// Landmarks of `whnf_recurse`, derived fail-closed from the literal MIR.
#[derive(Debug, Clone, Copy)]
pub(crate) struct RecurseModeLandmarks {
    /// The exhaustive root WhnfMode switch block.
    pub mode_switch: BlockId,
    /// Full-mode arm target (the whnf_impl call block).
    pub full_arm: BlockId,
    /// The shared NoDelta arm target (mode values 1 and 2).
    pub nodelta_arm: BlockId,
    /// Transparency arm target (its own stack_safe call block).
    pub transp_arm: BlockId,
    pub whnf_impl: BlockId,
    pub cache_get: BlockId,
    pub cache_insert: BlockId,
    /// The NoDelta reducer stack_safe site (cache-miss path).
    pub nodelta_stack_safe: BlockId,
    /// Cache-hit arm (returns without reducing) and cache-miss arm.
    pub hit_arm: BlockId,
    pub miss_arm: BlockId,
    pub ret: BlockId,
}

/// Derive [`RecurseModeLandmarks`] — every step fail-closed.
pub(crate) fn recurse_mode_landmarks(func: &VerifiableFunction) -> Option<RecurseModeLandmarks> {
    // The root mode switch: the UNIQUE SwitchInt with exactly 4 arms, values
    // {0,1,2,3}, whose otherwise block is Unreachable (exhaustive enum).
    let mut mode_switch = None;
    for bb in &func.body.blocks {
        if let Terminator::SwitchInt { targets, otherwise, .. } = &bb.terminator
            && targets.len() == 4
        {
            let mut vals: Vec<u128> = targets.iter().map(|(v, _)| *v).collect();
            vals.sort_unstable();
            if vals == [0, 1, 2, 3]
                && block_by_id(func, *otherwise)
                    .is_some_and(|b| matches!(b.terminator, Terminator::Unreachable))
            {
                if mode_switch.is_some() {
                    return None;
                }
                mode_switch = Some(bb.id);
            }
        }
    }
    let mode_switch = mode_switch?;
    let ms_bb = block_by_id(func, mode_switch)?;
    let Terminator::SwitchInt { targets, .. } = &ms_bb.terminator else {
        return None;
    };
    let arm = |v: u128| targets.iter().find(|(av, _)| *av == v).map(|(_, t)| *t);
    let (full_arm, nd1, nd2, transp_arm) = (arm(0)?, arm(1)?, arm(2)?, arm(3)?);
    // The two NoDelta modes share one arm target (the shared cached path).
    if nd1 != nd2 {
        return None;
    }

    let whnf_impl = unique_opaque_call_block(func, "::whnf_impl::")?;
    let cache_get = unique_opaque_call_block(func, "SlidingCache")
        .or_else(|| unique_opaque_call_block(func, "::get::"))?;
    let cache_insert = unique_opaque_call_block(func, "::insert::")?;

    // The two stack_safe sites: the Transparency arm target is one; the OTHER
    // is the NoDelta reducer (on the cache-miss path).
    let mut stack_safes = Vec::new();
    for bb in &func.body.blocks {
        if let Terminator::Opaque { kind, .. } = &bb.terminator
            && kind.contains("expr::stack_safe::")
        {
            stack_safes.push(bb.id);
        }
    }
    stack_safes.sort_unstable_by_key(|b| b.0);
    let [ss_a, ss_b] = stack_safes.as_slice() else {
        return None;
    };
    let nodelta_stack_safe = if *ss_a == transp_arm {
        *ss_b
    } else if *ss_b == transp_arm {
        *ss_a
    } else {
        return None;
    };

    // The hit/miss switch: the Option switch after the cache get.
    let get_bb = block_by_id(func, cache_get)?;
    let Terminator::Opaque { targets: get_targets, .. } = &get_bb.terminator else {
        return None;
    };
    let hm_switch = get_targets.first().and_then(|t| block_by_id(func, *t))?;
    let Terminator::SwitchInt { targets: hm_arms, .. } = &hm_switch.terminator else {
        return None;
    };
    let hit_arm = hm_arms.iter().find(|(v, _)| *v == 1).map(|(_, t)| *t)?;
    let miss_arm = hm_arms.iter().find(|(v, _)| *v == 0).map(|(_, t)| *t)?;

    let mut returns =
        func.body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let (Some(ret), None) = (returns.next(), returns.next()) else {
        return None;
    };

    Some(RecurseModeLandmarks {
        mode_switch,
        full_arm,
        nodelta_arm: nd1,
        transp_arm,
        whnf_impl,
        cache_get,
        cache_insert,
        nodelta_stack_safe,
        hit_arm,
        miss_arm,
        ret: ret.id,
    })
}

/// THE MODE-FIDELITY WITNESS: on the literal `whnf_recurse` MIR —
///
///   Full        → reaches whnf_impl; NEVER the cache, the NoDelta reducer,
///                 or the Transparency reducer;
///   NoDelta     → reaches the cache get + the NoDelta stack_safe reducer +
///                 the insert; NEVER whnf_impl nor the Transparency reducer
///                 (δ-DISCIPLINE: no-δ re-entry cannot reach the δ-enabled
///                 implementation);
///   Transparency→ reaches its own reducer; NEVER whnf_impl nor the cache;
///   cache HIT   → returns WITHOUT reaching the reducer or the insert;
///   cache MISS  → reaches the reducer.
///
/// Fail-closed; the root switch must be the exhaustive 4-arm WhnfMode switch
/// (otherwise → Unreachable) with the two NoDelta modes sharing one arm.
#[must_use]
pub fn whnf_recurse_routes_by_mode(func: &VerifiableFunction) -> bool {
    let Some(lm) = recurse_mode_landmarks(func) else {
        return false;
    };
    let reach = |start: BlockId| reachable_blocks(func, start);
    let (Some(full_r), Some(nd_r), Some(tr_r), Some(hit_r), Some(miss_r)) = (
        reach(lm.full_arm),
        reach(lm.nodelta_arm),
        reach(lm.transp_arm),
        reach(lm.hit_arm),
        reach(lm.miss_arm),
    ) else {
        return false;
    };
    // Full: δ-enabled implementation only.
    if !full_r.contains(&lm.whnf_impl)
        || full_r.contains(&lm.cache_get)
        || full_r.contains(&lm.nodelta_stack_safe)
        || full_r.contains(&lm.transp_arm)
    {
        return false;
    }
    // NoDelta: cached no-δ reducer only — the δ-DISCIPLINE negative.
    if !nd_r.contains(&lm.cache_get)
        || !nd_r.contains(&lm.nodelta_stack_safe)
        || !nd_r.contains(&lm.cache_insert)
        || nd_r.contains(&lm.whnf_impl)
        || nd_r.contains(&lm.transp_arm)
    {
        return false;
    }
    // Transparency: its own reducer only.
    if !tr_r.contains(&lm.transp_arm)
        || tr_r.contains(&lm.whnf_impl)
        || tr_r.contains(&lm.cache_get)
        || tr_r.contains(&lm.nodelta_stack_safe)
    {
        return false;
    }
    // Cache coherence on the NoDelta path.
    if !hit_r.contains(&lm.ret)
        || hit_r.contains(&lm.nodelta_stack_safe)
        || hit_r.contains(&lm.cache_insert)
    {
        return false;
    }
    miss_r.contains(&lm.nodelta_stack_safe)
}

// ────────────────────────────────────────────────────────────────────────────
// STEP FUNCTION INTERIORS (round 3 fixtures): the δ step
// (`unfold_definition_cached`) and the ι-projection step
// (`reduce_proj_with_mode`), plus the `whnf_reduce_proj` shim that links
// `whnf_core_inner`'s ι-proj arm to the real step. These ground what the δ
// and ι-proj steps DO: δ's env unfold fires only on a Const-kind expr and
// only cache-missing Consts get unfolded+cached; ι-proj's field extraction
// fires only on a constructor-headed struct with the field present, and the
// complement rebuilds an honest stuck `proj`.
// ────────────────────────────────────────────────────────────────────────────

/// Landmarks of the δ step `unfold_definition_cached`, fail-closed.
#[derive(Debug, Clone, Copy)]
pub(crate) struct DeltaStepLandmarks {
    pub cache_get: BlockId,
    pub hit_arm: BlockId,
    pub miss_arm: BlockId,
    /// The Const-kind arm (kind switch value 3) and its complement.
    pub const_arm: BlockId,
    pub nonconst_arm: BlockId,
    pub env_unfold: BlockId,
    pub some_arm: BlockId,
    pub none_arm: BlockId,
    pub insert: BlockId,
    pub ret: BlockId,
}

pub(crate) fn delta_step_landmarks(func: &VerifiableFunction) -> Option<DeltaStepLandmarks> {
    let cache_get = unique_opaque_call_block(func, "SlidingCache")
        .or_else(|| unique_opaque_call_block(func, "::get::"))?;
    let get_bb = block_by_id(func, cache_get)?;
    let Terminator::Opaque { targets, .. } = &get_bb.terminator else {
        return None;
    };
    let hm = targets.first().and_then(|t| block_by_id(func, *t))?;
    let Terminator::SwitchInt { targets: hm_arms, .. } = &hm.terminator else {
        return None;
    };
    let hit_arm = hm_arms.iter().find(|(v, _)| *v == 1).map(|(_, t)| *t)?;
    let miss_arm = hm_arms.iter().find(|(v, _)| *v == 0).map(|(_, t)| *t)?;

    // The kind switch on the miss path: the unique single-arm SwitchInt with
    // case value 3 (ExprKind::Const) reachable from the miss arm.
    let miss_reach = reachable_blocks(func, miss_arm)?;
    let mut kind_switch = None;
    for bb in &func.body.blocks {
        if let Terminator::SwitchInt { targets, .. } = &bb.terminator
            && targets.len() == 1
            && targets[0].0 == 3
            && miss_reach.contains(&bb.id)
        {
            if kind_switch.is_some() {
                return None;
            }
            kind_switch = Some(bb.id);
        }
    }
    let ks_bb = block_by_id(func, kind_switch?)?;
    let Terminator::SwitchInt { targets: ks_arms, otherwise, .. } = &ks_bb.terminator else {
        return None;
    };
    let const_arm = ks_arms[0].1;
    let nonconst_arm = *otherwise;

    let env_unfold = unique_opaque_call_block(func, "::unfold_definition::")?;
    // The Option-try switch after the unfold: 0 = Some/continue, 1 = None.
    let mut try_switch = None;
    for bb in &func.body.blocks {
        if let Terminator::Opaque { kind, targets: t, .. } = &bb.terminator
            && kind.contains("Try>::branch")
        {
            if try_switch.is_some() {
                return None;
            }
            try_switch = t.first().copied();
        }
    }
    let ts_bb = block_by_id(func, try_switch?)?;
    let Terminator::SwitchInt { targets: ts_arms, .. } = &ts_bb.terminator else {
        return None;
    };
    let some_arm = ts_arms.iter().find(|(v, _)| *v == 0).map(|(_, t)| *t)?;
    let none_arm = ts_arms.iter().find(|(v, _)| *v == 1).map(|(_, t)| *t)?;

    let mut returns =
        func.body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let (Some(ret), None) = (returns.next(), returns.next()) else {
        return None;
    };

    Some(DeltaStepLandmarks {
        cache_get,
        hit_arm,
        miss_arm,
        const_arm,
        nonconst_arm,
        env_unfold,
        some_arm,
        none_arm,
        insert: unique_opaque_call_block(func, "::insert::")?,
        ret: ret.id,
    })
}

/// THE δ-INTERIOR WITNESS: inside `unfold_definition_cached` —
///
///   cache HIT      → returns; NEVER unfolds, NEVER inserts;
///   miss NON-Const → returns; NEVER unfolds, NEVER inserts (δ fires ONLY on
///                    a Const-kind expr — inside the step itself);
///   miss Const     → reaches the env unfold;
///   unfold Some    → reaches the cache insert;
///   unfold None    → returns WITHOUT inserting.
#[must_use]
pub fn unfold_definition_cached_delta_interior(func: &VerifiableFunction) -> bool {
    let Some(lm) = delta_step_landmarks(func) else {
        return false;
    };
    let reach = |b: BlockId| reachable_blocks(func, b);
    let (Some(hit_r), Some(nc_r), Some(c_r), Some(some_r), Some(none_r)) = (
        reach(lm.hit_arm),
        reach(lm.nonconst_arm),
        reach(lm.const_arm),
        reach(lm.some_arm),
        reach(lm.none_arm),
    ) else {
        return false;
    };
    if !hit_r.contains(&lm.ret) || hit_r.contains(&lm.env_unfold) || hit_r.contains(&lm.insert) {
        return false;
    }
    if !nc_r.contains(&lm.ret) || nc_r.contains(&lm.env_unfold) || nc_r.contains(&lm.insert) {
        return false;
    }
    if !c_r.contains(&lm.env_unfold) {
        return false;
    }
    if !some_r.contains(&lm.insert) {
        return false;
    }
    !none_r.contains(&lm.insert) && none_r.contains(&lm.ret)
}

/// Landmarks of the ι-projection step `reduce_proj_with_mode`, fail-closed.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ProjStepLandmarks {
    /// The exhaustive 4-arm mode switch (struct-normalizer selection).
    pub mode_switch: BlockId,
    pub get_app_fn: BlockId,
    /// The Const-head arm (head-kind switch value 3) and the stuck complement.
    pub const_head_arm: BlockId,
    pub stuck_arm: BlockId,
    pub get_constructor: BlockId,
    /// Constructor found / not-found arms.
    pub found_arm: BlockId,
    pub slice_get: BlockId,
    /// Field present / missing arms.
    pub field_arm: BlockId,
    pub nofield_arm: BlockId,
    /// The whnf_recurse call on the EXTRACTED FIELD (not the mode-normalizer
    /// site).
    pub field_recurse: BlockId,
    pub proj_rebuild: BlockId,
    pub ret: BlockId,
}

pub(crate) fn proj_step_landmarks(func: &VerifiableFunction) -> Option<ProjStepLandmarks> {
    // The exhaustive mode switch (4 arms {0,1,2,3}, otherwise Unreachable).
    let mut mode_switch = None;
    for bb in &func.body.blocks {
        if let Terminator::SwitchInt { targets, otherwise, .. } = &bb.terminator
            && targets.len() == 4
        {
            let mut vals: Vec<u128> = targets.iter().map(|(v, _)| *v).collect();
            vals.sort_unstable();
            if vals == [0, 1, 2, 3]
                && block_by_id(func, *otherwise)
                    .is_some_and(|b| matches!(b.terminator, Terminator::Unreachable))
            {
                if mode_switch.is_some() {
                    return None;
                }
                mode_switch = Some(bb.id);
            }
        }
    }
    let mode_switch = mode_switch?;
    let ms_bb = block_by_id(func, mode_switch)?;
    let Terminator::SwitchInt { targets: ms_arms, .. } = &ms_bb.terminator else {
        return None;
    };
    let mode_arm = |v: u128| ms_arms.iter().find(|(av, _)| *av == v).map(|(_, t)| *t);
    let mode_recurse = mode_arm(1)?;

    let get_app_fn = unique_opaque_call_block(func, "::get_app_fn::")?;
    let gaf_bb = block_by_id(func, get_app_fn)?;
    let Terminator::Opaque { targets, .. } = &gaf_bb.terminator else {
        return None;
    };
    let head_switch = targets.first().and_then(|t| block_by_id(func, *t))?;
    let Terminator::SwitchInt { targets: hs_arms, otherwise: stuck_arm, .. } =
        &head_switch.terminator
    else {
        return None;
    };
    let (&(3, const_head_arm), []) = (hs_arms.first()?, &hs_arms[1..]) else {
        return None;
    };

    let get_constructor = unique_opaque_call_block(func, "::get_constructor::")?;
    let gc_bb = block_by_id(func, get_constructor)?;
    let Terminator::Opaque { targets: gc_targets, .. } = &gc_bb.terminator else {
        return None;
    };
    let found_switch = gc_targets.first().and_then(|t| block_by_id(func, *t))?;
    let Terminator::SwitchInt { targets: fs_arms, .. } = &found_switch.terminator else {
        return None;
    };
    let found_arm = fs_arms.iter().find(|(v, _)| *v == 1).map(|(_, t)| *t)?;
    let notfound_arm = fs_arms.iter().find(|(v, _)| *v == 0).map(|(_, t)| *t)?;
    // The not-found arm must BE the stuck complement (one shared join).
    if notfound_arm != *stuck_arm {
        return None;
    }

    let slice_get = unique_opaque_call_block(func, "slice::<impl [&expr::Expr]>::get")?;
    let sg_bb = block_by_id(func, slice_get)?;
    let Terminator::Opaque { targets: sg_targets, .. } = &sg_bb.terminator else {
        return None;
    };
    let field_switch = sg_targets.first().and_then(|t| block_by_id(func, *t))?;
    let Terminator::SwitchInt { targets: fld_arms, .. } = &field_switch.terminator else {
        return None;
    };
    let field_arm = fld_arms.iter().find(|(v, _)| *v == 1).map(|(_, t)| *t)?;
    let nofield_arm = fld_arms.iter().find(|(v, _)| *v == 0).map(|(_, t)| *t)?;

    // The TWO whnf_recurse sites: the mode arm's normalizer vs the extracted
    // field's recurse — disambiguated by mode-arm position.
    let mut recurse_sites = Vec::new();
    for bb in &func.body.blocks {
        if let Terminator::Opaque { kind, .. } = &bb.terminator
            && kind.contains("::whnf_recurse::")
        {
            recurse_sites.push(bb.id);
        }
    }
    recurse_sites.sort_unstable_by_key(|b| b.0);
    let [ra, rb] = recurse_sites.as_slice() else {
        return None;
    };
    let field_recurse = if *ra == mode_recurse {
        *rb
    } else if *rb == mode_recurse {
        *ra
    } else {
        return None;
    };
    // The field arm IS the field-recurse call block.
    if field_arm != field_recurse {
        return None;
    }

    let proj_rebuild = unique_opaque_call_block(func, "::proj::")?;
    let mut returns =
        func.body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let (Some(ret), None) = (returns.next(), returns.next()) else {
        return None;
    };

    Some(ProjStepLandmarks {
        mode_switch,
        get_app_fn,
        const_head_arm,
        stuck_arm: *stuck_arm,
        get_constructor,
        found_arm,
        slice_get,
        field_arm,
        nofield_arm,
        field_recurse,
        proj_rebuild,
        ret: ret.id,
    })
}

/// THE ι-PROJ INTERIOR WITNESS: inside `reduce_proj_with_mode` —
///
///   non-Const head   → rebuilds a STUCK proj; NEVER looks up a constructor,
///                      NEVER touches the field slice or recurses into a field;
///   Const head       → reaches the constructor lookup;
///   constructor found→ reaches the field-index slice lookup;
///   field present    → recurses into the EXTRACTED FIELD and returns WITHOUT
///                      rebuilding a stuck proj;
///   field missing    → rebuilds the stuck proj; NEVER recurses into a field.
///
/// i.e. ι-proj fires exactly on a constructor-headed struct with the field
/// present; every complement is the honest stuck rebuild.
#[must_use]
pub fn reduce_proj_fires_only_on_constructor(func: &VerifiableFunction) -> bool {
    let Some(lm) = proj_step_landmarks(func) else {
        return false;
    };
    let reach = |b: BlockId| reachable_blocks(func, b);
    let (Some(stuck_r), Some(ch_r), Some(found_r), Some(field_r), Some(nofield_r)) = (
        reach(lm.stuck_arm),
        reach(lm.const_head_arm),
        reach(lm.found_arm),
        reach(lm.field_arm),
        reach(lm.nofield_arm),
    ) else {
        return false;
    };
    if !stuck_r.contains(&lm.proj_rebuild)
        || stuck_r.contains(&lm.get_constructor)
        || stuck_r.contains(&lm.slice_get)
        || stuck_r.contains(&lm.field_recurse)
    {
        return false;
    }
    if !ch_r.contains(&lm.get_constructor) {
        return false;
    }
    if !found_r.contains(&lm.slice_get) {
        return false;
    }
    if !field_r.contains(&lm.ret) || field_r.contains(&lm.proj_rebuild) {
        return false;
    }
    nofield_r.contains(&lm.proj_rebuild) && !nofield_r.contains(&lm.field_recurse)
}

/// THE SPINE LINK: `whnf_reduce_proj` (the ι-proj callee `whnf_core_inner`
/// actually routes to) is a pure delegation shim — its sole call is
/// `reduce_proj_with_mode`, tail-flowing to the unique Return, and no
/// statement anywhere writes the return place.
#[must_use]
pub fn whnf_reduce_proj_delegates(func: &VerifiableFunction) -> bool {
    if func.body.blocks.len() != 2 {
        return false;
    }
    for bb in &func.body.blocks {
        for st in &bb.stmts {
            if let Statement::Assign { place, .. } = st
                && place.local == RETURN_LOCAL
            {
                return false;
            }
        }
    }
    let b0 = &func.body.blocks[0];
    let b1 = &func.body.blocks[1];
    if !matches!(b1.terminator, Terminator::Return) {
        return false;
    }
    let Terminator::Opaque { kind, targets, .. } = &b0.terminator else {
        return false;
    };
    kind.starts_with("Call::tc::whnf_proj")
        && kind.contains("::reduce_proj_with_mode::")
        && targets.as_slice() == [BlockId(1)]
}

#[cfg(test)]
mod tests {
    use trust_ir::ProofEvidence;

    use super::*;

    // Two costs live in this module and only one of them justifies `#[ignore]`.
    // A test that builds `Specification::new()` and kernel-checks a derivation
    // spends minutes and belongs in the slow lane
    // (`scripts/trust_kernel_derivation_lane.sh`). A test that reads a sealed
    // MIR fixture and asserts a structural/landmark property spends
    // microseconds — measured 2026-07-24, all nineteen of them together take
    // 0.15 s in a debug build — so ignoring those bought nothing and cost
    // everything: they ran nowhere, which is the same as not existing. Keep the
    // split by what a test actually does, not by which module it lives in.

    /// THE MILESTONE (first kernel-discharged checker-core STRUCTURAL
    /// postcondition) + the full no-masquerade story, all on a SINGLE expensive
    /// `Specification::new()` build:
    ///
    /// * each of the five sealed model-level WHNF heads (`sort`/`lam`/`pi`, a
    ///   delta-dead `const`, and its neutral application-spine closure) LINKs and
    ///   DISCHARGES to a kernel-CHECKED `CleanCic`
    ///   (real `is_whnf.*` proof checked against the `is_whnf(_0)` goal);
    /// * the `pi` payload serialize + round-trip re-checks (same spec);
    /// * a byte-tampered `pi` term fails the re-check (fail-closed);
    /// * a zeroed lineage fails the re-check (fail-closed);
    /// * NEGATIVE CONTROL (LOAD-BEARING): a bvar-headed stuck application and a
    ///   lambda-headed beta redex FAIL CLOSED at LINK — `certify_with_spec`
    ///   returns `None`, never `Certified`;
    /// * TAMPER: the `sort` proof is kernel-REJECTED against the `lam` goal;
    /// * DELTA CONTROL: a known reducing const links as a `NeutralConst`
    ///   candidate but is kernel-REJECTED.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn is_whnf_discharge_closes_and_fails_closed() {
        let outcome = run_on_large_stack(|| {
            let spec = Specification::new().expect("spec should build");
            let env = spec.env();

            // Each WHNF head links + discharges to a CleanCic.
            let mut minted = Vec::new();
            for fixture in [&WHNF_SORT, &WHNF_LAM, &WHNF_PI, &WHNF_NEUTRAL_CONST, &WHNF_NEUTRAL_APP]
            {
                let head = link_whnf(env, fixture.kexpr_src)
                    .unwrap_or_else(|| panic!("{} must LINK to a WHNF head", fixture.label))
                    .head;
                let expected = match fixture.kexpr_src {
                    s if s.starts_with("KExpr.sort") => WhnfHead::Sort,
                    s if s.starts_with("KExpr.lam") => WhnfHead::Lam,
                    s if s.starts_with("KExpr.pi") => WhnfHead::Pi,
                    s if s.starts_with("KExpr.app") => WhnfHead::NeutralApp,
                    _ => WhnfHead::NeutralConst,
                };
                assert_eq!(head, expected, "{} head classification", fixture.label);

                let ev = certify_with_spec(&spec, fixture)
                    .unwrap_or_else(|| panic!("{} must discharge to CleanCic", fixture.label));
                minted.push(ev);
            }

            // Round-trip + tamper + zeroed-lineage on the `pi` certificate.
            let ProofEvidence::CleanCic { term, context, lineage, kernel_recheck } =
                minted[2].clone()
            else {
                panic!("expected CleanCic evidence for pi");
            };
            let roundtrip_ok = recheck_with_spec(&spec, &WHNF_PI, &term, &context, &lineage);
            let mut tampered = term.clone();
            tampered[0] ^= 0xff;
            let tamper_rejected =
                !recheck_with_spec(&spec, &WHNF_PI, &tampered, &context, &lineage);
            let zero_lineage_rejected = !recheck_with_spec(
                &spec,
                &WHNF_PI,
                &term,
                &context,
                &trust_ir::ProofDigest::zero(),
            );

            // NEGATIVE CONTROLS.
            let stuck_app_fails = stuck_app_link_fails_closed(env);
            let wrong_ctor_rejected = wrong_ctor_kernel_rejected(env);
            let reducing_const_rejected = delta_reducing_const_kernel_rejected(env);

            (
                minted,
                kernel_recheck.is_none(),
                !term.is_empty() && !context.is_empty(),
                lineage != trust_ir::ProofDigest::zero(),
                roundtrip_ok,
                tamper_rejected,
                zero_lineage_rejected,
                stuck_app_fails,
                wrong_ctor_rejected,
                reducing_const_rejected,
            )
        })
        .expect("discharge thread must not panic");

        let (
            minted,
            recheck_none,
            nonempty_payload,
            lineage_bound,
            roundtrip_ok,
            tamper_rejected,
            zero_lineage_rejected,
            stuck_app_fails,
            wrong_ctor_rejected,
            reducing_const_rejected,
        ) = outcome;

        assert_eq!(minted.len(), 5, "all five sealed WHNF heads must discharge to CleanCic");
        for ev in &minted {
            assert!(matches!(ev, ProofEvidence::CleanCic { .. }), "each mint is CleanCic");
        }
        assert!(recheck_none, "no inline kernel_recheck sidecar");
        assert!(nonempty_payload, "nonempty CleanCic payload");
        assert!(lineage_bound, "pi lineage must be bound (nonzero)");
        assert!(roundtrip_ok, "pi CleanCic payload must round-trip re-check via the clean kernel");
        assert!(tamper_rejected, "a byte-tampered pi term must fail the kernel re-check");
        assert!(zero_lineage_rejected, "a zeroed lineage must fail closed");
        assert!(
            stuck_app_fails,
            "NO MASQUERADE: the bvar-headed stuck application MUST fail closed at LINK"
        );
        assert!(
            wrong_ctor_rejected,
            "NO MASQUERADE: the `sort` proof MUST be kernel-rejected against the `lam` goal"
        );
        assert!(
            reducing_const_rejected,
            "NO MASQUERADE: a delta-reducing const MUST be kernel-rejected"
        );
    }

    /// CONSUMER INDEPENDENCE: the PUBLIC `certify_is_whnf` mints and the PUBLIC
    /// `recheck_is_whnf` re-checks through a FRESHLY rebuilt spec + goal (not the
    /// mint's spec object). All five sealed public fixtures are accepted, and
    /// a byte-tampered term fails that independent re-check. Exercises the real
    /// public API + serialized-payload transport.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn all_sealed_whnf_fixtures_recheck_consumer_independently() {
        let mut pi_payload = None;
        for fixture in [&WHNF_SORT, &WHNF_LAM, &WHNF_PI, &WHNF_NEUTRAL_CONST, &WHNF_NEUTRAL_APP] {
            let evidence = certify_is_whnf(fixture)
                .unwrap_or_else(|| panic!("{} must discharge via the public API", fixture.label));
            let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
                panic!("expected CleanCic evidence");
            };
            assert!(
                recheck_is_whnf(fixture, &term, &context, &lineage),
                "{} must recheck via an independently rebuilt spec + kernel",
                fixture.label
            );
            if std::ptr::eq(fixture, &WHNF_PI) {
                pi_payload = Some((term, context, lineage));
            }
        }

        let (mut tampered, context, lineage) = pi_payload.expect("pi fixture visited");
        tampered[0] ^= 0xff;
        assert!(
            !recheck_is_whnf(&WHNF_PI, &tampered, &context, &lineage),
            "tampered pi term must fail the consumer-independent kernel re-check"
        );
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn nested_sorry_is_rejected_by_ambient_and_public_fixture_lanes() {
        static HOSTILE: WhnfFixture =
            WhnfFixture { label: "hostile nested sorry", kexpr_src: "KExpr.sort (@sorry Level)" };
        let (ambient_accepts_benign, ambient_rejects_hostile) = run_on_large_stack(|| {
            let spec = Specification::new().expect("spec should build");
            let benign = link_whnf(spec.env(), WHNF_SORT.kexpr_src)
                .is_some_and(|linked| kernel_checks_goal(spec.env(), &linked.proof, &linked.goal));
            let hostile = link_whnf(spec.env(), HOSTILE.kexpr_src)
                .is_none_or(|linked| !kernel_checks_goal(spec.env(), &linked.proof, &linked.goal));
            (benign, hostile)
        })
        .expect("nested-sorry audit thread");
        assert!(
            ambient_accepts_benign,
            "non-vacuity: the same ambient pipeline must accept an audited Sort WHNF"
        );
        assert!(
            ambient_rejects_hostile,
            "the ambient pipeline must reject nested sorry during linking or kernel checking"
        );
        assert!(
            certify_is_whnf(&HOSTILE).is_none(),
            "the public lane is sealed to audited fixtures and must reject caller-authored terms"
        );
        let context = crate::canonical_empty_context_bytes().expect("canonical context");
        assert!(!recheck_is_whnf(
            &HOSTILE,
            b"attacker term",
            &context,
            &trust_ir::ProofDigest::zero(),
        ));
    }

    // ════════════════════════════════════════════════════════════════════════
    // MIR-GROUNDED lane (Blocker-A): head derived from REAL clean-kernel MIR.
    // ════════════════════════════════════════════════════════════════════════

    /// Load a checked-in REAL clean-kernel MIR fixture. The `body.blocks` (the
    /// load-bearing MIR: statements, aggregates, from_kind call, terminators) are
    /// VERBATIM from a fork extraction (`RUSTC=<stage2 fork> RUSTC_BOOTSTRAP=1
    /// cargo rustc -p clean-kernel --lib -- -Ztrust-policy=advisory
    /// -Ztrust-dump=mir:<dir>`); ONLY the algorithm-irrelevant `return_ty` / local type
    /// annotations were stubbed to `Bool` to keep the fixture small (the analysis
    /// never reads them). Provenance + regen instructions: the fixture directory's
    /// `PROVENANCE.md`.
    fn load_mir_fixture(name: &str) -> VerifiableFunction {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures/checker_core_is_whnf_mir")
            .join(name);
        let json = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read MIR fixture {}: {e}", path.display()));
        serde_json::from_str(&json)
            .unwrap_or_else(|e| panic!("parse MIR fixture {}: {e}", path.display()))
    }

    // POSITIVE (WHNF-head) fixtures.
    const FX_PROP: &str = "clean_kernel.expr.Expr.prop.json"; // ExprKind::Sort (variant 2)
    const FX_SORT: &str = "clean_kernel.expr.Expr.sort.json"; // ExprKind::Sort (variant 2)
    const FX_ARROW: &str = "clean_kernel.expr.Expr.arrow.json"; // ExprKind::Pi (variant 6)
    // NEGATIVE (non-WHNF) fixtures — one real literal constructor per representative
    // non-WHNF `ExprKind` variant; EACH must fail closed at MIR extraction.
    const FX_BVAR: &str = "clean_kernel.expr.Expr.bvar.json"; // ExprKind::BVar  (variant 0)
    const FX_FVAR: &str = "clean_kernel.expr.Expr.fvar.json"; // ExprKind::FVar  (variant 1)
    const FX_CONST: &str = "clean_kernel.expr.Expr.const_str.json"; // ExprKind::Const (variant 3)
    const FX_APP: &str = "clean_kernel.expr.Expr.app.json"; // ExprKind::App   (variant 4)
    const FX_LET: &str = "clean_kernel.expr.Expr.let_named.json"; // ExprKind::Let  (variant 7)
    const FX_LIT: &str = "clean_kernel.expr.Expr.nat_lit.json"; // ExprKind::Lit   (variant 8)
    const FX_PROJ: &str = "clean_kernel.expr.Expr.proj.json"; // ExprKind::Proj  (variant 9)
    // NOTE: ExprKind::MData (variant 10) has NO fixture — `Expr::mdata` is not
    // monomorphized in the crate-lib MIR dump, so it cannot be fork-extracted
    // (same limitation as `Expr::lam` / `Expr::pi`). Its WHNF classification is
    // asserted at the MAPPING level (see EXTRACTION_SKIPPED + the classification
    // table below); the EXTRACTION-level witness is skipped VISIBLY, not hidden.
    // The `Expr { kind, meta }` constructor the head-trace flows through.
    const FX_FROM_KIND: &str = "clean_kernel.expr.Expr.from_kind.json";
    // The LITERAL reducer: `TypeChecker::whnf_impl`'s early-return identity match.
    const FX_WHNF_IMPL: &str = "clean_kernel.tc.whnf.whnf_impl.json";
    const FX_WHNF_CORE_INNER: &str = "clean_kernel.tc.whnf.whnf_core_inner.json";
    const FX_BETA_IOTA: &str = "clean_kernel.tc.whnf.beta_or_iota_step.json";
    const FX_WHNF_RECURSE: &str = "clean_kernel.tc.whnf_proj.whnf_recurse.json";
    const FX_DELTA_STEP: &str = "clean_kernel.tc.whnf_proj.unfold_definition_cached.json";
    const FX_PROJ_STEP: &str = "clean_kernel.tc.whnf_proj.reduce_proj_with_mode.json";
    const FX_PROJ_SHIM: &str = "clean_kernel.tc.whnf_proj.whnf_reduce_proj.json";

    /// Every real NON-WHNF constructor fixture, tagged with the `ExprKind` variant
    /// index it builds. Each MUST extract to `None` (fail closed) — the end-to-end
    /// no-masquerade witness over real fork-extracted MIR (complements the
    /// mapping-level exhaustive table below).
    const NON_WHNF_FIXTURES: &[(&str, usize)] = &[
        (FX_BVAR, 0),
        (FX_FVAR, 1),
        (FX_CONST, 3),
        (FX_APP, 4),
        (FX_LET, 7),
        (FX_LIT, 8),
        (FX_PROJ, 9),
    ];

    /// EXTRACTION-level SKIP register (gap DOCUMENTED, not hidden). These non-WHNF
    /// `ExprKind` variants have NO fork-extracted MIR fixture because the
    /// constructor is not monomorphized in the crate-lib MIR dump, so no real MIR
    /// can be extracted for them (same limitation as `Expr::lam` / `Expr::pi`).
    /// Their WHNF classification is STILL fully asserted at the MAPPING level (the
    /// `EXPRKIND_CLASSIFICATION` table + the exhaustive `0..=63` sweep both pin
    /// variant -> `None`, so completeness and fail-closed no-masquerade survive);
    /// ONLY the end-to-end real-MIR extraction witness is deferred. Each entry:
    /// `(constructor, variant, reason)`.
    const EXTRACTION_SKIPPED: &[(&str, usize, &str)] = &[(
        "Expr::mdata",
        10,
        "Expr::mdata not monomorphized in crate-lib dump; classification asserted \
         at mapping level; extraction-level check pending monomorphization",
    )];

    /// THE CRUX (fast, no spec build): the WHNF head is DERIVED FROM THE REAL
    /// fork-extracted clean-kernel MIR — the return-value construction, not a
    /// hand-supplied string. Positive heads classify; NON-WHNF-returning literal
    /// fns FAIL CLOSED at the MIR-extraction step (the no-masquerade witness); and
    /// `Expr::from_kind` is MIR-CONFIRMED kind-preserving (so the trace through it
    /// is grounded, not assumed).
    #[test]
    fn mir_head_extraction_grounds_on_real_clean_kernel_mir() {
        // from_kind is STRUCTURALLY kind-preserving (MIR-checked, not assumed).
        assert!(
            mir_from_kind_is_kind_preserving(&load_mir_fixture(FX_FROM_KIND)),
            "Expr::from_kind MIR must show it returns Expr{{ kind: <arg>, .. }} \
             (field 0 traces to the kind argument) — grounds the from_kind trace"
        );
        // A non-`from_kind` fn must NOT pass the kind-preservation check.
        assert!(
            !mir_from_kind_is_kind_preserving(&load_mir_fixture(FX_PROP)),
            "a fn that is not the Expr{{..}} constructor must not pass kind-preservation"
        );

        // POSITIVE: statically-WHNF-headed literal constructors classify from MIR.
        assert_eq!(
            extract_whnf_head_from_mir(&load_mir_fixture(FX_PROP)),
            Some(WhnfHead::Sort),
            "Expr::prop builds ExprKind::Sort (variant 2) -> Sort, read from real MIR"
        );
        assert_eq!(
            extract_whnf_head_from_mir(&load_mir_fixture(FX_SORT)),
            Some(WhnfHead::Sort),
            "Expr::sort builds ExprKind::Sort (variant 2) -> Sort, read from real MIR"
        );
        assert_eq!(
            extract_whnf_head_from_mir(&load_mir_fixture(FX_ARROW)),
            Some(WhnfHead::Pi),
            "Expr::arrow builds ExprKind::Pi (variant 6) -> Pi, read from real MIR"
        );

        // NEGATIVE CONTROL (LOAD-BEARING, MANDATORY): literal fns returning a
        // NON-WHNF head FAIL CLOSED at the MIR-extraction step — the witness that
        // the grounding is real, not rubber-stamped.
        assert_eq!(
            extract_whnf_head_from_mir(&load_mir_fixture(FX_APP)),
            None,
            "NO MASQUERADE: Expr::app builds ExprKind::App (variant 4, a stuck app) \
             -> MUST fail closed at MIR extraction (is_whnf has no app ctor)"
        );
        assert_eq!(
            extract_whnf_head_from_mir(&load_mir_fixture(FX_BVAR)),
            None,
            "NO MASQUERADE: Expr::bvar builds ExprKind::BVar (variant 0) \
             -> MUST fail closed at MIR extraction"
        );
    }

    /// FULL-`ExprKind` ROBUSTNESS (fast, no spec build): the variant->WHNF-head
    /// extraction is CORRECT AND COMPLETE against the REAL clean-kernel `ExprKind`.
    ///
    /// Two independent completeness proofs, plus the no-masquerade witness:
    ///
    /// 1. STRUCTURAL (mapping-level, covers real + FUTURE variants): the exhaustive
    ///    classification table below enumerates EVERY real `ExprKind` variant with
    ///    its index and expected head; `exprkind_variant_to_whnf_head` must agree
    ///    for each. Then, over the full index range `0..=63` (well past the ~25
    ///    real variants), the mapping returns `Some` ONLY for the three genuine
    ///    WHNF heads {2 Sort, 5 Lam, 6 Pi} and `None` for EVERYTHING else — so
    ///    every non-WHNF variant, and any variant a future kernel adds, FAILS
    ///    CLOSED. A false WHNF certificate is impossible unless the enum is
    ///    REORDERED so 2/5/6 no longer mean Sort/Lam/Pi — which the real
    ///    fork-extracted fixtures (proof 2) pin.
    ///
    /// 2. END-TO-END (real-MIR, `NON_WHNF_FIXTURES`): a real literal constructor
    ///    for each EXTRACTABLE representative non-WHNF variant (BVar/FVar/Const/App/
    ///    Let/Lit/Proj) extracts to `None` from its REAL fork-extracted MIR — the
    ///    load-bearing no-masquerade witness that real non-WHNF kernel fns do not
    ///    mint a WHNF head. The variant index the fn ACTUALLY builds (read from the
    ///    MIR aggregate) is also asserted, pinning index<->constructor. Variants
    ///    whose constructor is NOT monomorphized in the crate-lib MIR dump (MData;
    ///    see `EXTRACTION_SKIPPED`) cannot be fork-extracted, so their
    ///    extraction-level witness is DEFERRED — but their mapping-level
    ///    classification is still asserted here (proof 1), and the skip register is
    ///    checked to remain fail-closed. The gap is documented, never hidden.
    #[test]
    fn full_exprkind_classification_is_complete_and_fails_closed() {
        // ── The FULL clean-kernel ExprKind classification (recorded f9f8024d) ──
        // index -> (variant name, expected discharge head). Only Sort/Lam/Pi are
        // WHNF; every other variant is NON-WHNF -> None (fail closed).
        const EXPRKIND_CLASSIFICATION: &[(usize, &str, Option<WhnfHead>)] = &[
            (0, "BVar", None),
            (1, "FVar", None),
            (2, "Sort", Some(WhnfHead::Sort)),
            (3, "Const", None),
            (4, "App", None),
            (5, "Lam", Some(WhnfHead::Lam)),
            (6, "Pi", Some(WhnfHead::Pi)),
            (7, "Let", None),
            (8, "Lit", None),
            (9, "Proj", None),
            (10, "MData", None),
            (11, "SProp", None),
            (12, "Squash", None),
            (13, "CubicalInterval", None),
            (14, "CubicalI0", None),
            (15, "CubicalI1", None),
            (16, "CubicalPath", None),
            (17, "CubicalPathLam", None),
            (18, "CubicalPathApp", None),
            (19, "CubicalHComp", None),
            (20, "CubicalTransp", None),
            // Recorded f9f8024d ends the enum here (24 variants). Working-tree
            // 97950495 inserts CubicalCoe at 21 and pushes ZFC to 22/23/24; both
            // layouts map these tail variants to None, so the classification is
            // agnostic to the shift. Listing the f9f8024d tail:
            (21, "ZFCSet", None),
            (22, "ZFCMem", None),
            (23, "ZFCComprehension", None),
        ];

        // Proof 1a: the mapping agrees with the full classification table.
        for &(idx, name, expected) in EXPRKIND_CLASSIFICATION {
            assert_eq!(
                exprkind_variant_to_whnf_head(idx),
                expected,
                "ExprKind variant {idx} ({name}) classification mismatch"
            );
        }

        // Proof 1b: EXHAUSTIVE fail-closed over a range far beyond the real enum —
        // `Some` ONLY for {2,5,6}; every other index (real non-WHNF + future) is
        // None. This is the completeness+no-masquerade guarantee at the mapping.
        for idx in 0usize..=63 {
            let head = exprkind_variant_to_whnf_head(idx);
            match idx {
                2 => assert_eq!(head, Some(WhnfHead::Sort), "variant 2 must be Sort"),
                5 => assert_eq!(head, Some(WhnfHead::Lam), "variant 5 must be Lam"),
                6 => assert_eq!(head, Some(WhnfHead::Pi), "variant 6 must be Pi"),
                _ => assert_eq!(
                    head, None,
                    "NO MASQUERADE: non-WHNF variant index {idx} MUST fail closed (None)"
                ),
            }
        }

        // Proof 2: every REAL non-WHNF constructor fn fails closed at MIR
        // extraction, and builds exactly the variant we expect (index<->ctor pin).
        for &(fixture, expected_variant) in NON_WHNF_FIXTURES {
            let func = load_mir_fixture(fixture);
            assert_eq!(
                extract_whnf_head_from_mir(&func),
                None,
                "NO MASQUERADE: real non-WHNF constructor {fixture} (ExprKind variant \
                 {expected_variant}) MUST fail closed at MIR extraction"
            );
            // The mapping for the variant this fn actually builds is also None,
            // cross-checking that {2,5,6} are the ONLY discharge heads.
            assert_eq!(
                exprkind_variant_to_whnf_head(expected_variant),
                None,
                "variant {expected_variant} ({fixture}) must be non-WHNF in the mapping"
            );
        }

        // Proof 2 (SKIP register): variants whose constructor is not monomorphized
        // in the crate-lib MIR dump have no fork-extractable fixture, so their
        // EXTRACTION-level no-masquerade witness is DEFERRED. The gap is DOCUMENTED,
        // never hidden: for each skipped variant we STILL assert the mapping-level
        // classification is `None` (fail closed), so completeness + no-masquerade
        // survive at the mapping level — only the real-MIR extraction is pending.
        for &(ctor, variant, reason) in EXTRACTION_SKIPPED {
            assert_eq!(
                exprkind_variant_to_whnf_head(variant),
                None,
                "EXTRACTION_SKIPPED variant {variant} ({ctor}) must STILL be non-WHNF \
                 (fail closed) at the mapping level — {reason}"
            );
        }
    }

    /// THE MILESTONE (heavy, ONE spec build): the MIR-derived WHNF head DISCHARGES
    /// to a kernel-CHECKED `CleanCic`, the NON-WHNF-returning literal fns fail
    /// closed at certify, and the `prop` payload round-trips + rejects tamper — all
    /// on a single expensive `Specification::new()`.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn mir_grounded_discharge_closes_and_fails_closed() {
        let outcome = run_on_large_stack(|| {
            let spec = Specification::new().expect("spec should build");

            // POSITIVE: prop (Sort) and arrow (Pi) discharge to CleanCic from MIR.
            let prop = load_mir_fixture(FX_PROP);
            let arrow = load_mir_fixture(FX_ARROW);
            let prop_ev = certify_from_mir_with_spec(&spec, &prop);
            let arrow_ev = certify_from_mir_with_spec(&spec, &arrow);

            // NEGATIVE: app (App) and bvar (BVar) fail closed at certify.
            let app_none = certify_from_mir_with_spec(&spec, &load_mir_fixture(FX_APP)).is_none();
            let bvar_none = certify_from_mir_with_spec(&spec, &load_mir_fixture(FX_BVAR)).is_none();

            // Round-trip + tamper on the prop (Sort) certificate.
            let (roundtrip_ok, tamper_rejected) = match &prop_ev {
                Some(ProofEvidence::CleanCic { term, context, lineage, .. }) => {
                    let ok = recheck_from_mir_with_spec(&spec, &prop, term, context, lineage);
                    let mut tampered = term.clone();
                    tampered[0] ^= 0xff;
                    let rej =
                        !recheck_from_mir_with_spec(&spec, &prop, &tampered, context, lineage);
                    (ok, rej)
                }
                _ => (false, false),
            };

            (prop_ev, arrow_ev, app_none, bvar_none, roundtrip_ok, tamper_rejected)
        })
        .expect("discharge thread must not panic");

        let (prop_ev, arrow_ev, app_none, bvar_none, roundtrip_ok, tamper_rejected) = outcome;
        assert!(
            matches!(prop_ev, Some(ProofEvidence::CleanCic { .. })),
            "MIR-grounded Sort head (Expr::prop) must discharge to a kernel-checked CleanCic"
        );
        assert!(
            matches!(arrow_ev, Some(ProofEvidence::CleanCic { .. })),
            "MIR-grounded Pi head (Expr::arrow) must discharge to a kernel-checked CleanCic"
        );
        assert!(app_none, "NO MASQUERADE: Expr::app (non-WHNF) must fail closed at certify");
        assert!(bvar_none, "NO MASQUERADE: Expr::bvar (non-WHNF) must fail closed at certify");
        assert!(roundtrip_ok, "MIR-grounded prop CleanCic must round-trip re-check via the kernel");
        assert!(tamper_rejected, "a byte-tampered MIR-grounded prop term must fail the re-check");
    }

    /// CONSUMER INDEPENDENCE (heavy): the PUBLIC `certify_is_whnf_from_mir` mints
    /// and the PUBLIC `recheck_is_whnf_from_mir` re-checks through a FRESHLY
    /// rebuilt spec that RE-EXTRACTS the head from the MIR, and a tampered term
    /// fails that independent re-check.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn mir_grounded_public_api_is_consumer_independent() {
        let prop = load_mir_fixture(FX_PROP);
        let evidence = certify_is_whnf_from_mir(&prop)
            .expect("Expr::prop must discharge to CleanCic via the public MIR-grounded API");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            recheck_is_whnf_from_mir(&prop, &term, &context, &lineage),
            "serialized MIR-grounded CleanCic must re-check via an INDEPENDENTLY rebuilt spec + \
             re-extracted MIR head"
        );
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(
            !recheck_is_whnf_from_mir(&prop, &tampered, &context, &lineage),
            "tampered MIR-grounded term must fail the consumer-independent kernel re-check"
        );

        // Exact-fixture authority: the public structural analyzer is deliberately
        // advisory. These same-def-path bodies exploit its lack of CFG
        // reachability/unique-return-writer/callee-path checks, but neither mint
        // nor recheck may treat them as certificate authority.
        let mut unreachable_fake = prop.clone();
        let ctor_index = unreachable_fake
            .body
            .blocks
            .iter()
            .position(|bb| {
                matches!(
                    &bb.terminator,
                    Terminator::Call { func, dest, .. }
                        if final_segment(func) == "from_kind" && dest.local == RETURN_LOCAL
                )
            })
            .expect("prop fixture has from_kind call");
        let mut fake_block = unreachable_fake.body.blocks[ctor_index].clone();
        fake_block.id = BlockId(10_000);
        for stmt in &mut fake_block.stmts {
            if let Statement::Assign { place, .. } = stmt {
                place.local = 99;
            }
        }
        if let Terminator::Call { args, .. } = &mut fake_block.terminator {
            args[0] = Operand::Move(Place::local(99));
        }
        // The actual reachable constructor now returns App; the unreachable fake
        // still advertises Sort and is scanned first by the advisory recognizer.
        for stmt in &mut unreachable_fake.body.blocks[ctor_index].stmts {
            if let Statement::Assign {
                rvalue: Rvalue::Aggregate(AggregateKind::Adt { variant, .. }, _),
                ..
            } = stmt
            {
                *variant = 4;
            }
        }
        unreachable_fake.body.blocks.insert(0, fake_block);
        assert_eq!(
            extract_whnf_head_from_mir(&unreachable_fake),
            Some(WhnfHead::Sort),
            "non-vacuity: unreachable fake from_kind fools the advisory recognizer"
        );

        let mut alternate_writer = prop.clone();
        let mut writer = alternate_writer.body.blocks[ctor_index].stmts[0].clone();
        if let Statement::Assign { place, .. } = &mut writer {
            place.local = RETURN_LOCAL;
        }
        alternate_writer
            .body
            .blocks
            .iter_mut()
            .find(|bb| matches!(bb.terminator, Terminator::Return))
            .expect("prop fixture has return block")
            .stmts
            .push(writer);
        assert_eq!(extract_whnf_head_from_mir(&alternate_writer), Some(WhnfHead::Sort));

        let mut fake_callee = prop.clone();
        if let Terminator::Call { func, .. } = &mut fake_callee.body.blocks[ctor_index].terminator {
            *func = "attacker::from_kind".to_string();
        }
        assert_eq!(extract_whnf_head_from_mir(&fake_callee), Some(WhnfHead::Sort));

        for hostile in [&unreachable_fake, &alternate_writer, &fake_callee] {
            assert_eq!(hostile.def_path, prop.def_path, "test preserves def_path");
            assert!(
                certify_is_whnf_from_mir(hostile).is_none(),
                "same-def-path MIR drift must not mint"
            );
            assert!(
                !recheck_is_whnf_from_mir(hostile, &term, &context, &lineage),
                "same-def-path MIR drift must not recheck honest evidence"
            );
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // LITERAL-`whnf` identity-path brick — first property about the real REDUCER.
    // ════════════════════════════════════════════════════════════════════════

    // Input `ExprKind` variants of `whnf`'s early-return match (whnf.rs:145-165).
    const V_BVAR: usize = 0; // identity, but NO is_whnf.bvar ctor -> partial
    const V_FVAR: usize = 1; // CONDITIONAL arm -> NOT identity (negative control)
    const V_SORT: usize = 2; // identity -> is_whnf.sort   ✓ discharge
    const V_CONST: usize = 3; // falls through (recursive core) -> NOT identity
    const V_APP: usize = 4; // falls through (recursive core) -> NOT identity
    const V_LAM: usize = 5; // identity -> is_whnf.lam    ✓ discharge
    const V_PI: usize = 6; // identity -> is_whnf.pi     ✓ discharge
    const V_LET: usize = 7; // falls through (recursive core) -> NOT identity
    const V_LIT: usize = 8; // identity, but NO is_whnf.lit ctor -> partial
    const V_PROJ: usize = 9; // falls through (recursive core) -> NOT identity
    const V_MDATA: usize = 10; // falls through (recursive core) -> NOT identity

    /// Deep-copy the real `whnf_impl` MIR but CORRUPT the identity block so it
    /// clones a DIFFERENT local (`_1` = `self`) instead of the argument `_2` = `e`
    /// — i.e. "`return self.clone()`", a matched block that does NOT return the
    /// argument unchanged. Analogous to the byte-tamper controls: it exercises the
    /// analyzer's rejection of a non-identity clone WITHOUT hand-authoring the
    /// claim-carrying MIR (the whole body is the real extraction; only the clone's
    /// operand is flipped). The clone-of-`self` block must FAIL the identity check.
    fn whnf_impl_with_clone_of_self() -> VerifiableFunction {
        let mut func = load_mir_fixture(FX_WHNF_IMPL);
        let mut corrupted = false;
        for bb in &mut func.body.blocks {
            if let Terminator::Call { func: callee, args, dest, .. } = &mut bb.terminator {
                if dest.local == RETURN_LOCAL
                    && dest.projections.is_empty()
                    && final_segment(callee) == "clone"
                {
                    // Was `Copy(_2)` (= e); flip to `Copy(_1)` (= self).
                    args[0] = Operand::Copy(Place::local(1));
                    corrupted = true;
                }
            }
        }
        assert!(corrupted, "the real whnf_impl MIR must contain the `_0 = clone(e)` identity call");
        func
    }

    /// THE CRUX (fast, no spec build): the IDENTITY of the literal `whnf` reducer
    /// on its early-return heads is READ FROM the real fork-extracted MIR — the
    /// `SwitchInt(discriminant((*e).kind))` routing + the `return e.clone()`
    /// copy-trace-to-argument — not assumed. Positive heads confirm; the
    /// CONDITIONAL FVar arm, the App/… fall-through into the recursive core, a
    /// clone-of-`self` corruption, and a non-`whnf` fn ALL fail closed.
    #[test]
    fn whnf_identity_path_grounds_on_real_clean_kernel_mir() {
        let whnf = load_mir_fixture(FX_WHNF_IMPL);

        // The five unconditional early-return heads are the IDENTITY, read from MIR.
        for v in [V_BVAR, V_SORT, V_LAM, V_PI, V_LIT] {
            assert!(
                whnf_returns_arg_identity_for_variant(&whnf, v),
                "whnf's early-return match returns `e.clone()` unchanged for variant {v} \
                 (Sort/Pi/Lam/Lit/BVar) — read from the real MIR"
            );
        }

        // Sort/Lam/Pi discharge to a head; Lit/BVar prove identity but have NO
        // is_whnf ctor -> head is None (the honest partial result).
        assert_eq!(whnf_identity_path_head(&whnf, V_SORT), Some(WhnfHead::Sort));
        assert_eq!(whnf_identity_path_head(&whnf, V_LAM), Some(WhnfHead::Lam));
        assert_eq!(whnf_identity_path_head(&whnf, V_PI), Some(WhnfHead::Pi));
        for v in [V_BVAR, V_LIT] {
            assert!(
                whnf_returns_arg_identity_for_variant(&whnf, v),
                "identity IS proven from MIR for variant {v}"
            );
            assert_eq!(
                whnf_identity_path_head(&whnf, v),
                None,
                "variant {v} (Lit/BVar) proves identity but FAILS CLOSED at is_whnf discharge \
                 (no is_whnf.lit/bvar ctor) — the honest partial result"
            );
        }

        // NEGATIVE CONTROL (i): the FVar arm is CONDITIONAL (borrows self.ctx, only
        // sometimes returns e.clone()) — a matched block that does NOT return the
        // argument unchanged. It MUST fail the identity check.
        assert!(
            !whnf_returns_arg_identity_for_variant(&whnf, V_FVAR),
            "NO MASQUERADE: the CONDITIONAL FVar arm is not an unconditional identity \
             -> MUST fail the identity check"
        );
        assert_eq!(whnf_identity_path_head(&whnf, V_FVAR), None);

        // NEGATIVE CONTROL (ii): App (and every other `_ =>` head) FALLS THROUGH the
        // early return into the RECURSIVE core (no explicit SwitchInt target). It
        // MUST fail closed — the witness that this brick claims NOTHING about the
        // recursive whnf.
        for v in [V_APP, V_CONST, V_LET, V_PROJ, V_MDATA] {
            assert!(
                !whnf_returns_arg_identity_for_variant(&whnf, v),
                "NO MASQUERADE: variant {v} falls through whnf's early return into the \
                 recursive core -> MUST fail closed at the identity analyzer"
            );
            assert_eq!(whnf_identity_path_head(&whnf, v), None);
        }

        // NEGATIVE CONTROL (iii): a corrupted MIR whose matched block returns a
        // clone of `self` (`_1`), NOT the argument `e` (`_2`), MUST fail — the
        // clone source no longer traces to the discriminated argument.
        let self_clone = whnf_impl_with_clone_of_self();
        for v in [V_SORT, V_LAM, V_PI, V_LIT, V_BVAR] {
            assert!(
                !whnf_returns_arg_identity_for_variant(&self_clone, v),
                "NO MASQUERADE: a block returning clone(self) is NOT the identity on e \
                 -> variant {v} must fail the identity check"
            );
        }

        // CROSS-LANE fail-closed: a clean-kernel CONSTRUCTOR fn does not head-match
        // an argument's ExprKind at all, so it has no whnf identity path.
        let prop = load_mir_fixture(FX_PROP);
        for v in [V_SORT, V_LAM, V_PI] {
            assert!(
                !whnf_returns_arg_identity_for_variant(&prop, v),
                "a constructor fn (Expr::prop) has no discriminant-on-arg SwitchInt \
                 -> no whnf identity path (variant {v})"
            );
        }
    }

    /// THE MILESTONE (heavy, ONE spec build): the MIR-confirmed identity heads
    /// Sort/Lam/Pi DISCHARGE `is_whnf` on the value the literal `whnf` returns, and
    /// the honest partials + the negative controls all fail closed — the FIRST
    /// kernel-checked property about the literal REDUCER (not a constructor).
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_identity_discharge_closes_and_fails_closed() {
        let outcome = run_on_large_stack(|| {
            let whnf = load_mir_fixture(FX_WHNF_IMPL);
            let spec = Specification::new().expect("spec should build");

            // POSITIVE: Sort/Lam/Pi identity heads discharge to CleanCic.
            let minted: Vec<_> = [V_SORT, V_LAM, V_PI]
                .into_iter()
                .map(|v| certify_whnf_identity_with_spec(&spec, &whnf, v))
                .collect();

            // HONEST PARTIAL: Lit/BVar prove identity but fail closed at discharge.
            let lit_none = certify_whnf_identity_with_spec(&spec, &whnf, V_LIT).is_none();
            let bvar_none = certify_whnf_identity_with_spec(&spec, &whnf, V_BVAR).is_none();

            // NEGATIVE CONTROLS: FVar (conditional) and App (fall-through) fail.
            let fvar_none = certify_whnf_identity_with_spec(&spec, &whnf, V_FVAR).is_none();
            let app_none = certify_whnf_identity_with_spec(&spec, &whnf, V_APP).is_none();

            // Round-trip + tamper on the Pi certificate.
            let (roundtrip_ok, tamper_rejected) = match &minted[2] {
                Some(ProofEvidence::CleanCic { term, context, lineage, .. }) => {
                    let ok =
                        recheck_whnf_identity_with_spec(&spec, &whnf, V_PI, term, context, lineage);
                    let mut tampered = term.clone();
                    tampered[0] ^= 0xff;
                    let rej = !recheck_whnf_identity_with_spec(
                        &spec, &whnf, V_PI, &tampered, context, lineage,
                    );
                    (ok, rej)
                }
                _ => (false, false),
            };

            (minted, lit_none, bvar_none, fvar_none, app_none, roundtrip_ok, tamper_rejected)
        })
        .expect("discharge thread must not panic");

        let (minted, lit_none, bvar_none, fvar_none, app_none, roundtrip_ok, tamper_rejected) =
            outcome;
        assert_eq!(minted.len(), 3);
        for ev in &minted {
            assert!(
                matches!(ev, Some(ProofEvidence::CleanCic { .. })),
                "each MIR-confirmed whnf identity head (Sort/Lam/Pi) must discharge to CleanCic"
            );
        }
        assert!(
            lit_none,
            "HONEST PARTIAL: Lit proves identity but fails closed at is_whnf discharge"
        );
        assert!(
            bvar_none,
            "HONEST PARTIAL: BVar proves identity but fails closed at is_whnf discharge"
        );
        assert!(fvar_none, "NO MASQUERADE: the conditional FVar arm must fail closed at certify");
        assert!(app_none, "NO MASQUERADE: the App fall-through must fail closed at certify");
        assert!(
            roundtrip_ok,
            "the whnf-identity Pi CleanCic must round-trip re-check via the kernel"
        );
        assert!(tamper_rejected, "a byte-tampered whnf-identity Pi term must fail the re-check");
    }

    /// CONSUMER INDEPENDENCE (heavy): the PUBLIC `certify_whnf_identity_from_mir`
    /// mints and `recheck_whnf_identity_from_mir` re-checks through a FRESHLY
    /// rebuilt spec that RE-CONFIRMS the identity from the MIR; a tampered term
    /// fails that independent re-check.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn whnf_identity_public_api_is_consumer_independent() {
        let whnf = load_mir_fixture(FX_WHNF_IMPL);
        let evidence = certify_whnf_identity_from_mir(&whnf, V_PI)
            .expect("whnf Pi identity head must discharge via the public API");
        let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
            panic!("expected CleanCic evidence");
        };
        assert!(
            recheck_whnf_identity_from_mir(&whnf, V_PI, &term, &context, &lineage),
            "serialized whnf-identity CleanCic must re-check via an INDEPENDENTLY rebuilt spec + \
             re-confirmed MIR identity"
        );
        let mut tampered = term.clone();
        tampered[0] ^= 0xff;
        assert!(
            !recheck_whnf_identity_from_mir(&whnf, V_PI, &tampered, &context, &lineage),
            "tampered whnf-identity term must fail the consumer-independent kernel re-check"
        );
        // A non-identity variant (App, fall-through) must NOT mint via the public API.
        assert!(
            certify_whnf_identity_from_mir(&whnf, V_APP).is_none(),
            "NO MASQUERADE: the App fall-through must fail closed via the public API"
        );

        // A fake unreachable switch can fool the advisory switch scanner while
        // the real entry switch routes Pi to the recursive fallback. Exact
        // embedded-fixture sealing must reject this same-def-path body.
        let mut unreachable_switch = whnf.clone();
        let entry_index = unreachable_switch
            .body
            .blocks
            .iter()
            .position(|bb| bb.id == BlockId(0))
            .expect("whnf fixture has entry block");
        let fake_switch = BasicBlock {
            id: BlockId(10_000),
            stmts: Vec::new(),
            terminator: unreachable_switch.body.blocks[entry_index].terminator.clone(),
        };
        if let Terminator::SwitchInt { targets, .. } =
            &mut unreachable_switch.body.blocks[entry_index].terminator
        {
            targets.clear();
        }
        unreachable_switch.body.blocks.insert(0, fake_switch);
        assert!(
            whnf_returns_arg_identity_for_variant(&unreachable_switch, V_PI),
            "non-vacuity: unreachable fake switch fools the advisory recognizer"
        );
        assert_eq!(unreachable_switch.def_path, whnf.def_path);
        assert!(certify_whnf_identity_from_mir(&unreachable_switch, V_PI).is_none());
        assert!(!recheck_whnf_identity_from_mir(
            &unreachable_switch,
            V_PI,
            &term,
            &context,
            &lineage,
        ));
    }

    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn all_three_recheck_families_reject_relineaged_sorry_beta_and_context_bytes() {
        let (fixture_case, mir_case, identity_case) = run_on_large_stack(|| {
            let spec = Specification::new().expect("spec should build");
            let env = spec.env();
            let context = crate::canonical_empty_context_bytes().expect("canonical context");

            let adversarial_terms = |linked: &LinkedWhnf| {
                let level = clean_kernel::TypeChecker::new(env)
                    .infer_sort(&linked.goal)
                    .expect("goal sort");
                let sorry = Expr::app(
                    Expr::const_(Name::from_string("sorry"), vec![level]),
                    linked.goal.clone(),
                );
                assert!(kernel_checks_goal(env, &sorry, &linked.goal));
                let beta = Expr::app(
                    Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        linked.goal.clone(),
                        Expr::bvar(0),
                    ),
                    linked.proof.clone(),
                );
                assert!(kernel_checks_goal(env, &beta, &linked.goal));
                (
                    serialize_term(&sorry).expect("serialize sorry"),
                    serialize_term(&beta).expect("serialize beta"),
                    serialize_term(&linked.proof).expect("serialize canonical proof"),
                )
            };

            let fixture_linked = link_whnf(env, WHNF_PI.kexpr_src).expect("fixture links");
            let (sorry, beta, canonical) = adversarial_terms(&fixture_linked);
            let fixture_case = (
                !recheck_with_spec(
                    &spec,
                    &WHNF_PI,
                    &sorry,
                    &context,
                    &lineage_digest(&WHNF_PI, fixture_linked.head, &sorry, &context),
                ),
                !recheck_with_spec(
                    &spec,
                    &WHNF_PI,
                    &beta,
                    &context,
                    &lineage_digest(&WHNF_PI, fixture_linked.head, &beta, &context),
                ),
                canonical,
                context.clone(),
            );

            let prop = load_mir_fixture(FX_PROP);
            let mir_head = extract_whnf_head_from_mir(&prop).expect("MIR head");
            let mir_linked = link_whnf(env, canonical_kexpr_src(mir_head)).expect("MIR links");
            let (sorry, beta, canonical) = adversarial_terms(&mir_linked);
            let mir_case = (
                prop.clone(),
                !recheck_from_mir_with_spec(
                    &spec,
                    &prop,
                    &sorry,
                    &context,
                    &mir_lineage_digest(&prop, mir_head, &sorry, &context)
                        .expect("sealed MIR lineage"),
                ),
                !recheck_from_mir_with_spec(
                    &spec,
                    &prop,
                    &beta,
                    &context,
                    &mir_lineage_digest(&prop, mir_head, &beta, &context)
                        .expect("sealed MIR lineage"),
                ),
                canonical,
                context.clone(),
            );

            let whnf = load_mir_fixture(FX_WHNF_IMPL);
            let identity_head = whnf_identity_path_head(&whnf, V_PI).expect("identity head");
            let identity_linked =
                link_whnf(env, canonical_kexpr_src(identity_head)).expect("identity links");
            let (sorry, beta, canonical) = adversarial_terms(&identity_linked);
            let identity_case = (
                whnf.clone(),
                !recheck_whnf_identity_with_spec(
                    &spec,
                    &whnf,
                    V_PI,
                    &sorry,
                    &context,
                    &whnf_identity_lineage_digest(&whnf, V_PI, identity_head, &sorry, &context)
                        .expect("sealed whnf lineage"),
                ),
                !recheck_whnf_identity_with_spec(
                    &spec,
                    &whnf,
                    V_PI,
                    &beta,
                    &context,
                    &whnf_identity_lineage_digest(&whnf, V_PI, identity_head, &beta, &context)
                        .expect("sealed whnf lineage"),
                ),
                canonical,
                context,
            );
            (fixture_case, mir_case, identity_case)
        })
        .expect("adversarial audit thread");

        assert!(fixture_case.0 && fixture_case.1);
        let mut bad_context = fixture_case.3;
        bad_context.push(0);
        let relined = lineage_digest(&WHNF_PI, WhnfHead::Pi, &fixture_case.2, &bad_context);
        assert!(!recheck_is_whnf(&WHNF_PI, &fixture_case.2, &bad_context, &relined,));

        assert!(mir_case.1 && mir_case.2);
        let mut bad_context = mir_case.4;
        bad_context.push(0);
        let head = extract_whnf_head_from_mir(&mir_case.0).expect("MIR head");
        let relined = mir_lineage_digest(&mir_case.0, head, &mir_case.3, &bad_context)
            .expect("sealed MIR lineage");
        assert!(!recheck_is_whnf_from_mir(&mir_case.0, &mir_case.3, &bad_context, &relined,));

        assert!(identity_case.1 && identity_case.2);
        let mut bad_context = identity_case.4;
        bad_context.push(0);
        let head = whnf_identity_path_head(&identity_case.0, V_PI).expect("identity head");
        let relined = whnf_identity_lineage_digest(
            &identity_case.0,
            V_PI,
            head,
            &identity_case.3,
            &bad_context,
        )
        .expect("sealed whnf lineage");
        assert!(!recheck_whnf_identity_from_mir(
            &identity_case.0,
            V_PI,
            &identity_case.3,
            &bad_context,
            &relined,
        ));
    }

    /// NEUTRAL FRAGMENT (const head): the checker-core structural postcondition
    /// `is_whnf(_0)` is kernel-discharged for a NEUTRAL const head — the fragment the
    /// sort/lam/pi arms failed closed on before `const_whnf` was made reducible.
    /// `WHNF_NEUTRAL_CONST` (an opaque const absent from `the_red_env`) LINKs to
    /// `is_whnf.neutral (KExpr.const n us) (is_neutral.const n us (Eq.refl ..none..))`
    /// and DISCHARGES to a `CleanCic`: the clean kernel accepts the derived term by
    /// UNFOLDING the reducible `const_whnf` and reducing `delta_reduct (red_def
    /// the_red_env) (KExpr.const n us)` to `none`. SOUNDNESS: a const that DELTA-REDUCES
    /// makes that reduct non-`none`, so the kernel REJECTS the proof — the `delta_reduct
    /// = none` computation is the discriminating gate. Round-trip + tamper hold, and the
    /// wrong-ctor / stuck-app / reducing-const no-masquerade controls still fire.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn neutral_const_is_whnf_discharges_and_fails_closed() {
        let outcome = run_on_large_stack(|| {
            let spec = Specification::new().expect("spec should build");
            let env = spec.env();

            // LINK classifies the opaque const head as NeutralConst.
            let linked = link_whnf(env, WHNF_NEUTRAL_CONST.kexpr_src)
                .expect("opaque const must LINK to a neutral WHNF head");
            assert_eq!(linked.head, WhnfHead::NeutralConst, "const head classification");

            // DISCHARGE to a CleanCic through the standard mint (whose gate INCLUDES the
            // stuck-app, wrong-ctor, and reducing-const no-masquerade controls).
            let ev = certify_with_spec(&spec, &WHNF_NEUTRAL_CONST)
                .expect("neutral const must discharge to CleanCic");
            let ProofEvidence::CleanCic { term, context, lineage, kernel_recheck } = ev else {
                panic!("expected CleanCic evidence for neutral const");
            };

            let roundtrip_ok =
                recheck_with_spec(&spec, &WHNF_NEUTRAL_CONST, &term, &context, &lineage);
            let mut tampered = term.clone();
            tampered[0] ^= 0xff;
            let tamper_rejected =
                !recheck_with_spec(&spec, &WHNF_NEUTRAL_CONST, &tampered, &context, &lineage);
            let stuck_app_fails = stuck_app_link_fails_closed(env);
            let wrong_ctor_rejected = wrong_ctor_kernel_rejected(env);

            // LOAD-BEARING DELTA CONTROL. This deliberately uses a private,
            // ad-hoc fixture: its const occurs in `the_red_env`, so LINK must
            // classify it as a NeutralConst candidate while the kernel and the
            // internal mint both reject its false `const_whnf` witness.
            let reducing_fixture = WhnfFixture {
                label: "delta-reducing const must fail closed",
                kexpr_src: DELTA_REDUCING_CONST_KEXPR_SRC,
            };
            let reducing_linked = link_whnf(env, reducing_fixture.kexpr_src)
                .expect("the reducing const must LINK as a candidate");
            let reducing_linked_as_const = reducing_linked.head == WhnfHead::NeutralConst;
            let reducing_kernel_rejected =
                !kernel_checks_goal(env, &reducing_linked.proof, &reducing_linked.goal);
            let reducing_mint_rejected = certify_with_spec(&spec, &reducing_fixture).is_none();

            (
                kernel_recheck.is_none(),
                !term.is_empty() && !context.is_empty(),
                roundtrip_ok,
                tamper_rejected,
                stuck_app_fails,
                wrong_ctor_rejected,
                reducing_linked_as_const,
                reducing_kernel_rejected,
                reducing_mint_rejected,
            )
        })
        .expect("neutral-const discharge test must complete");

        let (
            rk_none,
            nonempty,
            roundtrip_ok,
            tamper_rejected,
            stuck_app_fails,
            wrong_ctor_rejected,
            reducing_linked_as_const,
            reducing_kernel_rejected,
            reducing_mint_rejected,
        ) = outcome;
        assert!(rk_none, "consumer-side kernel_recheck stays None until recheck");
        assert!(nonempty, "term + context must be non-empty");
        assert!(roundtrip_ok, "neutral-const certificate must round-trip re-check");
        assert!(tamper_rejected, "tampered neutral-const term must fail the re-check");
        assert!(stuck_app_fails, "stuck-app link must still fail closed");
        assert!(wrong_ctor_rejected, "wrong-ctor must still be kernel-rejected");
        assert!(
            reducing_linked_as_const,
            "the delta-reducing control must LINK as NeutralConst before discharge"
        );
        assert!(
            reducing_kernel_rejected,
            "the kernel must reject const_whnf for a delta-reducing const"
        );
        assert!(
            reducing_mint_rejected,
            "certify_with_spec must fail closed for the private reducing-const fixture"
        );
    }

    /// NEUTRAL APPLICATION SPINE: a stuck two-deep application `(c s0) s0` of an opaque
    /// constant — exactly the shape the real whnf reducer returns for stuck
    /// applications — LINKs via the RECURSIVE `is_neutral.app` spine proof and
    /// DISCHARGES `is_whnf(_0)` to a kernel-checked `CleanCic` (two `is_neutral.app`
    /// nodes over `is_neutral.const n us (Eq.refl ..none..)`, kernel unfolds the
    /// reducible `const_whnf`). DISCRIMINATION: a LAM-headed application — a genuine
    /// beta REDEX, not a normal form — must FAIL CLOSED at the link (the spine walk
    /// refuses the lam head), and the bvar-headed STUCK_APP control still fails closed.
    #[test]
    #[ignore = "multi-minute clean-verify kernel-recheck derivation (each test builds + FULLY kernel-type-checks `Specification::new()` and re-derives/kernel-checks the proof term): moved to the opt-in SLOW LANE so `targo test --workspace --lib` (the `quick` domination gate) stays fast. Run this lane via `scripts/trust_kernel_derivation_lane.sh` (the release-built kernel-derivation slow lane, which times each test and fails on any non-closure; a debug `cargo test -- --ignored` is multiples slower). The cheap `checker_core_*_fn` function-grounding lanes and every non-`checker_core` correctness test stay inline."]
    fn neutral_app_spine_is_whnf_discharges_and_fails_closed() {
        let outcome = run_on_large_stack(|| {
            let spec = Specification::new().expect("spec should build");
            let env = spec.env();

            // LINK classifies the stuck const-headed spine as NeutralApp.
            let linked = link_whnf(env, WHNF_NEUTRAL_APP.kexpr_src)
                .expect("stuck const-headed app spine must LINK as neutral");
            assert_eq!(linked.head, WhnfHead::NeutralApp, "app-spine head classification");

            // DISCHARGE through the standard mint (gated on all no-masquerade controls).
            let ev = certify_with_spec(&spec, &WHNF_NEUTRAL_APP)
                .expect("neutral app spine must discharge to CleanCic");
            let ProofEvidence::CleanCic { term, context, lineage, .. } = ev else {
                panic!("expected CleanCic evidence for neutral app spine");
            };
            let roundtrip_ok =
                recheck_with_spec(&spec, &WHNF_NEUTRAL_APP, &term, &context, &lineage);
            let mut tampered = term.clone();
            tampered[0] ^= 0xff;
            let tamper_rejected =
                !recheck_with_spec(&spec, &WHNF_NEUTRAL_APP, &tampered, &context, &lineage);

            // DISCRIMINATION: beta redex + bvar-headed stuck app both fail closed.
            let redex_fails = redex_app_link_fails_closed(env);
            let stuck_app_fails = stuck_app_link_fails_closed(env);

            (roundtrip_ok, tamper_rejected, redex_fails, stuck_app_fails)
        })
        .expect("neutral-app-spine discharge test must complete");

        let (roundtrip_ok, tamper_rejected, redex_fails, stuck_app_fails) = outcome;
        assert!(roundtrip_ok, "neutral-app-spine certificate must round-trip re-check");
        assert!(tamper_rejected, "tampered spine term must fail the re-check");
        assert!(redex_fails, "a lam-headed beta REDEX must NOT link as neutral");
        assert!(stuck_app_fails, "the bvar-headed stuck app must still fail closed");
    }
    /// δ-INTERIOR on the real `unfold_definition_cached` MIR: the env unfold
    /// fires ONLY on a cache-missing Const-kind expr; hit/non-Const/None paths
    /// never unfold or insert; Some inserts.
    #[test]
    fn delta_interior_holds_on_real_mir() {
        let step = load_mir_fixture(FX_DELTA_STEP);
        delta_step_landmarks(&step).expect("the real delta-step MIR must yield landmarks");
        assert!(
            unfold_definition_cached_delta_interior(&step),
            "the delta-interior partition must hold"
        );
    }

    /// NO MASQUERADE (δ interior): renaming the env unfold breaks landmark
    /// derivation; redirecting the non-Const arm onto the Const arm makes the
    /// non-Const path reach the unfold — both fail closed.
    #[test]
    fn delta_interior_tamper_fails_closed() {
        let mut renamed = load_mir_fixture(FX_DELTA_STEP);
        for bb in &mut renamed.body.blocks {
            if let Terminator::Opaque { kind, .. } = &mut bb.terminator {
                *kind = kind.replace("::unfold_definition::", "::not_delta::");
            }
        }
        assert!(
            !unfold_definition_cached_delta_interior(&renamed),
            "a renamed env unfold must fail the witness closed"
        );

        let mut redirected = load_mir_fixture(FX_DELTA_STEP);
        let lm = delta_step_landmarks(&redirected).expect("landmarks");
        let (const_arm, nonconst_arm) = (lm.const_arm, lm.nonconst_arm);
        for bb in &mut redirected.body.blocks {
            if let Terminator::SwitchInt { targets, otherwise, .. } = &mut bb.terminator
                && targets.len() == 1
                && targets[0].0 == 3
                && targets[0].1 == const_arm
                && *otherwise == nonconst_arm
            {
                *otherwise = const_arm; // non-Const now unfolds too
            }
        }
        assert!(
            !unfold_definition_cached_delta_interior(&redirected),
            "routing non-Const into the unfold must fail the interior check"
        );
    }

    /// ι-PROJ INTERIOR on the real `reduce_proj_with_mode` MIR: field
    /// extraction fires exactly on a constructor-headed struct with the field
    /// present; every complement is the honest stuck-proj rebuild.
    #[test]
    fn proj_interior_holds_on_real_mir() {
        let step = load_mir_fixture(FX_PROJ_STEP);
        proj_step_landmarks(&step).expect("the real proj-step MIR must yield landmarks");
        assert!(
            reduce_proj_fires_only_on_constructor(&step),
            "the proj-interior partition must hold"
        );
    }

    /// NO MASQUERADE (ι-proj interior): renaming the constructor lookup breaks
    /// landmark derivation; redirecting the stuck complement onto the
    /// Const-head arm pollutes the exclusions — both fail closed.
    #[test]
    fn proj_interior_tamper_fails_closed() {
        let mut renamed = load_mir_fixture(FX_PROJ_STEP);
        for bb in &mut renamed.body.blocks {
            if let Terminator::Opaque { kind, .. } = &mut bb.terminator {
                *kind = kind.replace("::get_constructor::", "::not_ctor::");
            }
        }
        assert!(
            !reduce_proj_fires_only_on_constructor(&renamed),
            "a renamed constructor lookup must fail the witness closed"
        );

        let mut redirected = load_mir_fixture(FX_PROJ_STEP);
        let lm = proj_step_landmarks(&redirected).expect("landmarks");
        let const_head = lm.const_head_arm;
        // Redirect the head switch's otherwise (stuck) onto the Const arm.
        let mut done = false;
        for bb in &mut redirected.body.blocks {
            if let Terminator::SwitchInt { targets, otherwise, .. } = &mut bb.terminator
                && targets.len() == 1
                && targets[0].0 == 3
                && targets[0].1 == const_head
            {
                *otherwise = const_head;
                done = true;
            }
        }
        assert!(done, "head switch located");
        assert!(
            !reduce_proj_fires_only_on_constructor(&redirected),
            "routing the stuck complement into the ctor lookup must fail closed"
        );
    }

    /// SPINE LINK: whnf_reduce_proj is a pure delegation shim to
    /// reduce_proj_with_mode (and a tampered callee fails closed).
    #[test]
    fn whnf_reduce_proj_shim_links_the_spine() {
        let shim = load_mir_fixture(FX_PROJ_SHIM);
        assert!(whnf_reduce_proj_delegates(&shim), "the shim must delegate");
        let mut renamed = shim.clone();
        for bb in &mut renamed.body.blocks {
            if let Terminator::Opaque { kind, .. } = &mut bb.terminator {
                *kind = kind.replace("::reduce_proj_with_mode::", "::elsewhere::");
            }
        }
        assert!(!whnf_reduce_proj_delegates(&renamed), "a renamed callee fails closed");
    }

    /// MODE FIDELITY on the real `whnf_recurse` MIR: the exhaustive WhnfMode
    /// switch routes Full/NoDelta/Transparency to disjoint reducers, and the
    /// δ-DISCIPLINE negative holds (NoDelta never reaches whnf_impl).
    #[test]
    fn whnf_recurse_mode_fidelity_holds_on_real_mir() {
        let rec = load_mir_fixture(FX_WHNF_RECURSE);
        let lm = recurse_mode_landmarks(&rec)
            .expect("the real whnf_recurse MIR must yield mode landmarks");
        assert_ne!(lm.full_arm, lm.nodelta_arm, "mode arms are distinct");
        assert!(whnf_recurse_routes_by_mode(&rec), "the mode-fidelity routing partition must hold");
    }

    /// NO MASQUERADE (mode fidelity): tampering fails closed. (a) Renaming
    /// whnf_impl breaks landmark derivation. (b) Redirecting the NoDelta arms
    /// onto the Full arm violates the δ-discipline negative.
    #[test]
    fn whnf_recurse_mode_fidelity_tamper_fails_closed() {
        let mut renamed = load_mir_fixture(FX_WHNF_RECURSE);
        for bb in &mut renamed.body.blocks {
            if let Terminator::Opaque { kind, .. } = &mut bb.terminator {
                *kind = kind.replace("::whnf_impl::", "::not_impl::");
            }
        }
        assert!(
            !whnf_recurse_routes_by_mode(&renamed),
            "a renamed whnf_impl callee must fail the witness closed"
        );

        let mut redirected = load_mir_fixture(FX_WHNF_RECURSE);
        let lm = recurse_mode_landmarks(&redirected).expect("landmarks");
        let full = lm.full_arm;
        for bb in &mut redirected.body.blocks {
            if bb.id == lm.mode_switch
                && let Terminator::SwitchInt { targets, .. } = &mut bb.terminator
            {
                for (v, t) in targets.iter_mut() {
                    if *v == 1 || *v == 2 {
                        *t = full; // NoDelta now routes into the δ-enabled path
                    }
                }
            }
        }
        assert!(
            !whnf_recurse_routes_by_mode(&redirected),
            "routing NoDelta into whnf_impl must fail the delta-discipline check"
        );
    }

    /// REDEX-GATED CONTRACTION on the real `beta_or_iota_step` MIR: the
    /// is_lam test exclusively partitions β (instantiate_rev) vs the five
    /// ι-family reducers.
    #[test]
    fn beta_or_iota_step_redex_gating_holds_on_real_mir() {
        let step = load_mir_fixture(FX_BETA_IOTA);
        let lm = beta_iota_landmarks(&step)
            .expect("the real beta_or_iota_step MIR must yield landmarks");
        assert_ne!(lm.beta_arm, lm.iota_arm, "the is_lam partition arms are distinct");
        assert!(
            beta_or_iota_step_gates_contraction_by_redex(&step),
            "the redex-gated exclusive contraction partition must hold"
        );
    }

    /// NO MASQUERADE (redex gating): tampering fails closed. (a) Renaming the
    /// β substitution callee breaks the landmark derivation -> witness false.
    /// (b) Redirecting the is_lam FALSE arm to the TRUE arm makes the ι path
    /// reach instantiate_rev -> the exclusion check fails.
    #[test]
    fn beta_or_iota_step_redex_gating_tamper_fails_closed() {
        let mut renamed = load_mir_fixture(FX_BETA_IOTA);
        for bb in &mut renamed.body.blocks {
            if let Terminator::Opaque { kind, .. } = &mut bb.terminator {
                *kind = kind.replace("::instantiate_rev::", "::not_subst::");
            }
        }
        assert!(
            !beta_or_iota_step_gates_contraction_by_redex(&renamed),
            "a renamed substitution callee must fail the witness closed"
        );

        let mut redirected = load_mir_fixture(FX_BETA_IOTA);
        let lm = beta_iota_landmarks(&redirected).expect("landmarks");
        let is_lam = unique_opaque_call_block(&redirected, "::is_lam::").expect("is_lam");
        let is_lam_bb = block_by_id(&redirected, is_lam).expect("is_lam bb");
        let Terminator::Opaque { targets, .. } = &is_lam_bb.terminator else {
            panic!("is_lam is opaque");
        };
        let switch_id = *targets.first().expect("switch target");
        let beta_arm = lm.beta_arm;
        for bb in &mut redirected.body.blocks {
            if bb.id == switch_id
                && let Terminator::SwitchInt { targets, .. } = &mut bb.terminator
            {
                for (v, t) in targets.iter_mut() {
                    if *v == 0 {
                        *t = beta_arm; // ι arm now routes into the β arm
                    }
                }
            }
        }
        assert!(
            !beta_or_iota_step_gates_contraction_by_redex(&redirected),
            "routing the ι arm into the β arm must fail the exclusion check"
        );
    }

    /// STEP ROUTING on the real `whnf_core_inner` MIR: the per-iteration
    /// partition is exactly the measured one — δ only from Const, β/ι (+
    /// accelerators + Glue elim) only from App, ι-proj only from Proj, path-β
    /// only from PathApp, each kan step only from its own cubical kind, and
    /// FVar/Let/MData call NO step.
    #[test]
    fn whnf_core_inner_step_routing_holds_on_real_mir() {
        let core = load_mir_fixture(FX_WHNF_CORE_INNER);
        let lm = core_routing_landmarks(&core)
            .expect("the real whnf_core_inner MIR must yield routing landmarks");
        assert_eq!(
            lm.arms.iter().map(|(v, _)| *v).collect::<Vec<_>>(),
            vec![1, 3, 4, 7, 9, 10, 18, 19, 20, 21],
            "root kind-switch arms = FVar/Const/App/Let/Proj/MData + cubical kinds"
        );
        assert!(
            whnf_core_inner_routes_steps_by_kind(&core),
            "the exact step-routing partition must hold on the real MIR"
        );
    }

    /// NO MASQUERADE (step routing): tampering fails closed. (a) Renaming the
    /// δ callee breaks landmark derivation -> witness false. (b) Redirecting
    /// the Const arm onto the App arm's target makes Const reach β/ι -> the
    /// exactness check fails.
    #[test]
    fn whnf_core_inner_step_routing_tamper_fails_closed() {
        let mut renamed = load_mir_fixture(FX_WHNF_CORE_INNER);
        for bb in &mut renamed.body.blocks {
            if let Terminator::Opaque { kind, .. } = &mut bb.terminator {
                *kind = kind.replace("::unfold_definition_cached::", "::not_delta::");
            }
        }
        assert!(
            !whnf_core_inner_routes_steps_by_kind(&renamed),
            "a renamed delta callee must fail the witness closed"
        );

        let mut redirected = load_mir_fixture(FX_WHNF_CORE_INNER);
        let lm = core_routing_landmarks(&redirected).expect("landmarks");
        let app_target = lm.arms.iter().find(|(v, _)| *v == 4).expect("App arm").1;
        for bb in &mut redirected.body.blocks {
            if bb.id == lm.head
                && let Terminator::SwitchInt { targets, .. } = &mut bb.terminator
            {
                for (v, t) in targets.iter_mut() {
                    if *v == 3 {
                        *t = app_target;
                    }
                }
            }
        }
        assert!(
            !whnf_core_inner_routes_steps_by_kind(&redirected),
            "redirecting Const onto the App arm must fail the exact partition"
        );
    }

    /// DISPATCH TOTALITY over the REAL outer `whnf_impl` MIR — the OUTER half of the
    /// literal reducer branch analysis (the model-level twin is the attested
    /// `whnf_progress_bd` case split). Every one of the 25 `ExprKind` variants is
    /// classified into exactly one of four classes, read fail-closed off the real MIR:
    ///
    ///   * identity-WHNF `{2 Sort, 5 Lam, 6 Pi}` — `_0 = e.clone()` of an already-WHNF
    ///     ctor head (each dischargeable via `is_whnf.{sort,lam,pi}`);
    ///   * identity-residual `{0 BVar, 8 Lit}` — identity return the narrow `is_whnf`
    ///     cannot classify (clean-verify's honest `stuck` residual);
    ///   * fvar-lookup `{1}` — the conditional local-context arm;
    ///   * recursive-core `{3 Const, 4 App, 7 Let, 9 Proj, 10 MData, 11..=24}` — the
    ///     `otherwise` complement, structurally confirmed to route into
    ///     `_0 = stack_safe(closure)` (the reduction loop; the inner half of the
    ///     analysis, against the closure body's MIR).
    ///
    /// No variant is unaccounted — the totality witness for the outer dispatch.
    #[test]
    fn whnf_dispatch_partition_is_total_on_real_mir() {
        let whnf = load_mir_fixture(FX_WHNF_IMPL);
        let p = whnf_dispatch_partition(&whnf)
            .expect("the real whnf_impl MIR must yield a total dispatch partition");
        assert_eq!(p.identity_whnf, vec![2, 5, 6], "identity-WHNF class = Sort/Lam/Pi");
        assert_eq!(p.identity_residual, vec![0, 8], "identity-residual class = BVar/Lit");
        assert_eq!(p.fvar_lookup, vec![1], "fvar-lookup class = FVar");
        // The recursive-core complement covers the reducible core forms AND every
        // extended form (SProp/Squash/cubical/ZFC, 11..=24) — all route through
        // `otherwise` into stack_safe. (CORRECTION 2026-07-17: first landed with the
        // range truncated to 0..11, which silently excluded 11..=24 from the claim.)
        let expected_core: Vec<usize> = [3usize, 4, 7, 9, 10].into_iter().chain(11..25).collect();
        assert_eq!(
            p.recursive_core, expected_core,
            "recursive-core complement = Const/App/Let/Proj/MData + all extended forms"
        );
    }

    /// NO MASQUERADE (dispatch totality): tampering the real MIR must fail the
    /// partition closed. (a) Redirecting the Sort arm to the FVar block breaks the
    /// identity read for an expected-identity variant -> `None`. (b) Renaming the
    /// `stack_safe` callee breaks the recursive-core routing witness -> `None`.
    #[test]
    fn whnf_dispatch_partition_tamper_fails_closed() {
        // (a) Redirect variant 2 (Sort) to variant 1's (FVar's) target block.
        let mut redirected = load_mir_fixture(FX_WHNF_IMPL);
        let mut fvar_target = None;
        for bb in &redirected.body.blocks {
            if let Terminator::SwitchInt { targets, .. } = &bb.terminator {
                fvar_target =
                    fvar_target.or_else(|| targets.iter().find(|(v, _)| *v == 1).map(|(_, t)| *t));
            }
        }
        let fvar_target = fvar_target.expect("real MIR has an FVar arm");
        for bb in &mut redirected.body.blocks {
            if let Terminator::SwitchInt { targets, .. } = &mut bb.terminator {
                for (v, t) in targets.iter_mut() {
                    if *v == 2 {
                        *t = fvar_target;
                    }
                }
            }
        }
        assert!(
            whnf_dispatch_partition(&redirected).is_none(),
            "redirecting the Sort arm off its identity block must fail the partition closed"
        );

        // (b) Rename the stack_safe callee: the recursive-core witness must fail.
        let mut renamed = load_mir_fixture(FX_WHNF_IMPL);
        for bb in &mut renamed.body.blocks {
            if let Terminator::Call { func: callee, .. } = &mut bb.terminator
                && final_segment(callee) == "stack_safe"
            {
                *callee = "expr::not_stack_safe".to_string();
            }
        }
        assert!(
            whnf_dispatch_partition(&renamed).is_none(),
            "breaking the stack_safe routing must fail the recursive-core witness closed"
        );
    }

    /// The real `whnf_impl::{closure#1}` — the `stack_safe` payload — with types
    /// stubbed provenance-style (blocks verbatim from the 2026-07-17 fork extraction;
    /// see PROVENANCE.md).
    const FX_WHNF_IMPL_CLOSURE1: &str = "clean_kernel.tc.whnf.whnf_impl.closure1.json";

    /// PAYLOAD WITNESS on the real MIR: the closure `whnf_impl` hands to `stack_safe`
    /// in its recursive-core branch is a PURE `whnf_inner(self, e)` passthrough —
    /// capture unpack, ONE call (the fork's Opaque-encoded `whnf_inner`), bare Return,
    /// nothing else writing `_0`. Extends the dispatch-totality chain one literal link:
    /// recursive-core variants -> stack_safe(closure#1) -> whnf_inner (the reduction
    /// loop's entry). NO MASQUERADE: renaming the callee in the Opaque kind, or
    /// injecting a `_0`-writing statement, must fail the witness closed.
    #[test]
    fn whnf_stack_safe_payload_witness_grounds_and_fails_closed() {
        let closure = load_mir_fixture(FX_WHNF_IMPL_CLOSURE1);
        assert!(
            whnf_stack_safe_payload_is_whnf_inner(&closure),
            "the real stack_safe payload must be a pure whnf_inner passthrough"
        );

        // Tamper (a): rename the callee inside the Opaque kind.
        let mut renamed = load_mir_fixture(FX_WHNF_IMPL_CLOSURE1);
        for bb in &mut renamed.body.blocks {
            if let Terminator::Opaque { kind, .. } = &mut bb.terminator {
                *kind = kind.replace("whnf_inner", "not_whnf_inner");
            }
        }
        assert!(
            !whnf_stack_safe_payload_is_whnf_inner(&renamed),
            "a payload calling something other than whnf_inner must fail the witness"
        );

        // Tamper (b): inject a statement writing the return place `_0`.
        let mut writes_ret = load_mir_fixture(FX_WHNF_IMPL_CLOSURE1);
        let steal = writes_ret.body.blocks[0].stmts[0].clone();
        if let Statement::Assign { mut place, rvalue, span } = steal {
            place.local = RETURN_LOCAL;
            place.projections.clear();
            writes_ret.body.blocks[0].stmts.push(Statement::Assign { place, rvalue, span });
        } else {
            panic!("fixture block 0 must start with an Assign");
        }
        assert!(
            !whnf_stack_safe_payload_is_whnf_inner(&writes_ret),
            "a payload with another writer of _0 must fail the witness (the call is no \
             longer the sole writer)"
        );
    }

    /// The real `whnf_inner` — the cached reduction wrapper (2026-07-17 extraction,
    /// types stubbed, blocks verbatim; PROVENANCE.md).
    const FX_WHNF_INNER: &str = "clean_kernel.tc.whnf.whnf_inner.json";

    /// CACHED-REDUCER witness on the real MIR: `whnf_inner` = cache-get -> Option
    /// switch { hit -> return cached (no reduce, no insert) | miss -> the ONE
    /// `whnf_outer_loop` reduction call -> the ONE cache insert }. The insert only
    /// stores the reducer's result (cache coherence). NO MASQUERADE: renaming the
    /// reducer callee, or rerouting the hit arm into the miss path, fails the witness.
    #[test]
    fn whnf_inner_cached_reducer_witness_grounds_and_fails_closed() {
        let inner = load_mir_fixture(FX_WHNF_INNER);
        assert!(
            whnf_inner_is_cached_reducer(&inner),
            "the real whnf_inner must witness as a cached whnf_outer_loop wrapper"
        );

        // Tamper (a): rename the reducer callee in its Opaque kind.
        let mut renamed = load_mir_fixture(FX_WHNF_INNER);
        for bb in &mut renamed.body.blocks {
            if let Terminator::Opaque { kind, .. } = &mut bb.terminator {
                *kind = kind.replace("whnf_outer_loop", "not_the_reducer");
            }
        }
        assert!(
            !whnf_inner_is_cached_reducer(&renamed),
            "a wrapper without the whnf_outer_loop call must fail the witness"
        );

        // Tamper (b): make BOTH switch arms route to the miss path (the reducer
        // becomes reachable from both arms — no genuine hit path).
        let mut both_miss = load_mir_fixture(FX_WHNF_INNER);
        let mut miss_target = None;
        // Identify the miss arm: the arm from which the reducer is reachable.
        let reducer = both_miss
            .body
            .blocks
            .iter()
            .find_map(|bb| match &bb.terminator {
                Terminator::Opaque { kind, .. } if kind.contains("whnf_outer_loop") => Some(bb.id),
                _ => None,
            })
            .expect("real whnf_inner has the reducer call");
        for bb in &both_miss.body.blocks {
            if let Terminator::SwitchInt { targets, .. } = &bb.terminator
                && targets.len() == 2
            {
                for (_, t) in targets {
                    if reachable_blocks(&both_miss, *t).is_some_and(|r| r.contains(&reducer)) {
                        miss_target = Some(*t);
                    }
                }
            }
        }
        let miss_target = miss_target.expect("real whnf_inner has a miss arm");
        for bb in &mut both_miss.body.blocks {
            if let Terminator::SwitchInt { targets, .. } = &mut bb.terminator
                && targets.len() == 2
            {
                for (_, t) in targets.iter_mut() {
                    *t = miss_target;
                }
            }
        }
        assert!(
            !whnf_inner_is_cached_reducer(&both_miss),
            "a wrapper whose BOTH arms reduce (no genuine cache-hit path) must fail"
        );
    }

    /// The real `whnf_outer_loop` — the reduce-until-fixpoint loop (2026-07-17
    /// extraction, types stubbed, blocks verbatim; PROVENANCE.md).
    const FX_WHNF_OUTER_LOOP: &str = "clean_kernel.tc.whnf_proj.whnf_outer_loop.json";

    /// FIXPOINT-EXIT witness on the real MIR: with the loop backedge CUT, the only
    /// arms that can reach `Return` are the eq-FIXPOINT arm, the CACHE-HIT arm, and
    /// the HEARTBEAT-bail arm — and the load-bearing negative holds: the CHANGED +
    /// CACHE-MISS arm cannot exit; it must re-loop. This is the literal-MIR content
    /// of "the reducer only returns unreducible (or cached-whnf, or budget-bailed)
    /// terms". NO MASQUERADE: renaming the eq callee, or rewiring the eq switch so
    /// the changed arm exits directly, must fail the witness closed.
    #[test]
    fn whnf_outer_loop_fixpoint_exit_witness_grounds_and_fails_closed() {
        let outer = load_mir_fixture(FX_WHNF_OUTER_LOOP);
        assert!(
            whnf_outer_loop_exits_only_at_fixpoint_cache_or_heartbeat(&outer),
            "the real whnf_outer_loop must witness fixpoint/cache/heartbeat-only exits"
        );

        // Tamper (a): rename the eq callee — the fixpoint check disappears.
        let mut no_eq = load_mir_fixture(FX_WHNF_OUTER_LOOP);
        for bb in &mut no_eq.body.blocks {
            if let Terminator::Opaque { kind, .. } = &mut bb.terminator {
                *kind = kind.replace("PartialEq>::eq", "PartialEq>::neq");
            }
        }
        assert!(
            !whnf_outer_loop_exits_only_at_fixpoint_cache_or_heartbeat(&no_eq),
            "a loop without the Expr::eq fixpoint check must fail the witness"
        );

        // Tamper (b): rewire the eq switch so the CHANGED (value 0) arm jumps
        // straight to the fixpoint arm's target — a loop that exits after a change
        // without consulting the cache. The changed path then has no cache lookup,
        // so the witness must fail closed.
        let mut changed_exits = load_mir_fixture(FX_WHNF_OUTER_LOOP);
        // Locate the eq block's switch and overwrite the value-0 target.
        let eq_id = changed_exits
            .body
            .blocks
            .iter()
            .find_map(|bb| match &bb.terminator {
                Terminator::Opaque { kind, .. } if kind.contains("PartialEq>::eq::") => Some(bb.id),
                _ => None,
            })
            .expect("real MIR has the eq block");
        let eq_next = match &changed_exits
            .body
            .blocks
            .iter()
            .find(|b| b.id == eq_id)
            .expect("eq block")
            .terminator
        {
            Terminator::Opaque { targets, .. } => targets[0],
            _ => panic!("eq block must be Opaque"),
        };
        let fixpoint_target = match &changed_exits
            .body
            .blocks
            .iter()
            .find(|b| b.id == eq_next)
            .expect("eq switch block")
            .terminator
        {
            Terminator::SwitchInt { otherwise, .. } => *otherwise,
            _ => panic!("eq continuation must be a SwitchInt"),
        };
        for bb in &mut changed_exits.body.blocks {
            if bb.id == eq_next
                && let Terminator::SwitchInt { targets, .. } = &mut bb.terminator
            {
                for (v, t) in targets.iter_mut() {
                    if *v == 0 {
                        *t = fixpoint_target;
                    }
                }
            }
        }
        assert!(
            !whnf_outer_loop_exits_only_at_fixpoint_cache_or_heartbeat(&changed_exits),
            "a loop whose changed arm exits directly (skipping cache + re-loop) must fail"
        );
    }
}
