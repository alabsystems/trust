// trust-clean/trustir_fold.rs — Trust: structural-fold lane, RUNGS A + B.
//
// RUNG A (mini-ADT pilot; landed 2026-07-10): the smallest end-to-end slice of
// the structural-recursion certification lane
// (docs/design/2026-07-10-structural-fold-lane.md §5 Rung A): an INT-VALUED
// structural fold over a single-SCC (self-recursive, no co-members) `Arc`-recursive
// enum, certified by
//
//   1. a RECURSOR-DEFINED-TOTAL interpreter — the fold model is a Clean
//      `Definition` whose value is a `<T>.rec` application, so TOTALITY is checked
//      by the kernel as a side effect of type-checking the definition: the
//      recursor's minor premises provide induction hypotheses ONLY for direct
//      children, so a non-structural recursion is not merely rejected, it is
//      INEXPRESSIBLE in the model (design §1);
//   2. IH-SLOT MAPPING — a recursive call site in the MIR is translated to the
//      recursor's induction-hypothesis slot, NEVER to an opaque call result
//      (design §3: "do not route self-calls through callReturnInstance");
//   3. STRICT-SUBTERM PROVENANCE — the recognizer admits a recursive call ONLY
//      when its argument is a field projection of the CURRENTLY-MATCHED variant's
//      payload, reached by an unbroken copy/move/`Arc`-deref chain with no
//      intervening writes; every other provenance is a NAMED decline (design §6:
//      `non_subterm_recursive_arg` for the scrutinee itself / a locally-rebuilt
//      node / a foreign-call result).
//
// RUNG B (2026-07-10, this file's extension; design §5 Rung B + §4):
//
//   4. RESULT-SORT FAMILY — the interpreter's result sort is now a parameter of
//      the registration family ([`FoldSort`]): `Int` (rung A, unchanged), `Bool`
//      (short-circuit `&&`/`||` walked as per-arm COND-TREES — `Bool.rec`
//      value-level conditionals — with Int-payload comparisons as Bool leaves),
//      and `Acc` (the ACCUMULATOR lane, design §4: motive `Acc → Acc` with `Acc`
//      an opaque type and ONE uninterpreted total insert op; the model pins the
//      EXACT program-order insert/recursion sequence — set-commutativity is
//      never asserted). Fail-closed accumulator rules, all NAMED declines:
//      the `&mut` accumulator is threaded UNCHANGED to every recursive call
//      (`accumulator_alias` otherwise), mutated ONLY via the pinned insert op
//      with the returned bool DISCARDED (`accumulator_read` if any read of the
//      insert result — or any other accumulator read — exists), and never
//      passed to a foreign callee (`accumulator_escape`). NO memo idiom is
//      admitted ANYWHERE in this recognizer, so the design's memo/accumulator
//      disjunction is enforced by construction (a memo get/put would appear as
//      a foreign call receiving the folder's state and decline).
//   5. OPAQUE PAYLOADS — a variant field that is neither an `Int` scalar nor
//      the pinned `Arc<Self>` recursive child is admitted as an OPAQUE atom
//      (design §1: "`Name`/`Level`/... payloads become opaque `Nat`-keyed
//      atoms"): the model gives its constructor an `Int`-atom argument that the
//      adequacy theorems ∀-quantify; ANY read of such a field is the NAMED
//      decline `opaque_payload_read`. (Soundness: the fold provably never
//      consumes the field, so the theorem holds under any atom assignment —
//      the denotation of the unread payload is irrelevant pointwise.)
//   6. SHARED ARM BLOCKS — `A | B =>` match arms (rung A's `duplicate_arm_target`
//      decline) are now walked PER-VARIANT through the shared block: the
//      variant-payload projection check is `Downcast(v_idx)`-exact, so a shared
//      arm that touches ANY variant-specific field still declines for the other
//      variant; only genuinely variant-independent shared arms certify.
//   7. P-STACK (design §2, the `stack_safe` premise, DEBUTED HERE) — clean-kernel
//      routes recursion through `stack_safe(|| …)` = `stacker::maybe_grow(32768,
//      1048576, f)` (third-party FFI via psm — UNCERTIFIABLE in-pipeline, ever).
//      Quarantined by exact-shape fingerprint, fail-closed: the callee's OWN
//      dumped body must be exactly the two-literal `maybe_grow` forwarding call,
//      and the closure argument's OWN dumped body (closure bodies are extractable
//      post-REBUILD) must be exactly the pinned recursive-call shape (capture the
//      `&Arc<child>` field ref, `Deref::deref` it, single call to the recognized
//      function) — then the whole `stack_safe` call maps to the IH slot of the
//      captured field, same strict-subterm provenance as a direct self call.
//      Any drift → NAMED decline `stack_safe_drift`. The premise carried:
//      P-STACK — `stacker::maybe_grow(r, s, f) = f()`, f called exactly once.
//      [`sem_stack_safe_wrapper_of`] additionally recognizes the public WRAPPER
//      idiom (`fn f(&self) { stack_safe(|| self.f_impl()) }`) so the wrapper row
//      certifies over the impl's fold witness via the same fingerprint.
//   8. NICHE-LAYOUT TAG MAP (rung A's open validation item, RESOLVED on real
//      dumps): the entry `SwitchInt(Discriminant(*param))`'s case values are the
//      enum's LOGICAL discriminants for EVERY layout encoding — `Rvalue::
//      Discriminant`'s MIR semantics is layout-independent, and the required
//      TyCtxt-vetted `exhaustive_enum_unreachable` flag is stamped by the
//      extraction ONLY when the case set EQUALS `adt_def.discriminants(tcx)`
//      (`trust-mir-extract/src/lib.rs::mark_exhaustive_enum_unreachable_switches`
//      → `place_enum_tags`). So the rung-A `disc_index_safe` (Direct-tag-layout)
//      gate is NOT needed for the tag→variant map's soundness and is dropped:
//      the REAL `clean_kernel::Level` (5 ctors, `Param(Name)` payload) is
//      niche-encoded (Param untagged; verified via `-Zprint-type-sizes` +
//      extraction probes 2026-07-10) yet its `is_zero` dump switches on logical
//      tags 0..=4 with the vetted flag. The map remains total + unique + flag-
//      gated — fail-closed for partial matches and raw (non-`Discriminant`)
//      tag switches.
//
// RUNG G (P-BOX-DEREF, 2026-07-12; the published-crate pointer premise —
// fixtures/fold-crate-lambda-calculus-3.5.0/PROVENANCE.md §5):
//
//   9. BOX CHILDREN (G1) — recursive children behind `std::boxed::Box`: the
//      SIBLING type walk `Box → "0": Unique → "pointer": NonNull → "pointer":
//      RawPtr → pointee` (G1a; never a relaxation of the Arc walk), including
//      the boxed 2-TUPLE child `Box<(enum, enum)>` (G2: ONE MIR field, TWO
//      recursor slots / per-component IH positions, reached as `&(*raw).0` /
//      `&(*raw).1`). Box deref is BUILT-IN (no callee to pin), so the premise
//      is quarantined by an EXACT two-block fingerprint of the compiler's
//      inline ub-check idiom (G1b): copy the Box out of the field ref,
//      project `.0.0`, cast to `*const pointee`, an ALIGNMENT check block
//      (`addr & (align-1) == 0`, align a power of two →
//      `Assert(MisalignedPointerDereference, expected: true)`), a NULL check
//      block (`!(addr == 0 & true)` → `Assert(Custom "null reference
//      constructed", expected: true)`), then the subterm borrow. The two
//      asserts are PREMISE-DISCHARGED — they ARE Box's validity invariant
//      (aligned + non-null), exactly the contract P-ARC-DEREF carries for
//      `Deref::deref` — and NONE of the idiom's address-arithmetic temps are
//      bound, so pointer values can never leak into the fold's Int lane. Any
//      drift (reordered/missing statements, wrong constants, swapped assert
//      messages/polarities, off-provenance Box copies, a naked ub-check
//      outside the idiom, a non-Box `Unique` walk) is the NAMED decline
//      `box_deref_drift`; a whole-body audit re-validates EVERY
//      Misaligned/null-custom assert pair — even on unwalked paths —
//      fail-closed.
//  10. FOLD PARAMETERS (G3) — value-sorted folds may thread ONE extra scalar
//      `Int` parameter (`has_free_variables_helper(&self, depth)`): the
//      motive becomes `Int → σ`, IH slots are `Int → σ` applied to the
//      recognizer-resolved argument (`ih (d+1)` at a binder — FoldExpr::
//      IhApp), the threaded parameter is never written (`param_reassigned`
//      otherwise). The `depth + 1` CheckedAdd's overflow VC is NOT premise-
//      covered — it stays the safety pillar's honest hostage, so the
//      published-crate first target mints its KERNEL WITNESS and remains
//      short of FULLY_FAITHFUL at exactly that measured VC (the intake's
//      honesty note, stated plainly rather than engineered around).
//
// RUNG-B SCOPE (fail-closed; everything outside declines by name): SCC-of-1
// (plus the stack_safe closure trampoline, which is fingerprint-collapsed into
// the same function), result sorts {Int, Bool, Acc}, no memo, exactly one
// accumulator, branching arms for value sorts (cond-trees), straight-line
// accumulator arms. Known out-of-scope (each verified against the real dumps,
// see the level-fold-corpus PROVENANCE): ADT-valued results (`Option<Level>` —
// the OptE domain is rung C's debut per design §5), smart-constructor rebuilds
// (`Level::max`/`imax` — NOT free ctors; need ADT-valued certified-callee
// denotations, design §3.4 = rung E transport), `HashMap` lookups, `Option`
// combinators, multi-accumulator threading (`collect_params_impl`'s
// `(&mut Vec, &mut HashSet)` pair), and struct-wrapped scrutinees with
// metadata guards (`Expr` — the Expr-scale rungs).
//
// HONESTY TIER — MODEL-ONLY, same as `trustir_adt.rs`: the live grounder
// (`clean_ground::ground_int`) cannot represent an ADT value, so this witness is
// a SELF-CONTAINED, freshly-registered, kernel-checked claim, not
// grounder-connected. NAMED TRANSLATION PREMISES (design §2/§6):
//   * P-ACYC — a runtime `Arc<Tree>` value is a finite tree/DAG, so it denotes a
//     value of the registered inductive. True by construction for the modeled
//     shape (immutable enum, `Arc` payloads built bottom-up, no `Weak`, no
//     interior mutability); a translation-adequacy premise, NOT a kernel axiom.
//   * P-ARC-DEREF — `<std::sync::Arc<T> as Deref>::deref` returns a reference to
//     the Arc's pointee (the strict subterm). Enforced by pinning: the callee
//     def-path must be `std::ops::Deref::deref`, the argument's declared type a
//     `&std::sync::Arc<..>` whose pointee (through the pinned
//     `ptr → NonNull → pointer → RawPtr → ArcInner → data` field path in the
//     dump's own type info) names the folded enum, and the destination's
//     declared type `&<enum>`.
//   * P-STACK (rung B) — `stacker::maybe_grow(red_zone, growth, f) = f()`, `f`
//     called exactly once (clean-kernel's own `stack_safe` contract). The
//     `maybe_grow` body is third-party FFI (psm) and permanently outside the
//     pipeline; the fingerprint quarantines the premise to exactly the
//     two-literal forwarding shape.
//   * P-BOX-DEREF (rung G) — a live `Box<T>`'s Unique/NonNull pointer is
//     non-null, aligned, and points at the box's pointee (the strict
//     subterm): dereferencing it yields the child, and the compiler's two
//     inline ub-check asserts (alignment, null) never fire. Quarantined by
//     the exact two-block fingerprint (module doc item 9) — the same
//     discipline as P-STACK, with the added rule that the idiom's
//     address-arithmetic temps are never bound.
//   * P-ACC-OPAQUE (rung B) — the accumulator model treats `HashSet::insert`
//     as an UNINTERPRETED TOTAL op `insertAcc : Acc → Int → Acc` (the `idxElem`
//     honesty tier): the certified claim is the exact insert/recursion SEQUENCE,
//     not set semantics; the op's totality (no panic path changing control
//     flow) is the same happy-path tier every pinned first-party idiom carries.
//
// RUNG-B DIVERGENCE FROM THE DESIGN DOC (noted, deliberate; carried from rung
// A): the witness is a per-function interpreter, not yet the once-registered
// universal `foldE` — the minor premises and the theorem RHS derive from the
// same recognized shape by TWO SEPARATE rendering paths (`minor_body_expr` vs
// `arm_rhs_expr`, different binder telescopes), and the FORGERY probes
// (`..._claimed` + the tests) pin that a wrong RHS (swapped children, wrong arm
// constant, swapped cond branches, reordered accumulator inserts) is
// `KernelRejected`, not accepted. The universal leaf-parametric interpreter
// lands with the Expr-scale rungs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeMap;

use clean_kernel::{
    BinderData, BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl,
    InductiveType, Level, Name, TypeChecker,
};
use trust_types::{
    AggregateKind, AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Operand, Place,
    Projection, Rvalue, Statement, Terminator, Ty, UnOp, VerifiableFunction,
};

use crate::trustir_anchor::{RefinementVerdict, cst, int_lit, int_ty};

/// Sibling dump bodies (def-path → parsed dump), used to resolve the
/// `stack_safe` trampoline's closure bodies (rung B, P-STACK). The driver
/// (`prove_dump_dir_with_budget`) threads the whole dump directory's map; an
/// empty map simply means the stack_safe idiom can never be resolved (those
/// shapes decline `stack_safe_drift` — fail-closed, never wrong).
pub type DumpBodies = BTreeMap<String, VerifiableFunction>;

fn bd() -> BinderData {
    BinderData::from(BinderInfo::Default)
}

fn l1() -> Level {
    Level::succ(Level::zero())
}

// ===========================================================================
// The recognized shape
// ===========================================================================

/// The fold's result sort — the rung-B registration-family parameter
/// (design §4: "the interpreter's result sort is a parameter").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FoldSort {
    /// `Int`-valued fold (rung A).
    Int,
    /// `Bool`-valued fold (rung B): cond-tree arms, comparisons as leaves.
    Bool,
    /// Accumulator fold (rung B, design §4): `fn(&Enum, &mut HashSet<i64>)`,
    /// modeled as `T → Acc → Acc` with the opaque `insertAcc` op.
    Acc,
}

/// One recognized structural fold over a recursive enum: the enum's full
/// variant structure (declaration order, real `SwitchInt` tags from the dump's
/// own type info) plus, per variant, the recognizer-reconstructed arm body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemStructFold {
    /// The folded enum's def-path name (from the switched param's declared type).
    pub enum_name: String,
    /// The fold's result sort.
    pub sort: FoldSort,
    /// Rung G (G3): the fold threads ONE extra scalar `Int` parameter (the
    /// `has_free_variables_helper(&self, depth)` family). The interpreter's
    /// motive becomes `Int → σ`, IH slots are `Int → σ` applied via
    /// [`FoldExpr::IhApp`], and the threaded parameter is never written.
    /// Value sorts only (`Int`/`Bool`) — never combined with `Acc`.
    pub depth: bool,
    /// Per-variant data, in DECLARATION ORDER (the dump `variants` order — the
    /// order the Clean constructors are registered in).
    pub variants: Vec<FoldVariant>,
}

/// One variant of the folded enum + its recognized arm.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoldVariant {
    /// Variant name (used for the Clean constructor name).
    pub name: String,
    /// The REAL `SwitchInt` tag this variant's arm was reached by — read from
    /// the dump's `VariantDef.discriminant`, NEVER assumed equal to the
    /// declaration index (the `TaggedTree` fixture pins tag != index).
    pub tag: i128,
    /// Recursor SLOT classification, in slot order — one Clean constructor
    /// argument per entry. For Int/`Arc`/`Box<enum>`/opaque MIR fields the
    /// slots are 1:1 with the MIR fields; a boxed recursive PAIR
    /// (`Box<(enum, enum)>`, rung G item G2) is ONE MIR field carrying TWO
    /// consecutive `Recursive` slots (per-component IH positions).
    pub fields: Vec<FoldFieldKind>,
    /// The recognizer-reconstructed arm value (of the fold's result sort;
    /// for `FoldSort::Acc` this is the final accumulator-state expression).
    pub arm: FoldExpr,
}

/// A variant field's classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FoldFieldKind {
    /// Scalar `Int` payload (any width/signedness — the kernel carrier is the
    /// unbounded `Int`; width obligations are the safety pillar's concern).
    PayloadInt,
    /// Recursive child (`Arc<enum>`): gets an IH slot in the recursor model.
    Recursive,
    /// Anything else — an OPAQUE atom (rung B; design §1): the model gives the
    /// constructor an `Int` atom the theorems ∀-quantify; ANY read declines
    /// (`opaque_payload_read`).
    PayloadOpaque,
}

/// The per-arm value expression, over IH slots, payload atoms, and (rung B)
/// bool cond-trees / accumulator-state chains.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FoldExpr {
    /// The induction hypothesis for the variant's recursive field `f`
    /// (field index, not IH rank). Sorted at the fold's result sort
    /// (`Int`/`Bool` folds only; accumulator folds use [`FoldExpr::AccRec`]).
    Ih(usize),
    /// The variant's `Int` payload field `f` (Int-sorted).
    Payload(usize),
    /// Integer literal (Int-sorted).
    Const(i128),
    /// Binary operation over two Int sub-values (Int-sorted).
    Bin(FoldBinOp, Box<FoldExpr>, Box<FoldExpr>),
    /// Bool literal (rung B; Bool-sorted).
    BoolConst(bool),
    /// Comparison of two Int sub-values (rung B; Bool-sorted).
    Cmp(FoldCmpOp, Box<FoldExpr>, Box<FoldExpr>),
    /// Value-level conditional `if c { t } else { e }` (rung B): `c` Bool-sorted,
    /// `t`/`e` same-sorted; renders as the `Bool.rec` value idiom. Reconstructed
    /// from short-circuit `&&`/`||` control flow.
    Cond(Box<FoldExpr>, Box<FoldExpr>, Box<FoldExpr>),
    /// The threaded accumulator parameter (rung B; Acc-sorted; accumulator
    /// folds only).
    AccParam,
    /// `insertAcc state value` (rung B; Acc-sorted): one pinned `HashSet::insert`
    /// in program order.
    AccInsert(Box<FoldExpr>, Box<FoldExpr>),
    /// The recursive call on field `f` threaded through accumulator state
    /// (rung B; Acc-sorted): the IH (of type `Acc → Acc`) applied to the state.
    AccRec(usize, Box<FoldExpr>),
    /// The threaded scalar fold parameter (rung G, G3; Int-sorted; depth
    /// folds only).
    DepthParam,
    /// The IH for recursive slot `f` APPLIED to a threaded-parameter argument
    /// (rung G, G3): `ih_f d` — sorted at the fold's value sort; the argument
    /// Int-sorted (`d`, `d + 1`, …). Depth folds only; a bare [`FoldExpr::Ih`]
    /// is ill-sorted there (the IH is a function, never a value).
    IhApp(usize, Box<FoldExpr>),
}

/// The Int binop vocabulary (rung A, unchanged). `Add`/`Sub`/`Mul` denote the
/// mathematical Int ops (adequate on the non-overflowing happy path — the
/// checked-op `Assert` forecloses the overflowing path at runtime and the
/// corresponding `ArithmeticOverflow` safety VC is the FF gate's separate
/// discharge burden); `Xor`/`Or`/`And` denote the opaque total
/// `Int.xor`/`Int.lor`/`Int.land` carriers (the established bitwise honesty tier).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FoldBinOp {
    Add,
    Sub,
    Mul,
    Xor,
    Or,
    And,
}

impl FoldBinOp {
    fn clean_name(self) -> &'static str {
        match self {
            FoldBinOp::Add => "Int.add",
            FoldBinOp::Sub => "Int.sub",
            FoldBinOp::Mul => "Int.mul",
            FoldBinOp::Xor => "Int.xor",
            FoldBinOp::Or => "Int.lor",
            FoldBinOp::And => "Int.land",
        }
    }

    fn of_mir(op: BinOp) -> Option<FoldBinOp> {
        match op {
            BinOp::Add => Some(FoldBinOp::Add),
            BinOp::Sub => Some(FoldBinOp::Sub),
            BinOp::Mul => Some(FoldBinOp::Mul),
            BinOp::BitXor => Some(FoldBinOp::Xor),
            BinOp::BitOr => Some(FoldBinOp::Or),
            BinOp::BitAnd => Some(FoldBinOp::And),
            _ => None,
        }
    }
}

/// The Bool comparison vocabulary (rung B). Renders via this module's OWN
/// hermetic copy of the established compare-as-value idiom (`decide`/`Int.lt`/
/// `Int.le`/`Int.beq`/`Bool.not`/`Int.decLt`/`Int.decLe` — byte-for-byte the
/// same prelude primitives `trustir_anchor::cmp_bool_expr` and
/// `mirsem::cmp_bool_expr` establish).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FoldCmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl FoldCmpOp {
    fn of_mir(op: BinOp) -> Option<FoldCmpOp> {
        match op {
            BinOp::Eq => Some(FoldCmpOp::Eq),
            BinOp::Ne => Some(FoldCmpOp::Ne),
            BinOp::Lt => Some(FoldCmpOp::Lt),
            BinOp::Le => Some(FoldCmpOp::Le),
            BinOp::Gt => Some(FoldCmpOp::Gt),
            BinOp::Ge => Some(FoldCmpOp::Ge),
            _ => None,
        }
    }
}

/// Hermetic compare-as-value rendering (see [`FoldCmpOp`]'s doc).
fn cmp_bool_expr(op: FoldCmpOp, a: Expr, b: Expr) -> Expr {
    let decide_lt = |x: Expr, y: Expr| {
        Expr::apps(
            cst("decide"),
            [
                Expr::apps(cst("Int.lt"), [x.clone(), y.clone()]),
                Expr::apps(cst("Int.decLt"), [x, y]),
            ],
        )
    };
    let decide_le = |x: Expr, y: Expr| {
        Expr::apps(
            cst("decide"),
            [
                Expr::apps(cst("Int.le"), [x.clone(), y.clone()]),
                Expr::apps(cst("Int.decLe"), [x, y]),
            ],
        )
    };
    match op {
        FoldCmpOp::Lt => decide_lt(a, b),
        FoldCmpOp::Le => decide_le(a, b),
        FoldCmpOp::Eq => Expr::apps(cst("Int.beq"), [a, b]),
        FoldCmpOp::Ne => Expr::app(cst("Bool.not"), Expr::apps(cst("Int.beq"), [a, b])),
        // Gt(a,b) ≡ Lt(b,a); Ge(a,b) ≡ Le(b,a) — swapped operands (matches
        // `register_eval_cond`).
        FoldCmpOp::Gt => decide_lt(b, a),
        FoldCmpOp::Ge => decide_le(b, a),
    }
}

// ===========================================================================
// Named declines (design §6 + §4)
// ===========================================================================

/// Why the recognizer declined — every decline is NAMED (design §6); nothing
/// outside the modeled fragment is ever silently accepted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FoldDecline {
    /// Return/parameter signature is not one of the modeled result sorts
    /// (`Int`, `Bool`, or the one-accumulator `Unit` shape). The historical
    /// name `non_int_return` is kept stable (rung A's pin); ADT-valued results
    /// (`Option<Level>`, …) land here until the rung-C OptE domain.
    NonIntReturn,
    /// No self-recursive call in the body (this lane certifies recursion; a
    /// non-recursive body belongs to the existing lanes).
    NotSelfRecursive,
    /// The parameter shape is outside the fragment: not `&Enum` (+ optionally
    /// ONE `&mut HashSet` accumulator), missing layout info, or a mutable /
    /// unrecognized signature.
    ParamShapeUnsupported(String),
    /// The folded parameter or the accumulator parameter is written.
    ParamReassigned,
    /// Entry block is not exactly `discr := Discriminant(*param); SwitchInt(discr)`.
    UnsupportedEntryBlock(String),
    /// The entry switch does not scrutinize the parameter's discriminant.
    NonDiscriminantSwitch,
    /// A switch target does not map TOTALLY onto the enum's variant set via the
    /// dump type info's own discriminant values (design §6: never assume
    /// tag == declaration index), or the switch lacks the TyCtxt-vetted
    /// `exhaustive_enum_unreachable` flag (which certifies the case values are
    /// EXACTLY the enum's logical discriminant set — see module doc item 8).
    UnmappedSwitchTarget(String),
    /// A recursive call's argument is NOT a strict subterm of the matched
    /// variant payload (design §6's headline kill): the scrutinee itself, a
    /// locally-rebuilt node, a foreign-call result, or unresolved provenance.
    NonSubtermRecursiveArg { detail: String },
    /// The same recursive field is consumed by two recursive calls on one path.
    DuplicateRecursiveCall,
    /// An OPAQUE variant payload (rung B: non-Int, non-recursive field) is
    /// read/borrowed — the model's atom is unread by construction, so any
    /// touch declines.
    OpaquePayloadTouched(String),
    /// A statement outside the arm vocabulary.
    UnsupportedArmStatement(String),
    /// A terminator outside the arm vocabulary (loops, unexpected switches,
    /// diverging calls, non-checked-op asserts).
    UnsupportedArmTerminator(String),
    /// A binary operation outside the vocabulary.
    UnsupportedBinOp(String),
    /// The arm's returned value depends on a foreign (non-self, non-pinned)
    /// call result.
    ForeignValueInArm(String),
    /// Rung B (design §4 rule iii): the accumulator (or a borrow of it) is
    /// passed to a foreign callee / leaves the modeled insert+recurse fragment.
    AccumulatorEscape(String),
    /// Rung B (design §4 rule ii): the accumulator is READ — including any use
    /// of the pinned insert op's bool result (control flow must never be
    /// accumulator-dependent).
    AccumulatorRead(String),
    /// Rung B (design §4 rule i): a recursive call's accumulator argument is
    /// not the threaded parameter itself (fresh/aliased/substituted state).
    AccumulatorAlias(String),
    /// Rung B (P-STACK): a `stack_safe`-shaped call whose own body / closure
    /// body / capture provenance drifts from the pinned fingerprint.
    StackSafeDrift(String),
    /// Rung G (P-BOX-DEREF): a body that claims the built-in Box-deref idiom
    /// (a `MisalignedPointerDereference` / `Custom("null reference
    /// constructed")` ub-check assert anywhere, or a borrow through a
    /// box-subterm raw pointer) but drifts from the pinned two-block
    /// fingerprint — reordered/missing statements, wrong constants, swapped
    /// assert messages/polarities, off-provenance Box copies, or a naked
    /// ub-check outside a validated pair.
    BoxDerefDrift(String),
}

impl FoldDecline {
    /// The stable snake_case decline name (design §6's kill table).
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            FoldDecline::NonIntReturn => "non_int_return",
            FoldDecline::NotSelfRecursive => "not_self_recursive",
            FoldDecline::ParamShapeUnsupported(_) => "param_shape_unsupported",
            FoldDecline::ParamReassigned => "param_reassigned",
            FoldDecline::UnsupportedEntryBlock(_) => "unsupported_entry_block",
            FoldDecline::NonDiscriminantSwitch => "non_discriminant_switch",
            FoldDecline::UnmappedSwitchTarget(_) => "unmapped_switch_target",
            FoldDecline::NonSubtermRecursiveArg { .. } => "non_subterm_recursive_arg",
            FoldDecline::DuplicateRecursiveCall => "duplicate_recursive_call",
            FoldDecline::OpaquePayloadTouched(_) => "opaque_payload_read",
            FoldDecline::UnsupportedArmStatement(_) => "unsupported_arm_statement",
            FoldDecline::UnsupportedArmTerminator(_) => "unsupported_arm_terminator",
            FoldDecline::UnsupportedBinOp(_) => "unsupported_bin_op",
            FoldDecline::ForeignValueInArm(_) => "foreign_value_in_arm",
            FoldDecline::AccumulatorEscape(_) => "accumulator_escape",
            FoldDecline::AccumulatorRead(_) => "accumulator_read",
            FoldDecline::AccumulatorAlias(_) => "accumulator_alias",
            FoldDecline::StackSafeDrift(_) => "stack_safe_drift",
            FoldDecline::BoxDerefDrift(_) => "box_deref_drift",
        }
    }
}

// ===========================================================================
// Pins
// ===========================================================================

/// The pinned Arc-deref callee def-path (P-ARC-DEREF; see the module doc).
const ARC_DEREF_CALLEE: &str = "std::ops::Deref::deref";
/// The pinned `std::sync::Arc` def-path.
const ARC_NAME: &str = "std::sync::Arc";

/// Field-position pins for the Arc pointee walk (P-ARC-DEREF).
const ARC_PTR_FIELD: &str = "ptr";
const NONNULL_NAME: &str = "std::ptr::NonNull";
const NONNULL_POINTER_FIELD: &str = "pointer";
const ARCINNER_DATA_FIELD: &str = "data";

/// The pinned accumulator container + insert op (rung B, design §4). The
/// def-path spelling is read off the real dumps (both the fixture corpus and
/// clean-kernel's own `collect_constants_into_impl` dump carry exactly this
/// generic-parameter rendering).
const HASHSET_NAME: &str = "std::collections::HashSet";
const HASHSET_INSERT_CALLEE: &str = "std::collections::HashSet::<T, S, A>::insert";

/// P-STACK pins: `stack_safe`'s body must be exactly
/// `stacker::maybe_grow(32768, 1048576, f)` (clean-kernel `expr/mod.rs:53-68`).
const STACKER_MAYBE_GROW: &str = "stacker::maybe_grow";
const STACK_SAFE_RED_ZONE: u128 = 32 * 1024;
const STACK_SAFE_GROWTH: u128 = 1024 * 1024;

/// The pinned `std::boxed::Box` def-path (rung G, P-BOX-DEREF).
const BOX_NAME: &str = "std::boxed::Box";
/// Field-position pins for the Box pointee walk (P-BOX-DEREF; measured on the
/// real published-crate dumps —
/// tests/fold_crate_lambda_calculus.rs::box_field_lowering_chain):
/// `Box."0" → Unique."pointer" → NonNull."pointer" → RawPtr → pointee`.
const UNIQUE_NAME: &str = "std::ptr::Unique";
const BOX_UNIQUE_FIELD: &str = "0";
const UNIQUE_NONNULL_FIELD: &str = "pointer";
/// The pinned message of the compiler's inline NULL ub-check assert — the
/// second block of the G1b box-deref fingerprint.
const BOX_NULL_ASSERT_MSG: &str = "null reference constructed";

/// Whether `name` is std's `ArcInner` def-path. The extraction renders it
/// crate-prefixed relative to the FIRST extern that re-exported `alloc`
/// (`alloc::sync::ArcInner` in the fixture dumps, `smallvec::alloc::sync::
/// ArcInner` in the clean-kernel extract — both observed on real dumps), so
/// the pin accepts exactly the `alloc::sync::ArcInner` suffix on a `::`
/// boundary.
fn is_arcinner_name(name: &str) -> bool {
    name == "alloc::sync::ArcInner" || name.ends_with("::alloc::sync::ArcInner")
}

/// Resolve the pointee type of a lowered `std::sync::Arc<..>` through the
/// pinned `ptr → NonNull → pointer → RawPtr → ArcInner → data` field path
/// (exactly the shape the real dumps carry). `None` (fail-closed) for anything
/// off-shape.
pub(crate) fn arc_pointee_ty(ty: &Ty) -> Option<&Ty> {
    let Ty::Adt { name, fields, .. } = ty else { return None };
    if name != ARC_NAME {
        return None;
    }
    let (_, nonnull) = fields.iter().find(|(n, _)| n == ARC_PTR_FIELD)?;
    let Ty::Adt { name: nn_name, fields: nn_fields, .. } = nonnull else { return None };
    if nn_name != NONNULL_NAME {
        return None;
    }
    let (_, rawptr) = nn_fields.iter().find(|(n, _)| n == NONNULL_POINTER_FIELD)?;
    let Ty::RawPtr { pointee, .. } = rawptr else { return None };
    let Ty::Adt { name: inner_name, fields: inner_fields, .. } = pointee.as_ref() else {
        return None;
    };
    if !is_arcinner_name(inner_name) {
        return None;
    }
    let (_, data) = inner_fields.iter().find(|(n, _)| n == ARCINNER_DATA_FIELD)?;
    Some(data)
}

/// Resolve the pointee type of a lowered `std::boxed::Box<..>` through the
/// pinned `"0" → Unique → "pointer" → NonNull → "pointer" → RawPtr` field path
/// (rung G, P-BOX-DEREF item G1a — exactly the shape the real published-crate
/// dumps carry). A SIBLING of [`arc_pointee_ty`], never a relaxation of it:
/// `None` (fail-closed) for anything off-shape.
pub(crate) fn box_pointee_ty(ty: &Ty) -> Option<&Ty> {
    let Ty::Adt { name, fields, .. } = ty else { return None };
    if name != BOX_NAME {
        return None;
    }
    let (_, unique) = fields.iter().find(|(n, _)| n == BOX_UNIQUE_FIELD)?;
    let Ty::Adt { name: u_name, fields: u_fields, .. } = unique else { return None };
    if u_name != UNIQUE_NAME {
        return None;
    }
    let (_, nonnull) = u_fields.iter().find(|(n, _)| n == UNIQUE_NONNULL_FIELD)?;
    let Ty::Adt { name: nn_name, fields: nn_fields, .. } = nonnull else { return None };
    if nn_name != NONNULL_NAME {
        return None;
    }
    let (_, rawptr) = nn_fields.iter().find(|(n, _)| n == NONNULL_POINTER_FIELD)?;
    let Ty::RawPtr { pointee, .. } = rawptr else { return None };
    Some(pointee)
}

/// Whether a lowered type NAMES the enum `enum_name` — either the full
/// `Ty::Adt` occurrence or the by-name recursive `Ty::Datatype` back-reference
/// the extraction emits at a recursive field position.
pub(crate) fn ty_names_enum(ty: &Ty, enum_name: &str) -> bool {
    match ty {
        Ty::Adt { name, .. } | Ty::Datatype { name, .. } => name == enum_name,
        _ => false,
    }
}

/// Whether `ty` is a pinned `Box` over the folded enum — `Some(false)` for the
/// single child `Box<enum>` (G1), `Some(true)` for the boxed recursive PAIR
/// `Box<(enum, enum)>` (G2), `None` for everything else (fail-closed).
fn box_recursive_form(ty: &Ty, enum_name: &str) -> Option<bool> {
    match box_pointee_ty(ty)? {
        p if ty_names_enum(p, enum_name) => Some(false),
        Ty::Tuple(elems)
            if elems.len() == 2 && elems.iter().all(|e| ty_names_enum(e, enum_name)) =>
        {
            Some(true)
        }
        _ => None,
    }
}

// ===========================================================================
// Recognizer (rung B: sorts {Int, Bool, Acc}, branching arms, P-STACK)
// ===========================================================================

/// The abstract value a walked local holds (per-path — branch walks clone the
/// binding state, so a binding is never consumed across an intervening write
/// or across branch joins).
#[derive(Debug, Clone)]
enum AbsVal {
    /// `&((*param) as V).f` where field `f` is a recursive `Arc` child
    /// (carries the field's recursor SLOT).
    ArcFieldRef(usize),
    /// `&((*param) as V).f` where MIR field `f` is a pinned `Box` recursive
    /// child (rung G, P-BOX-DEREF; carries the MIR FIELD index — the slot
    /// mapping happens at the fingerprinted subterm borrow). Its only legal
    /// consumer is the box-deref ub-check idiom.
    BoxFieldRef(usize),
    /// The fingerprint-validated raw pointer to Box MIR field `f`'s pointee
    /// (rung G): produced ONLY by the two-block box-deref idiom (both
    /// ub-check asserts premise-discharged under P-BOX-DEREF); consumed ONLY
    /// by `&(*raw)` / `&(*raw).k` subterm borrows.
    BoxSubtermPtr(usize),
    /// `&((*param) as V).f` where field `f` is an `Int` payload (slot index).
    IntFieldRef(usize),
    /// The deref of recursive slot `f` — a strict subterm handle (`&enum`).
    SubtermRef(usize),
    /// A resolved `Int`-sorted value.
    Int(FoldExpr),
    /// A resolved `Bool`-sorted value (rung B).
    Bool(FoldExpr),
    /// A `CheckedBinaryOp` result pair: `.0` = the value, `.1` = the overflow flag.
    CheckedPair(FoldExpr),
    /// A copy of the scrutinee reference itself (the parameter).
    ParamRef,
    /// The accumulator parameter, or a re-borrow of it (rung B).
    AccRef,
    /// A `&mut` borrow of a NON-accumulator local (rung B; only ever legal as
    /// an alias-kill witness).
    OtherMutBorrow(usize),
    /// A closure aggregate (rung B, P-STACK): name + resolved capture values.
    ClosureVal { name: String, caps: Vec<AbsVal> },
    /// A unit value (an accumulator-fold call's return).
    UnitVal,
    /// A locally-constructed aggregate (a REBUILT node — never a subterm).
    Rebuilt,
    /// A reference to a locally-rebuilt node.
    RebuiltRef,
    /// A foreign (non-self, non-pinned) call result — poison provenance.
    Foreign(String),
}

/// Recognize the structural-fold shape of `func` with NO sibling-body map
/// (rung-A compatible entry point: the `stack_safe` idiom can never resolve
/// without bodies and declines `stack_safe_drift`).
pub fn sem_structural_fold_shape_of(
    func: &VerifiableFunction,
) -> Result<SemStructFold, FoldDecline> {
    sem_structural_fold_shape_of_with_bodies(func, &DumpBodies::new())
}

/// Recognize the structural-fold shape of `func`, fail-closed with a NAMED
/// decline for everything outside the fragment. `bodies` is the sibling dump
/// map used to resolve `stack_safe` trampolines (P-STACK). See the module doc
/// for the exact fragment.
pub fn sem_structural_fold_shape_of_with_bodies(
    func: &VerifiableFunction,
    bodies: &DumpBodies,
) -> Result<SemStructFold, FoldDecline> {
    let body = &func.body;

    // (1) Result sort (rung B: the registration-family parameter; rung G item
    // G3 adds the depth-threaded value family).
    let second_param_is_int = body.locals.get(2).is_some_and(|l| matches!(l.ty, Ty::Int { .. }));
    let (sort, depth) = match (&body.return_ty, body.arg_count) {
        (Ty::Int { .. }, 1) => (FoldSort::Int, false),
        (Ty::Bool, 1) => (FoldSort::Bool, false),
        (Ty::Unit, 2) => (FoldSort::Acc, false),
        // Rung G (G3): a value-sorted fold threading ONE extra scalar `Int`
        // parameter (`has_free_variables_helper(&self, depth)`). A 2-param
        // value signature whose second parameter is NOT an Int scalar stays
        // the signature-family decline below (the binary tree fold
        // `is_isomorphic_to(&self, &other)` is a DIFFERENT, unmodeled family).
        (Ty::Int { .. }, 2) if second_param_is_int => (FoldSort::Int, true),
        (Ty::Bool, 2) if second_param_is_int => (FoldSort::Bool, true),
        // A Unit-returning traversal with a different arity is accumulator-
        // SHAPED but outside the one-accumulator model (e.g. clean-kernel's
        // `collect_params_impl` threads TWO accumulators) — name the param
        // shape, not the result sort.
        (Ty::Unit, n) => {
            return Err(FoldDecline::ParamShapeUnsupported(format!(
                "Unit-returning traversal with {n} params (rung B models exactly one \
                 folded param + one accumulator)"
            )));
        }
        _ => return Err(FoldDecline::NonIntReturn),
    };
    let depth_local: Option<usize> = depth.then_some(2);

    // (2) Self-recursive at all? (This lane certifies recursion.) A body whose
    // recursion is ONLY stack_safe-routed has no direct self call; admit it
    // here when any block builds a closure aggregate whose OWN body (from the
    // sibling map) calls back — the arm walk then enforces the full P-STACK
    // fingerprint fail-closed.
    let direct_self_recursive = body.blocks.iter().any(|b| {
        matches!(&b.terminator, Terminator::Call { func: callee, .. } if *callee == func.def_path)
    });
    let closure_self_recursive = body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| {
            let Statement::Assign {
                rvalue: Rvalue::Aggregate(AggregateKind::Closure { name, .. }, _),
                ..
            } = s
            else {
                return false;
            };
            bodies.get(name).is_some_and(|cb| {
                cb.body.blocks.iter().any(|cbb| {
                    matches!(&cbb.terminator, Terminator::Call { func: callee, .. }
                        if *callee == func.def_path)
                })
            })
        })
    });
    if !direct_self_recursive && !closure_self_recursive {
        return Err(FoldDecline::NotSelfRecursive);
    }

    // (3) Parameter shape: `&Enum` (immutable) at local 1; for `Acc` folds
    // additionally exactly one `&mut HashSet<..>` accumulator at local 2.
    let param_ty = &body
        .locals
        .get(1)
        .ok_or_else(|| FoldDecline::ParamShapeUnsupported("missing parameter local".to_string()))?
        .ty;
    let Ty::Ref { mutable: false, inner } = param_ty else {
        return Err(FoldDecline::ParamShapeUnsupported(
            "parameter is not an immutable reference".to_string(),
        ));
    };
    let Ty::Adt { name: enum_name, variants, .. } = inner.as_ref() else {
        return Err(FoldDecline::ParamShapeUnsupported(
            "parameter pointee is not a modeled enum".to_string(),
        ));
    };
    if variants.len() < 2 {
        return Err(FoldDecline::ParamShapeUnsupported(
            "pointee enum has < 2 variants".to_string(),
        ));
    }
    // NB deliberately NO `disc_index_safe` gate here (rung B; module doc item
    // 8): the tag→variant map below is over LOGICAL discriminants, whose
    // soundness for every layout encoding is certified by the required
    // TyCtxt-vetted `exhaustive_enum_unreachable` flag (case set ==
    // `adt_def.discriminants`), stamped only for genuine
    // `SwitchInt(Discriminant(..))` selectors.
    let acc_local: Option<usize> = match sort {
        FoldSort::Acc => {
            let acc_ty = &body
                .locals
                .get(2)
                .ok_or_else(|| {
                    FoldDecline::ParamShapeUnsupported("missing accumulator local".to_string())
                })?
                .ty;
            let Ty::Ref { mutable: true, inner } = acc_ty else {
                return Err(FoldDecline::ParamShapeUnsupported(
                    "second parameter is not a mutable reference".to_string(),
                ));
            };
            let Ty::Adt { name, .. } = inner.as_ref() else {
                return Err(FoldDecline::ParamShapeUnsupported(
                    "accumulator pointee is not the pinned container".to_string(),
                ));
            };
            if name != HASHSET_NAME {
                return Err(FoldDecline::ParamShapeUnsupported(format!(
                    "accumulator container {name} is not the pinned {HASHSET_NAME}"
                )));
            }
            Some(2)
        }
        _ => None,
    };

    // (4) Field classification from the dump's own type info: Int payload,
    // pinned Arc<enum> / Box<enum> / Box<(enum, enum)> recursive child (rung
    // G items G1a + G2), or (rung B) an OPAQUE atom whose every read declines.
    let plans: Vec<VariantPlan> = variants.iter().map(|v| VariantPlan::of(v, enum_name)).collect();

    // (5) Global fail-closed scans: no parameter (folded / accumulator /
    // threaded depth) is ever written; no raw borrow anywhere; for value
    // sorts no mutable borrow anywhere (so the immutable copy/move chains the
    // walker follows can never be invalidated by an aliased write).
    // Accumulator folds handle `&mut` borrows in the arm walk (each one must
    // resolve to a modeled role or decline by name).
    for b in &body.blocks {
        for s in &b.stmts {
            match s {
                Statement::Assign { place, rvalue, .. } => {
                    if place.local == 1
                        || Some(place.local) == acc_local
                        || Some(place.local) == depth_local
                    {
                        return Err(FoldDecline::ParamReassigned);
                    }
                    match rvalue {
                        Rvalue::Ref { mutable: true, .. } if acc_local.is_none() => {
                            return Err(FoldDecline::UnsupportedArmStatement(
                                "mutable borrow".to_string(),
                            ));
                        }
                        Rvalue::AddressOf(..) => {
                            return Err(FoldDecline::UnsupportedArmStatement(
                                "raw address-of".to_string(),
                            ));
                        }
                        _ => {}
                    }
                }
                Statement::SetDiscriminant { place, .. }
                    if place.local == 1
                        || Some(place.local) == acc_local
                        || Some(place.local) == depth_local =>
                {
                    return Err(FoldDecline::ParamReassigned);
                }
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &b.terminator {
            if dest.local == 1 || Some(dest.local) == acc_local || Some(dest.local) == depth_local {
                return Err(FoldDecline::ParamReassigned);
            }
        }
    }

    // (6) Entry block: exactly `d := Discriminant(*param)` + `SwitchInt(d)`.
    let entry = block_by_id(body, BlockId(0))
        .ok_or_else(|| FoldDecline::UnsupportedEntryBlock("no entry block".to_string()))?;
    let mut discr_local: Option<usize> = None;
    for s in &entry.stmts {
        match s {
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {}
            Statement::Assign { place, rvalue: Rvalue::Discriminant(p), .. }
                if place.projections.is_empty()
                    && p.local == 1
                    && p.projections == vec![Projection::Deref] =>
            {
                if discr_local.replace(place.local).is_some() {
                    return Err(FoldDecline::UnsupportedEntryBlock(
                        "two discriminant reads".to_string(),
                    ));
                }
            }
            other => {
                return Err(FoldDecline::UnsupportedEntryBlock(format!(
                    "unmodeled entry statement {other:?}"
                )));
            }
        }
    }
    let Some(d) = discr_local else {
        return Err(FoldDecline::NonDiscriminantSwitch);
    };
    // The discriminant temp must be single-assignment across the whole body.
    if crate::prove::local_write_count(body, d) != 1 {
        return Err(FoldDecline::NonDiscriminantSwitch);
    }
    let Terminator::SwitchInt { discr, targets, otherwise, exhaustive_enum_unreachable, .. } =
        &entry.terminator
    else {
        return Err(FoldDecline::UnsupportedEntryBlock("entry is not a SwitchInt".to_string()));
    };
    let (Operand::Copy(dp) | Operand::Move(dp)) = discr else {
        return Err(FoldDecline::NonDiscriminantSwitch);
    };
    if dp.local != d || !dp.projections.is_empty() {
        return Err(FoldDecline::NonDiscriminantSwitch);
    }

    // (7) TOTAL tag→variant map, read from the dump type info's OWN
    // discriminant values (never tag == declaration index): every variant an
    // explicit target, `otherwise` → `Unreachable`, and the TyCtxt-vetted
    // exhaustiveness flag (which certifies case set == the enum's LOGICAL
    // discriminant set — the niche-layout-proof anchor, module doc item 8).
    if !exhaustive_enum_unreachable {
        return Err(FoldDecline::UnmappedSwitchTarget(
            "switch lacks the TyCtxt-vetted exhaustive_enum_unreachable flag".to_string(),
        ));
    }
    let otherwise_block = block_by_id(body, *otherwise)
        .ok_or_else(|| FoldDecline::UnmappedSwitchTarget("missing otherwise block".to_string()))?;
    if !matches!(otherwise_block.terminator, Terminator::Unreachable) {
        return Err(FoldDecline::UnmappedSwitchTarget(
            "otherwise target is reachable (not Unreachable)".to_string(),
        ));
    }
    if targets.len() != variants.len() {
        return Err(FoldDecline::UnmappedSwitchTarget(format!(
            "{} switch targets for {} variants",
            targets.len(),
            variants.len()
        )));
    }
    // tag value → (variant declaration index, arm block); each variant exactly
    // once. Rung B: DISTINCT variants may share one arm BLOCK (`A | B =>` — the
    // walk is per-variant, so variant-specific reads still fail per-walk).
    let mut arm_of_variant: Vec<Option<BlockId>> = vec![None; variants.len()];
    for (tag_u, blk) in targets {
        let Ok(tag) = i128::try_from(*tag_u) else {
            return Err(FoldDecline::UnmappedSwitchTarget(format!(
                "switch tag {tag_u} exceeds the modeled i128 range"
            )));
        };
        let matching: Vec<usize> = variants
            .iter()
            .enumerate()
            .filter(|(_, v)| v.discriminant == tag)
            .map(|(i, _)| i)
            .collect();
        let [v_idx] = matching.as_slice() else {
            return Err(FoldDecline::UnmappedSwitchTarget(format!(
                "switch tag {tag} matches {} variant discriminants",
                matching.len()
            )));
        };
        if arm_of_variant[*v_idx].replace(*blk).is_some() {
            return Err(FoldDecline::UnmappedSwitchTarget(format!(
                "variant index {v_idx} targeted twice"
            )));
        }
    }

    // (8) The global never-read set for the pinned insert op's bool result
    // (rung B, design §4 rule ii — fail-closed: an unrecognized statement /
    // terminator class marks EVERYTHING read, so approval is impossible).
    let read_locals = body_read_locals(body);

    // (9) Per-variant arm walk.
    let ctx =
        ArmCtx { func, bodies, enum_name, sort, acc_local, depth_local, read_locals: &read_locals };
    let mut out_variants: Vec<FoldVariant> = Vec::with_capacity(variants.len());
    for (v_idx, v) in variants.iter().enumerate() {
        let arm_block = arm_of_variant[v_idx].ok_or_else(|| {
            FoldDecline::UnmappedSwitchTarget(format!("variant {} has no arm", v.name))
        })?;
        let arm = walk_arm(&ctx, v_idx, &plans[v_idx], arm_block)?;
        out_variants.push(FoldVariant {
            name: v.name.clone(),
            tag: v.discriminant,
            fields: plans[v_idx].slots.clone(),
            arm,
        });
    }

    // (10) Rung G (P-BOX-DEREF) whole-body audit, fail-closed: EVERY
    // Misaligned / null-custom ub-check assert in the body — including any
    // block no arm path walked — must be a structurally valid fingerprint
    // pair, so the premise's discharge scope is EXACTLY the pinned idiom.
    audit_box_ubchecks(body, enum_name)?;

    Ok(SemStructFold { enum_name: enum_name.clone(), sort, depth, variants: out_variants })
}

fn block_by_id(body: &trust_types::VerifiableBody, id: BlockId) -> Option<&BasicBlock> {
    body.blocks.iter().find(|b| b.id == id)
}

/// Whether `place` is exactly `((*param) as <variant v>).<field f>` — the
/// matched-variant payload projection.
fn variant_field_place(place: &Place, v_idx: usize) -> Option<usize> {
    if place.local != 1 {
        return None;
    }
    match place.projections.as_slice() {
        [Projection::Deref, Projection::Downcast(v), Projection::Field(f)] if *v == v_idx => {
            Some(*f)
        }
        _ => None,
    }
}

// ===========================================================================
// Rung G: per-variant field plans (MIR-field view vs recursor-slot view)
// ===========================================================================

/// A MIR field's pointer-family classification (rung G).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MirFieldShape {
    /// Scalar Int payload — one `PayloadInt` slot.
    Int,
    /// `Arc<enum>` recursive child (P-ARC-DEREF) — one `Recursive` slot.
    ArcRec,
    /// `Box<enum>` recursive child (P-BOX-DEREF, G1) — one `Recursive` slot.
    BoxRec,
    /// `Box<(enum, enum)>` recursive PAIR (P-BOX-DEREF, G2) — TWO
    /// consecutive `Recursive` slots (per-component IH positions).
    BoxRecPair,
    /// Anything else — one opaque atom slot; every read declines.
    Opaque,
}

/// One MIR field's classification + its FIRST recursor slot (`slot`, and
/// `slot + 1` for a `BoxRecPair`'s second component).
#[derive(Debug, Clone, Copy)]
struct MirField {
    shape: MirFieldShape,
    slot: usize,
}

/// Per-variant field plan: the MIR-field view (what the walker resolves
/// projections against) and the recursor SLOT view (what the Clean side
/// registers — one constructor argument per slot). For Arc/Int/opaque fields
/// the two coincide; a boxed 2-tuple child (G2) is ONE MIR field carrying TWO
/// recursive slots.
#[derive(Debug, Clone)]
struct VariantPlan {
    mir: Vec<MirField>,
    slots: Vec<FoldFieldKind>,
}

fn classify_mir_field(fty: &Ty, enum_name: &str) -> MirFieldShape {
    if matches!(fty, Ty::Int { .. }) {
        return MirFieldShape::Int;
    }
    if arc_pointee_ty(fty).is_some_and(|p| ty_names_enum(p, enum_name)) {
        return MirFieldShape::ArcRec;
    }
    match box_recursive_form(fty, enum_name) {
        Some(false) => MirFieldShape::BoxRec,
        Some(true) => MirFieldShape::BoxRecPair,
        None => MirFieldShape::Opaque,
    }
}

impl VariantPlan {
    fn of(v: &trust_types::VariantDef, enum_name: &str) -> VariantPlan {
        let mut mir = Vec::with_capacity(v.fields.len());
        let mut slots = Vec::new();
        for (_, fty) in &v.fields {
            let shape = classify_mir_field(fty, enum_name);
            mir.push(MirField { shape, slot: slots.len() });
            match shape {
                MirFieldShape::Int => slots.push(FoldFieldKind::PayloadInt),
                MirFieldShape::ArcRec | MirFieldShape::BoxRec => {
                    slots.push(FoldFieldKind::Recursive);
                }
                MirFieldShape::BoxRecPair => {
                    slots.push(FoldFieldKind::Recursive);
                    slots.push(FoldFieldKind::Recursive);
                }
                MirFieldShape::Opaque => slots.push(FoldFieldKind::PayloadOpaque),
            }
        }
        VariantPlan { mir, slots }
    }
}

/// All locals READ anywhere in the body (operand copies/moves, borrowed /
/// projected / discriminated / dropped places, switch selectors, assert
/// conditions, call arguments…). FAIL-CLOSED: any statement / terminator /
/// rvalue class this collector does not enumerate marks ALL locals read, so
/// the insert-result-discarded approval (rung B) can never be granted through
/// an unmodeled read channel.
fn body_read_locals(body: &trust_types::VerifiableBody) -> std::collections::BTreeSet<usize> {
    use std::collections::BTreeSet;
    let mut reads: BTreeSet<usize> = BTreeSet::new();
    let all: BTreeSet<usize> = (0..body.locals.len()).collect();
    let read_op = |op: &Operand, reads: &mut BTreeSet<usize>| {
        if let Operand::Copy(p) | Operand::Move(p) = op {
            reads.insert(p.local);
        }
    };
    for b in &body.blocks {
        for s in &b.stmts {
            match s {
                Statement::Assign { place, rvalue, .. } => {
                    // A projected destination reads its base local.
                    if !place.projections.is_empty() {
                        reads.insert(place.local);
                    }
                    match rvalue {
                        Rvalue::Use(op)
                        | Rvalue::UnaryOp(_, op)
                        | Rvalue::Cast(op, _)
                        | Rvalue::Repeat(op, _) => read_op(op, &mut reads),
                        Rvalue::BinaryOp(_, a, b2) | Rvalue::CheckedBinaryOp(_, a, b2) => {
                            read_op(a, &mut reads);
                            read_op(b2, &mut reads);
                        }
                        Rvalue::Ref { place: p, .. }
                        | Rvalue::Discriminant(p)
                        | Rvalue::Len(p)
                        | Rvalue::AddressOf(_, p)
                        | Rvalue::CopyForDeref(p) => {
                            reads.insert(p.local);
                        }
                        Rvalue::Aggregate(_, ops) => {
                            for op in ops {
                                read_op(op, &mut reads);
                            }
                        }
                        _ => return all, // unmodeled rvalue: everything is read
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Nop
                | Statement::Coverage
                | Statement::ConstEvalCounter => {}
                Statement::PlaceMention(p) => {
                    reads.insert(p.local);
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    reads.insert(place.local);
                }
                _ => return all, // unmodeled statement: everything is read
            }
        }
        match &b.terminator {
            // `Resume` (the unwind re-raise; a value-read-free control sink —
            // see its `write_effect` classification) reads nothing: the drops
            // on the unwind path are their own `Drop` terminators below.
            Terminator::Goto(_)
            | Terminator::Return
            | Terminator::Unreachable
            | Terminator::Resume => {}
            Terminator::SwitchInt { discr, .. } => read_op(discr, &mut reads),
            Terminator::Call { args, dest, .. } => {
                for a in args {
                    read_op(a, &mut reads);
                }
                if !dest.projections.is_empty() {
                    reads.insert(dest.local);
                }
            }
            Terminator::Assert { cond, .. } => read_op(cond, &mut reads),
            Terminator::Drop { place, .. } => {
                reads.insert(place.local);
            }
            _ => return all, // unmodeled terminator (Resume, …): everything is read
        }
    }
    // `Return` reads the return local.
    reads.insert(0);
    reads
}

/// Shared per-walk context.
struct ArmCtx<'a> {
    func: &'a VerifiableFunction,
    bodies: &'a DumpBodies,
    enum_name: &'a str,
    sort: FoldSort,
    acc_local: Option<usize>,
    /// Rung G (G3): the threaded scalar parameter's local (always 2), when
    /// the signature is the depth-fold family.
    depth_local: Option<usize>,
    read_locals: &'a std::collections::BTreeSet<usize>,
}

/// Per-path walk state (cloned at branches).
#[derive(Clone)]
struct WalkState {
    map: BTreeMap<usize, AbsVal>,
    used_rec_fields: std::collections::BTreeSet<usize>,
    visited: std::collections::BTreeSet<usize>,
    acc_state: FoldExpr,
    ret_written: bool,
}

/// Walk one arm (straight-line + rung-B bool branching) and reconstruct its
/// value expression. Fail-closed at every step; see the module doc for the
/// admitted vocabulary.
fn walk_arm(
    ctx: &ArmCtx<'_>,
    v_idx: usize,
    plan: &VariantPlan,
    start: BlockId,
) -> Result<FoldExpr, FoldDecline> {
    let state = WalkState {
        map: BTreeMap::new(),
        used_rec_fields: std::collections::BTreeSet::new(),
        visited: std::collections::BTreeSet::new(),
        acc_state: FoldExpr::AccParam,
        ret_written: false,
    };
    walk_from(ctx, v_idx, plan, start, state, 0)
}

/// Maximum branch-recursion depth (paranoid bound; real arms are tiny).
const MAX_BRANCH_DEPTH: usize = 32;

#[allow(clippy::too_many_lines)]
fn walk_from(
    ctx: &ArmCtx<'_>,
    v_idx: usize,
    plan: &VariantPlan,
    start: BlockId,
    mut st: WalkState,
    depth: usize,
) -> Result<FoldExpr, FoldDecline> {
    if depth > MAX_BRANCH_DEPTH {
        return Err(FoldDecline::UnsupportedArmTerminator("branch depth exceeded".to_string()));
    }
    let body = &ctx.func.body;
    let mut cur = start;

    loop {
        if !st.visited.insert(cur.0) {
            return Err(FoldDecline::UnsupportedArmTerminator("loop in arm".to_string()));
        }
        let block = block_by_id(body, cur).ok_or_else(|| {
            FoldDecline::UnsupportedArmTerminator(format!("missing block bb{}", cur.0))
        })?;

        // Rung G (P-BOX-DEREF): a block ending in the compiler's ALIGNMENT
        // ub-check assert claims to be the built-in box-deref idiom —
        // validate the whole two-block fingerprint fail-closed (every drift
        // is the NAMED `box_deref_drift` decline), bind the raw subterm
        // pointer, and continue past the NULL check block. NONE of the
        // idiom's address-arithmetic temps are bound, so pointer values can
        // never leak into the fold's Int lane.
        if matches!(
            &block.terminator,
            Terminator::Assert { msg: AssertMessage::MisalignedPointerDereference, .. }
        ) {
            let idiom = box_deref_idiom_of_block(ctx, v_idx, plan, block, &st.map)?;
            if !st.visited.insert(idiom.null_block.0) {
                return Err(FoldDecline::UnsupportedArmTerminator("loop in arm".to_string()));
            }
            if let Some((lead_local, f)) = idiom.lead_binding {
                st.map.insert(lead_local, AbsVal::BoxFieldRef(f));
            }
            st.map.insert(idiom.raw_local, AbsVal::BoxSubtermPtr(idiom.field));
            cur = idiom.cont;
            continue;
        }

        for s in &block.stmts {
            match s {
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Nop
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::PlaceMention(_) => {}
                Statement::Assign { place, rvalue, .. } => {
                    if !place.projections.is_empty() {
                        return Err(FoldDecline::UnsupportedArmStatement(
                            "projected place write".to_string(),
                        ));
                    }
                    let val: AbsVal = match rvalue {
                        Rvalue::Ref { mutable: false, place: p } => {
                            resolve_shared_borrow(ctx, v_idx, plan, p, &st.map)?
                        }
                        Rvalue::Ref { mutable: true, place: p } => {
                            // Rung B (acc folds only — value sorts declined in
                            // the global scan): a mutable borrow is admitted as
                            // a VALUE only; its only legal consumers are the
                            // pinned insert / self-call accumulator positions.
                            if Some(p.local) == ctx.acc_local
                                && (p.projections.is_empty()
                                    || p.projections == vec![Projection::Deref])
                            {
                                AbsVal::AccRef
                            } else if p.projections.is_empty() {
                                AbsVal::OtherMutBorrow(p.local)
                            } else {
                                return Err(FoldDecline::UnsupportedArmStatement(format!(
                                    "mutable borrow of unmodeled place {p:?}"
                                )));
                            }
                        }
                        Rvalue::Use(op) => resolve_operand(ctx, v_idx, plan, op, &st.map)?,
                        Rvalue::BinaryOp(op, a, b) => {
                            let ra = resolve_operand(ctx, v_idx, plan, a, &st.map)?;
                            let rb = resolve_operand(ctx, v_idx, plan, b, &st.map)?;
                            if let Some(fop) = FoldBinOp::of_mir(*op) {
                                AbsVal::Int(FoldExpr::Bin(
                                    fop,
                                    Box::new(as_int(ra)?),
                                    Box::new(as_int(rb)?),
                                ))
                            } else if let Some(cop) = FoldCmpOp::of_mir(*op) {
                                // Rung B: Int comparison as a Bool leaf.
                                AbsVal::Bool(FoldExpr::Cmp(
                                    cop,
                                    Box::new(as_int(ra)?),
                                    Box::new(as_int(rb)?),
                                ))
                            } else {
                                return Err(FoldDecline::UnsupportedBinOp(format!("{op:?}")));
                            }
                        }
                        Rvalue::CheckedBinaryOp(op, a, b) => {
                            let Some(fop) = FoldBinOp::of_mir(*op) else {
                                return Err(FoldDecline::UnsupportedBinOp(format!(
                                    "checked {op:?}"
                                )));
                            };
                            let ra = as_int(resolve_operand(ctx, v_idx, plan, a, &st.map)?)?;
                            let rb = as_int(resolve_operand(ctx, v_idx, plan, b, &st.map)?)?;
                            AbsVal::CheckedPair(FoldExpr::Bin(fop, Box::new(ra), Box::new(rb)))
                        }
                        Rvalue::Aggregate(AggregateKind::Closure { name, .. }, ops) => {
                            // Rung B (P-STACK): a closure aggregate is a VALUE
                            // whose captures are resolved NOW (program order);
                            // its only legal consumer is a fingerprinted
                            // stack_safe call. Accumulator folds admit NO
                            // closures at rung B (a capture could smuggle the
                            // accumulator past the foreign-call escape scan).
                            if ctx.sort == FoldSort::Acc {
                                return Err(FoldDecline::AccumulatorEscape(
                                    "closure aggregate in an accumulator arm (a capture \
                                     could carry the accumulator; rung B admits none)"
                                        .to_string(),
                                ));
                            }
                            let mut caps = Vec::with_capacity(ops.len());
                            for op in ops {
                                caps.push(resolve_operand(ctx, v_idx, plan, op, &st.map)?);
                            }
                            AbsVal::ClosureVal { name: name.clone(), caps }
                        }
                        Rvalue::Aggregate(_, ops) => {
                            // Accumulator folds: a non-closure aggregate must
                            // not embed the accumulator either (design §4 rule
                            // iii — no unmodeled channel may carry it).
                            if ctx.sort == FoldSort::Acc {
                                for op in ops {
                                    if let Operand::Copy(p) | Operand::Move(p) = op {
                                        let tainted = Some(p.local) == ctx.acc_local
                                            || matches!(
                                                st.map.get(&p.local),
                                                Some(AbsVal::AccRef | AbsVal::OtherMutBorrow(_))
                                            );
                                        if tainted {
                                            return Err(FoldDecline::AccumulatorEscape(
                                                "the accumulator is packed into an aggregate"
                                                    .to_string(),
                                            ));
                                        }
                                    }
                                }
                            }
                            AbsVal::Rebuilt
                        }
                        other => {
                            return Err(FoldDecline::UnsupportedArmStatement(format!(
                                "unmodeled rvalue {other:?}"
                            )));
                        }
                    };
                    if place.local == 0 {
                        if st.ret_written {
                            return Err(FoldDecline::UnsupportedArmStatement(
                                "return local written twice on one arm path".to_string(),
                            ));
                        }
                        st.ret_written = true;
                    }
                    st.map.insert(place.local, val);
                }
                other => {
                    return Err(FoldDecline::UnsupportedArmStatement(format!(
                        "unmodeled statement {other:?}"
                    )));
                }
            }
        }

        match &block.terminator {
            Terminator::Goto(next) => {
                cur = *next;
            }
            Terminator::Return => {
                return match ctx.sort {
                    FoldSort::Acc => Ok(st.acc_state),
                    FoldSort::Int => match st.map.get(&0) {
                        Some(AbsVal::Int(e)) => Ok(e.clone()),
                        Some(AbsVal::Foreign(who)) => {
                            Err(FoldDecline::ForeignValueInArm(who.clone()))
                        }
                        Some(other) => Err(FoldDecline::UnsupportedArmStatement(format!(
                            "non-Int return value {other:?}"
                        ))),
                        None => Err(FoldDecline::UnsupportedArmStatement(
                            "no return write on arm path".to_string(),
                        )),
                    },
                    FoldSort::Bool => match st.map.get(&0) {
                        Some(AbsVal::Bool(e)) => Ok(e.clone()),
                        Some(AbsVal::Foreign(who)) => {
                            Err(FoldDecline::ForeignValueInArm(who.clone()))
                        }
                        Some(other) => Err(FoldDecline::UnsupportedArmStatement(format!(
                            "non-Bool return value {other:?}"
                        ))),
                        None => Err(FoldDecline::UnsupportedArmStatement(
                            "no return write on arm path".to_string(),
                        )),
                    },
                };
            }
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                // Rung B: a BOOL branch (short-circuit &&/|| lowering) — the
                // selector must be a Bool-typed, Bool-valued local; the shape
                // exactly `[(0, else_bb)]` + otherwise = then_bb.
                if ctx.sort == FoldSort::Acc {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "branch in an accumulator arm (rung-B accumulator arms are \
                         straight-line; the exact insert sequence is the claim)"
                            .to_string(),
                    ));
                }
                let (Operand::Copy(dp) | Operand::Move(dp)) = discr else {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "switch on unmodeled selector".to_string(),
                    ));
                };
                if !dp.projections.is_empty() {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "switch on projected selector".to_string(),
                    ));
                }
                let selector_is_bool =
                    ctx.func.body.locals.get(dp.local).is_some_and(|l| matches!(l.ty, Ty::Bool));
                if !selector_is_bool {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "switch on a non-Bool selector inside an arm".to_string(),
                    ));
                }
                let Some(AbsVal::Bool(cond)) = st.map.get(&dp.local).cloned() else {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "switch on an unresolved Bool selector".to_string(),
                    ));
                };
                let [(0, else_bb)] = targets.as_slice() else {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "bool switch whose targets are not exactly [(0, else)]".to_string(),
                    ));
                };
                let then_val = walk_from(ctx, v_idx, plan, *otherwise, st.clone(), depth + 1)?;
                let else_val = walk_from(ctx, v_idx, plan, *else_bb, st, depth + 1)?;
                return Ok(FoldExpr::Cond(Box::new(cond), Box::new(then_val), Box::new(else_val)));
            }
            Terminator::Call { func: callee, args, dest, target, .. } => {
                if !dest.projections.is_empty() {
                    return Err(FoldDecline::UnsupportedArmStatement(
                        "projected call destination".to_string(),
                    ));
                }
                let Some(target) = target else {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "diverging call".to_string(),
                    ));
                };
                let val: AbsVal = if *callee == ctx.func.def_path {
                    // SELF call — the IH-slot mapping. Admitted ONLY with a
                    // strict-subterm argument (design §3.2 / §6); accumulator
                    // folds additionally require the threaded accumulator
                    // (design §4 rule i); depth folds (rung G item G3) carry
                    // the recognizer-resolved Int argument into the IH
                    // application.
                    let (node_arg, acc_arg, depth_arg) =
                        match (ctx.sort, ctx.depth_local.is_some(), args.as_slice()) {
                            (FoldSort::Acc, false, [n, a]) => (n, Some(a), None),
                            (FoldSort::Acc, _, _) => {
                                return Err(FoldDecline::UnsupportedArmStatement(format!(
                                    "accumulator self call with {} arguments",
                                    args.len()
                                )));
                            }
                            (_, true, [n, d]) => (n, None, Some(d)),
                            (_, false, [n]) => (n, None, None),
                            _ => {
                                return Err(FoldDecline::UnsupportedArmStatement(format!(
                                    "self call with {} arguments",
                                    args.len()
                                )));
                            }
                        };
                    let f = subterm_field_of_arg(ctx, node_arg, &st.map)?;
                    if !st.used_rec_fields.insert(f) {
                        return Err(FoldDecline::DuplicateRecursiveCall);
                    }
                    if let Some(acc_arg) = acc_arg {
                        check_acc_threading(ctx, acc_arg, &st.map)?;
                        st.acc_state = FoldExpr::AccRec(f, Box::new(st.acc_state.clone()));
                        AbsVal::UnitVal
                    } else if let Some(d_arg) = depth_arg {
                        let d_expr = as_int(resolve_operand(ctx, v_idx, plan, d_arg, &st.map)?)?;
                        let e = FoldExpr::IhApp(f, Box::new(d_expr));
                        match ctx.sort {
                            FoldSort::Int => AbsVal::Int(e),
                            FoldSort::Bool => AbsVal::Bool(e),
                            FoldSort::Acc => unreachable!("depth is never combined with Acc"),
                        }
                    } else {
                        match ctx.sort {
                            FoldSort::Int => AbsVal::Int(FoldExpr::Ih(f)),
                            FoldSort::Bool => AbsVal::Bool(FoldExpr::Ih(f)),
                            FoldSort::Acc => unreachable!("acc_arg is Some for Acc"),
                        }
                    }
                } else if *callee == ARC_DEREF_CALLEE {
                    // Pinned Arc-deref idiom (P-ARC-DEREF).
                    let [Operand::Copy(p) | Operand::Move(p)] = args.as_slice() else {
                        return Err(FoldDecline::UnsupportedArmStatement(
                            "deref call with unmodeled arguments".to_string(),
                        ));
                    };
                    if !p.projections.is_empty() {
                        return Err(FoldDecline::UnsupportedArmStatement(
                            "deref of a projected place".to_string(),
                        ));
                    }
                    let Some(AbsVal::ArcFieldRef(f)) = st.map.get(&p.local).cloned() else {
                        return Err(FoldDecline::UnsupportedArmStatement(
                            "Deref::deref of a non-Arc-field reference".to_string(),
                        ));
                    };
                    // The argument's declared type must be `&std::sync::Arc<..>`
                    // and the destination's `&<enum>` (both from the dump's own
                    // local declarations).
                    let arg_ok = body.locals.get(p.local).is_some_and(|l| {
                        matches!(&l.ty, Ty::Ref { mutable: false, inner }
                            if matches!(inner.as_ref(), Ty::Adt { name, .. } if name == ARC_NAME))
                    });
                    let dest_ok = body.locals.get(dest.local).is_some_and(|l| {
                        matches!(&l.ty, Ty::Ref { mutable: false, inner }
                            if ty_names_enum(inner, ctx.enum_name))
                    });
                    if !arg_ok || !dest_ok {
                        return Err(FoldDecline::UnsupportedArmStatement(
                            "Deref::deref whose argument/destination types do not pin \
                             Arc<enum> → &enum"
                                .to_string(),
                        ));
                    }
                    AbsVal::SubtermRef(f)
                } else if ctx.sort == FoldSort::Acc && *callee == HASHSET_INSERT_CALLEE {
                    // Rung B: the pinned insert op (design §4 rule ii — the
                    // bool result must be DISCARDED; the global never-read set
                    // is the fail-closed witness).
                    let [acc_op, val_op] = args.as_slice() else {
                        return Err(FoldDecline::UnsupportedArmStatement(format!(
                            "insert with {} arguments",
                            args.len()
                        )));
                    };
                    check_acc_threading(ctx, acc_op, &st.map)?;
                    let v = as_int(resolve_operand(ctx, v_idx, plan, val_op, &st.map)?)?;
                    if dest.local == 0 || ctx.read_locals.contains(&dest.local) {
                        return Err(FoldDecline::AccumulatorRead(
                            "the pinned insert's bool result is consumed (control flow \
                             must never be accumulator-dependent)"
                                .to_string(),
                        ));
                    }
                    st.acc_state = FoldExpr::AccInsert(Box::new(st.acc_state.clone()), Box::new(v));
                    // Deliberately NOT bound in the map: the never-read check
                    // above already guarantees no later use; leaving it
                    // unbound makes any missed use fail closed too.
                    cur = *target;
                    continue;
                } else {
                    // Rung B (P-STACK): a stack_safe trampoline call — the
                    // fingerprinted recursion route. Recognized BEFORE the
                    // foreign-poison fallback; every drift declines by name.
                    if let Some(res) = try_stack_safe_recursion(ctx, callee, args, &st.map) {
                        let f = res?;
                        if !st.used_rec_fields.insert(f) {
                            return Err(FoldDecline::DuplicateRecursiveCall);
                        }
                        match ctx.sort {
                            FoldSort::Int => AbsVal::Int(FoldExpr::Ih(f)),
                            FoldSort::Bool => AbsVal::Bool(FoldExpr::Ih(f)),
                            FoldSort::Acc => {
                                return Err(FoldDecline::StackSafeDrift(
                                    "stack_safe-routed recursion inside an accumulator fold \
                                     is outside rung B (Expr-scale rungs)"
                                        .to_string(),
                                ));
                            }
                        }
                    } else {
                        // Foreign callee. Accumulator folds: the accumulator
                        // must never reach it (design §4 rule iii) — directly,
                        // as a re-borrow, or through a double-reference to a
                        // local that holds it.
                        if ctx.sort == FoldSort::Acc {
                            for a in args {
                                if let Operand::Copy(p) | Operand::Move(p) = a {
                                    let is_acc = Some(p.local) == ctx.acc_local
                                        || match st.map.get(&p.local) {
                                            Some(AbsVal::AccRef) => true,
                                            Some(AbsVal::OtherMutBorrow(l)) => {
                                                matches!(st.map.get(l), Some(AbsVal::AccRef))
                                            }
                                            _ => false,
                                        };
                                    if is_acc {
                                        return Err(FoldDecline::AccumulatorEscape(format!(
                                            "the accumulator is passed to foreign callee \
                                             {callee}"
                                        )));
                                    }
                                }
                            }
                        }
                        // Poison provenance (a later use in a recursive-arg /
                        // return position declines by name).
                        AbsVal::Foreign(callee.clone())
                    }
                };
                if dest.local == 0 {
                    if st.ret_written {
                        return Err(FoldDecline::UnsupportedArmStatement(
                            "return local written twice on one arm path".to_string(),
                        ));
                    }
                    st.ret_written = true;
                }
                st.map.insert(dest.local, val);
                cur = *target;
            }
            Terminator::Assert { cond, expected, msg, target, .. } => {
                // Rung G (P-BOX-DEREF): ub-check asserts are legal ONLY inside
                // the fingerprinted idiom — the alignment head is intercepted
                // at block entry, so reaching one here (e.g. a jump straight
                // into a null-check block) is CFG drift, by name.
                if matches!(msg, AssertMessage::MisalignedPointerDereference)
                    || matches!(msg, AssertMessage::Custom(m) if m == BOX_NULL_ASSERT_MSG)
                {
                    return Err(FoldDecline::BoxDerefDrift(
                        "ub-check assert reached outside the pinned box-deref idiom".to_string(),
                    ));
                }
                // Admit ONLY the checked-binop overflow assert on its happy
                // path: cond = Move/Copy(pair.1), expected = false. The
                // overflow OBLIGATION is the safety pillar's separate burden.
                if *expected {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "assert with expected=true".to_string(),
                    ));
                }
                let (Operand::Move(p) | Operand::Copy(p)) = cond else {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "assert on unmodeled condition".to_string(),
                    ));
                };
                let is_checked_flag = p.projections == vec![Projection::Field(1)]
                    && matches!(st.map.get(&p.local), Some(AbsVal::CheckedPair(_)));
                if !is_checked_flag {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "assert not the checked-op overflow flag".to_string(),
                    ));
                }
                cur = *target;
            }
            Terminator::Drop { place, target, .. } => {
                // Dropping a local temp changes no modeled value; continue.
                if place.local == 0 || place.local == 1 || Some(place.local) == ctx.acc_local {
                    return Err(FoldDecline::UnsupportedArmTerminator(
                        "drop of the return/parameter local".to_string(),
                    ));
                }
                cur = *target;
            }
            other => {
                return Err(FoldDecline::UnsupportedArmTerminator(format!("{other:?}")));
            }
        }
    }
}

/// Resolve a shared (`&`) borrow rvalue to its abstract value.
fn resolve_shared_borrow(
    ctx: &ArmCtx<'_>,
    v_idx: usize,
    plan: &VariantPlan,
    p: &Place,
    map: &BTreeMap<usize, AbsVal>,
) -> Result<AbsVal, FoldDecline> {
    if let Some(f) = variant_field_place(p, v_idx) {
        return match plan.mir.get(f) {
            Some(MirField { shape: MirFieldShape::ArcRec, slot }) => Ok(AbsVal::ArcFieldRef(*slot)),
            // Rung G: the Box child field ref — carries the MIR field index;
            // its only legal consumer is the fingerprinted deref idiom.
            Some(MirField { shape: MirFieldShape::BoxRec | MirFieldShape::BoxRecPair, .. }) => {
                Ok(AbsVal::BoxFieldRef(f))
            }
            Some(MirField { shape: MirFieldShape::Int, slot }) => Ok(AbsVal::IntFieldRef(*slot)),
            Some(MirField { shape: MirFieldShape::Opaque, .. }) => {
                Err(FoldDecline::OpaquePayloadTouched(format!(
                    "borrow of opaque field {f} of {}::variant#{v_idx}",
                    ctx.enum_name
                )))
            }
            None => Err(FoldDecline::UnsupportedArmStatement(format!("out-of-range field {f}"))),
        };
    }
    // A shared re-borrow of the accumulator (rung B): tracked so a foreign
    // consumer declines `accumulator_escape`.
    if Some(p.local) == ctx.acc_local
        && (p.projections.is_empty() || p.projections == vec![Projection::Deref])
    {
        return Ok(AbsVal::AccRef);
    }
    // Rung G (P-BOX-DEREF): borrows THROUGH a fingerprint-validated subterm
    // raw pointer — `&(*raw)` for the single child, `&(*raw).k` for a pair
    // component — resolve to the strict-subterm handle at the field's slot.
    match p.projections.as_slice() {
        [Projection::Deref] => {
            if let Some(AbsVal::BoxSubtermPtr(f)) = map.get(&p.local) {
                return match plan.mir.get(*f) {
                    Some(MirField { shape: MirFieldShape::BoxRec, slot }) => {
                        Ok(AbsVal::SubtermRef(*slot))
                    }
                    _ => Err(FoldDecline::BoxDerefDrift(
                        "whole-pointee borrow of a boxed PAIR (components must be \
                         reached per-slot)"
                            .to_string(),
                    )),
                };
            }
        }
        [Projection::Deref, Projection::Field(k)] => {
            if let Some(AbsVal::BoxSubtermPtr(f)) = map.get(&p.local) {
                return match plan.mir.get(*f) {
                    Some(MirField { shape: MirFieldShape::BoxRecPair, slot }) if *k < 2 => {
                        Ok(AbsVal::SubtermRef(slot + k))
                    }
                    _ => Err(FoldDecline::BoxDerefDrift(format!(
                        "pair-component borrow drifts (field {f}, component {k})"
                    ))),
                };
            }
        }
        _ => {}
    }
    if p.projections.is_empty() {
        return match map.get(&p.local) {
            Some(AbsVal::Rebuilt) => Ok(AbsVal::RebuiltRef),
            _ => Err(FoldDecline::UnsupportedArmStatement(format!(
                "borrow of unmodeled local _{}",
                p.local
            ))),
        };
    }
    Err(FoldDecline::UnsupportedArmStatement(format!("borrow of unmodeled place {p:?}")))
}

/// Resolve an operand to its abstract value (per-path binding state).
fn resolve_operand(
    ctx: &ArmCtx<'_>,
    v_idx: usize,
    plan: &VariantPlan,
    op: &Operand,
    map: &BTreeMap<usize, AbsVal>,
) -> Result<AbsVal, FoldDecline> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => {
            // Direct by-value payload copy `((*param) as V).f`.
            if let Some(f) = variant_field_place(p, v_idx) {
                return match plan.mir.get(f) {
                    Some(MirField { shape: MirFieldShape::Int, slot }) => {
                        Ok(AbsVal::Int(FoldExpr::Payload(*slot)))
                    }
                    Some(MirField { shape: MirFieldShape::Opaque, .. }) => {
                        Err(FoldDecline::OpaquePayloadTouched(format!(
                            "by-value use of opaque field {f} of {}::variant#{v_idx}",
                            ctx.enum_name
                        )))
                    }
                    _ => Err(FoldDecline::UnsupportedArmStatement(format!(
                        "by-value use of non-Int variant field {f}"
                    ))),
                };
            }
            match p.projections.as_slice() {
                [] => {
                    if p.local == 1 {
                        return Ok(AbsVal::ParamRef);
                    }
                    if Some(p.local) == ctx.acc_local {
                        return Ok(AbsVal::AccRef);
                    }
                    // Rung G (G3): the threaded scalar parameter reads as an
                    // ordinary Int value.
                    if Some(p.local) == ctx.depth_local {
                        return Ok(AbsVal::Int(FoldExpr::DepthParam));
                    }
                    map.get(&p.local).cloned().ok_or_else(|| {
                        FoldDecline::UnsupportedArmStatement(format!(
                            "use of undefined local _{}",
                            p.local
                        ))
                    })
                }
                [Projection::Deref] => match map.get(&p.local) {
                    Some(AbsVal::IntFieldRef(f)) => Ok(AbsVal::Int(FoldExpr::Payload(*f))),
                    // Rung G: a Box child leaving the fingerprinted idiom is
                    // PREMISE drift, by name (the copy out of the field ref is
                    // legal ONLY as the idiom's own first statement).
                    Some(AbsVal::BoxFieldRef(_)) => Err(FoldDecline::BoxDerefDrift(
                        "the Box child is consumed outside the pinned deref idiom".to_string(),
                    )),
                    _ => Err(FoldDecline::UnsupportedArmStatement(format!(
                        "deref of unmodeled local _{}",
                        p.local
                    ))),
                },
                [Projection::Field(0)] => match map.get(&p.local) {
                    Some(AbsVal::CheckedPair(e)) => Ok(AbsVal::Int(e.clone())),
                    _ => Err(FoldDecline::UnsupportedArmStatement(format!(
                        "field projection of unmodeled local _{}",
                        p.local
                    ))),
                },
                _ => Err(FoldDecline::UnsupportedArmStatement(format!(
                    "unmodeled operand place {p:?}"
                ))),
            }
        }
        Operand::Constant(ConstValue::Int(i)) => Ok(AbsVal::Int(FoldExpr::Const(*i))),
        Operand::Constant(ConstValue::Uint(u, _)) => {
            let v = i128::try_from(*u).map_err(|_| {
                FoldDecline::UnsupportedArmStatement(format!(
                    "unsigned literal {u} exceeds the modeled i128 range"
                ))
            })?;
            Ok(AbsVal::Int(FoldExpr::Const(v)))
        }
        Operand::Constant(ConstValue::Bool(b)) => Ok(AbsVal::Bool(FoldExpr::BoolConst(*b))),
        other => Err(FoldDecline::UnsupportedArmStatement(format!("unmodeled operand {other:?}"))),
    }
}

fn as_int(v: AbsVal) -> Result<FoldExpr, FoldDecline> {
    match v {
        AbsVal::Int(e) => Ok(e),
        AbsVal::Foreign(who) => Err(FoldDecline::ForeignValueInArm(who)),
        other => Err(FoldDecline::UnsupportedArmStatement(format!(
            "non-Int value {other:?} in an Int position"
        ))),
    }
}

/// Resolve the NODE argument of a recursive call to its strict-subterm field,
/// or the NAMED non-subterm decline (design §6's headline kill).
fn subterm_field_of_arg(
    ctx: &ArmCtx<'_>,
    arg: &Operand,
    map: &BTreeMap<usize, AbsVal>,
) -> Result<usize, FoldDecline> {
    let provenance = match arg {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            if p.local == 1 {
                Some(AbsVal::ParamRef)
            } else {
                map.get(&p.local).cloned()
            }
        }
        _ => None,
    };
    match provenance {
        Some(AbsVal::SubtermRef(f)) => Ok(f),
        Some(AbsVal::ParamRef) => Err(FoldDecline::NonSubtermRecursiveArg {
            detail: "the scrutinee itself (f(x) = f(x)) — no IH slot exists for the whole \
                     value"
                .to_string(),
        }),
        Some(AbsVal::Rebuilt | AbsVal::RebuiltRef) => Err(FoldDecline::NonSubtermRecursiveArg {
            detail: "a locally-rebuilt node (fresh aggregate, not a field projection of the \
                     matched variant payload)"
                .to_string(),
        }),
        Some(AbsVal::Foreign(who)) => Err(FoldDecline::NonSubtermRecursiveArg {
            detail: format!(
                "a foreign-call result ({who}) — call-result provenance, not subterm \
                 provenance"
            ),
        }),
        _ => {
            let _ = ctx;
            Err(FoldDecline::NonSubtermRecursiveArg { detail: "unresolved provenance".to_string() })
        }
    }
}

/// Check a recursive call's ACCUMULATOR argument is the threaded parameter
/// itself (design §4 rule i) — else the NAMED `accumulator_alias` decline.
fn check_acc_threading(
    ctx: &ArmCtx<'_>,
    acc_arg: &Operand,
    map: &BTreeMap<usize, AbsVal>,
) -> Result<(), FoldDecline> {
    let ok = match acc_arg {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            Some(p.local) == ctx.acc_local || matches!(map.get(&p.local), Some(AbsVal::AccRef))
        }
        _ => false,
    };
    if ok {
        Ok(())
    } else {
        Err(FoldDecline::AccumulatorAlias(
            "the accumulator argument is not the threaded parameter (fresh/aliased/\
             substituted state)"
                .to_string(),
        ))
    }
}

// ===========================================================================
// P-BOX-DEREF: the built-in Box-deref ub-check fingerprint (rung G, G1b)
// ===========================================================================

/// The STRUCTURAL half of the G1b fingerprint (shared by the arm walk and the
/// whole-body audit): one ALIGNMENT block + its NULL partner, validated
/// statement-for-statement against the pinned idiom —
///
/// ```text
/// align:  [opt: _a = &((*_1) as V).f]
///         _b = copy (*_a)                      (_a: &Box<pointee>, _b: Box<pointee>)
///         _r = copy _b.0.0 as *const pointee   (Box → Unique → NonNull)
///         _u = _r as *const ()
///         _i = _u as usize
///         _m = Sub(const ALIGN, const 1)       (ALIGN a power of two)
///         _n = BitAnd(_i, _m)
///         _c = Eq(_n, const 0)
///         Assert(_c, expected: true, MisalignedPointerDereference) → null
/// null:   _u2 = _r as *const ()
///         _i2 = _u2 as usize
///         _e  = Eq(_i2, const 0)
///         _g  = BitAnd(_e, const true)
///         _c2 = Not(_g)
///         Assert(_c2, expected: true, Custom("null reference constructed")) → cont
/// ```
///
/// with `pointee` the folded enum (G1) or its 2-tuple (G2), checked against
/// the dump's OWN local declarations. The two asserts are premise-discharged
/// under P-BOX-DEREF (they ARE Box's validity invariant: aligned + non-null).
/// PURELY structural — subterm PROVENANCE (which variant field, the
/// current-variant downcast) is the walk-mode caller's added burden.
struct BoxUbcheckStructure {
    /// `_a` — the `&Box` local the value is copied out of.
    copied_from_local: usize,
    /// The optional leading field borrow (destination local, borrowed place).
    lead_borrow: Option<(usize, Place)>,
    /// `_r` — the raw subterm pointer local.
    raw_local: usize,
    /// Whether the pointee is the boxed PAIR form (G2).
    pair: bool,
    /// The NULL check block (the alignment assert's target).
    null_block: BlockId,
    /// Where execution continues after both premise-discharged checks.
    cont: BlockId,
}

/// Non-storage statements of a block (the idiom tolerates storage markers
/// anywhere, like every other fingerprint in this file).
fn real_stmts(b: &BasicBlock) -> Vec<&Statement> {
    b.stmts
        .iter()
        .filter(|s| {
            !matches!(s, Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop)
        })
        .collect()
}

/// `place = Cast(copy <src>, *const ())` — the idiom's unit-pointer cast.
fn expect_unit_ptr_cast(s: &Statement, src: usize) -> Result<usize, String> {
    let Statement::Assign {
        place,
        rvalue: Rvalue::Cast(Operand::Copy(x) | Operand::Move(x), ty),
        ..
    } = s
    else {
        return Err("unit-pointer cast drifts".to_string());
    };
    if !place.projections.is_empty() || x.local != src || !x.projections.is_empty() {
        return Err("unit-pointer cast source drifts".to_string());
    }
    if !matches!(ty, Ty::RawPtr { pointee, .. } if matches!(pointee.as_ref(), Ty::Unit)) {
        return Err("unit-pointer cast target drifts".to_string());
    }
    Ok(place.local)
}

/// `place = Cast(copy <src>, usize)` — the idiom's address cast.
fn expect_addr_cast(s: &Statement, src: usize) -> Result<usize, String> {
    let Statement::Assign {
        place,
        rvalue: Rvalue::Cast(Operand::Copy(x) | Operand::Move(x), ty),
        ..
    } = s
    else {
        return Err("address cast drifts".to_string());
    };
    if !place.projections.is_empty() || x.local != src || !x.projections.is_empty() {
        return Err("address cast source drifts".to_string());
    }
    if !matches!(ty, Ty::Int { signed: false, .. }) {
        return Err("address cast target drifts (want an unsigned Int)".to_string());
    }
    Ok(place.local)
}

#[allow(clippy::too_many_lines)]
fn box_ubcheck_structure(
    body: &trust_types::VerifiableBody,
    enum_name: &str,
    align_block: &BasicBlock,
) -> Result<BoxUbcheckStructure, String> {
    let stmts = real_stmts(align_block);
    // Optional leading `_a = &((*_1) as V).f` borrow (provenance checked by
    // the walk-mode caller; the audit only requires it to feed the copy).
    let (lead_borrow, rest): (Option<(usize, Place)>, &[&Statement]) = match stmts.split_first() {
        Some((
            Statement::Assign { place, rvalue: Rvalue::Ref { mutable: false, place: p }, .. },
            tail,
        )) if place.projections.is_empty() => (Some((place.local, p.clone())), tail),
        _ => (None, stmts.as_slice()),
    };
    let [s_copy, s_cast_raw, s_cast_unit, s_cast_addr, s_sub, s_and, s_eq] = rest else {
        return Err(format!(
            "alignment block carries {} statements (want the pinned 7 after the \
             optional field borrow)",
            rest.len()
        ));
    };
    // 1. `_b = copy (*_a)` — the Box value copied out of the field ref.
    let Statement::Assign {
        place: b_pl,
        rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
        ..
    } = s_copy
    else {
        return Err("first idiom statement is not the Box copy".to_string());
    };
    if !b_pl.projections.is_empty() || src.projections != vec![Projection::Deref] {
        return Err("Box copy shape drifts".to_string());
    }
    let a = src.local;
    let b = b_pl.local;
    if let Some((lead_local, _)) = &lead_borrow {
        if *lead_local != a {
            return Err("leading borrow does not feed the Box copy".to_string());
        }
    }
    // Declared types: `_a: &Box<pointee>`, `_b: Box<pointee>` — both the
    // pinned Box walk over the folded enum (single or pair form).
    let a_form = body.locals.get(a).and_then(|l| match &l.ty {
        Ty::Ref { mutable: false, inner } => box_recursive_form(inner, enum_name),
        _ => None,
    });
    let b_form = body.locals.get(b).and_then(|l| box_recursive_form(&l.ty, enum_name));
    let (Some(pair_a), Some(pair)) = (a_form, b_form) else {
        return Err("copied local is not a pinned Box over the folded enum".to_string());
    };
    if pair_a != pair {
        return Err("Box ref/value pointee forms disagree".to_string());
    }
    // 2. `_r = copy _b.0.0 as *const pointee` (Box → Unique → NonNull).
    let Statement::Assign {
        place: r_pl,
        rvalue: Rvalue::Cast(Operand::Copy(bp) | Operand::Move(bp), r_ty),
        ..
    } = s_cast_raw
    else {
        return Err("second idiom statement is not the raw-pointer cast".to_string());
    };
    if !r_pl.projections.is_empty()
        || bp.local != b
        || bp.projections != vec![Projection::Field(0), Projection::Field(0)]
    {
        return Err(
            "raw-pointer cast source is not the Box's Unique/NonNull projection".to_string()
        );
    }
    let raw = r_pl.local;
    let pointee_matches = |ty: &Ty| -> bool {
        match ty {
            Ty::RawPtr { pointee, .. } => match (pair, pointee.as_ref()) {
                (false, p) => ty_names_enum(p, enum_name),
                (true, Ty::Tuple(es)) => {
                    es.len() == 2 && es.iter().all(|e| ty_names_enum(e, enum_name))
                }
                _ => false,
            },
            _ => false,
        }
    };
    if !pointee_matches(r_ty) {
        return Err("raw-pointer cast target does not pin the Box pointee".to_string());
    }
    if !body.locals.get(raw).is_some_and(|l| pointee_matches(&l.ty)) {
        return Err("raw-pointer local's declared type drifts".to_string());
    }
    // 3-7. The alignment address arithmetic (its temps are NEVER bound by the
    // walk — pointer values cannot leak into the Int lane).
    let unit_local = expect_unit_ptr_cast(s_cast_unit, raw)?;
    let addr_local = expect_addr_cast(s_cast_addr, unit_local)?;
    let mask_local = {
        let Statement::Assign {
            place,
            rvalue:
                Rvalue::BinaryOp(
                    BinOp::Sub,
                    Operand::Constant(ConstValue::Uint(align, _)),
                    Operand::Constant(ConstValue::Uint(one, _)),
                ),
            ..
        } = s_sub
        else {
            return Err("alignment-mask statement drifts".to_string());
        };
        if !place.projections.is_empty() || *one != 1 || !align.is_power_of_two() {
            return Err("alignment-mask constants drift (want power-of-two − 1)".to_string());
        }
        place.local
    };
    let and_local = {
        let Statement::Assign {
            place,
            rvalue: Rvalue::BinaryOp(BinOp::BitAnd, Operand::Copy(x), Operand::Copy(y)),
            ..
        } = s_and
        else {
            return Err("alignment BitAnd drifts".to_string());
        };
        if !place.projections.is_empty()
            || x.local != addr_local
            || !x.projections.is_empty()
            || y.local != mask_local
            || !y.projections.is_empty()
        {
            return Err("alignment BitAnd operands drift".to_string());
        }
        place.local
    };
    let cond_local = {
        let Statement::Assign {
            place,
            rvalue:
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    Operand::Copy(x),
                    Operand::Constant(ConstValue::Uint(zero, _)),
                ),
            ..
        } = s_eq
        else {
            return Err("alignment Eq drifts".to_string());
        };
        if !place.projections.is_empty()
            || x.local != and_local
            || !x.projections.is_empty()
            || *zero != 0
        {
            return Err("alignment Eq operands drift".to_string());
        }
        place.local
    };
    // The ALIGNMENT assert: expected TRUE, the pinned message, cond = the Eq
    // temp, no unwind divergence in the modeled shape.
    let Terminator::Assert { cond, expected, msg, target, .. } = &align_block.terminator else {
        return Err("alignment block does not end in an assert".to_string());
    };
    if !matches!(msg, AssertMessage::MisalignedPointerDereference) {
        return Err("alignment assert message drifts".to_string());
    }
    if !*expected {
        return Err("alignment assert polarity drifts".to_string());
    }
    let (Operand::Copy(cp) | Operand::Move(cp)) = cond else {
        return Err("alignment assert condition shape drifts".to_string());
    };
    if cp.local != cond_local || !cp.projections.is_empty() {
        return Err("alignment assert condition is not the idiom's Eq temp".to_string());
    }
    // The NULL block.
    let null_id = *target;
    let Some(null_block) = block_by_id(body, null_id) else {
        return Err("missing null-check block".to_string());
    };
    let nstmts = real_stmts(null_block);
    let [n_cast_unit, n_cast_addr, n_eq, n_and, n_not] = nstmts.as_slice() else {
        return Err(format!("null block carries {} statements (want the pinned 5)", nstmts.len()));
    };
    let n_unit = expect_unit_ptr_cast(n_cast_unit, raw)?;
    let n_addr = expect_addr_cast(n_cast_addr, n_unit)?;
    let n_eq_local = {
        let Statement::Assign {
            place,
            rvalue:
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    Operand::Copy(x),
                    Operand::Constant(ConstValue::Uint(zero, _)),
                ),
            ..
        } = n_eq
        else {
            return Err("null Eq drifts".to_string());
        };
        if !place.projections.is_empty()
            || x.local != n_addr
            || !x.projections.is_empty()
            || *zero != 0
        {
            return Err("null Eq operands drift".to_string());
        }
        place.local
    };
    let n_and_local = {
        let Statement::Assign {
            place,
            rvalue:
                Rvalue::BinaryOp(
                    BinOp::BitAnd,
                    Operand::Copy(x),
                    Operand::Constant(ConstValue::Bool(true)),
                ),
            ..
        } = n_and
        else {
            return Err("null BitAnd drifts".to_string());
        };
        if !place.projections.is_empty() || x.local != n_eq_local || !x.projections.is_empty() {
            return Err("null BitAnd operands drift".to_string());
        }
        place.local
    };
    let n_not_local = {
        let Statement::Assign {
            place, rvalue: Rvalue::UnaryOp(UnOp::Not, Operand::Copy(x)), ..
        } = n_not
        else {
            return Err("null Not drifts".to_string());
        };
        if !place.projections.is_empty() || x.local != n_and_local || !x.projections.is_empty() {
            return Err("null Not operand drifts".to_string());
        }
        place.local
    };
    let Terminator::Assert { cond, expected, msg, target: n_target, .. } = &null_block.terminator
    else {
        return Err("null block does not end in an assert".to_string());
    };
    let AssertMessage::Custom(m) = msg else {
        return Err("null assert message drifts".to_string());
    };
    if m != BOX_NULL_ASSERT_MSG {
        return Err("null assert message drifts".to_string());
    }
    if !*expected {
        return Err("null assert polarity drifts".to_string());
    }
    let (Operand::Copy(np) | Operand::Move(np)) = cond else {
        return Err("null assert condition shape drifts".to_string());
    };
    if np.local != n_not_local || !np.projections.is_empty() {
        return Err("null assert condition is not the idiom's Not temp".to_string());
    }
    Ok(BoxUbcheckStructure {
        copied_from_local: a,
        lead_borrow,
        raw_local: raw,
        pair,
        null_block: null_id,
        cont: *n_target,
    })
}

/// The G1b fingerprint's walk-mode resolution: MIR field `field`'s subterm
/// raw pointer lives in `raw_local` after the two premise-discharged ub-check
/// blocks; `lead_binding` is the idiom's own leading field borrow (if any) to
/// record in the walk map.
struct BoxDerefIdiom {
    field: usize,
    raw_local: usize,
    lead_binding: Option<(usize, usize)>,
    null_block: BlockId,
    cont: BlockId,
}

/// Walk-mode fingerprint: the structural check PLUS strict-subterm
/// provenance — the copied-from local must be the CURRENT variant's Box field
/// ref (borrowed by the idiom's own leading statement, downcast-exact, or an
/// already-tracked binding on this path), and the pointee form must match the
/// field's classification. Every failure is the NAMED `box_deref_drift`.
fn box_deref_idiom_of_block(
    ctx: &ArmCtx<'_>,
    v_idx: usize,
    plan: &VariantPlan,
    align_block: &BasicBlock,
    map: &BTreeMap<usize, AbsVal>,
) -> Result<BoxDerefIdiom, FoldDecline> {
    let s = box_ubcheck_structure(&ctx.func.body, ctx.enum_name, align_block)
        .map_err(FoldDecline::BoxDerefDrift)?;
    let (field, lead_binding) = match &s.lead_borrow {
        Some((dest, p)) => {
            let Some(f) = variant_field_place(p, v_idx) else {
                return Err(FoldDecline::BoxDerefDrift(
                    "leading borrow is not the matched variant's payload field".to_string(),
                ));
            };
            (f, Some((*dest, f)))
        }
        None => match map.get(&s.copied_from_local) {
            Some(AbsVal::BoxFieldRef(f)) => (*f, None),
            _ => {
                return Err(FoldDecline::BoxDerefDrift(
                    "Box copy source has no tracked Box-field provenance".to_string(),
                ));
            }
        },
    };
    let shape_ok = matches!(
        (s.pair, plan.mir.get(field).map(|m| m.shape)),
        (false, Some(MirFieldShape::BoxRec)) | (true, Some(MirFieldShape::BoxRecPair))
    );
    if !shape_ok {
        return Err(FoldDecline::BoxDerefDrift(format!(
            "fingerprint pointee form does not match the classified field (field {field})"
        )));
    }
    Ok(BoxDerefIdiom {
        field,
        raw_local: s.raw_local,
        lead_binding,
        null_block: s.null_block,
        cont: s.cont,
    })
}

/// Rung G whole-body audit (fail-closed): every `MisalignedPointerDereference`
/// assert in the body must head a structurally valid box-ubcheck pair, and
/// every `Custom("null reference constructed")` assert must be some such
/// pair's second block — even on paths no arm walk visits. This keeps the
/// P-BOX-DEREF premise's discharge scope EXACTLY the fingerprinted idiom.
fn audit_box_ubchecks(
    body: &trust_types::VerifiableBody,
    enum_name: &str,
) -> Result<(), FoldDecline> {
    let mut valid_null_blocks: std::collections::BTreeSet<usize> =
        std::collections::BTreeSet::new();
    for b in &body.blocks {
        if matches!(
            &b.terminator,
            Terminator::Assert { msg: AssertMessage::MisalignedPointerDereference, .. }
        ) {
            match box_ubcheck_structure(body, enum_name, b) {
                Ok(s) => {
                    valid_null_blocks.insert(s.null_block.0);
                }
                Err(e) => return Err(FoldDecline::BoxDerefDrift(format!("bb{}: {e}", b.id.0))),
            }
        }
    }
    for b in &body.blocks {
        if let Terminator::Assert { msg: AssertMessage::Custom(m), .. } = &b.terminator {
            if m == BOX_NULL_ASSERT_MSG && !valid_null_blocks.contains(&b.id.0) {
                return Err(FoldDecline::BoxDerefDrift(format!(
                    "bb{}: naked null ub-check assert outside a validated pair",
                    b.id.0
                )));
            }
        }
    }
    Ok(())
}

// ===========================================================================
// P-STACK: the stack_safe trampoline + wrapper fingerprints (rung B)
// ===========================================================================

/// Whether `body` is EXACTLY clean-kernel's `stack_safe` shape: one block
/// calling `stacker::maybe_grow(32768, 1048576, <param 1>)` into `_0`,
/// then `Return`. (The dump is generic — locals are `Unsupported` params —
/// so only the call structure is checkable; it is fully load-bearing.)
pub(crate) fn stack_safe_body_matches(func: &VerifiableFunction) -> bool {
    let body = &func.body;
    if body.blocks.len() != 2 || body.arg_count != 1 {
        return false;
    }
    let Some(b0) = block_by_id(body, BlockId(0)) else { return false };
    if !b0.stmts.iter().all(|s| {
        matches!(s, Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop)
    }) {
        return false;
    }
    let Terminator::Call { func: callee, args, dest, target, .. } = &b0.terminator else {
        return false;
    };
    if callee != STACKER_MAYBE_GROW || dest.local != 0 || !dest.projections.is_empty() {
        return false;
    }
    let Some(t) = target else { return false };
    let Some(t_block) = block_by_id(body, *t) else { return false };
    if !matches!(t_block.terminator, Terminator::Return) || !t_block.stmts.is_empty() {
        return false;
    }
    let [a0, a1, a2] = args.as_slice() else { return false };
    let lit = |op: &Operand, want: u128| {
        matches!(op, Operand::Constant(ConstValue::Uint(v, _)) if *v == want)
            || matches!(op, Operand::Constant(ConstValue::Int(v)) if u128::try_from(*v) == Ok(want))
    };
    if !lit(a0, STACK_SAFE_RED_ZONE) || !lit(a1, STACK_SAFE_GROWTH) {
        return false;
    }
    matches!(a2, Operand::Copy(p) | Operand::Move(p) if p.local == 1 && p.projections.is_empty())
}

/// The closure-body fingerprint for stack_safe-routed RECURSION inside a fold
/// arm: `|_| { let a = self_captured_arc_ref; let s = Deref::deref(a); F(s) }`
/// — exactly (storage aside): bb0 `_x = Copy((_1.field 0))` +
/// `Call Deref::deref(_x) → _y`, bb1 `Call F(_y) → _0`, bb2 `Return`, with the
/// P-ARC-DEREF type pins on the closure's OWN locals. Returns the called `F`.
fn closure_deref_call_target<'a>(
    closure: &'a VerifiableFunction,
    enum_name: &str,
) -> Result<&'a str, String> {
    let body = &closure.body;
    if body.arg_count != 1 {
        return Err(format!("closure arity {} (want 1: the closure itself)", body.arg_count));
    }
    if body.blocks.len() != 3 {
        return Err(format!("closure has {} blocks (want 3)", body.blocks.len()));
    }
    let Some(b0) = block_by_id(body, BlockId(0)) else { return Err("no bb0".to_string()) };
    let mut upvar_local: Option<usize> = None;
    for s in &b0.stmts {
        match s {
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {}
            Statement::Assign {
                place,
                rvalue: Rvalue::Use(Operand::Copy(p) | Operand::Move(p)),
                ..
            } if place.projections.is_empty()
                && p.local == 1
                && p.projections == vec![Projection::Field(0)] =>
            {
                if upvar_local.replace(place.local).is_some() {
                    return Err("two upvar reads".to_string());
                }
            }
            other => return Err(format!("unmodeled closure statement {other:?}")),
        }
    }
    let Some(u) = upvar_local else { return Err("no upvar read".to_string()) };
    let Terminator::Call { func: callee, args, dest, target, .. } = &b0.terminator else {
        return Err("bb0 does not end in a call".to_string());
    };
    if callee != ARC_DEREF_CALLEE {
        return Err(format!("bb0 calls {callee}, not the pinned Arc deref"));
    }
    let [Operand::Copy(p) | Operand::Move(p)] = args.as_slice() else {
        return Err("deref arg shape".to_string());
    };
    if p.local != u || !p.projections.is_empty() {
        return Err("deref arg is not the captured upvar".to_string());
    }
    // P-ARC-DEREF type pins on the closure's own declared locals.
    let arg_ok = body.locals.get(u).is_some_and(|l| {
        matches!(&l.ty, Ty::Ref { mutable: false, inner }
            if matches!(inner.as_ref(), Ty::Adt { name, .. } if name == ARC_NAME))
    });
    let dest_ok = body.locals.get(dest.local).is_some_and(
        |l| matches!(&l.ty, Ty::Ref { mutable: false, inner } if ty_names_enum(inner, enum_name)),
    );
    if !arg_ok || !dest_ok {
        return Err("closure deref types do not pin Arc<enum> → &enum".to_string());
    }
    let Some(t1) = target else { return Err("diverging deref".to_string()) };
    let Some(b1) = block_by_id(body, *t1) else { return Err("missing deref target".to_string()) };
    if !b1.stmts.is_empty() {
        return Err("statements between deref and recursive call".to_string());
    }
    let Terminator::Call { func: rec_callee, args: rec_args, dest: rec_dest, target: t2, .. } =
        &b1.terminator
    else {
        return Err("no recursive call after deref".to_string());
    };
    let [Operand::Copy(rp) | Operand::Move(rp)] = rec_args.as_slice() else {
        return Err("recursive call arg shape".to_string());
    };
    if rp.local != dest.local || !rp.projections.is_empty() {
        return Err("recursive call arg is not the deref result".to_string());
    }
    if rec_dest.local != 0 || !rec_dest.projections.is_empty() {
        return Err("recursive call result is not the closure return".to_string());
    }
    let Some(t2) = t2 else { return Err("diverging recursive call".to_string()) };
    let Some(b2) = block_by_id(body, *t2) else { return Err("missing return block".to_string()) };
    if !matches!(b2.terminator, Terminator::Return) || !b2.stmts.is_empty() {
        return Err("closure does not return the call result directly".to_string());
    }
    Ok(rec_callee.as_str())
}

/// If this call is `stack_safe(<closure>)`, resolve it to the IH field of the
/// captured strict subterm — `Some(Ok(field))` — or the NAMED drift/subterm
/// decline. `None` means "not the stack_safe idiom at all" (falls through to
/// foreign-poison handling). Fail-closed at every piece: callee body absent /
/// off-fingerprint / capture off-provenance all decline BY NAME once the call
/// LOOKS like a trampoline (single closure-valued argument).
fn try_stack_safe_recursion(
    ctx: &ArmCtx<'_>,
    callee: &str,
    args: &[Operand],
    map: &BTreeMap<usize, AbsVal>,
) -> Option<Result<usize, FoldDecline>> {
    // The call must have exactly one argument, and it must resolve to a
    // closure value we tracked — otherwise this is not the idiom.
    let [Operand::Copy(p) | Operand::Move(p)] = args else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    let Some(AbsVal::ClosureVal { name, caps }) = map.get(&p.local) else { return None };
    // From here on every failure is a NAMED decline (the shape claims to be
    // the trampoline; drift must not silently poison-and-pass).
    let Some(tramp) = ctx.bodies.get(callee) else {
        return Some(Err(FoldDecline::StackSafeDrift(format!(
            "no sibling dump body for trampoline callee {callee}"
        ))));
    };
    if !stack_safe_body_matches(tramp) {
        return Some(Err(FoldDecline::StackSafeDrift(format!(
            "callee {callee} body is not the pinned two-literal maybe_grow forwarding shape"
        ))));
    }
    let Some(closure_fn) = ctx.bodies.get(name) else {
        return Some(Err(FoldDecline::StackSafeDrift(format!(
            "no sibling dump body for closure {name}"
        ))));
    };
    let target = match closure_deref_call_target(closure_fn, ctx.enum_name) {
        Ok(t) => t,
        Err(e) => {
            return Some(Err(FoldDecline::StackSafeDrift(format!(
                "closure {name} body drifts from the pinned recursive-call shape: {e}"
            ))));
        }
    };
    if target != ctx.func.def_path {
        return Some(Err(FoldDecline::StackSafeDrift(format!(
            "closure {name} calls {target}, not the recognized function"
        ))));
    }
    let [cap] = caps.as_slice() else {
        return Some(Err(FoldDecline::StackSafeDrift(format!(
            "closure {name} captures {} values (want exactly the child ref)",
            caps.len()
        ))));
    };
    match cap {
        AbsVal::ArcFieldRef(f) => Some(Ok(*f)),
        AbsVal::ParamRef => Some(Err(FoldDecline::NonSubtermRecursiveArg {
            detail: "the scrutinee itself, captured through the stack_safe closure — no IH \
                     slot exists for the whole value"
                .to_string(),
        })),
        other => Some(Err(FoldDecline::StackSafeDrift(format!(
            "closure capture has unmodeled provenance {other:?}"
        )))),
    }
}

/// A recognized `stack_safe` PUBLIC-WRAPPER shape (rung B, P-STACK):
/// `fn f(&self) -> R { stack_safe(|| self.inner(..)) }` — the wrapper's whole
/// body is one closure aggregate capturing exactly the parameter + one
/// fingerprinted trampoline call; the closure body is a single direct call to
/// `inner` with the captured parameter. The wrapper's denotation is therefore
/// (under P-STACK) exactly `inner`'s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackSafeWrapper {
    /// The delegated-to inner function's def path.
    pub inner_def_path: String,
}

/// Recognize the `stack_safe` wrapper shape of `func`, fail-closed. See
/// [`StackSafeWrapper`].
pub fn sem_stack_safe_wrapper_of(
    func: &VerifiableFunction,
    bodies: &DumpBodies,
) -> Result<StackSafeWrapper, FoldDecline> {
    let body = &func.body;
    if body.arg_count != 1 {
        return Err(FoldDecline::ParamShapeUnsupported(format!(
            "wrapper arg_count {} (rung B models the one-param wrapper)",
            body.arg_count
        )));
    }
    if body.blocks.len() != 2 {
        return Err(FoldDecline::UnsupportedEntryBlock(format!(
            "wrapper has {} blocks (want 2)",
            body.blocks.len()
        )));
    }
    let Some(b0) = block_by_id(body, BlockId(0)) else {
        return Err(FoldDecline::UnsupportedEntryBlock("no entry block".to_string()));
    };
    let mut closure: Option<(usize, &str)> = None;
    for s in &b0.stmts {
        match s {
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {}
            Statement::Assign {
                place,
                rvalue: Rvalue::Aggregate(AggregateKind::Closure { name, .. }, ops),
                ..
            } if place.projections.is_empty() => {
                let [Operand::Copy(cp) | Operand::Move(cp)] = ops.as_slice() else {
                    return Err(FoldDecline::StackSafeDrift(
                        "wrapper closure does not capture exactly the parameter".to_string(),
                    ));
                };
                if cp.local != 1 || !cp.projections.is_empty() {
                    return Err(FoldDecline::StackSafeDrift(
                        "wrapper closure capture is not the parameter".to_string(),
                    ));
                }
                if closure.replace((place.local, name.as_str())).is_some() {
                    return Err(FoldDecline::StackSafeDrift(
                        "two closure aggregates in the wrapper".to_string(),
                    ));
                }
            }
            other => {
                return Err(FoldDecline::UnsupportedEntryBlock(format!(
                    "unmodeled wrapper statement {other:?}"
                )));
            }
        }
    }
    let Some((closure_local, closure_name)) = closure else {
        return Err(FoldDecline::StackSafeDrift("wrapper builds no closure".to_string()));
    };
    let Terminator::Call { func: callee, args, dest, target, .. } = &b0.terminator else {
        return Err(FoldDecline::UnsupportedEntryBlock(
            "wrapper entry does not end in a call".to_string(),
        ));
    };
    let [Operand::Copy(ap) | Operand::Move(ap)] = args.as_slice() else {
        return Err(FoldDecline::StackSafeDrift("trampoline arg shape".to_string()));
    };
    if ap.local != closure_local || !ap.projections.is_empty() {
        return Err(FoldDecline::StackSafeDrift(
            "trampoline argument is not the built closure".to_string(),
        ));
    }
    if dest.local != 0 || !dest.projections.is_empty() {
        return Err(FoldDecline::StackSafeDrift(
            "trampoline result is not the wrapper return".to_string(),
        ));
    }
    let Some(t) = target else {
        return Err(FoldDecline::StackSafeDrift("diverging trampoline".to_string()));
    };
    let Some(b1) = block_by_id(body, *t) else {
        return Err(FoldDecline::StackSafeDrift("missing return block".to_string()));
    };
    if !matches!(b1.terminator, Terminator::Return) || !b1.stmts.is_empty() {
        return Err(FoldDecline::StackSafeDrift(
            "wrapper does not return the trampoline result directly".to_string(),
        ));
    }
    let Some(tramp) = bodies.get(callee) else {
        return Err(FoldDecline::StackSafeDrift(format!(
            "no sibling dump body for trampoline callee {callee}"
        )));
    };
    if !stack_safe_body_matches(tramp) {
        return Err(FoldDecline::StackSafeDrift(format!(
            "callee {callee} body is not the pinned two-literal maybe_grow forwarding shape"
        )));
    }
    let Some(closure_fn) = bodies.get(closure_name) else {
        return Err(FoldDecline::StackSafeDrift(format!(
            "no sibling dump body for closure {closure_name}"
        )));
    };
    let inner = wrapper_closure_direct_call_target(closure_fn)
        .map_err(|e| FoldDecline::StackSafeDrift(format!("closure {closure_name}: {e}")))?;
    Ok(StackSafeWrapper { inner_def_path: inner.to_string() })
}

/// The wrapper-closure fingerprint: `|_| inner(captured_param)` — bb0
/// `_x = Copy((_1.field 0))` + `Call inner(_x) → _0`, bb1 `Return`.
fn wrapper_closure_direct_call_target(closure: &VerifiableFunction) -> Result<&str, String> {
    let body = &closure.body;
    if body.arg_count != 1 {
        return Err(format!("closure arity {} (want 1)", body.arg_count));
    }
    if body.blocks.len() != 2 {
        return Err(format!("closure has {} blocks (want 2)", body.blocks.len()));
    }
    let Some(b0) = block_by_id(body, BlockId(0)) else { return Err("no bb0".to_string()) };
    let mut upvar_local: Option<usize> = None;
    for s in &b0.stmts {
        match s {
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {}
            Statement::Assign {
                place,
                rvalue: Rvalue::Use(Operand::Copy(p) | Operand::Move(p)),
                ..
            } if place.projections.is_empty()
                && p.local == 1
                && p.projections == vec![Projection::Field(0)] =>
            {
                if upvar_local.replace(place.local).is_some() {
                    return Err("two upvar reads".to_string());
                }
            }
            other => return Err(format!("unmodeled closure statement {other:?}")),
        }
    }
    let Some(u) = upvar_local else { return Err("no upvar read".to_string()) };
    let Terminator::Call { func: callee, args, dest, target, .. } = &b0.terminator else {
        return Err("bb0 does not end in a call".to_string());
    };
    let [Operand::Copy(p) | Operand::Move(p)] = args.as_slice() else {
        return Err("inner call arg shape".to_string());
    };
    if p.local != u || !p.projections.is_empty() {
        return Err("inner call arg is not the captured parameter".to_string());
    }
    if dest.local != 0 || !dest.projections.is_empty() {
        return Err("inner call result is not the closure return".to_string());
    }
    let Some(t) = target else { return Err("diverging inner call".to_string()) };
    let Some(b1) = block_by_id(body, *t) else { return Err("missing return block".to_string()) };
    if !matches!(b1.terminator, Terminator::Return) || !b1.stmts.is_empty() {
        return Err("closure does not return the call result directly".to_string());
    }
    Ok(callee.as_str())
}

// ===========================================================================
// Kernel witness: recursor-defined-total interpreter + per-variant adequacy
// ===========================================================================

/// Sanitize a Rust def-path fragment into a Clean name fragment.
fn sanitize(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        out.push('_');
    }
    out
}

/// Register the Opaque `Int.xor` / `Int.lor` carriers if absent — the SAME
/// "opaque, total, asserts nothing about the value" honesty tier (and the SAME
/// name/type/placeholder discipline) as `trustir_anchor::register_int_land`,
/// which `trustir_env()` already runs for `Int.land`.
fn register_int_bitwise_extras(env: &mut Environment) -> Result<(), String> {
    for name in ["Int.xor", "Int.lor"] {
        let int_binop_ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()));
        let placeholder = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), int_lit(0)));
        env.add_decl_if_absent(Declaration::Opaque {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_binop_ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl({name}): {e:?}"))?;
    }
    Ok(())
}

/// The accumulator carriers (rung B, design §4; P-ACC-OPAQUE): an opaque `Acc`
/// type and the ONE uninterpreted total `insertAcc : Acc → Int → Acc` op —
/// the `idxElem` honesty tier (opaque, total, asserts nothing about values).
const ACC_TY_NAME: &str = "Trust.TrustIr.StructFold.Acc";
const ACC_INSERT_NAME: &str = "Trust.TrustIr.StructFold.insertAcc";

fn register_acc_carriers(env: &mut Environment) -> Result<(), String> {
    env.add_decl_if_absent(Declaration::Opaque {
        name: Name::from_string(ACC_TY_NAME),
        level_params: vec![],
        type_: Expr::type_(),
        value: int_ty(),
    })
    .map_err(|e| format!("add_decl({ACC_TY_NAME}): {e:?}"))?;
    let acc = || cst(ACC_TY_NAME);
    let insert_ty = Expr::pi(bd(), acc(), Expr::pi(bd(), int_ty(), acc()));
    // Placeholder value: λ a v. a (total; asserts nothing).
    let placeholder = Expr::lam(bd(), acc(), Expr::lam(bd(), int_ty(), Expr::bvar(1)));
    env.add_decl_if_absent(Declaration::Opaque {
        name: Name::from_string(ACC_INSERT_NAME),
        level_params: vec![],
        type_: insert_ty,
        value: placeholder,
    })
    .map_err(|e| format!("add_decl({ACC_INSERT_NAME}): {e:?}"))?;
    Ok(())
}

/// The registered names for one witness build.
struct FoldNames {
    ind: String,
    ctors: Vec<String>,
    fold: String,
}

/// The Clean type of one result sort.
fn sort_ty(sort: FoldSort) -> Expr {
    match sort {
        FoldSort::Int => int_ty(),
        FoldSort::Bool => cst("Bool"),
        FoldSort::Acc => Expr::pi(bd(), cst(ACC_TY_NAME), cst(ACC_TY_NAME)),
    }
}

/// SORT-CHECK a [`FoldExpr`] (fail-closed defense shared by both renderers):
/// returns the expression's sort, or an error naming the ill-sorted node.
/// `depth` is the rung-G fold-parameter flag: it legalizes
/// [`FoldExpr::DepthParam`] / [`FoldExpr::IhApp`] and OUTLAWS the bare
/// [`FoldExpr::Ih`] (in a depth fold the IH is a function `Int → σ`, never a
/// value).
fn check_sort(
    e: &FoldExpr,
    kinds: &[FoldFieldKind],
    fold_sort: FoldSort,
    depth: bool,
) -> Result<FoldSort, String> {
    match e {
        FoldExpr::Payload(f) => {
            if kinds.get(*f) != Some(&FoldFieldKind::PayloadInt) {
                return Err(format!("payload read of non-Int field {f}"));
            }
            Ok(FoldSort::Int)
        }
        FoldExpr::Const(_) => Ok(FoldSort::Int),
        FoldExpr::BoolConst(_) => Ok(FoldSort::Bool),
        FoldExpr::DepthParam => {
            if !depth {
                return Err("depth parameter outside a depth fold".to_string());
            }
            Ok(FoldSort::Int)
        }
        FoldExpr::Ih(f) => {
            if kinds.get(*f) != Some(&FoldFieldKind::Recursive) {
                return Err(format!("IH of non-recursive field {f}"));
            }
            if fold_sort == FoldSort::Acc {
                return Err("bare IH inside an accumulator fold".to_string());
            }
            if depth {
                return Err("bare IH inside a depth fold (the IH is Int → σ)".to_string());
            }
            Ok(fold_sort)
        }
        FoldExpr::IhApp(f, d) => {
            if !depth {
                return Err("IH application outside a depth fold".to_string());
            }
            if kinds.get(*f) != Some(&FoldFieldKind::Recursive) {
                return Err(format!("IH of non-recursive slot {f}"));
            }
            if check_sort(d, kinds, fold_sort, depth)? != FoldSort::Int {
                return Err("IH depth argument is not Int-sorted".to_string());
            }
            if fold_sort == FoldSort::Acc {
                return Err("IH application inside an accumulator fold".to_string());
            }
            Ok(fold_sort)
        }
        FoldExpr::Bin(_, a, b) => {
            if check_sort(a, kinds, fold_sort, depth)? != FoldSort::Int
                || check_sort(b, kinds, fold_sort, depth)? != FoldSort::Int
            {
                return Err("binop over non-Int operands".to_string());
            }
            Ok(FoldSort::Int)
        }
        FoldExpr::Cmp(_, a, b) => {
            if check_sort(a, kinds, fold_sort, depth)? != FoldSort::Int
                || check_sort(b, kinds, fold_sort, depth)? != FoldSort::Int
            {
                return Err("comparison over non-Int operands".to_string());
            }
            Ok(FoldSort::Bool)
        }
        FoldExpr::Cond(c, t, f) => {
            if check_sort(c, kinds, fold_sort, depth)? != FoldSort::Bool {
                return Err("cond guard is not Bool-sorted".to_string());
            }
            let ts = check_sort(t, kinds, fold_sort, depth)?;
            let fs = check_sort(f, kinds, fold_sort, depth)?;
            if ts != fs {
                return Err("cond branches differ in sort".to_string());
            }
            Ok(ts)
        }
        FoldExpr::AccParam => {
            if fold_sort != FoldSort::Acc {
                return Err("accumulator state outside an accumulator fold".to_string());
            }
            Ok(FoldSort::Acc)
        }
        FoldExpr::AccInsert(st, v) => {
            if fold_sort != FoldSort::Acc
                || check_sort(st, kinds, fold_sort, depth)? != FoldSort::Acc
                || check_sort(v, kinds, fold_sort, depth)? != FoldSort::Int
            {
                return Err("ill-sorted accumulator insert".to_string());
            }
            Ok(FoldSort::Acc)
        }
        FoldExpr::AccRec(f, st) => {
            if kinds.get(*f) != Some(&FoldFieldKind::Recursive) {
                return Err(format!("accumulator IH of non-recursive field {f}"));
            }
            if fold_sort != FoldSort::Acc
                || check_sort(st, kinds, fold_sort, depth)? != FoldSort::Acc
            {
                return Err("ill-sorted accumulator recursion".to_string());
            }
            Ok(FoldSort::Acc)
        }
    }
}

/// The interpreter's per-node result type: `σ` for the plain value /
/// accumulator sorts, `Int → σ` for the depth family (rung G, G3) — the
/// motive's body, the IH binder type, and the fold's own codomain.
fn motive_result_ty(sort: FoldSort, depth: bool) -> Expr {
    if depth { Expr::pi(bd(), int_ty(), sort_ty(sort)) } else { sort_ty(sort) }
}

/// Renderer environment: how the two telescopes address fields / IHs / the
/// accumulator binder.
struct RenderEnv<'a> {
    kinds: &'a [FoldFieldKind],
    /// The fold's result sort (resolves `Ih` leaves' sort for `Cond` motives).
    fold_sort: FoldSort,
    /// bvar index of field `f` (under all binders of the telescope).
    field_bvar: &'a dyn Fn(usize) -> Result<u32, String>,
    /// The rendered IH VALUE for recursive field `f` (a bvar in the minor
    /// telescope; `fold x_f` in the adequacy telescope). For accumulator folds
    /// this is the `Acc → Acc` function (applied by `AccRec`); for depth folds
    /// (rung G) the `Int → σ` function (applied by `IhApp`).
    ih_value: &'a dyn Fn(usize) -> Result<Expr, String>,
    /// bvar index of the accumulator binder (accumulator folds only).
    acc_bvar: Option<u32>,
    /// bvar index of the threaded depth binder (rung G depth folds only).
    depth_bvar: Option<u32>,
}

/// Render a sort-checked [`FoldExpr`] under a telescope.
fn render_expr(e: &FoldExpr, env: &RenderEnv<'_>) -> Result<Expr, String> {
    match e {
        FoldExpr::Payload(f) => {
            if env.kinds.get(*f) != Some(&FoldFieldKind::PayloadInt) {
                return Err(format!("payload read of non-Int field {f}"));
            }
            Ok(Expr::bvar((env.field_bvar)(*f)?))
        }
        FoldExpr::Ih(f) => {
            if env.kinds.get(*f) != Some(&FoldFieldKind::Recursive) {
                return Err(format!("IH of non-recursive field {f}"));
            }
            (env.ih_value)(*f)
        }
        FoldExpr::Const(c) => Ok(int_lit(*c)),
        FoldExpr::BoolConst(b) => Ok(cst(if *b { "Bool.true" } else { "Bool.false" })),
        FoldExpr::Bin(op, a, b) => {
            Ok(Expr::apps(cst(op.clean_name()), [render_expr(a, env)?, render_expr(b, env)?]))
        }
        FoldExpr::Cmp(op, a, b) => {
            Ok(cmp_bool_expr(*op, render_expr(a, env)?, render_expr(b, env)?))
        }
        FoldExpr::DepthParam => {
            let Some(i) = env.depth_bvar else {
                return Err("depth parameter outside a depth telescope".to_string());
            };
            Ok(Expr::bvar(i))
        }
        FoldExpr::IhApp(f, d) => {
            if env.kinds.get(*f) != Some(&FoldFieldKind::Recursive) {
                return Err(format!("IH of non-recursive slot {f}"));
            }
            if env.depth_bvar.is_none() {
                return Err("IH application outside a depth telescope".to_string());
            }
            Ok(Expr::app((env.ih_value)(*f)?, render_expr(d, env)?))
        }
        FoldExpr::Cond(c, t, f) => {
            // The Bool.rec VALUE conditional (same idiom as trustir_adt):
            // Bool.rec (λ_. τ) else then cond. τ is the branch sort's type; the
            // sort checker guarantees both branches agree.
            let sort = check_sort(t, env.kinds, env.fold_sort, env.depth_bvar.is_some())?;
            let motive = Expr::lam(bd(), cst("Bool"), sort_ty(sort));
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1()]);
            Ok(Expr::apps(
                bool_rec,
                [motive, render_expr(f, env)?, render_expr(t, env)?, render_expr(c, env)?],
            ))
        }
        FoldExpr::AccParam => {
            let Some(i) = env.acc_bvar else {
                return Err("accumulator state outside an accumulator telescope".to_string());
            };
            Ok(Expr::bvar(i))
        }
        FoldExpr::AccInsert(st, v) => {
            Ok(Expr::apps(cst(ACC_INSERT_NAME), [render_expr(st, env)?, render_expr(v, env)?]))
        }
        FoldExpr::AccRec(f, st) => {
            if env.kinds.get(*f) != Some(&FoldFieldKind::Recursive) {
                return Err(format!("accumulator IH of non-recursive field {f}"));
            }
            Ok(Expr::app((env.ih_value)(*f)?, render_expr(st, env)?))
        }
    }
}

/// The constructor-field domain type for one field kind.
fn field_domain(kind: FoldFieldKind, t_ty: &Expr) -> Expr {
    match kind {
        FoldFieldKind::PayloadInt | FoldFieldKind::PayloadOpaque => int_ty(),
        FoldFieldKind::Recursive => t_ty.clone(),
    }
}

/// Render a [`FoldExpr`] inside the MINOR-PREMISE telescope of variant fields
/// `kinds`: binders are `field_0 … field_{n-1}, ih_0 … ih_{m-1}` (fields then
/// IHs, the kernel recursor's own minor layout) plus, for accumulator folds,
/// an innermost `acc` binder — or, for depth folds (rung G), an innermost
/// `d : Int` binder (the IHs then have type `Int → σ`).
fn minor_body_expr(
    e: &FoldExpr,
    kinds: &[FoldFieldKind],
    sort: FoldSort,
    depth: bool,
) -> Result<Expr, String> {
    if check_sort(e, kinds, sort, depth)? != sort {
        return Err("arm expression is not fold-sorted".to_string());
    }
    let n = kinds.len();
    let m = kinds.iter().filter(|k| matches!(k, FoldFieldKind::Recursive)).count();
    let inner_extra = usize::from(sort == FoldSort::Acc || depth);
    let to_u32 = |x: usize| u32::try_from(x).map_err(|_| "binder index overflow".to_string());
    let field_bvar = move |f: usize| to_u32(n + m + inner_extra - 1 - f);
    let ih_value = move |f: usize| -> Result<Expr, String> {
        let j = kinds[..f].iter().filter(|k| matches!(k, FoldFieldKind::Recursive)).count();
        Ok(Expr::bvar(to_u32(m + inner_extra - 1 - j)?))
    };
    let env = RenderEnv {
        kinds,
        fold_sort: sort,
        field_bvar: &field_bvar,
        ih_value: &ih_value,
        acc_bvar: (sort == FoldSort::Acc).then_some(0),
        depth_bvar: depth.then_some(0),
    };
    render_expr(e, &env)
}

/// Render a [`FoldExpr`] inside the ADEQUACY-THEOREM telescope of variant
/// fields `kinds`: binders are `x_0 … x_{n-1}` (+ innermost `acc` for
/// accumulator folds / `d` for depth folds), and an IH slot renders as
/// `fold x_f` — the recognizer-reconstructed RHS the theorem equates against
/// one ι-step of the registered interpreter.
fn arm_rhs_expr(
    e: &FoldExpr,
    kinds: &[FoldFieldKind],
    fold_name: &str,
    sort: FoldSort,
    depth: bool,
) -> Result<Expr, String> {
    if check_sort(e, kinds, sort, depth)? != sort {
        return Err("arm expression is not fold-sorted".to_string());
    }
    let n = kinds.len();
    let inner_extra = usize::from(sort == FoldSort::Acc || depth);
    let to_u32 = |x: usize| u32::try_from(x).map_err(|_| "binder index overflow".to_string());
    let field_bvar = move |f: usize| to_u32(n + inner_extra - 1 - f);
    let fold_name = fold_name.to_string();
    let ih_value = move |f: usize| -> Result<Expr, String> {
        Ok(Expr::app(cst(&fold_name), Expr::bvar(to_u32(n + inner_extra - 1 - f)?)))
    };
    let env = RenderEnv {
        kinds,
        fold_sort: sort,
        field_bvar: &field_bvar,
        ih_value: &ih_value,
        acc_bvar: (sort == FoldSort::Acc).then_some(0),
        depth_bvar: depth.then_some(0),
    };
    render_expr(e, &env)
}

/// Register the enum's inductive + the recursor-defined fold interpreter into a
/// fresh `trustir_env`, kernel-checking each declaration. Returns the built env
/// and the registered names. `Err` (fail-closed) on any kernel rejection.
fn build_fold_env(shape: &SemStructFold) -> Result<(Environment, FoldNames), String> {
    if shape.depth && shape.sort == FoldSort::Acc {
        return Err("depth threading is never combined with the accumulator sort".to_string());
    }
    let mut env = crate::trustir_anchor::trustir_env()?;
    register_int_bitwise_extras(&mut env)?;
    if shape.sort == FoldSort::Acc {
        register_acc_carriers(&mut env)?;
    }

    let ind = format!("Trust.TrustIr.StructFold.{}", sanitize(&shape.enum_name));
    let ind_name = Name::from_string(&ind);
    let t_ty = || cst(&ind);

    // Constructor names must be distinct after sanitization.
    let ctors: Vec<String> =
        shape.variants.iter().map(|v| format!("{ind}.{}", sanitize(&v.name))).collect();
    {
        let mut set = std::collections::BTreeSet::new();
        for c in &ctors {
            if !set.insert(c) {
                return Err(format!("constructor name collision after sanitization: {c}"));
            }
        }
    }

    // The inductive: one constructor per variant, fields in order
    // (Int/opaque payload → `Int` atom, recursive child → the inductive itself).
    let kernel_ctors: Vec<Constructor> = shape
        .variants
        .iter()
        .zip(&ctors)
        .map(|(v, cname)| {
            let mut ty = t_ty();
            for kind in v.fields.iter().rev() {
                ty = Expr::pi(bd(), field_domain(*kind, &t_ty()), ty);
            }
            Constructor { name: Name::from_string(cname), type_: ty }
        })
        .collect();
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ind_name.clone(),
            type_: Expr::type_(),
            constructors: kernel_ctors,
        }],
    })
    .map_err(|e| format!("add_inductive({ind}): {e:?}"))?;

    // The fold interpreter, DEFINED BY THE RECURSOR — the kernel checks
    // totality as a side effect of type-checking this definition. Depth folds
    // (rung G) carry the motive `Int → σ`.
    let fold = "Trust.TrustIr.StructFold.fold".to_string();
    let rec_const = Expr::const_(Name::from_string(&format!("{ind}.rec")), vec![l1()]);
    let motive = Expr::lam(bd(), t_ty(), motive_result_ty(shape.sort, shape.depth));
    let mut rec_args: Vec<Expr> = vec![motive];
    for v in &shape.variants {
        let mut minor = minor_body_expr(&v.arm, &v.fields, shape.sort, shape.depth)
            .map_err(|e| format!("minor body ({}): {e}", v.name))?;
        // Wrap inside-out: the accumulator / depth binder first (innermost),
        // then IH binders (each of the motive-result type), then field binders.
        if shape.sort == FoldSort::Acc {
            minor = Expr::lam(bd(), cst(ACC_TY_NAME), minor);
        }
        if shape.depth {
            minor = Expr::lam(bd(), int_ty(), minor);
        }
        let m = v.fields.iter().filter(|k| matches!(k, FoldFieldKind::Recursive)).count();
        for _ in 0..m {
            minor = Expr::lam(bd(), motive_result_ty(shape.sort, shape.depth), minor);
        }
        for kind in v.fields.iter().rev() {
            minor = Expr::lam(bd(), field_domain(*kind, &t_ty()), minor);
        }
        rec_args.push(minor);
    }
    let fold_value = Expr::apps(rec_const, rec_args);
    let fold_ty = Expr::pi(bd(), t_ty(), motive_result_ty(shape.sort, shape.depth));
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(&fold_value, &fold_ty).map_err(|e| format!("check_type(fold): {e:?}"))?;
    }
    env.add_decl(Declaration::Definition {
        name: Name::from_string(&fold),
        level_params: vec![],
        type_: fold_ty,
        value: fold_value,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(fold): {e:?}"))?;
    // The interpreter itself must be axiom-free (recursor + carriers only).
    match env.axiom_deps(&Name::from_string(&fold)) {
        Some(residue) if residue.is_empty() => {}
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            return Err(format!("fold definition carries axioms: {names:?}"));
        }
        None => return Err("fold definition not found after add".to_string()),
    }

    Ok((env, FoldNames { ind, ctors, fold }))
}

/// Check the structural-fold refinement for a recognized [`SemStructFold`]
/// against the real clean-kernel, modulo 3: register the inductive, define the
/// interpreter BY THE RECURSOR (kernel-checked totality), and prove one
/// adequacy theorem per variant (`∀ fields (∀ acc), fold (ctor fields) (acc) =
/// <recognizer-reconstructed arm>` — one-step ι(β)-reduction, design §3.3).
/// Fail-closed (`KernelRejected`) on any unresolved piece or kernel rejection.
#[must_use]
pub fn check_structural_fold_refinement(shape: &SemStructFold) -> RefinementVerdict {
    check_structural_fold_refinement_claimed(shape, &[])
}

/// [`check_structural_fold_refinement`] with per-variant `claims` RHS overrides
/// — the FAIL-CLOSED PROBE entry point (mirrors
/// `trustir_adt::check_adt_return_refinement_claimed` exactly): the `Eq.refl`
/// proof's ACTUAL type is `fold (ctor xs) (acc) = <honest arm>`, so a claimed
/// RHS not def-eq to the honest arm (swapped children, wrong constant, swapped
/// cond branches, reordered inserts, cross-arm claim) makes `check_type`
/// reject — proving the recipe is GENUINE. `claims[i]` overrides variant `i`'s
/// RHS; missing/`None` entries use the honest arm.
/// PUBLIC (probe surface, also used by the fixture-corpus integration tests):
/// exposing this cannot mint anything unsound — `claims` only substitutes the
/// STATEMENT's RHS, and acceptance still requires the kernel's def-eq check of
/// the very same `Eq.refl` proof, so any claim that passes is itself a
/// kernel-proven true equation.
#[must_use]
pub fn check_structural_fold_refinement_claimed(
    shape: &SemStructFold,
    claims: &[Option<Expr>],
) -> RefinementVerdict {
    let (mut env, names) = match build_fold_env(shape) {
        Ok(x) => x,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let t_ty = || cst(&names.ind);
    // The innermost APPLIED binder: the accumulator (rung B) or the threaded
    // depth parameter (rung G, G3) — the statement ∀-quantifies it and the
    // LHS/RHS are applied at it.
    let inner_ty: Option<Expr> = if shape.sort == FoldSort::Acc {
        Some(cst(ACC_TY_NAME))
    } else if shape.depth {
        Some(int_ty())
    } else {
        None
    };
    // The claimed equality's carrier type: the value sort's type, or `Acc`
    // itself for accumulator folds (whose statement is applied to `acc`).
    let eq_carrier = match shape.sort {
        FoldSort::Int => int_ty(),
        FoldSort::Bool => cst("Bool"),
        FoldSort::Acc => cst(ACC_TY_NAME),
    };
    let mut residue_names: Vec<String> = Vec::new();

    for (i, v) in shape.variants.iter().enumerate() {
        let n = v.fields.len();
        let inner_extra = usize::from(inner_ty.is_some());
        // LHS: fold (ctor x_0 … x_{n-1}) [acc|d] under n (+1) binders
        // (x_f = bvar(n + inner_extra - 1 - f), acc/d = bvar(0)).
        let ctor_app = Expr::apps(
            cst(&names.ctors[i]),
            (0..n).map(|f| Expr::bvar(u32::try_from(n + inner_extra - 1 - f).unwrap_or(u32::MAX))),
        );
        let mut lhs = Expr::app(cst(&names.fold), ctor_app);
        if inner_ty.is_some() {
            lhs = Expr::app(lhs, Expr::bvar(0));
        }
        let honest_rhs = match arm_rhs_expr(&v.arm, &v.fields, &names.fold, shape.sort, shape.depth)
        {
            Ok(e) => e,
            Err(e) => {
                return RefinementVerdict::KernelRejected(format!("arm RHS ({}): {e}", v.name));
            }
        };
        let rhs = claims.get(i).and_then(Option::as_ref).cloned().unwrap_or(honest_rhs);
        let eq = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1()]),
            [eq_carrier.clone(), lhs.clone(), rhs],
        );
        let mut statement = eq;
        if let Some(it) = &inner_ty {
            statement = Expr::pi(bd(), it.clone(), statement);
        }
        for kind in v.fields.iter().rev() {
            statement = Expr::pi(bd(), field_domain(*kind, &t_ty()), statement);
        }
        // PROOF: λ xs [acc|d]. Eq.refl τ (fold (ctor xs) [acc|d]) — genuinely a
        // one-step ι(β)-reduction check: the registered interpreter's reduct at
        // this constructor must be DEF-EQ to the recognizer-reconstructed RHS.
        let mut proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![l1()]),
            [eq_carrier.clone(), lhs],
        );
        if let Some(it) = &inner_ty {
            proof = Expr::lam(bd(), it.clone(), proof);
        }
        for kind in v.fields.iter().rev() {
            proof = Expr::lam(bd(), field_domain(*kind, &t_ty()), proof);
        }
        {
            let tc = TypeChecker::new(&env);
            if let Err(e) = tc.check_type(&proof, &statement) {
                return RefinementVerdict::KernelRejected(format!(
                    "check_type[arm {}]: {e:?}",
                    v.name
                ));
            }
        }
        let decl_name = Name::from_string(&format!(
            "Trust.TrustIr.Refinement.struct_fold_arm{i}_{}",
            sanitize(&v.name)
        ));
        if let Err(e) = env.add_decl(Declaration::Theorem {
            name: decl_name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        }) {
            return RefinementVerdict::KernelRejected(format!("add_decl[arm {}]: {e:?}", v.name));
        }
        match env.axiom_deps(&decl_name) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => residue_names.extend(residue.iter().map(ToString::to_string)),
            None => {
                return RefinementVerdict::KernelRejected(format!(
                    "decl not found after add: arm {}",
                    v.name
                ));
            }
        }
    }

    if residue_names.is_empty() {
        RefinementVerdict::ProvenModulo3
    } else {
        residue_names.sort();
        residue_names.dedup();
        RefinementVerdict::Residue(residue_names)
    }
}

/// PROBE-CONSTRUCTION helper (public for the fixture-corpus integration
/// tests): render variant `i`'s reconstructed RHS for a (possibly
/// deliberately-mutated) shape — build a WRONG shape (swapped children, wrong
/// constant, reordered inserts), render its arm RHS here, and claim it against
/// the HONEST shape's witness via
/// [`check_structural_fold_refinement_claimed`] — must be `KernelRejected`.
/// A pure renderer; exposes no acceptance path.
#[must_use]
pub fn probe_arm_rhs(shape: &SemStructFold, i: usize) -> Option<Expr> {
    let v = shape.variants.get(i)?;
    arm_rhs_expr(&v.arm, &v.fields, "Trust.TrustIr.StructFold.fold", shape.sort, shape.depth).ok()
}

#[cfg(test)]
pub(crate) use probe_arm_rhs as debug_arm_rhs_for_test;

// ===========================================================================
// Tests — kernel witness + forgery probes (the recognizer is pinned against
// REAL MIR by tests/structural_fold_corpus.rs and tests/level_fold_corpus.rs)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// The canonical `xor_all` shape over the corpus `Tree` enum
    /// (`Leaf(i64) | One(Arc<Tree>) | Two(Arc<Tree>, Arc<Tree>)`):
    /// `Leaf(v) => v; One(a) => f(a); Two(a, b) => f(a) ^ f(b)`.
    fn example_xor_all() -> SemStructFold {
        SemStructFold {
            enum_name: "Tree".to_string(),
            sort: FoldSort::Int,
            depth: false,
            variants: vec![
                FoldVariant {
                    name: "Leaf".to_string(),
                    tag: 0,
                    fields: vec![FoldFieldKind::PayloadInt],
                    arm: FoldExpr::Payload(0),
                },
                FoldVariant {
                    name: "One".to_string(),
                    tag: 1,
                    fields: vec![FoldFieldKind::Recursive],
                    arm: FoldExpr::Ih(0),
                },
                FoldVariant {
                    name: "Two".to_string(),
                    tag: 2,
                    fields: vec![FoldFieldKind::Recursive, FoldFieldKind::Recursive],
                    arm: FoldExpr::Bin(
                        FoldBinOp::Xor,
                        Box::new(FoldExpr::Ih(0)),
                        Box::new(FoldExpr::Ih(1)),
                    ),
                },
            ],
        }
    }

    /// The canonical `size` shape: `Leaf(_) => 1; One(a) => 1 + f(a);
    /// Two(a, b) => (1 + f(a)) + f(b)` — mixed payload-ignoring leaf +
    /// Add-combined IHs (the design doc's literal member).
    fn example_size() -> SemStructFold {
        SemStructFold {
            enum_name: "Tree".to_string(),
            sort: FoldSort::Int,
            depth: false,
            variants: vec![
                FoldVariant {
                    name: "Leaf".to_string(),
                    tag: 0,
                    fields: vec![FoldFieldKind::PayloadInt],
                    arm: FoldExpr::Const(1),
                },
                FoldVariant {
                    name: "One".to_string(),
                    tag: 1,
                    fields: vec![FoldFieldKind::Recursive],
                    arm: FoldExpr::Bin(
                        FoldBinOp::Add,
                        Box::new(FoldExpr::Const(1)),
                        Box::new(FoldExpr::Ih(0)),
                    ),
                },
                FoldVariant {
                    name: "Two".to_string(),
                    tag: 2,
                    fields: vec![FoldFieldKind::Recursive, FoldFieldKind::Recursive],
                    arm: FoldExpr::Bin(
                        FoldBinOp::Add,
                        Box::new(FoldExpr::Bin(
                            FoldBinOp::Add,
                            Box::new(FoldExpr::Const(1)),
                            Box::new(FoldExpr::Ih(0)),
                        )),
                        Box::new(FoldExpr::Ih(1)),
                    ),
                },
            ],
        }
    }

    /// The REAL `Level::is_zero` shape (5 ctors, opaque `Param(Name)` payload,
    /// short-circuit `&&` as a cond-tree — rung B's real-code bool pilot):
    /// `Zero => true; Succ(_) => false; Max(a,b) => if f(a) { f(b) } else
    /// { false }; IMax(_,b) => f(b); Param(_) => false`.
    fn example_level_is_zero() -> SemStructFold {
        SemStructFold {
            enum_name: "level::Level".to_string(),
            sort: FoldSort::Bool,
            depth: false,
            variants: vec![
                FoldVariant {
                    name: "Zero".to_string(),
                    tag: 0,
                    fields: vec![],
                    arm: FoldExpr::BoolConst(true),
                },
                FoldVariant {
                    name: "Succ".to_string(),
                    tag: 1,
                    fields: vec![FoldFieldKind::Recursive],
                    arm: FoldExpr::BoolConst(false),
                },
                FoldVariant {
                    name: "Max".to_string(),
                    tag: 2,
                    fields: vec![FoldFieldKind::Recursive, FoldFieldKind::Recursive],
                    arm: FoldExpr::Cond(
                        Box::new(FoldExpr::Ih(0)),
                        Box::new(FoldExpr::Ih(1)),
                        Box::new(FoldExpr::BoolConst(false)),
                    ),
                },
                FoldVariant {
                    name: "IMax".to_string(),
                    tag: 3,
                    fields: vec![FoldFieldKind::Recursive, FoldFieldKind::Recursive],
                    arm: FoldExpr::Ih(1),
                },
                FoldVariant {
                    name: "Param".to_string(),
                    tag: 4,
                    fields: vec![FoldFieldKind::PayloadOpaque],
                    arm: FoldExpr::BoolConst(false),
                },
            ],
        }
    }

    /// The corpus `collect_leaves` accumulator shape (design §4):
    /// `Leaf(v) => insert(acc, v); One(a) => f(a, acc);
    /// Two(a,b) => f(b, f(a, acc))`.
    fn example_collect_leaves() -> SemStructFold {
        SemStructFold {
            enum_name: "Tree".to_string(),
            sort: FoldSort::Acc,
            depth: false,
            variants: vec![
                FoldVariant {
                    name: "Leaf".to_string(),
                    tag: 0,
                    fields: vec![FoldFieldKind::PayloadInt],
                    arm: FoldExpr::AccInsert(
                        Box::new(FoldExpr::AccParam),
                        Box::new(FoldExpr::Payload(0)),
                    ),
                },
                FoldVariant {
                    name: "One".to_string(),
                    tag: 1,
                    fields: vec![FoldFieldKind::Recursive],
                    arm: FoldExpr::AccRec(0, Box::new(FoldExpr::AccParam)),
                },
                FoldVariant {
                    name: "Two".to_string(),
                    tag: 2,
                    fields: vec![FoldFieldKind::Recursive, FoldFieldKind::Recursive],
                    arm: FoldExpr::AccRec(
                        1,
                        Box::new(FoldExpr::AccRec(0, Box::new(FoldExpr::AccParam))),
                    ),
                },
            ],
        }
    }

    #[test]
    fn xor_all_fold_refinement_modulo3() {
        assert_eq!(
            check_structural_fold_refinement(&example_xor_all()),
            RefinementVerdict::ProvenModulo3
        );
    }

    #[test]
    fn size_fold_refinement_modulo3() {
        assert_eq!(
            check_structural_fold_refinement(&example_size()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// RUNG B: the real-code Bool fold witness (5-ctor Level mirror, opaque
    /// payload, cond-tree arm) mints modulo 3.
    #[test]
    fn level_is_zero_bool_fold_refinement_modulo3() {
        assert_eq!(
            check_structural_fold_refinement(&example_level_is_zero()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// RUNG B: the accumulator fold witness (motive `Acc → Acc`, opaque
    /// `insertAcc`, exact post-order sequence) mints modulo 3.
    #[test]
    fn collect_leaves_acc_fold_refinement_modulo3() {
        assert_eq!(
            check_structural_fold_refinement(&example_collect_leaves()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// FORGERY PROBE (design §6: "swapped children"): claim `Two`'s arm equals
    /// `f(b) ^ f(a)` (children swapped) when the interpreter computes
    /// `f(a) ^ f(b)`. `Int.xor` is an OPAQUE carrier, so the swapped term is
    /// NOT def-eq to the reduct — the kernel must reject.
    #[test]
    fn forgery_swapped_children_is_kernel_rejected() {
        let honest = example_xor_all();
        let mut swapped = honest.clone();
        swapped.variants[2].arm =
            FoldExpr::Bin(FoldBinOp::Xor, Box::new(FoldExpr::Ih(1)), Box::new(FoldExpr::Ih(0)));
        let wrong_rhs = debug_arm_rhs_for_test(&swapped, 2).expect("swapped RHS renders");
        let claims = vec![None, None, Some(wrong_rhs)];
        assert!(
            matches!(
                check_structural_fold_refinement_claimed(&honest, &claims),
                RefinementVerdict::KernelRejected(_)
            ),
            "a swapped-children claim must be KernelRejected"
        );
    }

    /// FORGERY PROBE (design §6: "wrong arm constant"): claim `size`'s `Leaf`
    /// arm equals `2` when the interpreter computes `1`.
    #[test]
    fn forgery_wrong_arm_constant_is_kernel_rejected() {
        let honest = example_size();
        let mut wrong = honest.clone();
        wrong.variants[0].arm = FoldExpr::Const(2);
        let wrong_rhs = debug_arm_rhs_for_test(&wrong, 0).expect("wrong-const RHS renders");
        let claims = vec![Some(wrong_rhs)];
        assert!(
            matches!(
                check_structural_fold_refinement_claimed(&honest, &claims),
                RefinementVerdict::KernelRejected(_)
            ),
            "a wrong-arm-constant claim must be KernelRejected"
        );
    }

    /// FORGERY PROBE (cross-arm / wrong-arm-mapping): claim the `One` arm's RHS
    /// (`f(a)` — a bare IH) for the `Leaf` arm of `xor_all` (whose honest arm
    /// is the payload read). The binder telescopes even differ in field KIND
    /// (`Int` vs the inductive), so the claim is ill-typed/not def-eq — reject.
    #[test]
    fn forgery_cross_arm_claim_is_kernel_rejected() {
        let honest = example_xor_all();
        // Render `One`'s RHS as if its single field were `Leaf`'s telescope:
        // `fold x0` where x0 is Leaf's Int payload binder — a type-incorrect
        // (Int where the inductive is expected) cross-arm forgery.
        let mut cross = honest.clone();
        cross.variants[0].arm = FoldExpr::Ih(0);
        cross.variants[0].fields = vec![FoldFieldKind::Recursive];
        let wrong_rhs = debug_arm_rhs_for_test(&cross, 0).expect("cross-arm RHS renders");
        let claims = vec![Some(wrong_rhs)];
        assert!(
            matches!(
                check_structural_fold_refinement_claimed(&honest, &claims),
                RefinementVerdict::KernelRejected(_)
            ),
            "a cross-arm claim must be KernelRejected"
        );
    }

    /// RUNG-B FORGERY PROBE (bool lane): claim `Max`'s cond arm with SWAPPED
    /// branches (`if f(a) { false } else { f(b) }`) against the honest
    /// `if f(a) { f(b) } else { false }` — the `Bool.rec` minors differ, so
    /// not def-eq → KernelRejected.
    #[test]
    fn forgery_swapped_cond_branches_is_kernel_rejected() {
        let honest = example_level_is_zero();
        let mut wrong = honest.clone();
        wrong.variants[2].arm = FoldExpr::Cond(
            Box::new(FoldExpr::Ih(0)),
            Box::new(FoldExpr::BoolConst(false)),
            Box::new(FoldExpr::Ih(1)),
        );
        let wrong_rhs = debug_arm_rhs_for_test(&wrong, 2).expect("swapped-cond RHS renders");
        let claims = vec![None, None, Some(wrong_rhs)];
        assert!(
            matches!(
                check_structural_fold_refinement_claimed(&honest, &claims),
                RefinementVerdict::KernelRejected(_)
            ),
            "a swapped-cond-branch claim must be KernelRejected"
        );
    }

    /// RUNG-B FORGERY PROBE (bool lane): claim `Succ`'s constant arm with the
    /// WRONG polarity (`true` where the interpreter computes `false`).
    #[test]
    fn forgery_wrong_bool_polarity_is_kernel_rejected() {
        let honest = example_level_is_zero();
        let mut wrong = honest.clone();
        wrong.variants[1].arm = FoldExpr::BoolConst(true);
        let wrong_rhs = debug_arm_rhs_for_test(&wrong, 1).expect("wrong-polarity RHS renders");
        let claims = vec![None, Some(wrong_rhs)];
        assert!(
            matches!(
                check_structural_fold_refinement_claimed(&honest, &claims),
                RefinementVerdict::KernelRejected(_)
            ),
            "a wrong-polarity claim must be KernelRejected"
        );
    }

    /// RUNG-B FORGERY PROBE (accumulator lane): claim `Two`'s arm with the
    /// recursion order REVERSED (`f(a, f(b, acc))` instead of the program's
    /// `f(b, f(a, acc))`) — `insertAcc`/the IHs are opaque, so the reordered
    /// sequence is not def-eq → KernelRejected. This is exactly the "the model
    /// pins the exact post-order sequence" claim of design §4.
    #[test]
    fn forgery_reordered_accumulator_sequence_is_kernel_rejected() {
        let honest = example_collect_leaves();
        let mut wrong = honest.clone();
        wrong.variants[2].arm =
            FoldExpr::AccRec(0, Box::new(FoldExpr::AccRec(1, Box::new(FoldExpr::AccParam))));
        let wrong_rhs = debug_arm_rhs_for_test(&wrong, 2).expect("reordered RHS renders");
        let claims = vec![None, None, Some(wrong_rhs)];
        assert!(
            matches!(
                check_structural_fold_refinement_claimed(&honest, &claims),
                RefinementVerdict::KernelRejected(_)
            ),
            "a reordered-accumulator claim must be KernelRejected"
        );
    }

    /// RUNG-B FORGERY PROBE (accumulator lane): claim `Leaf`'s arm DROPS the
    /// insert (`acc` unchanged) — not def-eq to `insertAcc acc v` → reject.
    #[test]
    fn forgery_dropped_insert_is_kernel_rejected() {
        let honest = example_collect_leaves();
        let mut wrong = honest.clone();
        wrong.variants[0].arm = FoldExpr::AccParam;
        let wrong_rhs = debug_arm_rhs_for_test(&wrong, 0).expect("dropped-insert RHS renders");
        let claims = vec![Some(wrong_rhs)];
        assert!(
            matches!(
                check_structural_fold_refinement_claimed(&honest, &claims),
                RefinementVerdict::KernelRejected(_)
            ),
            "a dropped-insert claim must be KernelRejected"
        );
    }

    /// A NON-STRUCTURAL model is INEXPRESSIBLE, not merely rejected: there is
    /// no `FoldExpr` constructor for "the fold of a rebuilt node" at all, and a
    /// fabricated `Ih` on a non-recursive field fails the witness builder
    /// before any kernel work. (The recognizer-side kills for `bad_self`/
    /// `bad_rebuilt`/`bad_nonsub` are pinned against the REAL corpus MIR in
    /// tests/structural_fold_corpus.rs.)
    #[test]
    fn fabricated_ih_on_payload_field_is_rejected() {
        let mut wrong = example_xor_all();
        wrong.variants[0].arm = FoldExpr::Ih(0); // Leaf's field 0 is PayloadInt
        assert!(
            matches!(
                check_structural_fold_refinement(&wrong),
                RefinementVerdict::KernelRejected(_)
            ),
            "an IH slot on a payload field must be rejected"
        );
    }

    /// RUNG B: a fabricated IH on an OPAQUE payload field is likewise rejected
    /// before any kernel work (the opaque atom has no IH slot).
    #[test]
    fn fabricated_ih_on_opaque_field_is_rejected() {
        let mut wrong = example_level_is_zero();
        wrong.variants[4].arm = FoldExpr::Ih(0); // Param's field 0 is PayloadOpaque
        assert!(
            matches!(
                check_structural_fold_refinement(&wrong),
                RefinementVerdict::KernelRejected(_)
            ),
            "an IH slot on an opaque payload field must be rejected"
        );
    }

    /// Explicit-discriminant honesty: the SAME fold shape with the REAL
    /// `TaggedTree` tags (10/20/30 — tag != declaration index) still proves;
    /// the tags are carried, never assumed equal to indices.
    #[test]
    fn tagged_tree_fold_refinement_modulo3() {
        let mut shape = example_xor_all();
        shape.enum_name = "TaggedTree".to_string();
        shape.variants[0].tag = 10;
        shape.variants[1].tag = 20;
        shape.variants[2].tag = 30;
        assert_eq!(check_structural_fold_refinement(&shape), RefinementVerdict::ProvenModulo3);
    }

    /// RUNG G (G2 + G3): the REAL `term::Term::has_free_variables_helper`
    /// shape — the published-crate first target. `Term { Var(usize),
    /// Abs(Box<Term>), App(Box<(Term, Term)>) }`: Abs's slot from the single
    /// Box child, App's TWO slots from the boxed pair (per-component IHs),
    /// the `depth` parameter threaded (`ih (d+1)` at the binder):
    /// `Var(i) => if i > d { true } else { i == 0 };
    ///  Abs(t) => f(t, d+1); App(t0,t1) => f(t0,d) || f(t1,d)`.
    fn example_has_free_vars_depth() -> SemStructFold {
        SemStructFold {
            enum_name: "term::Term".to_string(),
            sort: FoldSort::Bool,
            depth: true,
            variants: vec![
                FoldVariant {
                    name: "Var".to_string(),
                    tag: 0,
                    fields: vec![FoldFieldKind::PayloadInt],
                    arm: FoldExpr::Cond(
                        Box::new(FoldExpr::Cmp(
                            FoldCmpOp::Gt,
                            Box::new(FoldExpr::Payload(0)),
                            Box::new(FoldExpr::DepthParam),
                        )),
                        Box::new(FoldExpr::BoolConst(true)),
                        Box::new(FoldExpr::Cmp(
                            FoldCmpOp::Eq,
                            Box::new(FoldExpr::Payload(0)),
                            Box::new(FoldExpr::Const(0)),
                        )),
                    ),
                },
                FoldVariant {
                    name: "Abs".to_string(),
                    tag: 1,
                    fields: vec![FoldFieldKind::Recursive],
                    arm: FoldExpr::IhApp(
                        0,
                        Box::new(FoldExpr::Bin(
                            FoldBinOp::Add,
                            Box::new(FoldExpr::DepthParam),
                            Box::new(FoldExpr::Const(1)),
                        )),
                    ),
                },
                FoldVariant {
                    name: "App".to_string(),
                    tag: 2,
                    fields: vec![FoldFieldKind::Recursive, FoldFieldKind::Recursive],
                    arm: FoldExpr::Cond(
                        Box::new(FoldExpr::IhApp(0, Box::new(FoldExpr::DepthParam))),
                        Box::new(FoldExpr::BoolConst(true)),
                        Box::new(FoldExpr::IhApp(1, Box::new(FoldExpr::DepthParam))),
                    ),
                },
            ],
        }
    }

    /// RUNG G: the depth-threaded Bool fold witness (motive `Int → Bool`,
    /// per-component IH slots, `ih (d+1)` at the binder) mints modulo 3.
    #[test]
    fn has_free_vars_depth_fold_refinement_modulo3() {
        assert_eq!(
            check_structural_fold_refinement(&example_has_free_vars_depth()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// RUNG-G FORGERY PROBE: claim Abs's arm with the depth increment DROPPED
    /// (`ih d` instead of `ih (d+1)`) — `Int.add` renders opaquely enough that
    /// the wrong argument is not def-eq to the reduct — KernelRejected.
    #[test]
    fn forgery_dropped_depth_increment_is_kernel_rejected() {
        let honest = example_has_free_vars_depth();
        let mut wrong = honest.clone();
        wrong.variants[1].arm = FoldExpr::IhApp(0, Box::new(FoldExpr::DepthParam));
        let wrong_rhs = debug_arm_rhs_for_test(&wrong, 1).expect("dropped-increment RHS renders");
        let claims = vec![None, Some(wrong_rhs)];
        assert!(
            matches!(
                check_structural_fold_refinement_claimed(&honest, &claims),
                RefinementVerdict::KernelRejected(_)
            ),
            "a dropped-depth-increment claim must be KernelRejected"
        );
    }

    /// RUNG-G FORGERY PROBE (G2 pair slots): claim App's arm with the two
    /// component IHs SWAPPED (`f(t1,d) || f(t0,d)`) — not def-eq → reject.
    #[test]
    fn forgery_swapped_pair_components_is_kernel_rejected() {
        let honest = example_has_free_vars_depth();
        let mut wrong = honest.clone();
        wrong.variants[2].arm = FoldExpr::Cond(
            Box::new(FoldExpr::IhApp(1, Box::new(FoldExpr::DepthParam))),
            Box::new(FoldExpr::BoolConst(true)),
            Box::new(FoldExpr::IhApp(0, Box::new(FoldExpr::DepthParam))),
        );
        let wrong_rhs = debug_arm_rhs_for_test(&wrong, 2).expect("swapped-pair RHS renders");
        let claims = vec![None, None, Some(wrong_rhs)];
        assert!(
            matches!(
                check_structural_fold_refinement_claimed(&honest, &claims),
                RefinementVerdict::KernelRejected(_)
            ),
            "a swapped-pair-component claim must be KernelRejected"
        );
    }

    /// RUNG-G SORT DEFENSE: a bare IH inside a depth fold (the IH is `Int →
    /// σ`, never a value) and a DepthParam outside one are both rejected
    /// before any kernel work.
    #[test]
    fn depth_sort_violations_are_rejected() {
        let mut bare_ih = example_has_free_vars_depth();
        bare_ih.variants[1].arm = FoldExpr::Ih(0);
        assert!(
            matches!(
                check_structural_fold_refinement(&bare_ih),
                RefinementVerdict::KernelRejected(_)
            ),
            "a bare IH inside a depth fold must be rejected"
        );
        let mut stray_depth = example_xor_all();
        stray_depth.variants[0].arm = FoldExpr::DepthParam;
        assert!(
            matches!(
                check_structural_fold_refinement(&stray_depth),
                RefinementVerdict::KernelRejected(_)
            ),
            "a depth parameter outside a depth fold must be rejected"
        );
        let mut acc_depth = example_collect_leaves();
        acc_depth.depth = true;
        assert!(
            matches!(
                check_structural_fold_refinement(&acc_depth),
                RefinementVerdict::KernelRejected(_)
            ),
            "depth + accumulator must be rejected at the witness builder"
        );
    }
}
