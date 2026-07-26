// trust-clean/trustir_adt.rs — Trust: ADT-return leaf (gap-queue #2, 2026-07-07).
//
// The KERNEL-CHECKED witness for the Result/Option-ADT AGGREGATE RETURN shape
// (`mirsem::SemAdtReturn`): "if guard { <construct variant A> } else { <construct
// variant B> }" — the CONSTRUCTION dual of the just-landed discriminant-guard
// CONSUMPTION shape (that shape READS an enum's tag via `Rvalue::Discriminant`; this
// one WRITES it via a `Rvalue::Aggregate(AggregateKind::Adt{variant,..}, ops)`).
//
// SIBLING TO `trustir_anchor.rs`'s `IrGuardedIndex`/`IrGuardedConstIndex` — the SAME
// self-contained `Bool.rec` + `congrArg`-TRANSPORT recipe (case-split the guard, USE
// the `guard = true` hypothesis to transport the `Bool.rec` scrutinee to the taken
// branch's own constant, so the proof GENUINELY needs the hypothesis — a wrong branch
// target/value is NOT def-eq to the claimed RHS, so `check_type` REJECTS it), just
// generalized from an `Int` motive (the bounds-guarded slice element) to the OUTER
// ENUM's OWN freshly-registered Clean carrier — a REAL 2-constructor inductive built
// via the EXISTING Phase-4 `reflect::reflect_enum` / `clean_ground::register_adt_carriers`
// machinery. NO new reflect.rs/clean_ground.rs code: this module only CALLS that
// machinery with a `Ty::adt_enum(..)` it synthesizes from the recognized shape.
//
// MODEL-ONLY tier — the SAME honesty tier as `trustir_anchor::check_body_refinement_model`
// / `check_rvalue_refinement_model`: this witness does NOT relate to
// `clean_ground::ground_int` (`Int`-sorted only; it cannot represent an ADT value at
// all). It is a SELF-CONTAINED, freshly-registered, kernel-checked claim: "under this
// guard, the function's return equals THIS constructor application; under its
// negation, THAT one." The SOUNDNESS argument that this claim matches the MIR's own
// construction lives in the RECOGNIZER (`mirsem::sem_adt_return_shape_of` +
// `arm_adt_ctor_value_for`): every field comes from the real `Aggregate`, and each
// declaration-order aggregate variant index is mapped through the exact destination
// enum's first-class metadata to its declared discriminant.  Nothing is inferred
// from arm position; see their doc comments for the adversarial soundness gates.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use clean_kernel::{
    BinderData, BinderInfo, Declaration, Environment, Expr, Level, LevelVec, Name, TypeChecker,
};

use crate::mirsem::{
    MIRSEM_DISCRIMINANT_TAG_KEY, MIRSEM_IDX_ELEM_PRIME, MIRSEM_SET_KEY_EQ, SemAdtArm, SemAdtPayload,
    SemAdtPayloadExtract, SemAdtPayloadExtractDiverging, SemAdtReturn, SemAdtReturn3,
    SemAdtReturnOpaqueOrd, SemCmpOp, SemCondTree, SemFieldRmw, SemFieldSet, SemIterStep, SemOperand,
    SemRmwOp, SemRmwRhs, SemScalarSentinelSelect, SemStructField, SemStructReturn,
};
use crate::trustir_anchor::{
    RefinementVerdict, TRUSTIR_IDX_ELEM, TRUSTIR_ITER_HAS_NEXT, TRUSTIR_ITER_HAS_NEXT2,
    TRUSTIR_ITER_REGION, TRUSTIR_ITER_SEQ, TRUSTIR_PTR_OFFSET, TRUSTIR_SLICE_LEN,
    TRUSTIR_SLICE_START, cst, env_ty, eq_bool_false, eq_bool_true, int_lit,
};

fn bd() -> BinderData {
    BinderData::from(BinderInfo::Default)
}

// ---------------------------------------------------------------------------
// Operand / guard denotation — DIRECT env-application terms (the SAME "MODEL-ONLY,
// no syntax layer" style `IrGuardedIndex::guard_bool`/`elem_term` already use: no
// `IrOperand`/`evalOperand` round-trip, just `e p` / a literal, at the caller-chosen
// binder depth).
// ---------------------------------------------------------------------------

/// Resolve a [`SemOperand`] to its DIRECT env-application `Int` term at binder depth
/// `e_bvar` (the `Env` binder's de-Bruijn index): `Var p ↦ e p`, `Const c ↦ <lit c>`,
/// `Move` transparent (the move is transparent to the scalar value, mirroring
/// `mirsem::SemOperand::denotation`'s OWN `Move` arm). `None` (fail-closed) for
/// anything outside this small fragment — `Field`/`Index`/`Len` never arise for
/// THIS shape family (the ADT-return recognizer's payload resolution only ever
/// produces `Var`/`Const`/`Move`/`Discriminant`), declined here too for defense
/// in depth.
///
/// Trust: DISCRIMINANT-SWITCH ADT-RETURN (M5 residue #1, 2026-07-08) —
/// `Discriminant base ↦ idxElem (g base) -1`. This witness's environment is
/// [`crate::trustir_anchor::trustir_env`]'s (the TRUST-IR-side registration),
/// which declares [`TRUSTIR_IDX_ELEM`] (`Trust.TrustIr.idxElem`, the SAME
/// opaque selector [`crate::trustir_anchor::IrOperand::Field`] already
/// reuses) — NOT the MirSem-side `Trust.MirSem.idx_elem` (a DIFFERENT,
/// unrelated constant in a DIFFERENT environment; using it here would be an
/// `UnknownConst` kernel rejection, not a soundness issue, but still wrong).
/// The reserved KEY VALUE (`-1`) is shared with
/// [`crate::mirsem::MIRSEM_DISCRIMINANT_TAG_KEY`] purely for documentation
/// parity across the two sides — its numeric value carries no independent
/// soundness burden here (this witness is MODEL-ONLY / self-contained, never
/// compared against the MirSem carrier), only that it is a KEY, applied
/// consistently within this one witness. UNINTERPRETED, TOTAL,
/// DETERMINISTIC — asserts NOTHING about the tag's actual bit pattern, the
/// honest tier a discriminant-switch GUARD needs (the
/// `Ordering::reverse`-class shape
/// [`crate::mirsem::sem_adt_return_shape_of_discriminant_switch3`]
/// recognizes). ZERO new Clean declaration: `TRUSTIR_IDX_ELEM` is ALREADY
/// registered by `trustir_env()` for the field-read leaf.
// Trust: MULTI-VALUE SwitchInt leaf — widened to `pub(crate)` (body unchanged) so
// the sibling `trustir_multieq` module can resolve its own guard/arm `SemOperand`s
// in the SAME anchor vocabulary without duplicating this small converter (the SAME
// widening rationale as `trustir_anchor`'s `cst`/`env_ty`/`int_lit`/`eq_bool_true`/
// `eq_bool_false`).
pub(crate) fn sem_operand_to_expr(op: &SemOperand, e_bvar: u32) -> Option<Expr> {
    match op {
        SemOperand::Var(p) => Some(Expr::app(Expr::bvar(e_bvar), Expr::nat_lit(*p))),
        SemOperand::Const(c) => Some(int_lit(*c)),
        SemOperand::Move(inner) => sem_operand_to_expr(inner, e_bvar),
        // Trust: DISCRIMINANT-SWITCH ADT-RETURN — the reserved-key `idxElem`
        // carrier (see this fn's doc).
        SemOperand::Discriminant(base) => Some(Expr::apps(
            cst(TRUSTIR_IDX_ELEM),
            [sem_operand_to_expr(base, e_bvar)?, int_lit(MIRSEM_DISCRIMINANT_TAG_KEY)],
        )),
        // Trust: W20 REFERENCE-RETURN (value-tier reference denotation, 2026-07-21) —
        // the `Some(&s[i])` / `SliceIndex::get` slice-element-reference return lane.
        // `Index s i` denotes `idxElem (⟦s⟧) (⟦i⟧)` and `Len s` denotes `sliceLen (⟦s⟧)`,
        // the SAME opaque total selectors the array-index scalar lane and the field-read
        // leaf already ground through — byte-identical to `trustir_anchor::
        // operand_denotation`'s `IrOperand::Index`/`Len` cases (each IH is the recursive
        // `sem_operand_to_expr` call on that sub-operand). ZERO new Clean declarations:
        // `idxElem`/`sliceLen` are already `Declaration::Opaque` with EMPTY axiom_deps,
        // so the closed refinement term gains no axiom dependency (modulo-3 closure
        // preserved). VALUE-TIER CLAIM (verbatim): an immutable reference RETURN denotes
        // its referent's ELEMENT VALUE at the idx_elem tier — `Some(&s[0])` certifies as
        // "Some of the element-0 value-slot" — `idxElem(s, 0)` — deref-transparently,
        // consistent with W-REF-FWD's ref/deref cancellation and &self-param
        // transparency. This is NOT an address/aliasing claim: it asserts NOTHING about
        // addresses, reference identity, aliasing, liveness/validity, or the element's
        // concrete value — only that it denotes SOME Int stably determined by (s, i).
        SemOperand::Index(base, idx) => Some(Expr::apps(
            cst(TRUSTIR_IDX_ELEM),
            [sem_operand_to_expr(base, e_bvar)?, sem_operand_to_expr(idx, e_bvar)?],
        )),
        SemOperand::Len(base) => {
            Some(Expr::app(cst(TRUSTIR_SLICE_LEN), sem_operand_to_expr(base, e_bvar)?))
        }
        // Trust: ITER-NEXT VALUE-PATH (2026-07-21) — the ENTRY-TIME remaining-region
        // handle `IterRegion(p)` denotes `Trust.MirSem.iter_region (e p)` (the OPAQUE
        // total `Int → Int` handle constructor; see `TRUSTIR_ITER_REGION`). It appears
        // ONLY as the base of an `Index(IterRegion(p), Const 0)` payload, so the existing
        // `Index` arm above recurses into this arm and composes `idxElem(iter_region(e p),
        // 0)` — the element-0 value-slot of the entry region — with ZERO new axiom
        // dependency (both selectors `Opaque`, EMPTY axiom_deps, modulo-3 preserved). The
        // argument `e p` is BYTE-IDENTICAL to the `Var(p)` arm's env-application, so the
        // handle is rooted at the SAME `&mut Iter` param the guard's `IterHasNext(p)` reads
        // (coherence enforces the indices match). It is NEVER def-eq across two distinct
        // opaque keys, so a wrong-index / wrong-handle claim is kernel-REJECTED.
        SemOperand::IterRegion(p) => Some(Expr::app(
            cst(TRUSTIR_ITER_REGION),
            Expr::app(Expr::bvar(e_bvar), Expr::nat_lit(*p)),
        )),
        // Trust: RECORD-WITNESS (2026-07-22) — a struct-FIELD READ operand
        // `Field base fld` denotes `idxElem ⟦base⟧ (lit fld)`, the SAME opaque total
        // selector `Index`/`Discriminant` ground through (mirsem's `to_operand_expr`
        // Field-as-`Index base (Const fld)` desugar, mirsem.rs:2355). ASSERT (do NOT
        // assume) the non-negative field key is DISJOINT from the reserved negative
        // keys (`Discriminant` = -1, cast keys ≤ -2): a real `Field(fld: u64)` index is
        // always ≥ 0, so it can NEVER collide with a reserved key — a `Field(s, 0)` and a
        // `Discriminant(s)` on the SAME base stay provably distinct opaque applications.
        // ZERO new Clean declaration (`TRUSTIR_IDX_ELEM` is already `Opaque`, EMPTY
        // axiom_deps). VALUE-TIER: SOME Int stably determined by (base, fld); no
        // address/aliasing/validity content.
        SemOperand::Field(base, fld) => {
            let key = i128::from(*fld);
            debug_assert!(
                key >= 0 && key != MIRSEM_DISCRIMINANT_TAG_KEY,
                "a real field index is non-negative and disjoint from reserved negative idxElem keys"
            );
            if key < 0 {
                return None; // belt-and-suspenders (unreachable for a `u64` field index).
            }
            Some(Expr::apps(
                cst(TRUSTIR_IDX_ELEM),
                [sem_operand_to_expr(base, e_bvar)?, int_lit(key)],
            ))
        }
        _ => None,
    }
}

/// The guard `Bool` term for an arbitrary [`SemCmpOp`] comparison — mirrors
/// `clean_ground::ground_bool`'s Rust-side case analysis (`Gt`/`Ge` are the SWAPPED
/// `Lt`/`Le`; see its doc) over the SAME `decide`/`Int.decLt`/`Int.decLe`/`Int.beq`/
/// `Bool.not` prelude vocabulary `IrGuardedIndex::guard_bool` already uses for its one
/// hardcoded `Lt` — generalized here to the FULL comparison set the cast-crate
/// fallible-impl guard family actually uses (`half_promotion!`'s `<`, `from_unsigned!`'s
/// `>`, …).
fn guard_bool(op: SemCmpOp, a: &Expr, b: &Expr) -> Expr {
    let decide = |rel: &str, dec: &str, x: Expr, y: Expr| {
        Expr::apps(
            cst("decide"),
            [Expr::apps(cst(rel), [x.clone(), y.clone()]), Expr::apps(cst(dec), [x, y])],
        )
    };
    match op {
        SemCmpOp::Lt => decide("Int.lt", "Int.decLt", a.clone(), b.clone()),
        SemCmpOp::Le => decide("Int.le", "Int.decLe", a.clone(), b.clone()),
        // Gt(a,b) ≡ Lt(b,a); Ge(a,b) ≡ Le(b,a) — SWAPPED operands (mirrors ground_bool).
        SemCmpOp::Gt => decide("Int.lt", "Int.decLt", b.clone(), a.clone()),
        SemCmpOp::Ge => decide("Int.le", "Int.decLe", b.clone(), a.clone()),
        SemCmpOp::Eq => Expr::apps(cst("Int.beq"), [a.clone(), b.clone()]),
        SemCmpOp::Ne => {
            Expr::app(cst("Bool.not"), Expr::apps(cst("Int.beq"), [a.clone(), b.clone()]))
        }
    }
}

/// Build the guard's `Bool` term from a [`SemCondTree`] at binder depth `e_bvar`.
/// Declines (`None`) a CONJUNCTIVE `And` guard — out of scope for this increment (the
/// cast-crate fallible-impl target family's guards are all single comparisons; a
/// conjunctive-guard ADT-return is a follow-up, not a silent misdenotation: this
/// simply declines, same as every other fail-closed clause here).
fn cond_bool(cond: &SemCondTree, e_bvar: u32) -> Option<Expr> {
    match cond {
        SemCondTree::Leaf(c) => {
            let a = sem_operand_to_expr(&c.a, e_bvar)?;
            let b = sem_operand_to_expr(&c.b, e_bvar)?;
            Some(guard_bool(c.op, &a, &b))
        }
        // Trust: ITER-NEXT VALUE-PATH (2026-07-21) — the OPAQUE dispatch head
        // `IterHasNext(p)` denotes `Trust.MirSem.iter_has_next (e p) : Bool` (see
        // `TRUSTIR_ITER_HAS_NEXT`). The guard's kernel meaning is ABSTRACT: it is NOT the
        // concrete `Int.beq(cursor, end)` term — its tie to the real `ptr != end` guard is
        // enforced by the recognizer, so the certificate assumes no bridge premise. Used
        // as the `Bool.rec` scrutinee: `guard = true → Some(idxElem(iter_region(e p), 0))`.
        // Its `e p` argument carries the SAME param index as the payload's `IterRegion(p)`
        // (coherence enforces this), so guard and payload provably observe ONE handle at
        // ONE time (entry).
        SemCondTree::IterHasNext(p) => Some(Expr::app(
            cst(TRUSTIR_ITER_HAS_NEXT),
            Expr::app(Expr::bvar(e_bvar), Expr::nat_lit(*p)),
        )),
        // A conjunctive / disjunctive guard is out of scope for the ADT-return witness
        // (declined, same fail-closed posture as before).
        SemCondTree::And(..) | SemCondTree::Or(..) => None,
    }
}

// ---------------------------------------------------------------------------
// Carrier synthesis + registration — reuses the EXISTING Phase-4 enum reflection
// (`reflect::reflect_enum` / `clean_ground::register_adt_carriers`) UNCHANGED; this
// module only BUILDS the `trust_types::Ty::adt_enum(..)` input from the recognized
// shape.
// ---------------------------------------------------------------------------

/// The `Ty` for a freshly-synthesized SINGLE-VARIANT "stub" enum — used for a NESTED
/// `NullaryNested` payload (the `Error::Underflow`-class shape). This is DELIBERATELY
/// NOT a faithful reconstruction of the real Rust enum's full variant set (Error, e.g.,
/// really has 4 variants) — it only asserts "the payload IS constructor `V<variant>`",
/// which is exactly what the recognized MIR shape constructs and nothing more. Sound:
/// no claim is made about any OTHER variant.
fn nested_stub_ty(enum_name: &str, variant: i128) -> trust_types::Ty {
    use trust_types::{Ty, VariantDef};
    Ty::adt_enum(
        enum_name.to_string(),
        vec![VariantDef { name: format!("V{variant}"), discriminant: variant, fields: vec![] }],
    )
}

/// The outer enum's per-arm [`trust_types::VariantDef`] — a nullary variant (no
/// payload), a single SCALAR field (an `Int` carrier — any storage width decodes to
/// the SAME kernel `Int` type via `clean_ground::decode_el_code`'s `BitVec ↦ Int`
/// collapse; an [`SemAdtPayload::IntCast`] still retains and interprets its MIR
/// destination width before that value enters the constructor), or a single
/// NESTED-enum field (the
/// [`nested_stub_ty`] carrier).
fn nested_arm_name(enum_name: &str, position: usize) -> String {
    format!("{enum_name}#adt-return-{position}")
}

fn variant_def_for_arm(arm: &SemAdtArm, position: usize) -> trust_types::VariantDef {
    use trust_types::{Ty, VariantDef};
    let fields = match &arm.payload {
        None => vec![],
        // Trust: RECORD-WITNESS inc-2 — a `DowncastField` payload denotes to an `Int`
        // (`idxElem`), so its carrier field type is the SAME `Int{64}` as a scalar.
        Some(
            SemAdtPayload::Scalar(_)
            | SemAdtPayload::IntCast { .. }
            | SemAdtPayload::DowncastField { .. },
        ) => {
            vec![("0".to_string(), Ty::Int { width: 64, signed: true })]
        }
        Some(SemAdtPayload::NullaryNested { enum_name, variant }) => {
            vec![("0".to_string(), nested_stub_ty(&nested_arm_name(enum_name, position), *variant))]
        }
    };
    VariantDef { name: format!("Arm{}", arm.variant), discriminant: arm.variant, fields }
}

/// Register the OUTER enum's 2-variant carrier (+ any NESTED payload carrier a
/// `NullaryNested` arm needs, registered FIRST — dependency order: the outer
/// constructor's field type references the nested inductive by name, so it must
/// already resolve in `env` when the outer inductive is added). Returns
/// `(then_ctor_name, else_ctor_name, then_nested_closed_val, else_nested_closed_val,
/// outer_adt_name)`. `None` (fail-closed) if either registration is declined —
/// `register_adt_carriers` silently skips an inductive whose `add_inductive`/
/// axiom-gate fails, detected here by re-`get`-ing the registry.
///
/// Each nested payload is registered under an arm-position-qualified internal name.
/// This is load-bearing when both outer arms contain different variants of the same
/// Rust enum: name-idempotent carrier registration must not reuse arm 0's one-variant
/// stub for arm 1 and silently substitute the wrong nested constructor.
fn register_outer_enum(
    env: &mut Environment,
    r: &SemAdtReturn,
) -> Option<(String, String, Option<Expr>, Option<Expr>, String)> {
    let mut then_nested_val: Option<Expr> = None;
    let mut else_nested_val: Option<Expr> = None;
    for (position, (arm, slot)) in
        [(&r.then_arm, &mut then_nested_val), (&r.else_arm, &mut else_nested_val)]
            .into_iter()
            .enumerate()
    {
        if let Some(SemAdtPayload::NullaryNested { enum_name, variant }) = &arm.payload {
            let nested_ty = nested_stub_ty(&nested_arm_name(enum_name, position), *variant);
            let nested_carrier = crate::reflect::reflect_enum(&nested_ty)?;
            let name = nested_carrier.name.clone();
            let registry = crate::clean_ground::register_adt_carriers(
                env,
                std::slice::from_ref(&nested_carrier),
            );
            let confirmed = registry.get(&name)?;
            let ctor_name = confirmed.constructors.first()?.name.clone();
            *slot = Some(Expr::const_(Name::from_string(&ctor_name), LevelVec::new()));
        }
    }

    let then_def = variant_def_for_arm(&r.then_arm, 0);
    let else_def = variant_def_for_arm(&r.else_arm, 1);
    let outer_ty = trust_types::Ty::adt_enum(r.enum_name.clone(), vec![then_def, else_def]);
    let outer_carrier = crate::reflect::reflect_enum(&outer_ty)?;
    let name = outer_carrier.name.clone();
    let registry =
        crate::clean_ground::register_adt_carriers(env, std::slice::from_ref(&outer_carrier));
    let confirmed = registry.get(&name)?;
    let then_ctor_name = confirmed.constructors.first()?.name.clone();
    let else_ctor_name = confirmed.constructors.get(1)?.name.clone();
    Some((then_ctor_name, else_ctor_name, then_nested_val, else_nested_val, name))
}

/// A concrete `2^width` term using only the arithmetic constants already present in
/// the fresh TrustIR anchor environment.  Values through `2^126` are ordinary
/// positive `i128` literals; the two larger powers needed by `i128`/`u128` casts use
/// one multiplication of representable literals.  This keeps the model independent
/// of the larger bridge environment's optional `Int.pow` without building a
/// 128-node multiplication chain into every proof.
fn int_pow2_expr(width: u32) -> Expr {
    match width {
        0..=126 => int_lit(1_i128 << width),
        127 => Expr::apps(cst("Int.mul"), [int_lit(1_i128 << 63), int_lit(1_i128 << 64)]),
        128 => Expr::apps(cst("Int.mul"), [int_lit(1_i128 << 64), int_lit(1_i128 << 64)]),
        _ => unreachable!("integer cast width is validated before power construction"),
    }
}

/// Exact mathematical value of a Rust integer cast.  Integer `as` conversion first
/// reduces modulo `2^width`; signed destinations then interpret the upper half of
/// that residue class as negative.  The anchor environment's `Int.mod` is truncated
/// remainder, so a negative remainder is explicitly shifted into `[0, 2^width)`.
/// All operations are ordinary axiom-free Clean prelude terms, so the branch-
/// refinement theorem checks the cast expression itself instead of silently
/// replacing a narrowing/sign-changing cast with its source.
fn int_cast_expr(source: &SemOperand, width: u32, signed: bool, e_bvar: u32) -> Option<Expr> {
    if !matches!(width, 8 | 16 | 32 | 64 | 128) {
        return None;
    }
    let source = sem_operand_to_expr(source, e_bvar)?;
    let modulus = int_pow2_expr(width);
    let remainder = Expr::apps(cst("Int.mod"), [source, modulus.clone()]);
    let negative_remainder = Expr::apps(
        cst("decide"),
        [
            Expr::apps(cst("Int.lt"), [remainder.clone(), int_lit(0)]),
            Expr::apps(cst("Int.decLt"), [remainder.clone(), int_lit(0)]),
        ],
    );
    let int_motive = || Expr::lam(bd(), cst("Bool"), cst("Int"));
    let bool_rec = || Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let wrapped = Expr::apps(
        bool_rec(),
        [
            int_motive(),
            remainder.clone(),
            Expr::apps(cst("Int.add"), [remainder, modulus.clone()]),
            negative_remainder,
        ],
    );
    if !signed {
        return Some(wrapped);
    }
    let half = int_pow2_expr(width - 1);
    let upper_half = Expr::apps(
        cst("decide"),
        [
            Expr::apps(cst("Int.le"), [half.clone(), wrapped.clone()]),
            Expr::apps(cst("Int.decLe"), [half, wrapped.clone()]),
        ],
    );
    let negative = Expr::apps(cst("Int.sub"), [wrapped.clone(), modulus]);
    Some(Expr::apps(bool_rec(), [int_motive(), wrapped, negative, upper_half]))
}

/// Build ONE arm's constructed-value `Expr` at binder depth `e_bvar`: the registered
/// constructor const applied to its payload (a scalar env-read, an exact integer
/// cast, a nested closed ctor value, or no argument at all for a nullary variant).
fn arm_value_expr(
    ctor_name: &str,
    payload: &Option<SemAdtPayload>,
    nested_closed_val: Option<&Expr>,
    e_bvar: u32,
) -> Option<Expr> {
    let ctor = Expr::const_(Name::from_string(ctor_name), LevelVec::new());
    match payload {
        None => Some(ctor),
        Some(SemAdtPayload::Scalar(op)) => Some(Expr::app(ctor, sem_operand_to_expr(op, e_bvar)?)),
        Some(SemAdtPayload::IntCast { source, width, signed }) => {
            Some(Expr::app(ctor, int_cast_expr(source, *width, *signed, e_bvar)?))
        }
        // Trust: RECORD-WITNESS inc-2 (ok/err, 2026-07-22) — a DOWNCAST-FIELD payload
        // denotes through the EXISTING `sem_operand_to_expr` `Field`-as-`idxElem` path:
        // `ctor (idxElem ⟦Var(base_param)⟧ flat_key)`, with the VARIANT-DISJOINT flattened
        // key so the theorem builder is UNCHANGED (a denotation extension, not a recipe
        // change). The key is ≥ 1, so it is disjoint from the reserved negative keys.
        Some(SemAdtPayload::DowncastField { base_param, flat_key, .. }) => {
            let field = SemOperand::Field(Box::new(SemOperand::Var(*base_param)), *flat_key);
            Some(Expr::app(ctor, sem_operand_to_expr(&field, e_bvar)?))
        }
        Some(SemAdtPayload::NullaryNested { .. }) => {
            Some(Expr::app(ctor, nested_closed_val?.clone()))
        }
    }
}

// ---------------------------------------------------------------------------
// The refinement statement + proof — the `IrGuardedIndex` congrArg-transport recipe,
// generalized from `Int` to the registered outer ADT's OWN type.
// ---------------------------------------------------------------------------

/// Build `(env, statement, proof)`: `env` carries the freshly-registered outer (+
/// nested) ADT carrier(s); `statement` is `∀ (e:Env), guard e = true → select e =
/// <claimed OR then_val>`; `proof` is the `congrArg`-transport witness (ALWAYS a proof
/// of `select = then_val` — its TYPE, not its content, is what `claimed` can decouple
/// from). `None` (fail-closed) on any unresolved piece (an unsupported guard, a
/// payload outside the modeled fragment, a carrier registration failure).
///
/// `claimed` overrides the statement's RHS — `None` for the real, honest claim (the
/// PUBLIC [`check_adt_return_refinement`] always passes `None`); `Some(wrong_rhs)` is
/// the FAIL-CLOSED PROBE mechanism (mirrors `trustir_anchor::branch_refinement_statement`'s
/// `claimed` parameter exactly): the proof's ACTUAL type is `select = then_val`
/// regardless, so a `claimed` NOT def-eq to `then_val` makes `check_type` reject —
/// proving the recipe is GENUINE (not a tautology that accepts anything).
fn build_refinement(r: &SemAdtReturn, claimed: Option<&Expr>) -> Option<(Environment, Expr, Expr)> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (then_ctor, else_ctor, then_nested, else_nested, adt_name) =
        register_outer_enum(&mut env, r)?;
    let adt_ty = || Expr::const_(Name::from_string(&adt_name), LevelVec::new());
    let l1 = Level::succ(Level::zero());

    // STATEMENT: ∀ (e:Env), guard e = true → select e = <claimed OR then_val>.  Under
    // `λ e`: e=0.
    let guard0 = cond_bool(&r.cond, 0)?;
    let guard_eq = eq_bool_true(guard0);
    // Under `λ e λ hg`: hg=0, e=1.
    let then_v1 = arm_value_expr(&then_ctor, &r.then_arm.payload, then_nested.as_ref(), 1)?;
    let else_v1 = arm_value_expr(&else_ctor, &r.else_arm.payload, else_nested.as_ref(), 1)?;
    let guard1 = cond_bool(&r.cond, 1)?;
    let lhs = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), adt_ty());
        Expr::apps(bool_rec, [motive, else_v1, then_v1.clone(), guard1])
    };
    let rhs = claimed.cloned().unwrap_or_else(|| then_v1.clone());
    let eq =
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![l1.clone()]), [adt_ty(), lhs, rhs]);
    let statement = Expr::pi(bd(), env_ty(), Expr::pi(bd(), guard_eq, eq));

    // PROOF (genuine — uses the guard hypothesis via `congrArg` transport, mirroring
    // `guarded_index_refinement`'s proof EXACTLY, `Int` swapped for `adt_ty()`):
    //   congrArg (λ x:Bool. Bool.rec (λ_.AdtTy) else_val then_val x) hg
    //     : (Bool.rec … guard) = (Bool.rec … Bool.true)
    // and `Bool.rec … Bool.true` ι-reduces to `then_val` (the TRUE minor) — so the term
    // has type `select = then_val`, EXACTLY the statement codomain. A WRONG claim (the
    // else-arm's value, or the other variant's tag) is NOT def-eq to that reduct, so
    // `check_type` rejects it (the fail-closed regression test below probes this).
    let f = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), adt_ty());
        // Under `λ e λ hg λ x`: x=0, hg=1, e=2.
        let then_v2 = arm_value_expr(&then_ctor, &r.then_arm.payload, then_nested.as_ref(), 2)?;
        let else_v2 = arm_value_expr(&else_ctor, &r.else_arm.payload, else_nested.as_ref(), 2)?;
        let select_x = Expr::apps(bool_rec, [motive, else_v2, then_v2, Expr::bvar(0)]);
        Expr::lam(bd(), cst("Bool"), select_x)
    };
    let guard1_for_proof = cond_bool(&r.cond, 1)?;
    let congr = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [cst("Bool"), adt_ty(), guard1_for_proof, cst("Bool.true"), f, Expr::bvar(0)],
    );
    let guard0_for_proof = cond_bool(&r.cond, 0)?;
    let proof = Expr::lam(bd(), env_ty(), Expr::lam(bd(), eq_bool_true(guard0_for_proof), congr));

    Some((env, statement, proof))
}

/// The FALSE-arm sibling of [`build_refinement`].  A complete two-way return
/// certificate must establish both observations: the historical true-arm theorem
/// alone left the function's behavior under `guard = false` unconstrained.
fn build_refinement_else(
    r: &SemAdtReturn,
    claimed: Option<&Expr>,
) -> Option<(Environment, Expr, Expr)> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (then_ctor, else_ctor, then_nested, else_nested, adt_name) =
        register_outer_enum(&mut env, r)?;
    let adt_ty = || Expr::const_(Name::from_string(&adt_name), LevelVec::new());
    let l1 = Level::succ(Level::zero());

    let guard0 = cond_bool(&r.cond, 0)?;
    let guard_eq = eq_bool_false(guard0);
    let then_v1 = arm_value_expr(&then_ctor, &r.then_arm.payload, then_nested.as_ref(), 1)?;
    let else_v1 = arm_value_expr(&else_ctor, &r.else_arm.payload, else_nested.as_ref(), 1)?;
    let guard1 = cond_bool(&r.cond, 1)?;
    let lhs = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), adt_ty());
        Expr::apps(bool_rec, [motive, else_v1.clone(), then_v1, guard1])
    };
    let rhs = claimed.cloned().unwrap_or_else(|| else_v1.clone());
    let eq =
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![l1.clone()]), [adt_ty(), lhs, rhs]);
    let statement = Expr::pi(bd(), env_ty(), Expr::pi(bd(), guard_eq, eq));

    let f = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), adt_ty());
        let then_v2 = arm_value_expr(&then_ctor, &r.then_arm.payload, then_nested.as_ref(), 2)?;
        let else_v2 = arm_value_expr(&else_ctor, &r.else_arm.payload, else_nested.as_ref(), 2)?;
        Expr::lam(
            bd(),
            cst("Bool"),
            Expr::apps(bool_rec, [motive, else_v2, then_v2, Expr::bvar(0)]),
        )
    };
    let congr = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [cst("Bool"), adt_ty(), cond_bool(&r.cond, 1)?, cst("Bool.false"), f, Expr::bvar(0)],
    );
    let proof =
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), eq_bool_false(cond_bool(&r.cond, 0)?), congr));
    Some((env, statement, proof))
}

/// TEST-ONLY: the ELSE arm's constructed-value `Expr` (depth 1, matching
/// [`build_refinement`]'s own `else_v1`) for a recognized [`SemAdtReturn`] — the
/// FAIL-CLOSED PROBE's "wrong claim" (the guard is TRUE, so the honest RHS is the
/// THEN arm's value; claiming the ELSE arm's value instead is a genuine
/// wrong-variant-tag misdenotation, adversarial probe (a)). Builds its OWN carrier
/// registration (a fresh env, discarded) — the returned `Expr` only NAMES the
/// registered constructors, and `adt_inductive_name`/`adt_variant_ctor_name` are pure
/// functions of `r`'s own fields, so the SAME names resolve in the caller's
/// independently-built env.
#[cfg(test)]
fn else_value_for_test(r: &SemAdtReturn) -> Option<Expr> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (_then_ctor, else_ctor, _then_nested, else_nested, _adt_name) =
        register_outer_enum(&mut env, r)?;
    arm_value_expr(&else_ctor, &r.else_arm.payload, else_nested.as_ref(), 1)
}

#[cfg(test)]
fn then_value_for_test(r: &SemAdtReturn) -> Option<Expr> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (then_ctor, _else_ctor, then_nested, _else_nested, _adt_name) =
        register_outer_enum(&mut env, r)?;
    arm_value_expr(&then_ctor, &r.then_arm.payload, then_nested.as_ref(), 1)
}

/// TEST-ONLY, `pub(crate)`: the honest constructor application `S.mk ⟦f_0⟧e … ⟦f_n⟧e`
/// at binder depth 0 (`e` = bvar 0, the position a `claimed` RHS occupies under the
/// single `Π (e:Env)` binder) for a recognized [`SemStructReturn`]. The FAIL-CLOSED
/// PROBE builder: passing the honest value of a TRANSPOSED / wrong-carrier
/// [`SemStructReturn`] as `claimed` against a different one is a genuine
/// misdenotation. Builds its own carrier registration (a fresh env, discarded); the
/// returned `Expr` only NAMES the registered constructor, and the ctor name is a pure
/// function of `r.struct_ty`'s own name, so the SAME name resolves in the caller's
/// independently-built env. `pub(crate)` so the `mirsem::tests` MIR-order-fidelity
/// probe can build a cross-instance claim without duplicating the plumbing.
#[cfg(test)]
pub(crate) fn honest_value_for_test(r: &SemStructReturn) -> Option<Expr> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let carrier = crate::reflect::reflect_struct(&r.struct_ty)?;
    let registry =
        crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
    let confirmed = registry.get(&carrier.name)?;
    let mut app = Expr::const_(Name::from_string(&confirmed.ctor_name), LevelVec::new());
    for field in &r.fields {
        app = Expr::app(app, struct_field_expr(field, 0)?);
    }
    Some(app)
}

/// TEST-ONLY, `pub(crate)`: the SAME "wrong claim" probe mechanism as
/// [`else_value_for_test`], generalized to the 3-arm [`SemAdtReturn3`] and
/// widened to `pub(crate)` so the M5-residue adversarial probes in
/// `mirsem::tests` (the `Ordering::reverse`-class discriminant-switch shape and
/// the `Ord::cmp` `BinOp::Cmp` shape, both producing a `SemAdtReturn3`) can
/// build a cross-arm wrong-claim `Expr` without duplicating the carrier-
/// registration plumbing — arm_c's own closed value (depth 1).
#[cfg(test)]
pub(crate) fn debug_arm_c_value_for_test(r: &SemAdtReturn3) -> Option<Expr> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (_ca, _cb, cc, _na, _nb, nc, _name) = register_outer_enum3(&mut env, r)?;
    arm_value_expr(&cc, &r.arm_c.payload, nc.as_ref(), 1)
}

/// TEST-ONLY, `pub(crate)`: [`debug_arm_c_value_for_test`]'s sibling for arm_b's
/// own closed value (depth 1).
#[cfg(test)]
pub(crate) fn debug_arm_b_value_for_test(r: &SemAdtReturn3) -> Option<Expr> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (_ca, cb, _cc, _na, nb, _nc, _name) = register_outer_enum3(&mut env, r)?;
    arm_value_expr(&cb, &r.arm_b.payload, nb.as_ref(), 1)
}

/// Check the ADT-RETURN refinement for a recognized [`SemAdtReturn`] against the real
/// clean-kernel, modulo 3. Both the true and false observations are checked.
/// GENUINE (each proof's `congrArg` transport GENUINELY consumes its guard
/// hypothesis — the fail-closed regression test asserts a
/// deliberately-wrong claim is `KernelRejected`, not a dressed-up tautology) +
/// MODEL-ONLY (this witness's `env`/carriers are FRESHLY built per call from the
/// recognized shape — see the module doc for the honesty-tier note). Fail-closed
/// (`KernelRejected`) if the shape's guard/payloads fall outside the modeled fragment
/// or a carrier registration is declined.
#[must_use]
pub fn check_adt_return_refinement(r: &SemAdtReturn) -> RefinementVerdict {
    check_adt_return_refinement_claimed(r, None)
}

/// [`check_adt_return_refinement`] with an explicit `claimed` RHS override — the
/// FAIL-CLOSED PROBE entry point (see [`build_refinement`]'s doc). `pub(crate)` so the
/// regression test below (and any future adversarial probe) can construct a
/// deliberately-wrong claim without duplicating the carrier-registration plumbing.
#[must_use]
pub(crate) fn check_adt_return_refinement_claimed(
    r: &SemAdtReturn,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    let (Some(then_obligation), Some(else_obligation)) =
        (build_refinement(r, claimed), build_refinement_else(r, None))
    else {
        return RefinementVerdict::KernelRejected(
            "ADT-return: shape/carrier outside the modeled fragment".to_string(),
        );
    };
    let mut residue_names = Vec::new();
    for (suffix, (mut env, statement, proof)) in
        [("then", then_obligation), ("else", else_obligation)]
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("check_type[{suffix}]: {e:?}"));
        }
        drop(tc);
        let name = Name::from_string(&format!("Trust.TrustIr.Refinement.adt_return_{suffix}"));
        if let Err(e) = env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        }) {
            return RefinementVerdict::KernelRejected(format!("add_decl[{suffix}]: {e:?}"));
        }
        match env.axiom_deps(&name) {
            Some(residue) => residue_names.extend(residue.iter().map(ToString::to_string)),
            None => {
                return RefinementVerdict::KernelRejected(format!(
                    "decl not found after add[{suffix}]"
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

// ---------------------------------------------------------------------------
// Trust: W-PRIMED increment 1 (2026-07-22) — the T-STEP POST-STATE certificate quadruple
// over the two-key (generation-re-keyed) primed surface `iter_seq`/`iter_len`/
// `iter_has_next2`. A NEW sibling to `check_adt_return_refinement`: `SemAdtReturn` is NOT
// extended and `CalleeFact` is NOT touched (increment 1 is CALL-SITE-INERT). The quadruple
// (T-VAL2/T-NONE2/T-POST-SOME/T-POST-NONE) is four lowered-shape equalities over the
// per-certificate Definitions `ret2`/`post2` with the generation key UNBOUND (uninstantiated
// at any call site). The proof recipe is the SAME `Bool.rec` + `congrArg`-transport
// `check_adt_return_refinement` uses, quantified over `recv g : Int` (plain Pi) instead of
// `Env` — NO induction, NO imported-Lean structural recursion (the brecOn refusal is not in
// play here). HONESTY: these are RECOGNIZER-MINT-LICENSED lowered-shape equalities (the SAME
// thin tier as the landed T-SOME/T-NONE); the per-call step half of P-ITER-COUNT REMAINS NOT
// kernel-checked (that is increment 2's loopInvariantRule composition), and the real-code
// bridge (compiled `next()` vs the model) stays the recognizer's fail-closed structural
// attestation. NO new axioms: `iter_seq`/`iter_len` are Opaque-empty-deps, `iter_has_next2`
// is an axiom-free Definition, and the Option carrier passes the modulo-3 axiom gate.
// ---------------------------------------------------------------------------

/// The per-certificate `ret2`/`post2` Definition names (a single pinned certificate:
/// `<core::slice::iter::Iter as Iterator>::next`). Registered fresh per obligation into the
/// witness env. Neither references the one-arg `iter_region`/`iter_has_next` family (F-BRIDGE).
const ITER_STEP_RET2: &str = "Trust.MirSem.iter_next.ret2";
const ITER_STEP_POST2: &str = "Trust.MirSem.iter_next.post2";

/// Which of the four T-STEP theorems to build/check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IterStepThm {
    /// T-VAL2:  `iter_has_next2 recv g = true  → ret2 recv g = mkSome (iter_seq recv g)`.
    Val2,
    /// T-NONE2: `iter_has_next2 recv g = false → ret2 recv g = mkNone`.
    None2,
    /// T-POST-SOME: `iter_has_next2 recv g = true  → post2 recv g = Int.add g 1`.
    PostSome,
    /// T-POST-NONE: `iter_has_next2 recv g = false → post2 recv g = g`.
    PostNone,
}

/// The four T-STEP obligations, checked as a set by [`check_iter_step_refinement`].
const ITER_STEP_THMS: [IterStepThm; 4] =
    [IterStepThm::Val2, IterStepThm::None2, IterStepThm::PostSome, IterStepThm::PostNone];

// Two-key primed-surface term builders (free — no capture). `recv_b`/`g_b` are the de-Bruijn
// indices of the `recv`/`g` binders at the point of use.
fn iter_seq_e(recv_b: u32, g_b: u32) -> Expr {
    Expr::apps(cst(TRUSTIR_ITER_SEQ), [Expr::bvar(recv_b), Expr::bvar(g_b)])
}
fn iter_has_next2_e(recv_b: u32, g_b: u32) -> Expr {
    Expr::apps(cst(TRUSTIR_ITER_HAS_NEXT2), [Expr::bvar(recv_b), Expr::bvar(g_b)])
}
fn int_add1_e(g_b: u32) -> Expr {
    Expr::apps(cst("Int.add"), [Expr::bvar(g_b), int_lit(1)])
}

/// Build the witness env: `trustir_env()` (already carrying `iter_seq`/`iter_len`/
/// `iter_has_next2`) + the freshly-registered Option 2-variant carrier + the per-certificate
/// `ret2`/`post2` Definitions. Returns `(env, some_ctor, none_ctor, option_ty_name)`.
/// `None` (fail-closed) on a carrier decline or a Definition that fails to typecheck.
fn build_iter_step_env(step: &SemIterStep) -> Option<(Environment, String, String, String)> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    // Register the Option carrier (Some(Int) / None) through the UNCHANGED reflect path (the
    // `cond`/`recv_param` are irrelevant to carrier registration — only the arms/enum_name).
    let opt = SemAdtReturn {
        cond: SemCondTree::IterHasNext(step.recv_param),
        then_arm: SemAdtArm {
            variant: 1,
            payload: Some(SemAdtPayload::Scalar(SemOperand::Const(0))),
        },
        else_arm: SemAdtArm { variant: 0, payload: None },
        enum_name: "core::option::Option".to_string(),
    };
    let (some_ctor, none_ctor, _tn, _en, opt_name) = register_outer_enum(&mut env, &opt)?;

    let l1 = Level::succ(Level::zero());
    let bool_rec = || Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);

    // ret2 := λ recv g. Bool.rec (λ_:Bool. Option) mkNone (mkSome (iter_seq recv g))
    //                            (iter_has_next2 recv g)     -- under λ recv λ g: recv=1, g=0.
    let ret2_body = {
        let motive = Expr::lam(bd(), cst("Bool"), cst(&opt_name));
        let some = Expr::app(cst(&some_ctor), iter_seq_e(1, 0));
        let rec = Expr::apps(
            bool_rec(),
            [motive, cst(&none_ctor), some, iter_has_next2_e(1, 0)],
        );
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), rec))
    };
    let ret2_ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), cst(&opt_name)));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(ITER_STEP_RET2),
        level_params: vec![],
        type_: ret2_ty,
        value: ret2_body,
        is_reducible: true,
    })
    .ok()?;

    // post2 := λ recv g. Bool.rec (λ_:Bool. Int) g (Int.add g 1) (iter_has_next2 recv g).
    let post2_body = {
        let motive = Expr::lam(bd(), cst("Bool"), int_ty());
        let rec = Expr::apps(
            bool_rec(),
            [motive, Expr::bvar(0), int_add1_e(0), iter_has_next2_e(1, 0)],
        );
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), rec))
    };
    let post2_ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(ITER_STEP_POST2),
        level_params: vec![],
        type_: post2_ty,
        value: post2_body,
        is_reducible: true,
    })
    .ok()?;

    Some((env, some_ctor, none_ctor, opt_name))
}

/// Build `(env, statement, proof)` for ONE T-STEP obligation. `statement` is
/// `∀ (recv g : Int), iter_has_next2 recv g = <pol> → <ret2|post2> recv g = <claimed OR
/// honest minor>`; `proof` is the `congrArg`-transport witness (ALWAYS a proof of
/// `<def> recv g = <honest minor>` — its TYPE, not content, is what `claimed` decouples from).
/// `claimed` overrides the RHS (the FAIL-CLOSED PROBE mechanism, EXACTLY `build_refinement`'s).
fn build_iter_step_obligation(
    step: &SemIterStep,
    thm: IterStepThm,
    claimed: Option<&Expr>,
) -> Option<(Environment, Expr, Expr)> {
    let (env, some_ctor, none_ctor, opt_name) = build_iter_step_env(step)?;
    let l1 = Level::succ(Level::zero());
    let pol = matches!(thm, IterStepThm::Val2 | IterStepThm::PostSome);
    let is_ret2 = matches!(thm, IterStepThm::Val2 | IterStepThm::None2);
    let def_name = if is_ret2 { ITER_STEP_RET2 } else { ITER_STEP_POST2 };
    let motive_ty = || if is_ret2 { cst(&opt_name) } else { int_ty() };
    let def_e = |recv_b: u32, g_b: u32| {
        Expr::apps(cst(def_name), [Expr::bvar(recv_b), Expr::bvar(g_b)])
    };
    // The `Bool.rec` minors at a given (recv_b, g_b) — false (else) and true (then).
    let false_minor = |g_b: u32| -> Expr {
        if is_ret2 { cst(&none_ctor) } else { Expr::bvar(g_b) }
    };
    let true_minor = |recv_b: u32, g_b: u32| -> Expr {
        if is_ret2 { Expr::app(cst(&some_ctor), iter_seq_e(recv_b, g_b)) } else { int_add1_e(g_b) }
    };

    // STATEMENT (under `Π recv Π g Π hg`): at the eq, recv=2, g=1, hg=0; at `Π hg`, recv=1, g=0.
    let hyp_ty = {
        let hn = iter_has_next2_e(1, 0);
        if pol { eq_bool_true(hn) } else { eq_bool_false(hn) }
    };
    let honest_rhs = if pol { true_minor(2, 1) } else { false_minor(1) };
    let rhs = claimed.cloned().unwrap_or(honest_rhs);
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
        [motive_ty(), def_e(2, 1), rhs],
    );
    let statement =
        Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::pi(bd(), hyp_ty.clone(), eq)));

    // PROOF: `λ recv g hg. congrArg Bool motive_ty (iter_has_next2 recv g) <target> f hg`,
    //   f := `λ x:Bool. Bool.rec (λ_.motive_ty) <false'> <true'> x`. Under `λ recv λ g λ hg`,
    //   congr sees recv=2,g=1,hg=0; inside f (extra `λ x`) recv=3,g=2,x=0.
    //   `f (iter_has_next2 recv g)` δ-matches `<def> recv g` (ret2/post2 reducible); `f <target>`
    //   ι-reduces to the honest minor — so the term has type `<def> recv g = <honest minor>`.
    let f = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), motive_ty());
        let rec = Expr::apps(
            bool_rec,
            [motive, false_minor(2), true_minor(3, 2), Expr::bvar(0)],
        );
        Expr::lam(bd(), cst("Bool"), rec)
    };
    let target = if pol { cst("Bool.true") } else { cst("Bool.false") };
    let congr = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [cst("Bool"), motive_ty(), iter_has_next2_e(2, 1), target, f, Expr::bvar(0)],
    );
    let proof =
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, congr)));

    Some((env, statement, proof))
}

/// Check ONE T-STEP obligation modulo 3 (with an optional `claimed` RHS override for the
/// FAIL-CLOSED forgery probes). `pub(crate)` so the probe suite can build a
/// deliberately-wrong claim without duplicating the plumbing.
#[must_use]
pub(crate) fn iter_step_obligation_verdict(
    step: &SemIterStep,
    thm: IterStepThm,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    let Some((mut env, statement, proof)) = build_iter_step_obligation(step, thm, claimed) else {
        return RefinementVerdict::KernelRejected(
            "iter-step: shape/carrier outside the modeled fragment".to_string(),
        );
    };
    let tc = TypeChecker::new(&env);
    if let Err(e) = tc.check_type(&proof, &statement) {
        return RefinementVerdict::KernelRejected(format!("check_type[{thm:?}]: {e:?}"));
    }
    drop(tc);
    let name = Name::from_string(&format!("Trust.TrustIr.Refinement.iter_step_{thm:?}"));
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add_decl[{thm:?}]: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            RefinementVerdict::Residue(residue.iter().map(ToString::to_string).collect())
        }
        None => RefinementVerdict::KernelRejected(format!("decl not found after add[{thm:?}]")),
    }
}

/// Check the full T-STEP certificate quadruple for a recognized [`SemIterStep`] against the
/// real clean-kernel, modulo 3. GENUINE (the `iter_step_obligation_verdict` probes assert
/// deliberately-wrong claims are `KernelRejected`) + MODEL-ONLY (the `env`/carrier are freshly
/// built per call). Fail-closed (`KernelRejected`) on a str-family element (F-STRTYPE — a
/// `str` never denotes a slice element) or any obligation the kernel rejects.
///
/// CALL-SITE-INERT: nothing in the production verdict/cluster/funnel path calls this. See the
/// GATE-ITER-GEN-KEY-DISCIPLINE consumption-seam note on [`SemIterStep`] — increment 2 must land
/// the enumerated-chokepoint discipline BEFORE any T-STEP consumption.
#[must_use]
pub fn check_iter_step_refinement(step: &SemIterStep) -> RefinementVerdict {
    if matches!(step.element_ty, trust_types::Ty::Str) {
        return RefinementVerdict::KernelRejected(
            "iter-step: str-family element declined (F-STRTYPE)".to_string(),
        );
    }
    let mut residue = Vec::new();
    for thm in ITER_STEP_THMS {
        match iter_step_obligation_verdict(step, thm, None) {
            RefinementVerdict::ProvenModulo3 => {}
            RefinementVerdict::Residue(r) => residue.extend(r),
            rejected @ RefinementVerdict::KernelRejected(_) => return rejected,
        }
    }
    if residue.is_empty() {
        RefinementVerdict::ProvenModulo3
    } else {
        residue.sort();
        residue.dedup();
        RefinementVerdict::Residue(residue)
    }
}

/// TEST-ONLY, `pub(crate)`: resolve the pinned Option carrier's `(some_ctor, none_ctor)` names
/// for a recognized [`SemIterStep`] — the forgery probes need them to build a wrong Some/None
/// RHS. Builds its own carrier registration (a fresh env, discarded); the returned names are
/// pure functions of the Option enum, so they resolve in the probe's independently-built env.
#[cfg(test)]
pub(crate) fn iter_step_option_ctors_for_test(step: &SemIterStep) -> Option<(String, String)> {
    let (_env, some_ctor, none_ctor, _opt) = build_iter_step_env(step)?;
    Some((some_ctor, none_ctor))
}

// ===========================================================================
// Trust: W19 mutators inc-1 (2026-07-24) — THE FIELD-SETTER POST-STATE WITNESS.
//
// The kernel-checked T-SET / T-FRAME pair for `mirsem::SemFieldSet` (the recognized
// `fn set_x(&mut self, v) { self.x = v; }` shape). STRICTLY SIMPLER than the T-STEP
// quadruple: both theorems are Int-valued equalities, so there is NO Option/Unit
// carrier (no `register_outer_enum`) — a single per-certificate `set_post` Definition
// (the `ret2`/`post2` role) plays the selector, and the proof recipe is the
// `Bool.rec` + `congrArg`-transport BYTE-IDENTICAL to `build_iter_step_obligation`
// (case-split the `set_key_eq k fld` guard; the `guard = <pol>` hypothesis transports
// the `Bool.rec` scrutinee to the honest minor, so a wrong claimed RHS is NOT def-eq
// and `check_type` REJECTS it — the fail-closed probe). NO induction, plain Pi over
// Int (not Env). Levels `Bool.rec.{1}`, `Eq.{1}`, `congrArg.{1,1}` — the T-STEP levels
// verbatim.
//
// DESIGN CORRECTION vs the recon's literal bare-opaque wording: a bare opaque
// `idx_elem_prime` has NO defining equations, so it cannot satisfy T-SET/T-FRAME as
// kernel equations. Following the W-PRIMED construction, `idx_elem_prime` is the raw
// CONTENT base (the `iter_seq` role) and the theorems are stated about the `set_post`
// DEFINITION (the `ret2`/`post2` role). No cross-generation `idx_elem_prime(recv,fld,
// g+1) = set_post(...)` bridge is minted — that is the exact F12-forbidden
// cross-instantiation, deferred (see the `SemFieldSet` F12 record).
//
// MODEL-ONLY / RECOGNIZER-MINT-LICENSED thin tier: the certificate proves modulo 3
// that IF a body is a recognized single-scalar-field setter THEN the post-state
// selector equals `v` at the written field and is FRAMED elsewhere — a lowered-shape
// equality, with the compiled-store-vs-model bridge resting entirely on
// `clean_ground::sem_field_set_shape_of`'s fail-closed gates. NO new axioms
// (`idx_elem_prime` Opaque-empty, `set_key_eq` → `Int.beq` empty-deps, `set_post` →
// `Bool.rec`/`idx_elem_prime`/`set_key_eq`/lit, theorems → Eq/congrArg/Bool.rec —
// prelude/foundational). CALL-SITE-INERT: nothing in the production verdict/cluster/
// funnel path calls this.
// ===========================================================================

/// The per-certificate `set_post` Definition name (registered fresh per obligation into
/// the witness env, parameterized by the literal field key). Neither this nor the
/// shared surface references the LIVE 2-arg `idx_elem` field-read family
/// (F12/no-bridge). The load-bearing distinction is 3-arg GENERATION-KEYED vs 2-arg
/// UNTIMED.
pub(crate) const SET_POST: &str = "Trust.MirSem.field_set.set_post";

/// Which of the two field-setter theorems to build/check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FieldSetThm {
    /// T-SET (pol=true):  `set_key_eq k fld = true  → set_post recv k g v = v`.
    Set,
    /// T-FRAME (pol=false): `set_key_eq k fld = false → set_post recv k g v =
    /// idx_elem_prime recv k g`.
    Frame,
}

/// The two field-setter obligations, checked as a set by [`check_field_set_refinement`].
const FIELD_SET_THMS: [FieldSetThm; 2] = [FieldSetThm::Set, FieldSetThm::Frame];

// Field-setter surface term builders (free — no capture). `recv_b`/`k_b`/`g_b`/`v_b` are
// the de-Bruijn indices of the `recv`/`k`/`g`/`v` binders at the point of use.
fn idx_elem_prime_e(recv_b: u32, k_b: u32, g_b: u32) -> Expr {
    Expr::apps(cst(MIRSEM_IDX_ELEM_PRIME), [Expr::bvar(recv_b), Expr::bvar(k_b), Expr::bvar(g_b)])
}
/// `set_key_eq k <fld>` — the key `k` at binder `k_b`, `fld` a closed Int literal.
fn set_key_eq_e(k_b: u32, fld: i128) -> Expr {
    Expr::apps(cst(MIRSEM_SET_KEY_EQ), [Expr::bvar(k_b), int_lit(fld)])
}

/// Build the witness env: `trustir_env()` (already carrying `idx_elem_prime`/
/// `set_key_eq`) + the freshly-registered per-certificate `set_post` Definition,
/// parameterized by the literal field key `fld`. `None` (fail-closed) on a Definition
/// that fails to typecheck.
fn build_field_set_env(fld: i128) -> Option<Environment> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let l1 = Level::succ(Level::zero());
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1]);
    // set_post := λ recv k g v. @Bool.rec (λ_:Bool. Int) (idx_elem_prime recv k g) v
    //                                     (set_key_eq k <fld>)
    // Bool.rec arg order [motive, FALSE_case=frame, TRUE_case=v, scrutinee].
    // Under λ recv λ k λ g λ v: recv = 3, k = 2, g = 1, v = 0.
    let set_post_body = {
        let motive = Expr::lam(bd(), cst("Bool"), int_ty());
        let rec = Expr::apps(
            bool_rec,
            [motive, idx_elem_prime_e(3, 2, 1), Expr::bvar(0), set_key_eq_e(2, fld)],
        );
        Expr::lam(
            bd(),
            int_ty(),
            Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), rec))),
        )
    };
    let set_post_ty = Expr::pi(
        bd(),
        int_ty(),
        Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()))),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string(SET_POST),
        level_params: vec![],
        type_: set_post_ty,
        value: set_post_body,
        is_reducible: true,
    })
    .ok()?;
    Some(env)
}

/// Build `(env, statement, proof)` for ONE field-setter obligation. `statement` is
/// `∀ (recv k g v : Int), set_key_eq k <fld> = <pol> → set_post recv k g v = <claimed OR
/// honest minor>`; `proof` is the `congrArg`-transport witness (ALWAYS a proof of
/// `set_post recv k g v = <honest minor>` — its TYPE, not content, is what `claimed`
/// decouples from). `claimed` overrides the RHS (the FAIL-CLOSED PROBE, EXACTLY
/// `build_iter_step_obligation`'s). BYTE-IDENTICAL recipe, one obligation-pair simpler.
fn build_field_set_obligation(
    fs: &SemFieldSet,
    thm: FieldSetThm,
    claimed: Option<&Expr>,
) -> Option<(Environment, Expr, Expr)> {
    let fld = i128::from(fs.field_key);
    let env = build_field_set_env(fld)?;
    let l1 = Level::succ(Level::zero());
    let pol = matches!(thm, FieldSetThm::Set);
    let set_post_e = |recv_b: u32, k_b: u32, g_b: u32, v_b: u32| {
        Expr::apps(
            cst(SET_POST),
            [Expr::bvar(recv_b), Expr::bvar(k_b), Expr::bvar(g_b), Expr::bvar(v_b)],
        )
    };

    // STATEMENT (under `Π recv Π k Π g Π v Π hg`): at the eq recv=4,k=3,g=2,v=1,hg=0; at
    // `Π hg` (the hg binder TYPE) recv=3,k=2,g=1,v=0.
    let hyp_ty = {
        let guard = set_key_eq_e(2, fld);
        if pol { eq_bool_true(guard) } else { eq_bool_false(guard) }
    };
    // honest minor: TRUE (k==fld) ↦ v; FALSE (k!=fld) ↦ idx_elem_prime recv k g.
    let honest_rhs = if pol { Expr::bvar(1) } else { idx_elem_prime_e(4, 3, 2) };
    let rhs = claimed.cloned().unwrap_or(honest_rhs);
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
        [int_ty(), set_post_e(4, 3, 2, 1), rhs],
    );
    let statement = Expr::pi(
        bd(),
        int_ty(),
        Expr::pi(
            bd(),
            int_ty(),
            Expr::pi(
                bd(),
                int_ty(),
                Expr::pi(bd(), int_ty(), Expr::pi(bd(), hyp_ty.clone(), eq)),
            ),
        ),
    );

    // PROOF: `λ recv k g v hg. congrArg Bool Int (set_key_eq k fld) <target> f hg`,
    //   f := `λ x:Bool. @Bool.rec (λ_:Bool. Int) (idx_elem_prime recv k g) v x`.
    //   Under `λ recv λ k λ g λ v λ hg`: recv=4,k=3,g=2,v=1,hg=0; inside f (extra `λ x`):
    //   recv=5,k=4,g=3,v=2,hg=1,x=0. `f (set_key_eq k fld)` δ-matches `set_post recv k g
    //   v` (set_post reducible); `f <target>` ι-reduces to the honest minor.
    let f = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), int_ty());
        let rec = Expr::apps(
            bool_rec,
            [motive, idx_elem_prime_e(5, 4, 3), Expr::bvar(2), Expr::bvar(0)],
        );
        Expr::lam(bd(), cst("Bool"), rec)
    };
    let target = if pol { cst("Bool.true") } else { cst("Bool.false") };
    let congr = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [cst("Bool"), int_ty(), set_key_eq_e(3, fld), target, f, Expr::bvar(0)],
    );
    let proof = Expr::lam(
        bd(),
        int_ty(),
        Expr::lam(
            bd(),
            int_ty(),
            Expr::lam(
                bd(),
                int_ty(),
                Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, congr)),
            ),
        ),
    );

    Some((env, statement, proof))
}

/// Check ONE field-setter obligation modulo 3 (with an optional `claimed` RHS override
/// for the FAIL-CLOSED forgery probes). `pub(crate)` so the probe suite can build a
/// deliberately-wrong claim without duplicating the plumbing.
#[must_use]
pub(crate) fn field_set_obligation_verdict(
    fs: &SemFieldSet,
    thm: FieldSetThm,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    let Some((mut env, statement, proof)) = build_field_set_obligation(fs, thm, claimed) else {
        return RefinementVerdict::KernelRejected(
            "field-set: shape outside the modeled fragment".to_string(),
        );
    };
    let tc = TypeChecker::new(&env);
    if let Err(e) = tc.check_type(&proof, &statement) {
        return RefinementVerdict::KernelRejected(format!("check_type[{thm:?}]: {e:?}"));
    }
    drop(tc);
    let name = Name::from_string(&format!("Trust.TrustIr.Refinement.field_set_{thm:?}"));
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add_decl[{thm:?}]: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            RefinementVerdict::Residue(residue.iter().map(ToString::to_string).collect())
        }
        None => RefinementVerdict::KernelRejected(format!("decl not found after add[{thm:?}]")),
    }
}

/// Check the full T-SET / T-FRAME certificate pair for a recognized [`SemFieldSet`]
/// against the real clean-kernel, modulo 3. GENUINE (the `field_set_obligation_verdict`
/// probes assert deliberately-wrong claims are `KernelRejected`) + MODEL-ONLY (the `env`
/// is freshly built per call). Fail-closed (`KernelRejected`) on a non-scalar field type
/// (F-NONSCALAR — belt with the recognizer's G8) or any obligation the kernel rejects;
/// residues union. CALL-SITE-INERT: nothing in the production verdict/cluster/funnel path
/// calls this (the `check_iter_step_refinement` posture verbatim).
#[must_use]
pub fn check_field_set_refinement(fs: &SemFieldSet) -> RefinementVerdict {
    if !matches!(fs.field_ty, trust_types::Ty::Int { .. } | trust_types::Ty::Bool) {
        return RefinementVerdict::KernelRejected(
            "field-set: non-scalar field type declined (F-NONSCALAR)".to_string(),
        );
    }
    let mut residue = Vec::new();
    for thm in FIELD_SET_THMS {
        match field_set_obligation_verdict(fs, thm, None) {
            RefinementVerdict::ProvenModulo3 => {}
            RefinementVerdict::Residue(r) => residue.extend(r),
            rejected @ RefinementVerdict::KernelRejected(_) => return rejected,
        }
    }
    if residue.is_empty() {
        RefinementVerdict::ProvenModulo3
    } else {
        residue.sort();
        residue.dedup();
        RefinementVerdict::Residue(residue)
    }
}

// ===========================================================================
// Trust: W19 mutators inc-1.5 (2026-07-24) — THE CHECKED-RMW POST-STATE WITNESS.
//
// The kernel-checked T-SET / T-FRAME pair for `mirsem::SemFieldRmw` (the recognized
// `fn bump(&mut self) { self.x += 1; }` shape). STRUCTURALLY IDENTICAL to the inc-1
// field-setter pair — the `Bool.rec` + `congrArg`-transport recipe is BYTE-IDENTICAL
// (case-split the `set_key_eq k fld` guard; the `guard = <pol>` hypothesis transports
// the `Bool.rec` scrutinee to the honest minor, so a wrong claimed RHS is NOT def-eq
// and `check_type` REJECTS it). The ONE delta: the TRUE minor is no longer the bare
// `v` binder but the ARITHMETIC TERM `Int.<op> (idx_elem_prime recv <fld> g) <rhs>` —
// a function of the PRE-STATE selector at the SAME generation key `g` the frame uses.
// That is the whole content of inc-1.5, and it is why option (iii) (instantiating
// inc-1's ∀v-quantified T-SET at `v := <the term>`) was REJECTED at design: that
// instantiation yields `set_post recv k g <term> = <term>`, a statement about the
// SELECTOR APPLIED TO a value, carrying no information about what the BODY writes. The
// pre-state dependence only appears in the certificate's STATEMENT when the term is
// baked into the per-certificate DEFINITION, which is what `rmw_post` does. Stated that
// way deliberately: `rmw_post` is a definition this certificate itself mints with the
// answer already in it, so both theorems are d/ι-unfoldings. What they buy is that the
// STATEMENT is now pinned to a specific pre-state-dependent term, which the forgery
// probes show cannot be varied (a wrong delta, a wrong op, or an unchanged pre-state
// all fail `check_type`). The faithfulness of that term to the compiled store rests
// wholly on `clean_ground::sem_field_rmw_shape_of`, never on the kernel.
//
// NO NEW DECLARATIONS BEYOND `rmw_post`: `Int.add`/`Int.sub`/`Int.mul` are the
// prelude's REDUCIBLE, axiom-free Definitions already carried by `trustir_env()` (the
// T-STEP quadruple already proves an `Int.add g 1` post-state equality in this exact
// env), and `idx_elem_prime`/`set_key_eq` are the inc-1 surface unchanged. Modulo-3
// preserved; probe-pinned by `field_rmw_surface_has_empty_axiom_deps`.
//
// MODEL-ONLY / RECOGNIZER-MINT-LICENSED thin tier, with a PARTIAL-CORRECTNESS caveat
// that inc-1 does NOT have: see the WRAP-vs-INT FAITHFULNESS RECORD on
// `mirsem::SemFieldRmw`. In one line — the mathematical `Int.<op>` reading of a
// fixed-width machine op is licensed by the program's OWN overflow `Assert`, which the
// mint gate REQUIRES, so the claim holds on normally-returning runs only, and the
// unchecked (wrapping) lowering must never mint. CALL-SITE-INERT: nothing in the
// production verdict/cluster/funnel path calls this.
// ===========================================================================

/// The per-certificate `rmw_post` Definition name (registered fresh per obligation into
/// the witness env, parameterized by the literal field key, the op, and the right-hand
/// operand). Neither this nor the shared surface references the LIVE 2-arg `idx_elem`
/// field-read family (F12/no-bridge), and it is listed in the grounder-decline pin
/// `clean_ground::tests::field_post_preds_are_fail_closed_in_mirsem_grounder`.
pub(crate) const RMW_POST: &str = "Trust.MirSem.field_set.rmw_post";

/// Which of the two checked-RMW theorems to build/check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FieldRmwThm {
    /// T-SET (pol=true): `set_key_eq k fld = true → rmw_post recv k g v =
    /// Int.<op> (idx_elem_prime recv fld g) <rhs>`.
    Set,
    /// T-FRAME (pol=false): `set_key_eq k fld = false → rmw_post recv k g v =
    /// idx_elem_prime recv k g`.
    Frame,
}

/// The two checked-RMW obligations, checked as a set by [`check_field_rmw_refinement`].
const FIELD_RMW_THMS: [FieldRmwThm; 2] = [FieldRmwThm::Set, FieldRmwThm::Frame];

/// The prelude constant each recognized RMW op maps to. All three are REDUCIBLE,
/// axiom-free prelude `Declaration::Definition`s (never `Axiom`), so naming one adds
/// nothing to `axiom_deps`.
fn rmw_op_const(op: SemRmwOp) -> &'static str {
    match op {
        SemRmwOp::Add => "Int.add",
        SemRmwOp::Sub => "Int.sub",
        SemRmwOp::Mul => "Int.mul",
    }
}

/// The per-certificate WRITTEN-VALUE term `Int.<op> (idx_elem_prime recv <fld> g)
/// <rhs>`, built at the de-Bruijn indices the `recv`/`g`/`v` binders have at the point
/// of use. Note it does NOT mention the query key `k` — the value a body writes cannot
/// depend on which key the selector is later interrogated at — which is exactly what
/// keeps the `congrArg` transport (whose `f` abstracts ONLY the guard scrutinee) valid.
fn rmw_value_e(rmw: &SemFieldRmw, recv_b: u32, g_b: u32, v_b: u32) -> Expr {
    let pre = Expr::apps(cst(MIRSEM_IDX_ELEM_PRIME), [
        Expr::bvar(recv_b),
        int_lit(i128::from(rmw.field_key)),
        Expr::bvar(g_b),
    ]);
    let rhs = match rmw.rhs {
        SemRmwRhs::Const(c) => int_lit(c),
        SemRmwRhs::Param(_) => Expr::bvar(v_b),
    };
    Expr::apps(cst(rmw_op_const(rmw.op)), [pre, rhs])
}

/// Build the witness env: `trustir_env()` (already carrying `idx_elem_prime`/
/// `set_key_eq` and the prelude `Int.<op>`) + the freshly-registered per-certificate
/// `rmw_post` Definition. `None` (fail-closed) on a Definition that fails to typecheck.
fn build_field_rmw_env(rmw: &SemFieldRmw) -> Option<Environment> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let fld = i128::from(rmw.field_key);
    let l1 = Level::succ(Level::zero());
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1]);
    // rmw_post := λ recv k g v. @Bool.rec (λ_:Bool. Int) (idx_elem_prime recv k g)
    //                                     (Int.<op> (idx_elem_prime recv <fld> g) <rhs>)
    //                                     (set_key_eq k <fld>)
    // Bool.rec arg order [motive, FALSE_case=frame, TRUE_case=value, scrutinee].
    // Under λ recv λ k λ g λ v: recv = 3, k = 2, g = 1, v = 0.
    let rmw_post_body = {
        let motive = Expr::lam(bd(), cst("Bool"), int_ty());
        let rec = Expr::apps(bool_rec, [
            motive,
            idx_elem_prime_e(3, 2, 1),
            rmw_value_e(rmw, 3, 1, 0),
            set_key_eq_e(2, fld),
        ]);
        Expr::lam(
            bd(),
            int_ty(),
            Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), rec))),
        )
    };
    let rmw_post_ty = Expr::pi(
        bd(),
        int_ty(),
        Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()))),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string(RMW_POST),
        level_params: vec![],
        type_: rmw_post_ty,
        value: rmw_post_body,
        is_reducible: true,
    })
    .ok()?;
    Some(env)
}

/// Build `(env, statement, proof)` for ONE checked-RMW obligation. `statement` is
/// `∀ (recv k g v : Int), set_key_eq k <fld> = <pol> → rmw_post recv k g v = <claimed OR
/// honest minor>`; `proof` is the `congrArg`-transport witness (ALWAYS a proof of
/// `rmw_post recv k g v = <honest minor>` — its TYPE, not content, is what `claimed`
/// decouples from). `claimed` overrides the RHS (the FAIL-CLOSED PROBE). The recipe is
/// `build_field_set_obligation`'s, with the TRUE minor replaced by the arithmetic term.
fn build_field_rmw_obligation(
    rmw: &SemFieldRmw,
    thm: FieldRmwThm,
    claimed: Option<&Expr>,
) -> Option<(Environment, Expr, Expr)> {
    let fld = i128::from(rmw.field_key);
    let env = build_field_rmw_env(rmw)?;
    let l1 = Level::succ(Level::zero());
    let pol = matches!(thm, FieldRmwThm::Set);
    let rmw_post_e = |recv_b: u32, k_b: u32, g_b: u32, v_b: u32| {
        Expr::apps(cst(RMW_POST), [
            Expr::bvar(recv_b),
            Expr::bvar(k_b),
            Expr::bvar(g_b),
            Expr::bvar(v_b),
        ])
    };

    // STATEMENT (under `Π recv Π k Π g Π v Π hg`): at the eq recv=4,k=3,g=2,v=1,hg=0; at
    // `Π hg` (the hg binder TYPE) recv=3,k=2,g=1,v=0.
    let hyp_ty = {
        let guard = set_key_eq_e(2, fld);
        if pol { eq_bool_true(guard) } else { eq_bool_false(guard) }
    };
    // honest minor: TRUE (k==fld) ↦ the arithmetic term over the PRE-state selector;
    // FALSE (k!=fld) ↦ the untouched pre-state selector at the queried key.
    let honest_rhs =
        if pol { rmw_value_e(rmw, 4, 2, 1) } else { idx_elem_prime_e(4, 3, 2) };
    let rhs = claimed.cloned().unwrap_or(honest_rhs);
    let eq = Expr::apps(Expr::const_(Name::from_string("Eq"), vec![l1.clone()]), [
        int_ty(),
        rmw_post_e(4, 3, 2, 1),
        rhs,
    ]);
    let statement = Expr::pi(
        bd(),
        int_ty(),
        Expr::pi(
            bd(),
            int_ty(),
            Expr::pi(
                bd(),
                int_ty(),
                Expr::pi(bd(), int_ty(), Expr::pi(bd(), hyp_ty.clone(), eq)),
            ),
        ),
    );

    // PROOF: `λ recv k g v hg. congrArg Bool Int (set_key_eq k fld) <target> f hg`,
    //   f := `λ x:Bool. @Bool.rec (λ_:Bool. Int) (idx_elem_prime recv k g) <value> x`.
    //   Under `λ recv λ k λ g λ v λ hg`: recv=4,k=3,g=2,v=1,hg=0; inside f (extra `λ x`):
    //   recv=5,k=4,g=3,v=2,hg=1,x=0. `f (set_key_eq k fld)` δ-matches `rmw_post recv k g
    //   v` (rmw_post reducible); `f <target>` ι-reduces to the honest minor.
    let f = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), int_ty());
        let rec = Expr::apps(bool_rec, [
            motive,
            idx_elem_prime_e(5, 4, 3),
            rmw_value_e(rmw, 5, 3, 2),
            Expr::bvar(0),
        ]);
        Expr::lam(bd(), cst("Bool"), rec)
    };
    let target = if pol { cst("Bool.true") } else { cst("Bool.false") };
    let congr = Expr::apps(Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]), [
        cst("Bool"),
        int_ty(),
        set_key_eq_e(3, fld),
        target,
        f,
        Expr::bvar(0),
    ]);
    let proof = Expr::lam(
        bd(),
        int_ty(),
        Expr::lam(
            bd(),
            int_ty(),
            Expr::lam(
                bd(),
                int_ty(),
                Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, congr)),
            ),
        ),
    );

    Some((env, statement, proof))
}

/// Check ONE checked-RMW obligation modulo 3 (with an optional `claimed` RHS override
/// for the FAIL-CLOSED forgery probes). `pub(crate)` so the probe suite can build a
/// deliberately-wrong claim without duplicating the plumbing.
#[must_use]
pub(crate) fn field_rmw_obligation_verdict(
    rmw: &SemFieldRmw,
    thm: FieldRmwThm,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    let Some((mut env, statement, proof)) = build_field_rmw_obligation(rmw, thm, claimed) else {
        return RefinementVerdict::KernelRejected(
            "field-rmw: shape outside the modeled fragment".to_string(),
        );
    };
    let tc = TypeChecker::new(&env);
    if let Err(e) = tc.check_type(&proof, &statement) {
        return RefinementVerdict::KernelRejected(format!("check_type[{thm:?}]: {e:?}"));
    }
    drop(tc);
    // The minted theorem's NAME carries the caveat, so it travels with the kernel
    // object rather than living only in prose: this is a NORMAL-RETURN (partial
    // correctness) claim, not a total one. inc-1's `field_set_*` names have no such
    // qualifier precisely because a plain setter's post-state has no guarded path.
    let name =
        Name::from_string(&format!("Trust.TrustIr.Refinement.field_rmw_normal_return_{thm:?}"));
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add_decl[{thm:?}]: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            RefinementVerdict::Residue(residue.iter().map(ToString::to_string).collect())
        }
        None => RefinementVerdict::KernelRejected(format!("decl not found after add[{thm:?}]")),
    }
}

/// Check the full T-SET / T-FRAME certificate pair for a recognized [`SemFieldRmw`]
/// against the real clean-kernel, modulo 3. GENUINE (the `field_rmw_obligation_verdict`
/// probes assert deliberately-wrong claims are `KernelRejected`) + MODEL-ONLY (the `env`
/// is freshly built per call). Fail-closed (`KernelRejected`) on a non-`Int` field type
/// (F-NONINT — belt with the recognizer's G8: a `Bool` field has no arithmetic RMW
/// lowering, and `Int.<op>` on a Bool-typed slot would be a category error), on a field
/// wider than 64 bits (F-WIDTH) or a literal outside the field's declared range
/// (F-LITRANGE) — the belts for the mint gate's ENCODER-FIDELITY gates — or any
/// obligation the kernel rejects; residues union. CALL-SITE-INERT.
///
/// PARTIAL CORRECTNESS — read this before consuming the verdict. The equality holds only
/// on runs that RETURN NORMALLY. The recognized body's overflow `Assert` may divert to
/// unwind, on which the field is never written; nothing here proves it does not. The
/// minted theorem is named `Trust.TrustIr.Refinement.field_rmw_normal_return_*` for
/// exactly that reason, and the "returns normally" condition appears in NO kernel
/// hypothesis — it is discharged solely by `clean_ground::sem_field_rmw_shape_of`'s
/// structural admission of the guard spine. A `SemFieldRmw` built BY HAND (this entry is
/// `pub`, and so are the type's fields) therefore carries no overflow guarantee at all.
/// See the WRAP-vs-INT FAITHFULNESS RECORD on [`crate::mirsem::SemFieldRmw`].
#[must_use]
pub fn check_field_rmw_refinement(rmw: &SemFieldRmw) -> RefinementVerdict {
    // The belt must mirror EVERY structural precondition the mint gate enforces, because
    // this entry is `pub` and takes a `SemFieldRmw` VALUE — a hand-built one (as the
    // probe suite builds) never passed `clean_ground::sem_field_rmw_shape_of`. A belt
    // that checks less than the gate is not a belt.
    let trust_types::Ty::Int { width, signed } = rmw.field_ty else {
        return RefinementVerdict::KernelRejected(
            "field-rmw: non-Int field type declined (F-NONINT)".to_string(),
        );
    };
    // F-WIDTH: mirrors the mint gate's G-WIDTH. `int_lit` encodes via `nat_lit(n as
    // u64)`, so a 128-bit field's literal could silently truncate — see the
    // ENCODER-FIDELITY COROLLARY on `mirsem::SemFieldRmw`.
    if width == 0 || width > 64 {
        return RefinementVerdict::KernelRejected(format!(
            "field-rmw: {width}-bit field declined — int_lit cannot encode it exactly (F-WIDTH)"
        ));
    }
    // F-LITRANGE: mirrors the mint gate's G-LITRANGE.
    if let SemRmwRhs::Const(c) = rmw.rhs {
        let in_range = if signed {
            let bound = 1i128 << (width - 1);
            (-bound..bound).contains(&c)
        } else {
            let bound = 1i128 << width;
            (0..bound).contains(&c)
        };
        if !in_range {
            return RefinementVerdict::KernelRejected(format!(
                "field-rmw: literal {c} is outside the field's declared range (F-LITRANGE)"
            ));
        }
    }
    let mut residue = Vec::new();
    for thm in FIELD_RMW_THMS {
        match field_rmw_obligation_verdict(rmw, thm, None) {
            RefinementVerdict::ProvenModulo3 => {}
            RefinementVerdict::Residue(r) => residue.extend(r),
            rejected @ RefinementVerdict::KernelRejected(_) => return rejected,
        }
    }
    if residue.is_empty() {
        RefinementVerdict::ProvenModulo3
    } else {
        residue.sort();
        residue.dedup();
        RefinementVerdict::Residue(residue)
    }
}

// ---------------------------------------------------------------------------
// Trust: RECORD-WITNESS (single-variant struct-constructor, increment 1, 2026-07-22)
// — the kernel-checked witness for `mirsem::SemStructReturn`: the bare `fn new(a, b)
// -> S { S { a, b } }` shape. A DEGENERATE `build_refinement` with the guard and the
// Bool.rec/congrArg machinery DELETED — with no guard hypothesis the theorem is
// definitional, proved by `Eq.refl` (the exact `operand_model_proof`/`rvalue_model_proof`
// recipe, trustir_anchor.rs:8651/8768, lifted from an `Int` motive to the registered
// single-`.mk` carrier's OWN type). check_type BINDS the recognizer's assertion to a
// well-formed term over that carrier — arity, field order, and field sorts are all
// kernel-enforced — and the `claimed`-override probe keeps the recipe provably
// non-tautological (a wrong RHS is `KernelRejected`, not silently accepted).
//
// MODEL-ONLY tier — the SAME honesty tier as `check_body_refinement_model` / the
// `SemAdtReturn` family (this module's head doc); the carrier is FRESHLY registered
// per call through the UNCHANGED `reflect_struct → register_adt_carriers` path (which
// for a `!is_enum()` carrier ALSO calls `env.register_structure_fields`, so
// `Expr::proj` resolves), with `register_outer_enum`'s re-get-the-registry admission
// discipline. No new axioms: the inductive/recursor pass `adt_passes_axiom_gate`
// (empty axiom_deps), `Unit.unit`/`idxElem` are prelude/`Opaque` with empty closure,
// and the theorem references only those + Eq/Eq.refl — modulo-3 closure preserved.
// ---------------------------------------------------------------------------

/// Denote ONE struct field's value at binder depth `e_bvar` (the `Env` binder's
/// de-Bruijn index). A [`SemStructField::Scalar`] denotes through
/// [`sem_operand_to_expr`] (the entry-time env-application `Int` tier); a
/// [`SemStructField::Unit`] MARKER is the closed `Unit.unit` — the field's `.mk`
/// argument type is the kernel `Unit` a fieldless-Adt/`Ty::Unit` field reflects to,
/// so `Unit.unit` is exactly its canonical inhabitant (`concrete_field_default`
/// precedent, clean_ground.rs:409-418). `None` (fail-closed) for an unresolved scalar.
///
/// Trust: RECORD-WITNESS increment 3 (2026-07-22) — the POINTER-FIELD arms
/// (GATE-PTR-SLOT-OPACITY). A [`SemStructField::SliceStart`] denotes
/// `sliceStart ⟦root⟧` (a FRESH opaque APPLICATION on the root env read — NEVER the bare
/// `e p` slot, clause (a)). A [`SemStructField::EndOffset`] denotes
/// `ptrOffset (sliceStart ⟦base⟧) ⟦count⟧ (lit elem_size)`, where `⟦count⟧ = sliceLen ⟦q⟧`
/// (its `count` operand is a [`SemOperand::Len`]) and `elem_size` is the pointee-pinned
/// element byte size (clause (b) — a pointee-recast changing element size denotes
/// distinctly). Both are VALUE-TIER (SOME Int stably determined by the operands; no
/// address content) and are NEVER jointly promoted to an address-tier claim with the
/// raw-CFG offset discharge (clause (c) — enforced by the recognizer + forgery probe).
fn struct_field_expr(field: &SemStructField, e_bvar: u32) -> Option<Expr> {
    match field {
        SemStructField::Scalar(op) => sem_operand_to_expr(op, e_bvar),
        SemStructField::Unit => {
            Some(Expr::const_(Name::from_string("Unit.unit"), LevelVec::new()))
        }
        // GATE-PTR-SLOT-OPACITY(a): a slice-START pointer field — `sliceStart ⟦root⟧`,
        // a fresh opaque application on the root (provenance root ≠ value identity),
        // NEVER the bare `e p` slot.
        SemStructField::SliceStart(root) => {
            Some(Expr::app(cst(TRUSTIR_SLICE_START), sem_operand_to_expr(root, e_bvar)?))
        }
        // GATE-PTR-SLOT-OPACITY(a)+(b): a one-past-the-end pointer field —
        // `ptrOffset (sliceStart ⟦base⟧) ⟦count⟧ (lit elem_size)`. The base is itself a
        // `sliceStart` application (never a bare slot); the third `elem_size` argument
        // pins the pointee sort so a pointee-recast that changes element size denotes
        // distinctly (`is_pointerish`'s pointee-blind passthrough is inadmissible here).
        SemStructField::EndOffset { base, count, elem_size } => Some(Expr::apps(
            cst(TRUSTIR_PTR_OFFSET),
            [
                Expr::app(cst(TRUSTIR_SLICE_START), sem_operand_to_expr(base, e_bvar)?),
                sem_operand_to_expr(count, e_bvar)?,
                int_lit(i128::from(*elem_size)),
            ],
        )),
    }
}

/// Build `(env, statement, proof)` for a recognized [`SemStructReturn`]: `env` carries
/// the freshly-registered single-`.mk` carrier; `statement` is `∀ (e:Env), S.mk ⟦f_0⟧e
/// … ⟦f_n⟧e = <claimed OR the same ctor application>`; `proof` is `λ (e:Env), Eq.refl S
/// (S.mk ⟦f_0⟧e … ⟦f_n⟧e)`. `None` (fail-closed) on a carrier registration decline, a
/// generic (Pi-wrapped) `.mk`, an arity mismatch, or an unresolved field.
///
/// `claimed` overrides the statement's RHS — `None` for the real, honest claim (the
/// PUBLIC [`check_struct_return_refinement`] always passes `None`); `Some(wrong_rhs)`
/// is the FAIL-CLOSED PROBE mechanism (mirrors [`build_refinement`]'s `claimed`
/// parameter exactly): the proof's ACTUAL type is `S.mk … = S.mk …` regardless, so a
/// `claimed` NOT def-eq to the honest ctor application makes `check_type` reject —
/// proving the recipe is GENUINE (a swapped-field or wrong-value claim is caught).
fn build_struct_refinement(
    r: &SemStructReturn,
    claimed: Option<&Expr>,
) -> Option<(Environment, Expr, Expr)> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    // Register the single-`.mk` carrier through the UNCHANGED reflect/register path;
    // RE-GET the registry (a gate-failed inductive stays in the env but out of the
    // registry — never assume registration succeeded).
    let carrier = crate::reflect::reflect_struct(&r.struct_ty)?;
    if !carrier.type_params.is_empty() || carrier.is_enum() {
        return None; // concrete-only: a Pi-wrapped generic `.mk` is deferred (increment > 1).
    }
    let registry =
        crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
    let confirmed = registry.get(&carrier.name)?;
    if confirmed.fields.len() != r.fields.len() {
        return None; // arity: `.mk` argument count must equal the recognized field count.
    }
    let ctor_name = confirmed.ctor_name.clone();
    let adt_ty = || Expr::const_(Name::from_string(&carrier.name), LevelVec::new());
    let l1 = Level::succ(Level::zero());

    // The honest ctor application `S.mk ⟦f_0⟧e … ⟦f_n⟧e` at binder depth 0 (under `λ e`
    // / `Π (e:Env)`, `e` is bvar 0).
    let honest = {
        let mut app = Expr::const_(Name::from_string(&ctor_name), LevelVec::new());
        for field in &r.fields {
            app = Expr::app(app, struct_field_expr(field, 0)?);
        }
        app
    };

    // STATEMENT: ∀ (e:Env), S.mk … = <claimed OR honest>.
    let rhs = claimed.cloned().unwrap_or_else(|| honest.clone());
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
        [adt_ty(), honest.clone(), rhs],
    );
    let statement = Expr::pi(bd(), env_ty(), eq);

    // PROOF: λ (e:Env), Eq.refl S (S.mk …) — its type is `S.mk … = S.mk …`, so a wrong
    // `claimed` RHS is NOT def-eq to the reduct and `check_type` rejects it.
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![l1]);
    let proof = Expr::lam(bd(), env_ty(), Expr::apps(eq_refl, [adt_ty(), honest]));

    Some((env, statement, proof))
}

/// Check the RECORD (single-variant struct-constructor) refinement for a recognized
/// [`SemStructReturn`] against the real clean-kernel, modulo 3. GENUINE (the
/// `claimed`-override probe asserts a deliberately-wrong claim is `KernelRejected`,
/// not a dressed-up tautology) + MODEL-ONLY (the `env`/carrier are FRESHLY built per
/// call from the recognized shape). Fail-closed (`KernelRejected`) on any carrier
/// decline or an unresolved field.
#[must_use]
pub fn check_struct_return_refinement(r: &SemStructReturn) -> RefinementVerdict {
    check_struct_return_refinement_claimed(r, None)
}

/// [`check_struct_return_refinement`] with an explicit `claimed` RHS override — the
/// FAIL-CLOSED PROBE entry point (see [`build_struct_refinement`]'s doc). `pub(crate)`
/// so the forgery-probe suite can construct a deliberately-wrong claim without
/// duplicating the carrier-registration plumbing.
#[must_use]
pub(crate) fn check_struct_return_refinement_claimed(
    r: &SemStructReturn,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    let Some((mut env, statement, proof)) = build_struct_refinement(r, claimed) else {
        return RefinementVerdict::KernelRejected(
            "struct-return: shape/carrier outside the modeled fragment".to_string(),
        );
    };
    let tc = TypeChecker::new(&env);
    if let Err(e) = tc.check_type(&proof, &statement) {
        return RefinementVerdict::KernelRejected(format!("check_type: {e:?}"));
    }
    drop(tc);
    let name = Name::from_string("Trust.TrustIr.Refinement.struct_return");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            names.dedup();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

// ---------------------------------------------------------------------------
// Trust: OPAQUE-CHAIN ADT-RETURN (M6 Tier-1 SHAPE_GAP, 2026-07-10) — the
// kernel-checked witness for `mirsem::SemAdtReturnOpaque`: the guarded
// `Option` return whose arm payload is produced by a linear chain of opaque
// steps (see the recognizer's section comment in `mirsem.rs` for the shape
// and the honesty tier). The SAME `Bool.rec` + `congrArg`-transport recipe as
// `build_refinement` above, generalized with K EXTRA ∀-BOUND step binders —
// one per recognized call, `Bool`-sorted for a `Bool` dest, `Int` otherwise
// (the SAME `∀ (ret : Int)` framing `trustir_call`'s `callReturnInstance`
// binder and `TrustIrOtherOperand::Param` already use: an arbitrary value
// standing in for whatever the call returned; NEVER a fresh axiom, NEVER an
// uninterpreted function symbol that could equate two distinct call sites).
//
// STATEMENT: ∀ (e : Env) (s₀ : T₀) … (s_{k−1} : T_{k−1}),
//              guard = true → (Bool.rec (λ_.Adt) elseVal thenVal guard) = thenVal
// where guard is either the REAL comparison term (the `fold_bvar_opt` family)
// or the ∀-bound Bool step (the `fold_fvar_opt` newtype-Eq family), and
// thenVal/elseVal are the registered Option-carrier constructors applied to a
// step binder / entry-time operand denotation. The proof GENUINELY consumes
// the hypothesis via `congrArg` (a wrong claimed RHS is KernelRejected — the
// fail-closed probe below), exactly as the 2-arm witness above.
// ---------------------------------------------------------------------------

use crate::mirsem::{SemAdtReturnOpaque, SemChainVal, SemOpaqueCond};

/// Denote a [`SemChainVal`] at a context with `inner` binders bound AFTER the
/// last step binder (`inner = 0` in the guard-hypothesis TYPE position,
/// `1` under the hypothesis lambda/pi, `2` under the proof's extra `λ x`).
/// With `k` step binders the de-Bruijn layout outer→inner is
/// `e, s₀, …, s_{k−1}, <inner binders>`: step `i` ↦ `bvar(inner + k − 1 − i)`,
/// `e` ↦ `bvar(inner + k)`. Operands: `Var p ↦ e p`, `Const c ↦ <lit c>`,
/// `Field (Var p) f ↦ idxElem (e p) f` (the SAME opaque selector
/// [`TRUSTIR_IDX_ELEM`] the field-read leaf uses). `None` (fail-closed) for
/// anything else — the recognizer never produces it; declined here too for
/// defense in depth.
fn chain_val_expr(v: &SemChainVal, k: usize, inner: u32) -> Option<Expr> {
    let e_bvar = u32::try_from(k).ok()?.checked_add(inner)?;
    match v {
        SemChainVal::Step(i) => {
            let i = u32::try_from(*i).ok()?;
            let k = u32::try_from(k).ok()?;
            if i >= k {
                return None;
            }
            Some(Expr::bvar(inner + (k - 1 - i)))
        }
        SemChainVal::Operand(op) => match op {
            crate::mirsem::SemOperand::Var(p) => {
                Some(Expr::app(Expr::bvar(e_bvar), Expr::nat_lit(*p)))
            }
            crate::mirsem::SemOperand::Const(c) => Some(int_lit(*c)),
            crate::mirsem::SemOperand::Field(base, f) => {
                let crate::mirsem::SemOperand::Var(p) = base.as_ref() else { return None };
                Some(Expr::apps(
                    cst(TRUSTIR_IDX_ELEM),
                    [
                        Expr::app(Expr::bvar(e_bvar), Expr::nat_lit(*p)),
                        int_lit(i128::try_from(*f).ok()?),
                    ],
                ))
            }
            _ => None,
        },
    }
}

/// The guard `Bool` term of a [`SemAdtReturnOpaque`] at `inner` binders after
/// the last step binder — the real comparison via [`guard_bool`], or the
/// ∀-bound `Bool` step binder itself.
fn opaque_cond_expr(r: &SemAdtReturnOpaque, inner: u32) -> Option<Expr> {
    let k = r.steps.len();
    match &r.cond {
        SemOpaqueCond::Cmp { op, a, b } => {
            let a = chain_val_expr(&SemChainVal::Operand(a.clone()), k, inner)?;
            let b = chain_val_expr(&SemChainVal::Operand(b.clone()), k, inner)?;
            Some(guard_bool(*op, &a, &b))
        }
        SemOpaqueCond::StepBool(i) => {
            if !r.steps.get(*i)?.bool_typed {
                return None;
            }
            chain_val_expr(&SemChainVal::Step(*i), k, inner)
        }
    }
}

/// Register the Option carrier for a [`SemAdtReturnOpaque`] — the outer part
/// of [`register_outer_enum`] (no nested payloads exist in this family).
/// Returns `(then_ctor_name, else_ctor_name, outer_adt_name)`.
fn register_outer_enum_opaque(
    env: &mut Environment,
    r: &SemAdtReturnOpaque,
) -> Option<(String, String, String)> {
    use trust_types::{Ty, VariantDef};
    let def_for = |arm: &crate::mirsem::SemOpaqueArm| VariantDef {
        name: format!("Arm{}", arm.variant),
        discriminant: arm.variant,
        fields: if arm.payload.is_some() {
            vec![("0".to_string(), Ty::Int { width: 64, signed: true })]
        } else {
            vec![]
        },
    };
    let outer_ty =
        Ty::adt_enum(r.enum_name.clone(), vec![def_for(&r.then_arm), def_for(&r.else_arm)]);
    let outer_carrier = crate::reflect::reflect_enum(&outer_ty)?;
    let name = outer_carrier.name.clone();
    let registry =
        crate::clean_ground::register_adt_carriers(env, std::slice::from_ref(&outer_carrier));
    let confirmed = registry.get(&name)?;
    let then_ctor = confirmed.constructors.first()?.name.clone();
    let else_ctor = confirmed.constructors.get(1)?.name.clone();
    Some((then_ctor, else_ctor, name))
}

/// One arm's constructed value at `inner` binders after the last step binder.
fn opaque_arm_value(
    ctor_name: &str,
    payload: &Option<SemChainVal>,
    k: usize,
    inner: u32,
) -> Option<Expr> {
    let ctor = Expr::const_(Name::from_string(ctor_name), LevelVec::new());
    match payload {
        None => Some(ctor),
        Some(v) => Some(Expr::app(ctor, chain_val_expr(v, k, inner)?)),
    }
}

/// Build `(env, statement, proof)` for a [`SemAdtReturnOpaque`] (module-section
/// doc above). `claimed` overrides the statement's RHS — the fail-closed probe
/// mechanism, byte-for-byte the [`build_refinement`] convention.
fn build_refinement_opaque(
    r: &SemAdtReturnOpaque,
    claimed: Option<&Expr>,
) -> Option<(Environment, Expr, Expr)> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (then_ctor, else_ctor, adt_name) = register_outer_enum_opaque(&mut env, r)?;
    let adt_ty = || Expr::const_(Name::from_string(&adt_name), LevelVec::new());
    let l1 = Level::succ(Level::zero());
    let k = r.steps.len();
    let step_ty =
        |i: usize| -> Expr { if r.steps[i].bool_typed { cst("Bool") } else { cst("Int") } };

    // STATEMENT: ∀ e s₀ … s_{k−1}, guard = true → select = <claimed OR thenVal>.
    // Hypothesis TYPE position: inner = 0; codomain (under h): inner = 1.
    let guard0 = opaque_cond_expr(r, 0)?;
    let guard_eq = eq_bool_true(guard0);
    let then_v1 = opaque_arm_value(&then_ctor, &r.then_arm.payload, k, 1)?;
    let else_v1 = opaque_arm_value(&else_ctor, &r.else_arm.payload, k, 1)?;
    let guard1 = opaque_cond_expr(r, 1)?;
    let lhs = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), adt_ty());
        Expr::apps(bool_rec, [motive, else_v1, then_v1.clone(), guard1])
    };
    let rhs = claimed.cloned().unwrap_or_else(|| then_v1.clone());
    let eq =
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![l1.clone()]), [adt_ty(), lhs, rhs]);
    let mut statement = Expr::pi(bd(), guard_eq, eq);
    for i in (0..k).rev() {
        statement = Expr::pi(bd(), step_ty(i), statement);
    }
    let statement = Expr::pi(bd(), env_ty(), statement);

    // PROOF: λ e s₀ … s_{k−1} h. congrArg (λ x:Bool. Bool.rec motive elseV thenV x) h
    // — under the extra `λ x`: inner = 2.
    let f = {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), adt_ty());
        let then_v2 = opaque_arm_value(&then_ctor, &r.then_arm.payload, k, 2)?;
        let else_v2 = opaque_arm_value(&else_ctor, &r.else_arm.payload, k, 2)?;
        let select_x = Expr::apps(bool_rec, [motive, else_v2, then_v2, Expr::bvar(0)]);
        Expr::lam(bd(), cst("Bool"), select_x)
    };
    let guard1_for_proof = opaque_cond_expr(r, 1)?;
    let congr = Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        [cst("Bool"), adt_ty(), guard1_for_proof, cst("Bool.true"), f, Expr::bvar(0)],
    );
    let guard0_for_proof = opaque_cond_expr(r, 0)?;
    let mut proof = Expr::lam(bd(), eq_bool_true(guard0_for_proof), congr);
    for i in (0..k).rev() {
        proof = Expr::lam(bd(), step_ty(i), proof);
    }
    let proof = Expr::lam(bd(), env_ty(), proof);

    Some((env, statement, proof))
}

/// TEST-ONLY: the ELSE arm's value at `inner = 1` for a recognized
/// [`SemAdtReturnOpaque`] — the fail-closed probe's wrong claim (mirrors
/// [`else_value_for_test`]).
#[cfg(test)]
pub(crate) fn opaque_else_value_for_test(r: &SemAdtReturnOpaque) -> Option<Expr> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (_then_ctor, else_ctor, _name) = register_outer_enum_opaque(&mut env, r)?;
    opaque_arm_value(&else_ctor, &r.else_arm.payload, r.steps.len(), 1)
}

/// TEST-ONLY: the THEN arm's value at `inner = 1` with its payload REPLACED by
/// `wrong` — the ctor-arg-swap probe (claiming `Some(<a different step /
/// operand>)` must be KernelRejected).
#[cfg(test)]
pub(crate) fn opaque_then_value_with_payload_for_test(
    r: &SemAdtReturnOpaque,
    wrong: &SemChainVal,
) -> Option<Expr> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (then_ctor, _else_ctor, _name) = register_outer_enum_opaque(&mut env, r)?;
    if r.then_arm.payload.is_none() {
        return None;
    }
    opaque_arm_value(&then_ctor, &Some(wrong.clone()), r.steps.len(), 1)
}

/// Check the OPAQUE-CHAIN ADT-RETURN refinement for a recognized
/// [`SemAdtReturnOpaque`] against the real clean-kernel, modulo 3. GENUINE
/// (the `congrArg` transport consumes the guard hypothesis — the fail-closed
/// probes assert a wrong claim is `KernelRejected`) + MODEL-ONLY (the SAME
/// honesty tier as [`check_adt_return_refinement`], WEAKENED further — and
/// honestly — by the ∀-bound step binders: no call result carries ANY value
/// claim). Fail-closed (`KernelRejected`) outside the modeled fragment.
#[must_use]
pub fn check_adt_return_opaque_refinement(r: &SemAdtReturnOpaque) -> RefinementVerdict {
    check_adt_return_opaque_refinement_claimed(r, None)
}

/// [`check_adt_return_opaque_refinement`] with an explicit `claimed` RHS
/// override — the fail-closed probe entry point (mirrors
/// [`check_adt_return_refinement_claimed`]).
#[must_use]
pub(crate) fn check_adt_return_opaque_refinement_claimed(
    r: &SemAdtReturnOpaque,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    let Some((mut env, statement, proof)) = build_refinement_opaque(r, claimed) else {
        return RefinementVerdict::KernelRejected(
            "ADT-return(opaque): shape/carrier outside the modeled fragment".to_string(),
        );
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Refinement.adt_return_opaque");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

// ---------------------------------------------------------------------------
// Trust: SCALAR SENTINEL-SELECT witness (cmp-mono-select, 2026-07-16) — the
// kernel-checked witness for `mirsem::SemScalarSentinelSelect` (the
// monomorphized `<iN as Ord>::min`/`::max` two-arm select over the
// `__trust_total_clone` TOTAL sentinel Bool). The SCALAR-Int specialization of
// `build_refinement_opaque` above: k = 1 ∀-bound `Bool` step (the sentinel
// guard), the two arms passing through a by-value PARAMETER (`e p`) rather than
// constructing an `Option` variant, motive `λ_:Bool. Int`, `Eq` at `Int`.
//
// STATEMENT (two obligations — the FULL case split):
//   (0) ∀ (e : Env) (g : Bool), g = true  → (Bool.rec (λ_.Int) elseV thenV g) = thenV
//   (1) ∀ (e : Env) (g : Bool), g = false → (Bool.rec (λ_.Int) elseV thenV g) = elseV
// where thenV = `e then_var`, elseV = `e else_var`. Each proof `congrArg`s the
// guard hypothesis through `λ x:Bool. Bool.rec … x` (the SAME transport
// `build_refinement_opaque` uses), so a WRONG claimed arm is KernelRejected (the
// fail-closed probe). HONESTY: the guard `g` is UNINTERPRETED — the certificate
// says "the result is one of {then_var, else_var}, dispatched by the total Bool",
// asserting NOTHING about the guard's value (never value-faithful).
// ---------------------------------------------------------------------------

/// Build the two `(statement, proof)` obligations for a
/// [`SemScalarSentinelSelect`] (module-section doc above). `claims` overrides each
/// obligation's RHS — the fail-closed probe mechanism, mirroring
/// [`build_refinement_opaque`]'s `claimed` convention.
fn build_refinement_scalar_sentinel_select(
    r: &SemScalarSentinelSelect,
    claims: [Option<&Expr>; 2],
) -> Option<(Environment, Vec<(Expr, Expr)>)> {
    use crate::mirsem::SemChainVal;
    let env = crate::trustir_anchor::trustir_env().ok()?;
    let l1 = Level::succ(Level::zero());
    let int_ty = || cst("Int");
    // k = 1 opaque Bool step (the total sentinel guard); layout outer→inner: e, g.
    let k = 1usize;
    let then_val =
        |inner: u32| chain_val_expr(&SemChainVal::Operand(SemOperand::Var(r.then_var)), k, inner);
    let else_val =
        |inner: u32| chain_val_expr(&SemChainVal::Operand(SemOperand::Var(r.else_var)), k, inner);
    let guard = |inner: u32| chain_val_expr(&SemChainVal::Step(0), k, inner);
    // `Bool.rec (λ_:Bool. Int) elseV thenV guard` at `inner` binders.
    let select = |inner: u32| -> Option<Expr> {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), int_ty());
        Some(Expr::apps(bool_rec, [motive, else_val(inner)?, then_val(inner)?, guard(inner)?]))
    };
    let eq_at = |lhs: Expr, rhs: Expr| {
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![l1.clone()]), [int_ty(), lhs, rhs])
    };
    // The `congrArg` transport `λ x:Bool. Bool.rec (λ_.Int) elseV(2) thenV(2) x`
    // (the arms live under the extra `λ x`, i.e. inner = 2).
    let transport = || -> Option<Expr> {
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
        let motive = Expr::lam(bd(), cst("Bool"), int_ty());
        let sel_x = Expr::apps(bool_rec, [motive, else_val(2)?, then_val(2)?, Expr::bvar(0)]);
        Some(Expr::lam(bd(), cst("Bool"), sel_x))
    };

    let mut obligations = Vec::with_capacity(2);
    // Each obligation: (hypothesis, arm value, the `Bool.true`/`Bool.false` ctor).
    let cases: [(Expr, Expr, &str); 2] = [
        (eq_bool_true(guard(0)?), then_val(1)?, "Bool.true"),
        (eq_bool_false(guard(0)?), else_val(1)?, "Bool.false"),
    ];
    for (idx, (hyp0, default_rhs, bool_ctor)) in cases.into_iter().enumerate() {
        // STATEMENT: ∀ e g, hyp → select = <claimed OR arm value>. Hypothesis TYPE
        // position inner = 0; codomain (under h) inner = 1.
        let rhs = claims[idx].cloned().unwrap_or(default_rhs);
        let mut statement = Expr::pi(bd(), hyp0, eq_at(select(1)?, rhs));
        statement = Expr::pi(bd(), cst("Bool"), statement); // g : Bool
        statement = Expr::pi(bd(), env_ty(), statement); //    e : Env
        // PROOF: λ e g h. congrArg (λ x. Bool.rec … x) h — under the extra `λ x`
        // inner = 2; congrArg's `a` is the guard at inner = 1; `b` is the ctor.
        let congr = Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            [cst("Bool"), int_ty(), guard(1)?, cst(bool_ctor), transport()?, Expr::bvar(0)],
        );
        let mut proof = Expr::lam(bd(), eq_bool_true_or_false(idx, guard(0)?), congr);
        proof = Expr::lam(bd(), cst("Bool"), proof);
        proof = Expr::lam(bd(), env_ty(), proof);
        obligations.push((statement, proof));
    }
    Some((env, obligations))
}

/// The hypothesis Prop for obligation `idx` (0 = `= Bool.true`, 1 = `= Bool.false`).
fn eq_bool_true_or_false(idx: usize, g: Expr) -> Expr {
    if idx == 0 { eq_bool_true(g) } else { eq_bool_false(g) }
}

/// Check the SCALAR SENTINEL-SELECT refinement for a recognized
/// [`SemScalarSentinelSelect`] against the real clean-kernel, modulo 3. GENUINE
/// (each `congrArg` transport consumes the guard hypothesis — the fail-closed
/// probe [`check_scalar_sentinel_select_refinement_claimed`] asserts a wrong
/// claimed arm is `KernelRejected`) + MODEL-ONLY / UNINTERPRETED-BUT-TOTAL: the
/// guard is a ∀-bound `Bool`, so no value claim is made. Fail-closed
/// (`KernelRejected`) outside the modeled fragment.
#[must_use]
pub fn check_scalar_sentinel_select_refinement(r: &SemScalarSentinelSelect) -> RefinementVerdict {
    check_scalar_sentinel_select_refinement_claimed(r, [None, None])
}

/// [`check_scalar_sentinel_select_refinement`] with explicit per-obligation
/// `claimed` RHS overrides — the fail-closed probe entry point (mirrors
/// [`check_adt_return_opaque_refinement_claimed`]).
#[must_use]
pub(crate) fn check_scalar_sentinel_select_refinement_claimed(
    r: &SemScalarSentinelSelect,
    claims: [Option<&Expr>; 2],
) -> RefinementVerdict {
    let Some((mut env, obligations)) = build_refinement_scalar_sentinel_select(r, claims) else {
        return RefinementVerdict::KernelRejected(
            "scalar sentinel-select: shape outside the modeled fragment".to_string(),
        );
    };
    for (i, (statement, proof)) in obligations.into_iter().enumerate() {
        {
            let tc = TypeChecker::new(&env);
            if let Err(e) = tc.check_type(&proof, &statement) {
                return RefinementVerdict::KernelRejected(format!(
                    "scalar sentinel-select obligation {i} check_type: {e:?}"
                ));
            }
        }
        let name =
            Name::from_string(&format!("Trust.TrustIr.Refinement.scalar_sentinel_select_{i}"));
        if let Err(e) = env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        }) {
            return RefinementVerdict::KernelRejected(format!(
                "scalar sentinel-select obligation {i} add_decl: {e:?}"
            ));
        }
        match env.axiom_deps(&name) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                names.sort();
                return RefinementVerdict::Residue(names);
            }
            None => {
                return RefinementVerdict::KernelRejected(
                    "scalar sentinel-select: decl not found after add".to_string(),
                );
            }
        }
    }
    RefinementVerdict::ProvenModulo3
}

// ---------------------------------------------------------------------------
// Trust: exact ORDERING-DISPATCH OPAQUE-CHAIN witness. The cmp/lift/bvar
// results are universally bound; this proves only Ordering-variant -> Option
// arm dispatch, never a callee value or comparison-semantics claim.
// ---------------------------------------------------------------------------

fn register_ordering_carrier(
    env: &mut Environment,
    recognized: &SemAdtReturnOpaqueOrd,
) -> Option<(Vec<String>, String)> {
    use trust_types::{Ty, VariantDef};
    let defs = recognized
        .ord_variants
        .iter()
        .map(|(name, tag)| VariantDef { name: name.clone(), discriminant: *tag, fields: vec![] })
        .collect::<Vec<_>>();
    if defs.len() != 3 {
        return None;
    }
    let carrier = crate::reflect::reflect_enum(&Ty::adt_enum("std::cmp::Ordering", defs))?;
    let name = carrier.name.clone();
    let registry = crate::clean_ground::register_adt_carriers(env, &[carrier]);
    let confirmed = registry.get(&name)?;
    if confirmed.constructors.len() != 3 {
        return None;
    }
    Some((confirmed.constructors.iter().map(|ctor| ctor.name.clone()).collect(), name))
}

fn register_outer_enum_opaque_ord(
    env: &mut Environment,
    recognized: &SemAdtReturnOpaqueOrd,
) -> Option<(std::collections::BTreeMap<i128, String>, String)> {
    use trust_types::{Ty, VariantDef};
    let mut variants = recognized.arms.iter().map(|(_, arm)| arm.variant).collect::<Vec<_>>();
    variants.sort_unstable();
    variants.dedup();
    if variants != [0, 1] {
        return None;
    }
    let defs = variants
        .iter()
        .map(|variant| VariantDef {
            name: format!("Arm{variant}"),
            discriminant: *variant,
            fields: if *variant == 1 {
                vec![("0".to_string(), Ty::Int { width: 64, signed: true })]
            } else {
                vec![]
            },
        })
        .collect::<Vec<_>>();
    let carrier = crate::reflect::reflect_enum(&Ty::adt_enum(&recognized.enum_name, defs))?;
    let name = carrier.name.clone();
    let registry = crate::clean_ground::register_adt_carriers(env, &[carrier]);
    let confirmed = registry.get(&name)?;
    if confirmed.constructors.len() != variants.len() {
        return None;
    }
    Some((
        variants
            .into_iter()
            .zip(confirmed.constructors.iter().map(|ctor| ctor.name.clone()))
            .collect(),
        name,
    ))
}

fn build_refinement_opaque_ord(
    recognized: &SemAdtReturnOpaqueOrd,
    claims: [Option<&Expr>; 3],
) -> Option<(Environment, Vec<(Expr, Expr)>)> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (ordering_ctors, ordering_name) = register_ordering_carrier(&mut env, recognized)?;
    let (option_ctors, option_name) = register_outer_enum_opaque_ord(&mut env, recognized)?;
    let ordering_ty = || Expr::const_(Name::from_string(&ordering_name), LevelVec::new());
    let option_ty = || Expr::const_(Name::from_string(&option_name), LevelVec::new());
    let level_one = Level::succ(Level::zero());
    let step_count = recognized.steps.len();
    if recognized.cmp_step >= step_count || recognized.arms.len() != 3 {
        return None;
    }
    let step_ty = |index: usize| {
        if index == recognized.cmp_step {
            ordering_ty()
        } else if recognized.steps[index].bool_typed {
            cst("Bool")
        } else {
            cst("Int")
        }
    };
    let scrutinee = |inner: u32| {
        chain_val_expr(&crate::mirsem::SemChainVal::Step(recognized.cmp_step), step_count, inner)
    };
    let arm_value = |position: usize, inner: u32| -> Option<Expr> {
        let (_, arm) = recognized.arms.get(position)?;
        let ctor = option_ctors.get(&arm.variant)?;
        opaque_arm_value(ctor, &arm.payload, step_count, inner)
    };
    let ordering_rec = |inner: u32, value: Expr| -> Option<Expr> {
        let rec = Expr::const_(
            Name::from_string(&format!("{ordering_name}.rec")),
            vec![level_one.clone()],
        );
        let motive = Expr::lam(bd(), ordering_ty(), option_ty());
        Some(Expr::apps(
            rec,
            [motive, arm_value(0, inner)?, arm_value(1, inner)?, arm_value(2, inner)?, value],
        ))
    };
    let eq_at = |ty: Expr, lhs: Expr, rhs: Expr| {
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![level_one.clone()]), [ty, lhs, rhs])
    };

    let mut obligations = Vec::new();
    for position in 0..3 {
        let ctor = Expr::const_(Name::from_string(&ordering_ctors[position]), LevelVec::new());
        let hypothesis = eq_at(ordering_ty(), scrutinee(0)?, ctor.clone());
        let lhs = ordering_rec(1, scrutinee(1)?)?;
        let rhs = match claims[position] {
            Some(claim) => claim.clone(),
            None => arm_value(position, 1)?,
        };
        let mut statement = Expr::pi(bd(), hypothesis.clone(), eq_at(option_ty(), lhs, rhs));
        for index in (0..step_count).rev() {
            statement = Expr::pi(bd(), step_ty(index), statement);
        }
        let statement = Expr::pi(bd(), env_ty(), statement);

        let transport = Expr::lam(bd(), ordering_ty(), ordering_rec(2, Expr::bvar(0))?);
        let congr_arg = Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![level_one.clone(), level_one.clone()]),
            [ordering_ty(), option_ty(), scrutinee(1)?, ctor, transport, Expr::bvar(0)],
        );
        let mut proof = Expr::lam(bd(), hypothesis, congr_arg);
        for index in (0..step_count).rev() {
            proof = Expr::lam(bd(), step_ty(index), proof);
        }
        obligations.push((statement, Expr::lam(bd(), env_ty(), proof)));
    }
    Some((env, obligations))
}

/// Kernel-check the exact ordering-dispatch refinement modulo 3.
#[must_use]
pub fn check_adt_return_opaque_ord_refinement(
    recognized: &SemAdtReturnOpaqueOrd,
) -> RefinementVerdict {
    check_adt_return_opaque_ord_refinement_claimed(recognized, [None, None, None])
}

/// Claimed-arm override used by fail-closed forgery probes.
#[must_use]
pub fn check_adt_return_opaque_ord_refinement_claimed(
    recognized: &SemAdtReturnOpaqueOrd,
    claims: [Option<&Expr>; 3],
) -> RefinementVerdict {
    let Some((mut env, obligations)) = build_refinement_opaque_ord(recognized, claims) else {
        return RefinementVerdict::KernelRejected(
            "ADT-return(opaque-ord): shape/carrier outside exact fragment".to_string(),
        );
    };
    for (position, (statement, proof)) in obligations.into_iter().enumerate() {
        if let Err(error) = TypeChecker::new(&env).check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("check_type[{position}]: {error:?}"));
        }
        let name = Name::from_string(&format!(
            "Trust.TrustIr.Refinement.adt_return_opaque_ord_{position}"
        ));
        if let Err(error) = env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        }) {
            return RefinementVerdict::KernelRejected(format!("add_decl[{position}]: {error:?}"));
        }
        match env.axiom_deps(&name) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names = residue.iter().map(ToString::to_string).collect::<Vec<_>>();
                names.sort();
                return RefinementVerdict::Residue(names);
            }
            None => {
                return RefinementVerdict::KernelRejected(format!(
                    "decl not found after add [{position}]"
                ));
            }
        }
    }
    RefinementVerdict::ProvenModulo3
}

/// Build an arm value for a wrong-arm/wrong-payload kernel probe.
#[must_use]
pub fn opaque_ord_arm_value_probe(
    recognized: &SemAdtReturnOpaqueOrd,
    position: usize,
) -> Option<Expr> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    register_ordering_carrier(&mut env, recognized)?;
    let (option_ctors, _) = register_outer_enum_opaque_ord(&mut env, recognized)?;
    let (_, arm) = recognized.arms.get(position)?;
    let ctor = option_ctors.get(&arm.variant)?;
    opaque_arm_value(ctor, &arm.payload, recognized.steps.len(), 1)
}

// ---------------------------------------------------------------------------
// Trust: ADT PAYLOAD-EXTRACTION SELECT (optres-payload-extract, 2026-07-17) —
// the value-faithful kernel witness for `mirsem::SemAdtPayloadExtract`: the
// FIRST witness that reads a variant's PAYLOAD out of an enum (`unwrap_or` with
// a PARAMETER default). TWO per-constructor ι-reduction obligations over the
// enum inductive's AUTO-DERIVED recursor (registered modulo 3 by
// `register_adt_carriers`):
//
//   SOME/payload : ∀ (d:Int) (x⃗:τ⃗_ext), E.rec.{1} (λ_.Int) [minors] (C_ext x⃗) = x_f
//   NONE/default : ∀ (d:Int) (y⃗:τ⃗_def), E.rec.{1} (λ_.Int) [minors] (C_def y⃗) = d
//
// where the ext-variant minor is the de-Bruijn field read `λx⃗. x_f` and every
// OTHER (default) minor is `λ(fields). d` — so the LHS ι-reduces to the field on
// the extract variant and to the outer default `d` otherwise. VALUE-FAITHFUL
// (the payload read is the genuine field, not the default — proved by the
// swapped-minor / some→default forgery probes) + DISPATCH-FAITHFUL (the arm
// routing, proved in the recognizer's gates). The `d` is a FRESH Π-bound Int, so
// this certifies the extraction MODEL + the recognizer's dispatch bridge — it is
// "extraction-model + dispatch bridge certified modulo 3", NOT a claim about the
// caller's concrete default value (MODEL-only, the same tier as the sibling
// witnesses in this module).
//
// The obligations are ι-reduction TAUTOLOGIES (they verify the recursor MODEL) —
// so the whole denotation burden rests on `sem_adt_payload_extract_of_discriminant_switch`'s
// gates, which MUST remain present.
// ---------------------------------------------------------------------------

/// Build the TWO payload-extraction obligations `[(some_stmt, some_proof),
/// (none_stmt, none_proof)]` in a fresh `trustir_env` carrying the registered
/// enum inductive. `claims` overrides each obligation's Eq RHS (the SOME→default
/// / NONE→nonzero / NONE→payload FAIL-CLOSED probe mechanism, the byte-for-byte
/// [`build_refinement`] convention). `swap_target_minor` builds the ext-variant
/// minor to ALSO return the default (the swapped-minor probe, proving the honest
/// build genuinely reads the field). `None` (⇒ `KernelRejected`) on any carrier /
/// shape outside the sound fragment (parameterized, ≠2 constructors, non-scalar
/// field, out-of-range variant).
fn build_payload_extract(
    r: &SemAdtPayloadExtract,
    claims: [Option<&Expr>; 2],
    swap_target_minor: bool,
) -> Option<(Environment, Vec<(Expr, Expr)>)> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let carrier = crate::reflect::reflect_enum(&r.self_ty)?;
    if carrier.is_parameterized() {
        return None;
    }
    let name = carrier.name.clone();
    let registry =
        crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
    let confirmed = registry.get(&name)?;
    // Sound subset: exactly 2 constructors, the extract variant in range.
    if confirmed.constructors.len() != 2 {
        return None;
    }
    let target_v = r.extract_variant;
    if target_v > 1 {
        return None;
    }
    let other_v = 1 - target_v;
    let ext_ctor = confirmed.constructors.get(target_v)?;
    let def_ctor = confirmed.constructors.get(other_v)?;
    let (_, field_carrier) = ext_ctor.fields.get(r.extract_field_idx)?;
    let field_ty = crate::clean_ground::carrier_code_to_kernel_type(field_carrier)?;
    let l1 = Level::succ(Level::zero());
    let eq_at = |lhs: Expr, rhs: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [field_ty.clone(), lhs, rhs],
        )
    };
    let refl = |v: Expr| {
        Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]), [field_ty.clone(), v])
    };

    // The two constructors' field kernel TYPES (for the base's fresh Π binders).
    let ext_field_tys: Vec<Expr> = ext_ctor
        .fields
        .iter()
        .map(|(_, c)| crate::clean_ground::carrier_code_to_kernel_type(c))
        .collect::<Option<_>>()?;
    let def_field_tys: Vec<Expr> = def_ctor
        .fields
        .iter()
        .map(|(_, c)| crate::clean_ground::carrier_code_to_kernel_type(c))
        .collect::<Option<_>>()?;
    let p = ext_field_tys.len();
    let k = def_field_tys.len();

    let ext_ctor_const = Expr::const_(Name::from_string(&ext_ctor.name), LevelVec::new());
    let def_ctor_const = Expr::const_(Name::from_string(&def_ctor.name), LevelVec::new());

    // `E.rec.{1} (λ_.Int) [minors] base` where the default (non-target) minor,
    // under `n` field binders, references the outer `d` at `bvar(d_apps + n)`.
    let build_rec = |base: Expr, d_apps: u32| -> Option<Expr> {
        crate::clean_ground::enum_field_recursor_accessor_with_default(
            base,
            &carrier,
            target_v,
            r.extract_field_idx,
            !swap_target_minor,
            &|n| Some(Expr::bvar(d_apps + n)),
        )
    };

    let mut obligations: Vec<(Expr, Expr)> = Vec::with_capacity(2);

    // ---- SOME / payload obligation: ∀ d x⃗_ext. E.rec … (C_ext x⃗) = x_f ----
    {
        // Binders outer→inner: d, x_0, …, x_{p-1}. At apps level d = bvar(p),
        // x_j = bvar(p-1-j).
        let d_apps = u32::try_from(p).ok()?;
        let base = if p == 0 {
            ext_ctor_const.clone()
        } else {
            let mut args = Vec::with_capacity(p);
            for j in 0..p {
                args.push(Expr::bvar(u32::try_from(p - 1 - j).ok()?));
            }
            Expr::apps(ext_ctor_const.clone(), args)
        };
        let rec = build_rec(base, d_apps)?;
        let honest_rhs = Expr::bvar(u32::try_from(p.checked_sub(1 + r.extract_field_idx)?).ok()?);
        let rhs = claims[0].cloned().unwrap_or_else(|| honest_rhs.clone());
        let mut statement = eq_at(rec, rhs);
        for ft in ext_field_tys.iter().rev() {
            statement = Expr::pi(bd(), ft.clone(), statement);
        }
        statement = Expr::pi(bd(), field_ty.clone(), statement); // Π(d:Int)
        let mut proof = refl(honest_rhs);
        for ft in ext_field_tys.iter().rev() {
            proof = Expr::lam(bd(), ft.clone(), proof);
        }
        proof = Expr::lam(bd(), field_ty.clone(), proof);
        obligations.push((statement, proof));
    }

    // ---- NONE / default obligation: ∀ d y⃗_def. E.rec … (C_def y⃗) = d ----
    {
        // Binders outer→inner: d, y_0, …, y_{k-1}. At apps level d = bvar(k),
        // y_i = bvar(k-1-i).
        let d_apps = u32::try_from(k).ok()?;
        let base = if k == 0 {
            def_ctor_const.clone()
        } else {
            let mut args = Vec::with_capacity(k);
            for i in 0..k {
                args.push(Expr::bvar(u32::try_from(k - 1 - i).ok()?));
            }
            Expr::apps(def_ctor_const.clone(), args)
        };
        let rec = build_rec(base, d_apps)?;
        let honest_rhs = Expr::bvar(u32::try_from(k).ok()?); // d
        let rhs = claims[1].cloned().unwrap_or_else(|| honest_rhs.clone());
        let mut statement = eq_at(rec, rhs);
        for ft in def_field_tys.iter().rev() {
            statement = Expr::pi(bd(), ft.clone(), statement);
        }
        statement = Expr::pi(bd(), field_ty.clone(), statement); // Π(d:Int)
        let mut proof = refl(honest_rhs);
        for ft in def_field_tys.iter().rev() {
            proof = Expr::lam(bd(), ft.clone(), proof);
        }
        proof = Expr::lam(bd(), field_ty.clone(), proof);
        obligations.push((statement, proof));
    }

    Some((env, obligations))
}

/// Kernel-check the value-faithful PAYLOAD-EXTRACTION refinement (both
/// obligations) modulo 3. `ProvenModulo3` iff BOTH the SOME (field-read) and
/// NONE (default) recursor obligations `check_type` AND rest on ⊆ the 3
/// foundational axioms; `KernelRejected`/`Residue` otherwise (fail-closed).
#[must_use]
pub fn check_payload_extract_refinement(r: &SemAdtPayloadExtract) -> RefinementVerdict {
    check_payload_extract_refinement_claimed(r, [None, None], false)
}

/// [`check_payload_extract_refinement`] with the FAIL-CLOSED forgery-probe knobs:
/// `claims` overrides each obligation's Eq RHS (`[SOME, NONE]`); `swap_target_minor`
/// builds the ext-variant minor to return the default instead of reading the field.
/// A WRONG claim or a swapped minor makes the honest `Eq.refl` reduct not def-eq to
/// the statement, so `check_type` REJECTS — proving the witness is genuine, not a
/// tautology that accepts anything.
#[must_use]
pub(crate) fn check_payload_extract_refinement_claimed(
    r: &SemAdtPayloadExtract,
    claims: [Option<&Expr>; 2],
    swap_target_minor: bool,
) -> RefinementVerdict {
    let Some((mut env, obligations)) = build_payload_extract(r, claims, swap_target_minor) else {
        return RefinementVerdict::KernelRejected(
            "payload-extract: shape/carrier outside exact fragment".to_string(),
        );
    };
    for (position, (statement, proof)) in obligations.into_iter().enumerate() {
        if let Err(error) = TypeChecker::new(&env).check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("check_type[{position}]: {error:?}"));
        }
        let name = Name::from_string(&format!(
            "Trust.TrustIr.PayloadExtract.{}",
            if position == 0 { "some" } else { "none" }
        ));
        if let Err(error) = env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        }) {
            return RefinementVerdict::KernelRejected(format!("add_decl[{position}]: {error:?}"));
        }
        match env.axiom_deps(&name) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names = residue.iter().map(ToString::to_string).collect::<Vec<_>>();
                names.sort();
                return RefinementVerdict::Residue(names);
            }
            None => {
                return RefinementVerdict::KernelRejected(format!(
                    "decl not found after add [{position}]"
                ));
            }
        }
    }
    RefinementVerdict::ProvenModulo3
}

/// TEST/PROBE helper: the SOME obligation's honest RHS `x_f` (the extract field
/// de-Bruijn read) AND the shared `d` binder — for the some→default forgery probe
/// (`claims[0] = d`, distinct from `x_f`, must be `KernelRejected`). Returns
/// `(d_bvar, xf_bvar)` at the SOME obligation's Eq depth. `None` outside the fragment.
#[cfg(test)]
pub(crate) fn payload_extract_some_probe_bvars(r: &SemAdtPayloadExtract) -> Option<(Expr, Expr)> {
    let carrier = crate::reflect::reflect_enum(&r.self_ty)?;
    let p = carrier.constructors.get(r.extract_variant)?.fields.len();
    let d = Expr::bvar(u32::try_from(p).ok()?);
    let xf = Expr::bvar(u32::try_from(p.checked_sub(1 + r.extract_field_idx)?).ok()?);
    Some((d, xf))
}

// ---------------------------------------------------------------------------
// Trust: DIVERGENCE-GUARDED ADT PAYLOAD EXTRACTION (W-UNWRAP-DIVERGE,
// 2026-07-17) — the value-faithful kernel witness for
// `mirsem::SemAdtPayloadExtractDiverging` (`unwrap`/`expect`). Composes the SOME
// obligation of the paired `build_payload_extract` lane with the divergence
// discipline in the recognizer: the None/Err arm DIVERGES (panic), so there is NO
// None-side value obligation. The kernel burden is the SINGLE SOME-side
// ι-reduction TAUTOLOGY:
//
//   SOME/payload : ∀ (d:Int) (x⃗:τ⃗_ext), E.rec.{1} (λ_.Int) [minors] (C_ext x⃗) = x_f
//
// where the ext-variant minor is the de-Bruijn field read `λx⃗. x_f`. This is the
// SAME obligation the paired lane checks at index 0 — value-faithful (the payload
// read is the genuine field, proved by the swapped-minor / some→const forgery
// probes) + dispatch-faithful (the arm routing, proved in the recognizer's gates).
// The recursor's default minor `d` is a FRESH Π-bound Int (never referenced by the
// SOME obligation's reduct); it stands in for the divergent arm, whose value is
// NEVER observed. HONESTY: this certifies "on the non-panicking path the return IS
// the Some/Ok payload", NOT an `unwrap`/`expect` totality claim (the None/Err path
// is a divergence, modeled as such — no value).
// ---------------------------------------------------------------------------

/// Kernel-check the DIVERGENCE-GUARDED payload extraction (the SOME obligation
/// ONLY) modulo 3. `ProvenModulo3` iff the SOME (field-read) recursor obligation
/// `check_type`s AND rests on ⊆ the 3 foundational axioms; `KernelRejected`/`Residue`
/// otherwise (fail-closed). There is NO None-side obligation — the None/Err arm
/// diverges (panic), carrying no value.
#[must_use]
pub fn check_payload_extract_diverging_refinement(
    r: &SemAdtPayloadExtractDiverging,
) -> RefinementVerdict {
    check_payload_extract_diverging_refinement_claimed(r, None, false)
}

/// [`check_payload_extract_diverging_refinement`] with the FAIL-CLOSED forgery-probe
/// knobs on the SOME obligation: `some_claim` overrides the Eq RHS (the some→const
/// probe — claiming the extracted value is a constant instead of the field must be
/// `KernelRejected`); `swap_target_minor` builds the ext-variant minor to return the
/// default `d` instead of reading the field (the swapped-minor probe). A wrong claim
/// or a swapped minor makes the honest `Eq.refl` reduct not def-eq to the statement,
/// so `check_type` REJECTS — proving the witness is genuine, not a tautology that
/// accepts anything.
#[must_use]
pub(crate) fn check_payload_extract_diverging_refinement_claimed(
    r: &SemAdtPayloadExtractDiverging,
    some_claim: Option<&Expr>,
    swap_target_minor: bool,
) -> RefinementVerdict {
    // Reuse the paired lane's builder via a `SemAdtPayloadExtract` PROXY. This is
    // sound because `build_payload_extract` NEVER reads `default_var` (the None
    // obligation binds a FRESH `d`, not the caller default); the diverging witness
    // then checks ONLY the SOME obligation (index 0), so the proxy's `default_var`
    // is inert. The `[some_claim, None]` NONE claim is likewise inert (never checked).
    let proxy = SemAdtPayloadExtract {
        self_ty: r.self_ty.clone(),
        extract_variant: r.extract_variant,
        extract_field_idx: r.extract_field_idx,
        default_var: 0, // INERT — build_payload_extract does not read default_var, and
                        // the diverging witness checks the SOME obligation only.
    };
    let Some((mut env, obligations)) = build_payload_extract(&proxy, [some_claim, None], swap_target_minor)
    else {
        return RefinementVerdict::KernelRejected(
            "payload-extract-diverging: shape/carrier outside exact fragment".to_string(),
        );
    };
    // The SOME/payload obligation is the FIRST one `build_payload_extract` pushes. The
    // NONE obligation is DISCARDED here — the diverging arm carries no value.
    let Some((statement, proof)) = obligations.into_iter().next() else {
        return RefinementVerdict::KernelRejected(
            "payload-extract-diverging: no SOME obligation built".to_string(),
        );
    };
    if let Err(error) = TypeChecker::new(&env).check_type(&proof, &statement) {
        return RefinementVerdict::KernelRejected(format!("check_type[some]: {error:?}"));
    }
    let name = Name::from_string("Trust.TrustIr.PayloadExtractDiverging.some");
    if let Err(error) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add_decl[some]: {error:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names = residue.iter().map(ToString::to_string).collect::<Vec<_>>();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("decl not found after add [some]".to_string()),
    }
}

// ---------------------------------------------------------------------------
// Trust: W6 CLOSURE-COMPOSITION KERNEL WITNESS (increment 1, 2026-07-18) — the
// kernel-checked witness for `mirsem::SemAdtMapCompose` (the mono
// `Option::<i32>::map` over a non-capturing spec-free FnOnce closure). A
// MECHANICAL FUSION of `build_payload_extract`'s recursor-minor recipe (the
// enum inductive's AUTO-DERIVED recursor, registered modulo 3) with
// `trustir_call::branch_call_model_rhs`'s `callResult (Call.mk cid arg <bound
// ret>)` call-modeling idiom — the some-minor's value is the reflected Option
// carrier's `Some` constructor APPLIED to the opaque call result, the none-minor
// is the nullary `None` constructor.
//
// Environment: `trustir_call::trustir_call_env()` (the whole trust-ir denotation
// + the Call theory — `Call`/`callResult`/`Call.mk`, ZERO `Trust.MirSem` names)
// EXTENDED with `register_adt_carriers` on the reflected Option<i32> enum E (the
// input and output are the SAME registered carrier; registration additive/
// idempotent). Let `T` be E itself, `C_none : T` and `C_some : Int → T` its
// reflected constructors, `cid` the registry callee-id, `argOp` the trust-ir
// embedding of the env operand (content-free — callee-identity soundness rests on
// the recognizer's EXACT-match pinning + the registry index, per the branch_call
// negative-control discipline).
//
// TWO ι-reduction obligations over E's recursor with motive `λ_. T` and minors
// `mNone = C_none`, `mSome = λ x. C_some (callResult (Call.mk cid argOp ret))`:
//
//   SOME : ∀ (ret : Int) (x : Int),
//            E.rec.{1} (λ_.T) mNone mSome (C_some x)
//              = C_some (callResult (Call.mk cid argOp ret))
//   NONE : ∀ (ret : Int),
//            E.rec.{1} (λ_.T) mNone mSome C_none = C_none
//
// Each is ONE ι-step then `Eq.refl` (`callResult` is the REDUCIBLE `Call.rec`
// projection, so `callResult (Call.mk _ _ X)` ι-reduces to `X` for the Π-bound
// `ret` — exactly the `branch_call_model_rhs` adequacy argument). The some-minor
// INTENTIONALLY IGNORES its field binder `x` under the one-arg model: the theorem
// does NOT state "f applied to x" — that link is the recognizer's gates 3+5.
//
// HONESTY TIER — MODEL-ONLY, split-claims: dispatch + Some(call_result)/None
// construction faithful modulo 3 (the recursor case-split ↔ MIR discriminant-
// switch/Downcast/Aggregate correspondence lives in `mirsem`'s recognizer gates
// 2/3/7, the SAME "extraction-model + dispatch bridge" discipline as
// `build_payload_extract`). The closure CALL is the opaque `callResult` carrier
// pinned to the EXACT certified callee (identity), NOT an `f(x)` value claim. The
// contract half is the UNCHANGED per-site `check_call_return_instance(cid, argOp)`
// (vacuous for increment-1 spec-free closures), driven by `prove.rs`.
// ---------------------------------------------------------------------------

/// Build the TWO map-compose obligations `[(some_stmt, some_proof), (none_stmt,
/// none_proof)]` in a fresh `trustir_call_env` carrying the registered Option
/// carrier. `arg` is the trust-ir embedding of the closure env operand.
///
/// `claims` overrides each obligation's `Eq` RHS (the SOME→wrong-variant /
/// NONE→C_some / concrete-value FAIL-CLOSED probes — the byte-for-byte
/// [`build_payload_extract`] convention). `swap_minors` EXCHANGES what each minor
/// produces (the none minor produces the `Some`-call value, the call minor
/// produces `None`) — the swapped-minor probe, proving the honest build genuinely
/// routes the arms. `None` (⇒ `KernelRejected`) on any carrier/shape outside the
/// sound fragment (parameterized, ≠ 2 constructors, the call variant not a single
/// Int field, the none variant not nullary, an out-of-range variant).
fn build_map_compose(
    r: &crate::mirsem::SemAdtMapCompose,
    arg: &crate::trustir_anchor::IrOperand,
    claims: [Option<&Expr>; 2],
    swap_minors: bool,
) -> Option<(Environment, Vec<(Expr, Expr)>)> {
    let mut env = crate::trustir_call::trustir_call_env().ok()?;
    let carrier = crate::reflect::reflect_enum(&r.self_ty)?;
    if carrier.is_parameterized() {
        return None;
    }
    let name = carrier.name.clone();
    let registry =
        crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
    let confirmed = registry.get(&name)?;
    if confirmed.constructors.len() != 2 {
        return None;
    }
    let call_v = r.call_variant;
    let none_v = r.none_variant;
    if call_v > 1 || none_v > 1 || call_v == none_v {
        return None;
    }
    let call_ctor = confirmed.constructors.get(call_v)?;
    let none_ctor = confirmed.constructors.get(none_v)?;
    // The CALL variant carries EXACTLY one Int field; the NONE variant is nullary.
    if call_ctor.fields.len() != 1 || !none_ctor.fields.is_empty() {
        return None;
    }
    let (_, call_field_carrier) = call_ctor.fields.first()?;
    let call_field_ty = crate::clean_ground::carrier_code_to_kernel_type(call_field_carrier)?;

    let l1 = Level::succ(Level::zero());
    let enum_ty = Expr::const_(Name::from_string(&name), LevelVec::new()); // T
    let call_ctor_const = Expr::const_(Name::from_string(&call_ctor.name), LevelVec::new());
    let none_ctor_const = Expr::const_(Name::from_string(&none_ctor.name), LevelVec::new());
    let rec = Expr::const_(Name::from_string(&format!("{name}.rec")), vec![l1.clone()]);
    // motive `λ _:E. E` — non-dependent large elimination into `Sort 1` (`T : Type`),
    // the SAME recursor level `build_payload_extract` uses (into `Int : Sort 1`).
    let motive = Expr::lam(bd(), enum_ty.clone(), enum_ty.clone());

    let eq_at = |lhs: Expr, rhs: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [enum_ty.clone(), lhs, rhs],
        )
    };
    let refl = |v: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            [enum_ty.clone(), v],
        )
    };
    // The `ret` binder's TYPE and the some-minor's VALUE are the ONE axis on which
    // `map` and `and_then` differ (W6 increment 2):
    //   * MapWrap    — the closure returns `Int`; `ret : Int` is the opaque call
    //     result, wrapped `C_some (callResult (Call.mk cid argOp ret))` into `T`.
    //   * AndThenFlat — the closure returns `T` (the SAME `Option` carrier); `ret :
    //     T` IS the opaque return (the call result IS the return, no `Some`-rewrap).
    //     The Int-typed `callResult` can NOT carry an `Option`, so — exactly as the
    //     `adt_return_opaque` lane models a non-Int opaque call result — the return
    //     is a ∀-bound carrier value; callee identity is pinned by the recognizer's
    //     EXACT-match gate + the per-site `check_call_return_instance` (prove.rs (c)),
    //     NOT by a (falsifying) `C_some` wrap.
    let ret_ty = match r.kind {
        crate::mirsem::ComposeReturn::MapWrap => int_ty(),
        crate::mirsem::ComposeReturn::AndThenFlat => enum_ty.clone(),
    };
    let call_val = |ret: Expr| -> Expr {
        match r.kind {
            crate::mirsem::ComposeReturn::MapWrap => {
                let call_mk = Expr::apps(
                    cst(crate::trustir_call::TRUSTIR_CALL_MK),
                    [Expr::nat_lit(r.callee_id), arg.to_operand_expr(), ret],
                );
                Expr::app(
                    call_ctor_const.clone(),
                    Expr::app(cst(crate::trustir_call::TRUSTIR_CALL_RESULT), call_mk),
                )
            }
            crate::mirsem::ComposeReturn::AndThenFlat => ret,
        }
    };

    // Minors in CONSTRUCTOR-INDEX order, built at a recursor-application depth where
    // `ret` sits at `bvar(ret_at)`. The none minor is nullary (no field binders); the
    // call minor abstracts its one Int field (ignored under the one-arg model), so its
    // body sits under +1 binder.
    let build_minors = |ret_at: u32| -> Option<Vec<Expr>> {
        // Honest bodies (non-swapped): none ↦ C_none, call ↦ C_some(callResult ret).
        let none_body = if swap_minors { call_val(Expr::bvar(ret_at)) } else { none_ctor_const.clone() };
        let none_minor = none_body; // nullary — no field lambda.
        let call_inner = if swap_minors { none_ctor_const.clone() } else { call_val(Expr::bvar(ret_at + 1)) };
        let call_minor = Expr::lam(bd(), call_field_ty.clone(), call_inner);
        let mut minors: Vec<Option<Expr>> = vec![None, None];
        *minors.get_mut(none_v)? = Some(none_minor);
        *minors.get_mut(call_v)? = Some(call_minor);
        minors.into_iter().collect()
    };

    let mut obligations: Vec<(Expr, Expr)> = Vec::with_capacity(2);

    // ---- SOME obligation: ∀ (ret:Int)(x:Int). E.rec … (C_some x) = C_some(callResult(Call.mk cid arg ret)) ----
    {
        // Binders outer→inner: ret, x. At recursor-app depth (the Eq body): ret=bvar1, x=bvar0.
        let minors = build_minors(1)?;
        let base = Expr::app(call_ctor_const.clone(), Expr::bvar(0)); // C_some x
        let mut args = Vec::with_capacity(4);
        args.push(motive.clone());
        args.extend(minors);
        args.push(base);
        let lhs = Expr::apps(rec.clone(), args);
        let honest_rhs = call_val(Expr::bvar(1)); // MapWrap: C_some(callResult …); Flat: ret
        let rhs = claims[0].cloned().unwrap_or_else(|| honest_rhs.clone());
        let mut statement = eq_at(lhs, rhs);
        statement = Expr::pi(bd(), int_ty(), statement); // Π(x:Int)
        statement = Expr::pi(bd(), ret_ty.clone(), statement); // Π(ret:Int|T)
        let mut proof = refl(honest_rhs);
        proof = Expr::lam(bd(), int_ty(), proof); // λ(x:Int)
        proof = Expr::lam(bd(), ret_ty.clone(), proof); // λ(ret:Int|T)
        obligations.push((statement, proof));
    }

    // ---- NONE obligation: ∀ (ret:Int). E.rec … C_none = C_none ----
    {
        // Binders: ret only (the call minor still references `ret`, so `ret` must be
        // bound for the term to be closed). At recursor-app depth: ret=bvar0.
        let minors = build_minors(0)?;
        let mut args = Vec::with_capacity(4);
        args.push(motive.clone());
        args.extend(minors);
        args.push(none_ctor_const.clone()); // C_none
        let lhs = Expr::apps(rec.clone(), args);
        let honest_rhs = none_ctor_const.clone();
        let rhs = claims[1].cloned().unwrap_or_else(|| honest_rhs.clone());
        let mut statement = eq_at(lhs, rhs);
        statement = Expr::pi(bd(), ret_ty.clone(), statement); // Π(ret:Int|T)
        let mut proof = refl(honest_rhs);
        proof = Expr::lam(bd(), ret_ty.clone(), proof); // λ(ret:Int|T)
        obligations.push((statement, proof));
    }

    Some((env, obligations))
}

/// `Int` kernel type (local mirror of `trustir_call`'s `int_ty`, kept module-local
/// so this witness's binder types read directly).
fn int_ty() -> Expr {
    cst("Int")
}

/// Kernel-check the W6 map-compose refinement (both ι-obligations) modulo 3.
/// `ProvenModulo3` iff BOTH the SOME (Some(call_result) construction) and NONE
/// (None construction) recursor obligations `check_type` AND rest on ⊆ the 3
/// foundational axioms; `KernelRejected`/`Residue` otherwise (fail-closed). `arg`
/// is the trust-ir embedding of the closure env operand.
#[must_use]
pub fn check_map_compose_refinement(
    r: &crate::mirsem::SemAdtMapCompose,
    arg: &crate::trustir_anchor::IrOperand,
) -> RefinementVerdict {
    check_map_compose_refinement_claimed(r, arg, [None, None], false)
}

/// [`check_map_compose_refinement`] with the FAIL-CLOSED forgery-probe knobs:
/// `claims` overrides each obligation's `Eq` RHS (`[SOME, NONE]` — the wrong-variant
/// / concrete-value / ret-slot probes); `swap_minors` exchanges the minor bodies.
/// A WRONG claim or a swapped minor makes the honest `Eq.refl` reduct not def-eq to
/// the statement, so `check_type` REJECTS — proving the witness is genuine, not a
/// tautology that accepts anything.
#[must_use]
pub(crate) fn check_map_compose_refinement_claimed(
    r: &crate::mirsem::SemAdtMapCompose,
    arg: &crate::trustir_anchor::IrOperand,
    claims: [Option<&Expr>; 2],
    swap_minors: bool,
) -> RefinementVerdict {
    let Some((mut env, obligations)) = build_map_compose(r, arg, claims, swap_minors) else {
        return RefinementVerdict::KernelRejected(
            "map-compose: shape/carrier outside exact fragment".to_string(),
        );
    };
    for (position, (statement, proof)) in obligations.into_iter().enumerate() {
        if let Err(error) = TypeChecker::new(&env).check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("check_type[{position}]: {error:?}"));
        }
        let name = Name::from_string(&format!(
            "Trust.TrustIr.MapCompose.{}",
            if position == 0 { "some" } else { "none" }
        ));
        if let Err(error) = env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        }) {
            return RefinementVerdict::KernelRejected(format!("add_decl[{position}]: {error:?}"));
        }
        match env.axiom_deps(&name) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names = residue.iter().map(ToString::to_string).collect::<Vec<_>>();
                names.sort();
                return RefinementVerdict::Residue(names);
            }
            None => {
                return RefinementVerdict::KernelRejected(format!(
                    "decl not found after add [{position}]"
                ));
            }
        }
    }
    RefinementVerdict::ProvenModulo3
}

// ---------------------------------------------------------------------------
// Trust: W6 PREDICATE-FILTER KERNEL WITNESS (increment 2, 2026-07-18) — the
// kernel-checked witness for `mirsem::SemAdtFilterCompose` (the mono
// `Option::<i32>::filter` over a non-capturing spec-free `FnOnce(&i32) -> bool`
// closure). A FUSION of the map-compose recursor recipe with the
// `build_refinement_opaque` StepBool tier: the some-minor NESTS a `Bool.rec`
// predicate-select INSIDE the enum recursor's Some branch, over a ∀-BOUND OPAQUE
// `Bool` (the Int `callResult` can NOT carry a Bool; the predicate result is the
// SAME ∀-bound-opaque device the `adt_return_opaque` StepBool tier uses). Some(x)
// is RECONSTRUCTED from the recursor field binder `x` (== the ORIGINAL payload, per
// the recognizer's reconstruct-local pin).
//
// TWO ι-reduction obligations over E's recursor (motive `λ_. T`, minors `mNone =
// C_none`, `mSome = λx. Bool.rec (λ_.T) C_none (C_some x) b`):
//
//   SOME : ∀ (b : Bool) (x : Int),
//            E.rec (λ_.T) mNone mSome (C_some x)
//              = Bool.rec (λ_.T) C_none (C_some x) b
//   NONE : ∀ (b : Bool),
//            E.rec (λ_.T) mNone mSome C_none = C_none
//
// Each is ONE enum-recursor ι-step then `Eq.refl` (the some-minor β-reduces to the
// `Bool.rec` select, def-eq to the RHS). The predicate `b : Bool` is UNINTERPRETED —
// the theorem states "on Some(x), filter returns `if b then Some(x) else None`",
// asserting NOTHING about `b`'s value (never a `predicate(x)` claim).
//
// HONESTY TIER — MODEL-ONLY, split-claims (identical to map-compose, weakened by the
// ∀-bound `b`): dispatch + predicate-conditioned Some(x)/None reconstruction faithful
// modulo 3; the predicate is opaque; callee identity is the recognizer's EXACT-match
// gate + the per-site `check_call_return_instance` (prove.rs (c)).
// ---------------------------------------------------------------------------

/// Build the TWO filter-compose obligations `[(some_stmt, some_proof), (none_stmt,
/// none_proof)]` in a fresh `trustir_call_env` carrying the registered Option
/// carrier. `claims` overrides each obligation's `Eq` RHS (the FAIL-CLOSED probes);
/// `swap_minors` FLIPS the some-minor's `Bool.rec` branch orientation (true↦None,
/// false↦Some) — the predicate-orientation probe. `None` (⇒ `KernelRejected`) on any
/// carrier/shape outside the sound fragment.
fn build_filter_compose(
    r: &crate::mirsem::SemAdtFilterCompose,
    claims: [Option<&Expr>; 2],
    swap_minors: bool,
) -> Option<(Environment, Vec<(Expr, Expr)>)> {
    let mut env = crate::trustir_call::trustir_call_env().ok()?;
    let carrier = crate::reflect::reflect_enum(&r.self_ty)?;
    if carrier.is_parameterized() {
        return None;
    }
    let name = carrier.name.clone();
    let registry =
        crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
    let confirmed = registry.get(&name)?;
    if confirmed.constructors.len() != 2 {
        return None;
    }
    let some_v = r.some_variant;
    let none_v = r.none_variant;
    if some_v > 1 || none_v > 1 || some_v == none_v {
        return None;
    }
    let some_ctor = confirmed.constructors.get(some_v)?;
    let none_ctor = confirmed.constructors.get(none_v)?;
    // The SOME variant carries EXACTLY one Int field; the NONE variant is nullary.
    if some_ctor.fields.len() != 1 || !none_ctor.fields.is_empty() {
        return None;
    }
    let (_, some_field_carrier) = some_ctor.fields.first()?;
    let some_field_ty = crate::clean_ground::carrier_code_to_kernel_type(some_field_carrier)?;

    let l1 = Level::succ(Level::zero());
    let enum_ty = Expr::const_(Name::from_string(&name), LevelVec::new()); // T
    let some_ctor_const = Expr::const_(Name::from_string(&some_ctor.name), LevelVec::new());
    let none_ctor_const = Expr::const_(Name::from_string(&none_ctor.name), LevelVec::new());
    let rec = Expr::const_(Name::from_string(&format!("{name}.rec")), vec![l1.clone()]);
    let motive = Expr::lam(bd(), enum_ty.clone(), enum_ty.clone());
    let bool_rec = || Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
    let bool_motive = || Expr::lam(bd(), cst("Bool"), enum_ty.clone()); // λ_:Bool. T

    let eq_at = |lhs: Expr, rhs: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [enum_ty.clone(), lhs, rhs],
        )
    };
    let refl = |v: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            [enum_ty.clone(), v],
        )
    };
    // `Bool.rec (λ_.T) C_none (C_some x) b` at bool binder `b_at` and payload `x`.
    let select_val = |b_at: u32, x: Expr| -> Expr {
        Expr::apps(
            bool_rec(),
            [
                bool_motive(),
                none_ctor_const.clone(),
                Expr::app(some_ctor_const.clone(), x),
                Expr::bvar(b_at),
            ],
        )
    };

    // Minors in CONSTRUCTOR-INDEX order. The none minor is nullary; the some minor
    // abstracts its one Int field (`x` at bvar 0), so `b` sits at `b_at + 1` inside.
    let build_minors = |b_at: u32| -> Option<Vec<Expr>> {
        let none_minor = none_ctor_const.clone();
        let some_inner = if swap_minors {
            // FLIPPED orientation: b=false ↦ Some(x), b=true ↦ None (the wrong select).
            Expr::apps(
                bool_rec(),
                [
                    bool_motive(),
                    Expr::app(some_ctor_const.clone(), Expr::bvar(0)),
                    none_ctor_const.clone(),
                    Expr::bvar(b_at + 1),
                ],
            )
        } else {
            select_val(b_at + 1, Expr::bvar(0))
        };
        let some_minor = Expr::lam(bd(), some_field_ty.clone(), some_inner);
        let mut minors: Vec<Option<Expr>> = vec![None, None];
        *minors.get_mut(none_v)? = Some(none_minor);
        *minors.get_mut(some_v)? = Some(some_minor);
        minors.into_iter().collect()
    };

    let mut obligations: Vec<(Expr, Expr)> = Vec::with_capacity(2);

    // ---- SOME: ∀ (b:Bool)(x:Int). E.rec … (C_some x) = Bool.rec (λ_.T) C_none (C_some x) b ----
    {
        // Binders outer→inner: b, x. At recursor-app depth: b=bvar(1), x=bvar(0).
        let minors = build_minors(1)?;
        let base = Expr::app(some_ctor_const.clone(), Expr::bvar(0)); // C_some x
        let mut args = Vec::with_capacity(4);
        args.push(motive.clone());
        args.extend(minors);
        args.push(base);
        let lhs = Expr::apps(rec.clone(), args);
        let honest_rhs = select_val(1, Expr::bvar(0)); // Bool.rec (λ_.T) C_none (C_some x) b
        let rhs = claims[0].cloned().unwrap_or_else(|| honest_rhs.clone());
        let mut statement = eq_at(lhs, rhs);
        statement = Expr::pi(bd(), int_ty(), statement); // Π(x:Int)
        statement = Expr::pi(bd(), cst("Bool"), statement); // Π(b:Bool)
        let mut proof = refl(honest_rhs);
        proof = Expr::lam(bd(), int_ty(), proof); // λ(x:Int)
        proof = Expr::lam(bd(), cst("Bool"), proof); // λ(b:Bool)
        obligations.push((statement, proof));
    }

    // ---- NONE: ∀ (b:Bool). E.rec … C_none = C_none ----
    {
        // `b` must be bound (the some-minor references it). At recursor-app depth: b=bvar(0).
        let minors = build_minors(0)?;
        let mut args = Vec::with_capacity(4);
        args.push(motive.clone());
        args.extend(minors);
        args.push(none_ctor_const.clone()); // C_none
        let lhs = Expr::apps(rec.clone(), args);
        let honest_rhs = none_ctor_const.clone();
        let rhs = claims[1].cloned().unwrap_or_else(|| honest_rhs.clone());
        let mut statement = eq_at(lhs, rhs);
        statement = Expr::pi(bd(), cst("Bool"), statement); // Π(b:Bool)
        let mut proof = refl(honest_rhs);
        proof = Expr::lam(bd(), cst("Bool"), proof); // λ(b:Bool)
        obligations.push((statement, proof));
    }

    Some((env, obligations))
}

/// Kernel-check the W6 filter-compose refinement (both ι-obligations) modulo 3.
/// `ProvenModulo3` iff BOTH the SOME (predicate-conditioned Some(x)/None select) and
/// NONE (None construction) recursor obligations `check_type` AND rest on ⊆ the 3
/// foundational axioms; `KernelRejected`/`Residue` otherwise (fail-closed).
#[must_use]
pub fn check_filter_compose_refinement(
    r: &crate::mirsem::SemAdtFilterCompose,
) -> RefinementVerdict {
    check_filter_compose_refinement_claimed(r, [None, None], false)
}

/// [`check_filter_compose_refinement`] with the FAIL-CLOSED forgery-probe knobs:
/// `claims` overrides each obligation's `Eq` RHS; `swap_minors` flips the some-minor's
/// `Bool.rec` orientation. A WRONG claim or a flipped select makes the honest
/// `Eq.refl` reduct not def-eq to the statement, so `check_type` REJECTS.
#[must_use]
pub(crate) fn check_filter_compose_refinement_claimed(
    r: &crate::mirsem::SemAdtFilterCompose,
    claims: [Option<&Expr>; 2],
    swap_minors: bool,
) -> RefinementVerdict {
    let Some((mut env, obligations)) = build_filter_compose(r, claims, swap_minors) else {
        return RefinementVerdict::KernelRejected(
            "filter-compose: shape/carrier outside exact fragment".to_string(),
        );
    };
    for (position, (statement, proof)) in obligations.into_iter().enumerate() {
        if let Err(error) = TypeChecker::new(&env).check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("check_type[{position}]: {error:?}"));
        }
        let name = Name::from_string(&format!(
            "Trust.TrustIr.FilterCompose.{}",
            if position == 0 { "some" } else { "none" }
        ));
        if let Err(error) = env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        }) {
            return RefinementVerdict::KernelRejected(format!("add_decl[{position}]: {error:?}"));
        }
        match env.axiom_deps(&name) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names = residue.iter().map(ToString::to_string).collect::<Vec<_>>();
                names.sort();
                return RefinementVerdict::Residue(names);
            }
            None => {
                return RefinementVerdict::KernelRejected(format!(
                    "decl not found after add [{position}]"
                ));
            }
        }
    }
    RefinementVerdict::ProvenModulo3
}

// ---------------------------------------------------------------------------
// Trust: ADT-return leaf, 3-OUTCOME GUARD CHAIN (gap-queue #2 follow-up #1,
// 2026-07-08) — the kernel-checked witness for `mirsem::SemAdtReturn3`:
// `if cond1 { A } else if cond2 { B } else { C }`. Generalizes the `Bool.rec` +
// `congrArg`-transport recipe above from a FLAT 2-way case split to a NESTED
// one: the CLAIMED value is `Bool.rec motive (Bool.rec motive C B cond2) A
// cond1` (evaluate the OUTER split first; its else-branch IS the INNER split),
// and each of the three obligations is proven separately:
//   * arm A (`cond1 = true`)                — ONE `congrArg` (identical
//     recipe to the 2-arm witness, the "else" value just happens to be the
//     unevaluated inner `Bool.rec` term instead of a flat constructor).
//   * arm B (`cond1 = false`, `cond2 = true`) and arm C (`cond1 = false`,
//     `cond2 = false`) — TWO composed `congrArg`s (outer transport under
//     `cond1 = false` lands on the inner `Bool.rec` term BY COMPUTATION, not
//     an extra lemma; inner transport under `cond2 = {true,false}` lands on
//     `B`/`C`), composed via `Eq.trans` — the SAME two-link `Eq.trans` pattern
//     `clean_ground.rs`'s ring-bridge proofs already use for a chained
//     computation, just Bool-case-split instead of ring identities.
//
// OUTER-ENUM REGISTRATION NOTE: unlike the 2-arm witness (which reuses the
// REAL outer variant tags 1:1, since there are exactly two), this 3-arm
// witness registers a FRESH 3-constructor stub keyed by ARM POSITION (not
// deduplicated by the arms' shared Rust-level variant, e.g. `from_signed!`'s
// arm A/B are BOTH `Err(..)` — variant 1 — with DIFFERENT nested payloads).
// Deduplicating would hit `register_outer_enum`'s own documented SCOPE
// BOUNDARY: two arms nesting the SAME `enum_name` at DIFFERENT variants would
// have the SECOND `register_adt_carriers` call silently REUSE the FIRST arm's
// single-variant stub (registry lookup is idempotent-by-name), so the SECOND
// arm's claimed nested constructor would be WRONG. That boundary is NOT
// reachable by the 2-arm target family but IS reachable here (`from_signed!`'s
// Underflow/Overflow both nest `Error` at different variants) — so each arm's
// nested payload registers under its OWN synthetic per-arm name
// (`"{enum_name}#chain{idx}"`), never colliding with a sibling arm's. Each
// arm's aggregate/nested-aggregate variant INDICES are mapped through their exact
// destination enum metadata (never guessed) — the per-arm ctor identity is fresh,
// but the TAG values baked into each `VariantDef.discriminant` remain the declared
// ones, including explicit or negative discriminants.
// ---------------------------------------------------------------------------

/// Register the outer 3-constructor stub (`Arm0`/`Arm1`/`Arm2`, one per ARM
/// POSITION — see the module doc for why this does not dedupe by Rust-level
/// variant) plus each `NullaryNested` arm's OWN nested carrier (registered
/// FIRST, dependency order, under a synthetic per-arm name so two arms nesting
/// the SAME `enum_name` at different variants never collide). Returns
/// `(ctor_a, ctor_b, ctor_c, nested_a, nested_b, nested_c, outer_adt_name)`.
/// `None` (fail-closed) if any registration is declined.
fn register_outer_enum3(
    env: &mut Environment,
    r: &SemAdtReturn3,
) -> Option<(String, String, String, Option<Expr>, Option<Expr>, Option<Expr>, String)> {
    use trust_types::{Ty, VariantDef};
    let arms = [&r.arm_a, &r.arm_b, &r.arm_c];
    let mut nested_vals: [Option<Expr>; 3] = [None, None, None];
    let mut field_tys: [Vec<(String, Ty)>; 3] = [vec![], vec![], vec![]];
    for (i, arm) in arms.iter().enumerate() {
        match &arm.payload {
            None => {}
            Some(SemAdtPayload::Scalar(_) | SemAdtPayload::IntCast { .. }) => {
                field_tys[i] = vec![("0".to_string(), Ty::Int { width: 64, signed: true })];
            }
            Some(SemAdtPayload::NullaryNested { enum_name, variant }) => {
                let synthetic_name = format!("{enum_name}#chain{i}");
                let nested_ty = nested_stub_ty(&synthetic_name, *variant);
                let nested_carrier = crate::reflect::reflect_enum(&nested_ty)?;
                let name = nested_carrier.name.clone();
                let registry = crate::clean_ground::register_adt_carriers(
                    env,
                    std::slice::from_ref(&nested_carrier),
                );
                let confirmed = registry.get(&name)?;
                let ctor_name = confirmed.constructors.first()?.name.clone();
                nested_vals[i] = Some(Expr::const_(Name::from_string(&ctor_name), LevelVec::new()));
                field_tys[i] = vec![("0".to_string(), nested_stub_ty(&synthetic_name, *variant))];
            }
            // Trust: RECORD-WITNESS inc-2 — a `DowncastField` payload is minted ONLY by the
            // 2-arm `sem_adt_return_shape_of` lane (`Result::ok`/`err`), never in a 3-arm
            // chain; fail closed here rather than mis-typing it as a scalar.
            Some(SemAdtPayload::DowncastField { .. }) => return None,
        }
    }
    let defs: Vec<VariantDef> = (0..3)
        .map(|i| VariantDef {
            name: format!("Arm{i}"),
            discriminant: arms[i].variant,
            fields: std::mem::take(&mut field_tys[i]),
        })
        .collect();
    let outer_ty = Ty::adt_enum(r.enum_name.clone(), defs);
    let outer_carrier = crate::reflect::reflect_enum(&outer_ty)?;
    let name = outer_carrier.name.clone();
    let registry =
        crate::clean_ground::register_adt_carriers(env, std::slice::from_ref(&outer_carrier));
    let confirmed = registry.get(&name)?;
    let ctor_a = confirmed.constructors.first()?.name.clone();
    let ctor_b = confirmed.constructors.get(1)?.name.clone();
    let ctor_c = confirmed.constructors.get(2)?.name.clone();
    let [nested_a, nested_b, nested_c] = nested_vals;
    Some((ctor_a, ctor_b, ctor_c, nested_a, nested_b, nested_c, name))
}

/// The registered constructor names + nested closed values, bundled so the
/// per-statement builders below don't thread 6 positional parameters.
struct Ctors3 {
    a: String,
    b: String,
    c: String,
    nested_a: Option<Expr>,
    nested_b: Option<Expr>,
    nested_c: Option<Expr>,
}

/// Build the CLAIMED `select3` term at binder depth `e_bvar`: `Bool.rec motive
/// (Bool.rec motive C B cond2) A cond1` — used, UNEVALUATED, as every
/// statement's LHS; only the RHS (and the hypotheses) differ per arm.
fn select3_expr(r: &SemAdtReturn3, adt_ty: &Expr, ctors: &Ctors3, e_bvar: u32) -> Option<Expr> {
    let l1 = Level::succ(Level::zero());
    let motive = Expr::lam(bd(), cst("Bool"), adt_ty.clone());
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![l1]);
    let a_val = arm_value_expr(&ctors.a, &r.arm_a.payload, ctors.nested_a.as_ref(), e_bvar)?;
    let b_val = arm_value_expr(&ctors.b, &r.arm_b.payload, ctors.nested_b.as_ref(), e_bvar)?;
    let c_val = arm_value_expr(&ctors.c, &r.arm_c.payload, ctors.nested_c.as_ref(), e_bvar)?;
    let guard2 = cond_bool(&r.cond2, e_bvar)?;
    let inner = Expr::apps(bool_rec.clone(), [motive.clone(), c_val, b_val, guard2]);
    let guard1 = cond_bool(&r.cond1, e_bvar)?;
    Some(Expr::apps(bool_rec, [motive, inner, a_val, guard1]))
}

/// Build `(env, [(statement, proof); 3])` for the three obligations (module doc
/// above). `claims` overrides each arm's RHS — `[None, None, None]` for the
/// real, honest claim; a `Some(wrong)` entry is the FAIL-CLOSED PROBE mechanism
/// (mirrors [`build_refinement`]'s `claimed` parameter). `None` (fail-closed)
/// on any unresolved piece.
fn build_refinement3(
    r: &SemAdtReturn3,
    claims: [Option<&Expr>; 3],
) -> Option<(Environment, [(Expr, Expr); 3])> {
    let mut env = crate::trustir_anchor::trustir_env().ok()?;
    let (ca, cb, cc, na, nb, nc, adt_name) = register_outer_enum3(&mut env, r)?;
    let ctors = Ctors3 { a: ca, b: cb, c: cc, nested_a: na, nested_b: nb, nested_c: nc };
    let adt_ty = Expr::const_(Name::from_string(&adt_name), LevelVec::new());
    let l1 = Level::succ(Level::zero());
    let bool_rec = || Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]);
    let motive = || Expr::lam(bd(), cst("Bool"), adt_ty.clone());
    let eq_ty = |lhs: Expr, rhs: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [adt_ty.clone(), lhs, rhs],
        )
    };
    let congr_arg = |a: Expr, b: Expr, f: Expr, h: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            [cst("Bool"), adt_ty.clone(), a, b, f, h],
        )
    };

    // ---- Statement A: guard1=true → select3 = armA ----
    // ∀e. (cond1 e = true) → (select3 e = armA e). Under `λe`: e=0.
    let guard1_e0 = cond_bool(&r.cond1, 0)?;
    let hyp_a = eq_bool_true(guard1_e0);
    // Under `λe λh1`: h1=0,e=1.
    let select3_e1 = select3_expr(r, &adt_ty, &ctors, 1)?;
    let arm_a_e1 = arm_value_expr(&ctors.a, &r.arm_a.payload, ctors.nested_a.as_ref(), 1)?;
    let rhs_a = claims[0].cloned().unwrap_or_else(|| arm_a_e1.clone());
    let eq_a = eq_ty(select3_e1, rhs_a);
    let statement_a = Expr::pi(bd(), env_ty(), Expr::pi(bd(), hyp_a, eq_a));
    // PROOF: λe λh1. congrArg f1 h1, f1 = λx. Bool.rec motive inner armA x
    //   (under `λe λh1 λx`: x=0,h1=1,e=2).
    let f1_body_at = |e_bvar: u32| -> Option<Expr> {
        let c_val = arm_value_expr(&ctors.c, &r.arm_c.payload, ctors.nested_c.as_ref(), e_bvar)?;
        let b_val = arm_value_expr(&ctors.b, &r.arm_b.payload, ctors.nested_b.as_ref(), e_bvar)?;
        let guard2 = cond_bool(&r.cond2, e_bvar)?;
        let inner = Expr::apps(bool_rec(), [motive(), c_val, b_val, guard2]);
        let a_val = arm_value_expr(&ctors.a, &r.arm_a.payload, ctors.nested_a.as_ref(), e_bvar)?;
        Some(Expr::apps(bool_rec(), [motive(), inner, a_val, Expr::bvar(0)]))
    };
    let f1 = Expr::lam(bd(), cst("Bool"), f1_body_at(2)?);
    let guard1_e1 = cond_bool(&r.cond1, 1)?;
    let congr_a = congr_arg(guard1_e1, cst("Bool.true"), f1, Expr::bvar(0));
    let guard1_e0_p = cond_bool(&r.cond1, 0)?;
    let proof_a = Expr::lam(bd(), env_ty(), Expr::lam(bd(), eq_bool_true(guard1_e0_p), congr_a));

    // ---- Statements B/C: guard1=false → guard2={true,false} → select3 = arm{B,C} ----
    let build_bc = |payload: &Option<SemAdtPayload>,
                    ctor_x: &str,
                    nested_x: Option<&Expr>,
                    want_true: bool,
                    claim: Option<&Expr>|
     -> Option<(Expr, Expr)> {
        // STATEMENT: ∀e. cond1=false → cond2={true|false} → select3 = armX.
        let guard1_e0 = cond_bool(&r.cond1, 0)?;
        let h1_ty = eq_bool_false(guard1_e0);
        let guard2_e1 = cond_bool(&r.cond2, 1)?; // under λe λh1: h1=0,e=1.
        let h2_ty = if want_true { eq_bool_true(guard2_e1) } else { eq_bool_false(guard2_e1) };
        // under λe λh1 λh2: h2=0,h1=1,e=2.
        let select3_e2 = select3_expr(r, &adt_ty, &ctors, 2)?;
        let arm_x_e2 = arm_value_expr(ctor_x, payload, nested_x, 2)?;
        let rhs_x = claim.cloned().unwrap_or_else(|| arm_x_e2.clone());
        let eq_x = eq_ty(select3_e2, rhs_x);
        let statement =
            Expr::pi(bd(), env_ty(), Expr::pi(bd(), h1_ty, Expr::pi(bd(), h2_ty, eq_x)));

        // PROOF: λe λh1 λh2. Eq.trans (congrArg f1 h1) (congrArg g2 h2).
        // f1/g2 each add ONE more binder (x/y): under λe λh1 λh2 λ{x,y}:
        // {x,y}=0,h2=1,h1=2,e=3 — so their OWN bodies resolve `e`/`cond2` at
        // depth 3, matching `f1_body_at(3)` (reused verbatim from statement A's
        // builder — SAME closed-form term, just one level deeper here since two
        // hypotheses are bound instead of one).
        let f1 = Expr::lam(bd(), cst("Bool"), f1_body_at(3)?);
        let guard1_e2 = cond_bool(&r.cond1, 2)?; // under λe λh1 λh2 (no extra binder): e=2.
        let outer_congr = congr_arg(guard1_e2, cst("Bool.false"), f1, Expr::bvar(1)); // h1.
        let g2 = {
            let c_val = arm_value_expr(&ctors.c, &r.arm_c.payload, ctors.nested_c.as_ref(), 3)?;
            let b_val = arm_value_expr(&ctors.b, &r.arm_b.payload, ctors.nested_b.as_ref(), 3)?;
            Expr::lam(
                bd(),
                cst("Bool"),
                Expr::apps(bool_rec(), [motive(), c_val, b_val, Expr::bvar(0)]),
            )
        };
        let guard2_e2 = cond_bool(&r.cond2, 2)?;
        let want_bool = if want_true { cst("Bool.true") } else { cst("Bool.false") };
        let inner_congr = congr_arg(guard2_e2, want_bool, g2, Expr::bvar(0)); // h2.
        // Eq.trans {adt_ty} {select3(e)} {inner(e)} {armX(e)} outer_congr inner_congr.
        let inner_e2 = {
            let c_val = arm_value_expr(&ctors.c, &r.arm_c.payload, ctors.nested_c.as_ref(), 2)?;
            let b_val = arm_value_expr(&ctors.b, &r.arm_b.payload, ctors.nested_b.as_ref(), 2)?;
            let guard2 = cond_bool(&r.cond2, 2)?;
            Expr::apps(bool_rec(), [motive(), c_val, b_val, guard2])
        };
        let select3_e2_ty = select3_expr(r, &adt_ty, &ctors, 2)?;
        let arm_x_e2_ty = arm_value_expr(ctor_x, payload, nested_x, 2)?;
        let trans = Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            [adt_ty.clone(), select3_e2_ty, inner_e2, arm_x_e2_ty, outer_congr, inner_congr],
        );
        let h1_ty_p = eq_bool_false(cond_bool(&r.cond1, 0)?);
        let guard2_e1_p = cond_bool(&r.cond2, 1)?;
        let h2_ty_p =
            if want_true { eq_bool_true(guard2_e1_p) } else { eq_bool_false(guard2_e1_p) };
        let proof =
            Expr::lam(bd(), env_ty(), Expr::lam(bd(), h1_ty_p, Expr::lam(bd(), h2_ty_p, trans)));
        Some((statement, proof))
    };

    let (statement_b, proof_b) =
        build_bc(&r.arm_b.payload, &ctors.b, ctors.nested_b.as_ref(), true, claims[1])?;
    let (statement_c, proof_c) =
        build_bc(&r.arm_c.payload, &ctors.c, ctors.nested_c.as_ref(), false, claims[2])?;

    Some((env, [(statement_a, proof_a), (statement_b, proof_b), (statement_c, proof_c)]))
}

/// Check the 3-outcome guard-chain ADT-RETURN refinement for a recognized
/// [`SemAdtReturn3`] against the real clean-kernel, modulo 3. THREE separate
/// obligations (module doc above) share ONE freshly-built env; the combined
/// verdict is `KernelRejected` if ANY obligation rejects, `Residue` (union of
/// axiom names) if any obligation carries a non-foundational residue and none
/// reject, else `ProvenModulo3`.
#[must_use]
pub fn check_adt_return3_refinement(r: &SemAdtReturn3) -> RefinementVerdict {
    check_adt_return3_refinement_claimed(r, [None, None, None])
}

/// [`check_adt_return3_refinement`] with explicit per-arm `claims` overrides —
/// the FAIL-CLOSED PROBE entry point (mirrors
/// [`check_adt_return_refinement_claimed`]).
#[must_use]
pub(crate) fn check_adt_return3_refinement_claimed(
    r: &SemAdtReturn3,
    claims: [Option<&Expr>; 3],
) -> RefinementVerdict {
    let Some((mut env, obligations)) = build_refinement3(r, claims) else {
        return RefinementVerdict::KernelRejected(
            "ADT-return(chain): shape/carrier outside the modeled fragment".to_string(),
        );
    };
    let names = ["arm_a", "arm_b", "arm_c"];
    let mut residue_names: Vec<String> = Vec::new();
    for (i, (statement, proof)) in obligations.into_iter().enumerate() {
        {
            let tc = TypeChecker::new(&env);
            if let Err(e) = tc.check_type(&proof, &statement) {
                return RefinementVerdict::KernelRejected(format!(
                    "check_type[{}]: {e:?}",
                    names[i]
                ));
            }
        }
        let name = Name::from_string(&format!("Trust.TrustIr.Refinement.adt_return3_{}", names[i]));
        if let Err(e) = env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        }) {
            return RefinementVerdict::KernelRejected(format!("add_decl[{}]: {e:?}", names[i]));
        }
        match env.axiom_deps(&name) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => residue_names.extend(residue.iter().map(ToString::to_string)),
            None => {
                return RefinementVerdict::KernelRejected(format!(
                    "decl not found after add: {}",
                    names[i]
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mirsem::{
        SemAdtArm, SemAdtPayload, SemAdtReturn, SemCmpOp, SemCond, SemCondTree, SemOperand,
        SemStructField, SemStructReturn,
    };

    // ---------------------------------------------------------------------------
    // Trust: RECORD-WITNESS increment 1 (2026-07-22) — the single-variant
    // struct-constructor KERNEL forgery-probe suite. The guard-free `Eq.refl` recipe
    // is definitional, so these probes are the ONLY thing proving the recipe is not an
    // unfalsifiable stub: each wrong `claimed` RHS must be `KernelRejected`, and after
    // each the honest path (`claimed = None`) must STILL certify (non-tautology AND
    // non-vacuity witnessed in the same test).
    // ---------------------------------------------------------------------------

    fn int64() -> trust_types::Ty {
        trust_types::Ty::Int { width: 64, signed: true }
    }

    /// `main::Pair { a: i64, b: i64 }` — the anchor two-scalar record.
    fn pair_struct_ty() -> trust_types::Ty {
        trust_types::Ty::adt("main::Pair", vec![("a".into(), int64()), ("b".into(), int64())])
    }

    /// `main::Three { a: i64, m: PhantomData<u32>, b: i64 }` — the PhantomData marker
    /// record (the marker field is a FIELDLESS `Ty::Adt`, reflecting to kernel `Unit`).
    fn three_struct_ty() -> trust_types::Ty {
        trust_types::Ty::adt(
            "main::Three",
            vec![
                ("a".into(), int64()),
                ("m".into(), trust_types::Ty::adt("core::marker::PhantomData", vec![])),
                ("b".into(), int64()),
            ],
        )
    }

    /// The honest `mk_pair`: `Pair.mk (e 0) (e 1)`.
    fn record_mk_pair() -> SemStructReturn {
        SemStructReturn {
            struct_ty: pair_struct_ty(),
            fields: vec![
                SemStructField::Scalar(SemOperand::Var(0)),
                SemStructField::Scalar(SemOperand::Var(1)),
            ],
        }
    }

    /// The honest `mk_three`: `Three.mk (e 0) Unit.unit (e 1)`.
    fn record_mk_three() -> SemStructReturn {
        SemStructReturn {
            struct_ty: three_struct_ty(),
            fields: vec![
                SemStructField::Scalar(SemOperand::Var(0)),
                SemStructField::Unit,
                SemStructField::Scalar(SemOperand::Var(1)),
            ],
        }
    }

    #[test]
    fn record_two_scalar_refinement_modulo3() {
        // The bare `S { a, b }` record closes modulo 3 — the registered single-`.mk`
        // inductive/recursor pass the axiom gate, and the theorem references only that
        // + Eq/Eq.refl (empty residue).
        assert_eq!(check_struct_return_refinement(&record_mk_pair()), RefinementVerdict::ProvenModulo3);
    }

    #[test]
    fn record_phantomdata_marker_refinement_modulo3() {
        // The Unit marker field is the closed `Unit.unit` `.mk` argument (kernel `Unit`
        // is axiom-free prelude); the record closes modulo 3.
        assert_eq!(
            check_struct_return_refinement(&record_mk_three()),
            RefinementVerdict::ProvenModulo3
        );
    }

    #[test]
    fn record_field_read_operand_refinement_modulo3() {
        // The NEW `Field` operand arm: a struct field sourced from `idxElem(e p, fld)`
        // (`Field base fld`) denotes through the opaque `TRUSTIR_IDX_ELEM` selector
        // (empty axiom_deps), so a record built from field-read operands closes modulo 3.
        let r = SemStructReturn {
            struct_ty: pair_struct_ty(),
            fields: vec![
                SemStructField::Scalar(SemOperand::Field(Box::new(SemOperand::Var(0)), 0)),
                SemStructField::Scalar(SemOperand::Field(Box::new(SemOperand::Var(0)), 1)),
            ],
        };
        assert_eq!(check_struct_return_refinement(&r), RefinementVerdict::ProvenModulo3);
    }

    #[test]
    fn record_swapped_field_claim_is_kernel_rejected() {
        // FORGERY: claim `Pair.mk (e 1) (e 0)` for the honest `Pair.mk (e 0) (e 1)`.
        // `e 0` and `e 1` are DISTINCT env reads (never def-eq), so a self-consistently
        // transposed claim is caught — the kernel DOES enforce operand identity per slot.
        let honest = record_mk_pair();
        let swapped = SemStructReturn {
            struct_ty: pair_struct_ty(),
            fields: vec![
                SemStructField::Scalar(SemOperand::Var(1)),
                SemStructField::Scalar(SemOperand::Var(0)),
            ],
        };
        let claim = honest_value_for_test(&swapped).expect("swapped claim builds");
        assert!(matches!(
            check_struct_return_refinement_claimed(&honest, Some(&claim)),
            RefinementVerdict::KernelRejected(_)
        ));
        // META: the honest path still certifies (non-tautology + non-vacuity).
        assert_eq!(check_struct_return_refinement(&honest), RefinementVerdict::ProvenModulo3);
    }

    #[test]
    fn record_wrong_value_claim_is_kernel_rejected() {
        // FORGERY: replace the field-a denotation `e 0` with the literal `7`.
        let honest = record_mk_pair();
        let wrong = SemStructReturn {
            struct_ty: pair_struct_ty(),
            fields: vec![
                SemStructField::Scalar(SemOperand::Const(7)),
                SemStructField::Scalar(SemOperand::Var(1)),
            ],
        };
        let claim = honest_value_for_test(&wrong).expect("wrong-value claim builds");
        assert!(matches!(
            check_struct_return_refinement_claimed(&honest, Some(&claim)),
            RefinementVerdict::KernelRejected(_)
        ));
        assert_eq!(check_struct_return_refinement(&honest), RefinementVerdict::ProvenModulo3);
    }

    #[test]
    fn record_dropped_marker_underapplied_ctor_is_kernel_rejected() {
        // FORGERY: claim `Three.mk (e 0) (e 1)` — the Unit MARKER slot omitted. The
        // under-applied `.mk` has type `Int → Three`, not `Three`, so the `Eq` type
        // argument mismatches and `check_type` rejects it.
        let honest = record_mk_three();
        let underapplied = SemStructReturn {
            struct_ty: three_struct_ty(),
            fields: vec![
                SemStructField::Scalar(SemOperand::Var(0)),
                SemStructField::Scalar(SemOperand::Var(1)),
            ],
        };
        let claim = honest_value_for_test(&underapplied).expect("under-applied claim builds");
        assert!(matches!(
            check_struct_return_refinement_claimed(&honest, Some(&claim)),
            RefinementVerdict::KernelRejected(_)
        ));
        assert_eq!(check_struct_return_refinement(&honest), RefinementVerdict::ProvenModulo3);
    }

    #[test]
    fn record_wrong_carrier_claim_is_kernel_rejected() {
        // FORGERY: claim a value at a DIFFERENT struct's ctor (`Three.mk …`) against the
        // Pair record — `Trust.Adt.main::Three.mk` is unregistered in the Pair env, so
        // the statement is ill-typed and `check_type` rejects it.
        let honest = record_mk_pair();
        let other = honest_value_for_test(&record_mk_three()).expect("Three value builds");
        assert!(matches!(
            check_struct_return_refinement_claimed(&honest, Some(&other)),
            RefinementVerdict::KernelRejected(_)
        ));
        assert_eq!(check_struct_return_refinement(&honest), RefinementVerdict::ProvenModulo3);
    }

    /// The canonical `half_promotion!`-shape: `if src < 0 { Err(Error::Underflow) }
    /// else { Ok(src as u16) }` — matching the REAL `cast` 0.3.0 fixture
    /// (`_64::<impl From<i16> for u16>::cast`).
    fn example_half_promotion() -> SemAdtReturn {
        SemAdtReturn {
            cond: SemCondTree::Leaf(SemCond {
                op: SemCmpOp::Lt,
                a: SemOperand::Var(0),
                b: SemOperand::Const(0),
            }),
            then_arm: SemAdtArm {
                variant: 1,
                payload: Some(SemAdtPayload::NullaryNested {
                    enum_name: "Error".to_string(),
                    variant: 3,
                }),
            },
            else_arm: SemAdtArm {
                variant: 0,
                payload: Some(SemAdtPayload::IntCast {
                    source: SemOperand::Var(0),
                    width: 16,
                    signed: false,
                }),
            },
            enum_name: "core::result::Result".to_string(),
        }
    }

    #[test]
    fn adt_return_refinement_modulo3() {
        assert_eq!(
            check_adt_return_refinement(&example_half_promotion()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// Trust: W20 REFERENCE-RETURN — a synthetic `slice::first` guarded reference-return:
    /// `if sliceLen(s) >= 1 { Some(idxElem(s, 0)) } else { None }` (`Option<&i32>`; the
    /// Some payload is the element-0 VALUE-SLOT, deref-transparently — NOT an address).
    fn example_slice_first() -> SemAdtReturn {
        SemAdtReturn {
            cond: SemCondTree::Leaf(SemCond {
                op: SemCmpOp::Ge,
                a: SemOperand::Len(Box::new(SemOperand::Var(0))),
                b: SemOperand::Const(1),
            }),
            then_arm: SemAdtArm {
                variant: 1,
                payload: Some(SemAdtPayload::Scalar(SemOperand::Index(
                    Box::new(SemOperand::Var(0)),
                    Box::new(SemOperand::Const(0)),
                ))),
            },
            else_arm: SemAdtArm { variant: 0, payload: None },
            enum_name: "std::option::Option".to_string(),
        }
    }

    /// A synthetic `SliceIndex::get`: `if i < sliceLen(s) { Some(idxElem(s, i)) } else
    /// { None }` — the slice handle is `Var(1)`, the index is `Var(0)`.
    fn example_slice_get() -> SemAdtReturn {
        SemAdtReturn {
            cond: SemCondTree::Leaf(SemCond {
                op: SemCmpOp::Lt,
                a: SemOperand::Var(0),
                b: SemOperand::Len(Box::new(SemOperand::Var(1))),
            }),
            then_arm: SemAdtArm {
                variant: 1,
                payload: Some(SemAdtPayload::Scalar(SemOperand::Index(
                    Box::new(SemOperand::Var(1)),
                    Box::new(SemOperand::Var(0)),
                ))),
            },
            else_arm: SemAdtArm { variant: 0, payload: None },
            enum_name: "std::option::Option".to_string(),
        }
    }

    #[test]
    fn adt_return_slice_first_reference_refinement_modulo3() {
        // The value-tier reference return `Some(idxElem(s, 0))` closes modulo 3 —
        // `idxElem`/`sliceLen` are `Declaration::Opaque` with EMPTY axiom_deps, so NO new
        // axiom enters the closure.
        assert_eq!(
            check_adt_return_refinement(&example_slice_first()),
            RefinementVerdict::ProvenModulo3
        );
    }

    #[test]
    fn adt_return_slice_get_reference_refinement_modulo3() {
        assert_eq!(
            check_adt_return_refinement(&example_slice_get()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// FORGERY PROBE (e): the Some-arm payload CLAIMS `idxElem(s, 1)` while the recognized
    /// projection reads index 0 — the `congrArg`-transport proof's ACTUAL type is `select
    /// = C_some(idxElem(s, 0))`, and `idxElem(s, 0)` vs `idxElem(s, 1)` differ in the
    /// opaque selector's integer key (never def-eq), so `check_type` REJECTS — the kernel
    /// genuinely catches a wrong-index claim.
    #[test]
    fn adt_return_slice_ref_wrong_index_claim_is_kernel_rejected() {
        let honest = example_slice_first();
        let mut forged = honest.clone();
        forged.then_arm.payload = Some(SemAdtPayload::Scalar(SemOperand::Index(
            Box::new(SemOperand::Var(0)),
            Box::new(SemOperand::Const(1)),
        )));
        let wrong_rhs = then_value_for_test(&forged).expect("forged then-arm value builds");
        assert!(
            matches!(
                check_adt_return_refinement_claimed(&honest, Some(&wrong_rhs)),
                RefinementVerdict::KernelRejected(_)
            ),
            "claiming idxElem(s, 1) when the projection reads index 0 must be kernel-rejected"
        );
    }

    /// Trust: ITER-NEXT VALUE-PATH — the guarded-ADT-return VALUE certificate for
    /// `<core::slice::iter::Iter<'_, i32> as Iterator>::next`: `if iter_has_next(self)
    /// { Some(idxElem(iter_region(self), 0)) } else { None }` (`Option<&i32>`; the Some
    /// payload is the ENTRY element-0 value-slot). The guard is the OPAQUE `iter_has_next`
    /// dispatch head; the handle the OPAQUE `iter_region` — the SHAPE
    /// `clean_ground::sem_iter_next_shape_of` mints.
    fn example_iter_next() -> SemAdtReturn {
        SemAdtReturn {
            cond: SemCondTree::IterHasNext(0),
            then_arm: SemAdtArm {
                variant: 1,
                payload: Some(SemAdtPayload::Scalar(SemOperand::Index(
                    Box::new(SemOperand::IterRegion(0)),
                    Box::new(SemOperand::Const(0)),
                ))),
            },
            else_arm: SemAdtArm { variant: 0, payload: None },
            enum_name: "core::option::Option".to_string(),
        }
    }

    /// POSITIVE — T-SOME (`iter_has_next(self)=true → Some(idxElem(iter_region(self),0))`)
    /// and T-NONE (`false → None`) both close modulo 3: `iter_region`/`iter_has_next` are
    /// `Declaration::Opaque` with EMPTY axiom_deps, so NO new axiom enters the closure.
    /// This is the positive end-to-end check R3 asks for (a ref-typed `Some` payload at the
    /// Int carrier tier registers + certifies on the real Option metadata).
    #[test]
    fn adt_return_iter_next_value_refinement_modulo3() {
        assert_eq!(
            check_adt_return_refinement(&example_iter_next()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// FORGERY F6 — the Some-arm payload CLAIMS `idxElem(iter_region(self), 1)` while the
    /// recognized snapshot reads index 0: the opaque selector's integer key (0 vs 1) is
    /// never def-eq, so `check_type` REJECTS — the kernel genuinely catches a wrong-index
    /// claim (the recipe is NOT a tautology). The iter-lane twin of the slice-ref probe.
    #[test]
    fn adt_return_iter_next_wrong_index_claim_is_kernel_rejected() {
        let honest = example_iter_next();
        let mut forged = honest.clone();
        forged.then_arm.payload = Some(SemAdtPayload::Scalar(SemOperand::Index(
            Box::new(SemOperand::IterRegion(0)),
            Box::new(SemOperand::Const(1)),
        )));
        let wrong_rhs = then_value_for_test(&forged).expect("forged then-arm value builds");
        assert!(
            matches!(
                check_adt_return_refinement_claimed(&honest, Some(&wrong_rhs)),
                RefinementVerdict::KernelRejected(_)
            ),
            "claiming idxElem(iter_region, 1) when the snapshot reads index 0 must be rejected"
        );
    }

    /// FORGERY (polarity, kernel) — claiming the ELSE (`None`) value under the TRUE
    /// (has-next) guard is kernel-rejected: the `congrArg` transport proves `select =
    /// Some(..)`, and `None`/`Some` are DISTINCT by inductive `noConfusion`. Pins T-SOME's
    /// arm to the `Some` constructor (R4 polarity).
    #[test]
    fn adt_return_iter_next_wrong_variant_claim_is_kernel_rejected() {
        let honest = example_iter_next();
        let wrong_rhs = else_value_for_test(&honest).expect("else-arm value builds");
        assert!(matches!(
            check_adt_return_refinement_claimed(&honest, Some(&wrong_rhs)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    // =======================================================================
    // Trust: W-PRIMED increment 1 (2026-07-22) — the T-STEP post-state certificate
    // quadruple KERNEL forgery-probe suite (the two-key primed surface). CALL-SITE-INERT:
    // these exercise `check_iter_step_refinement` / `iter_step_obligation_verdict` directly;
    // NOTHING in the production verdict/cluster/funnel path consumes a `SemIterStep`.
    // =======================================================================

    /// The recognized `slice::Iter::next` `SemIterStep` (receiver local 1, i32 element) — the
    /// shape `clean_ground::sem_iter_step_shape_of` mints from the pinned dump.
    fn example_iter_step() -> SemIterStep {
        SemIterStep { recv_param: 1, element_ty: trust_types::Ty::Int { width: 32, signed: true } }
    }

    /// Recursively collect every `Const` NAME an `Expr` mentions (F-BRIDGE census).
    fn collect_const_names(e: &Expr, out: &mut Vec<Name>) {
        use clean_kernel::ExprKind;
        match e.kind() {
            ExprKind::Const(n, _) => out.push(n.clone()),
            ExprKind::App(f, a) => {
                collect_const_names(f, out);
                collect_const_names(a, out);
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                collect_const_names(t, out);
                collect_const_names(b, out);
            }
            ExprKind::Let(_, t, v, b, _) => {
                collect_const_names(t, out);
                collect_const_names(v, out);
                collect_const_names(b, out);
            }
            ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) | ExprKind::Squash(x) => {
                collect_const_names(x, out);
            }
            _ => {}
        }
    }

    /// POSITIVE — the full T-STEP quadruple (T-VAL2/T-NONE2/T-POST-SOME/T-POST-NONE) closes
    /// modulo 3 for the honest pinned `slice::Iter::next` step shape: `iter_seq`/`iter_len`
    /// are `Opaque` with EMPTY axiom_deps, `iter_has_next2` an axiom-free Definition, the
    /// Option carrier passes the modulo-3 gate — so NO new axiom enters the closure.
    #[test]
    fn iter_step_quadruple_proves_modulo3() {
        assert_eq!(check_iter_step_refinement(&example_iter_step()), RefinementVerdict::ProvenModulo3);
    }

    /// F-STRIDE2 (kernel half) — claiming `post2 = Int.add g 2` under the true guard is
    /// KernelRejected: the honest lowering advances by exactly `+1`, and `g+1` vs `g+2` are
    /// distinct `Int` reducts (never def-eq). The F6 twin, at the generation (post-state) tier.
    #[test]
    fn iter_step_forgery_stride2_post_kernel_rejected() {
        let step = example_iter_step();
        // At the eq depth (recv=2, g=1): `Int.add g 2`.
        let forged = Expr::apps(cst("Int.add"), [Expr::bvar(1), int_lit(2)]);
        assert!(matches!(
            iter_step_obligation_verdict(&step, IterStepThm::PostSome, Some(&forged)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// F-WRONGINDEX — claiming the Some payload `iter_seq recv (g+1)` while the shape reads the
    /// entry-generation head `iter_seq recv g` is KernelRejected: the opaque's distinct second
    /// key (`g` vs `g+1`) is never def-eq.
    #[test]
    fn iter_step_forgery_wrong_index_kernel_rejected() {
        let step = example_iter_step();
        let (some_ctor, _none) = iter_step_option_ctors_for_test(&step).expect("option ctors");
        // At the eq depth (recv=2, g=1): `mkSome (iter_seq recv (g+1))`.
        let forged = Expr::app(
            cst(&some_ctor),
            Expr::apps(cst(TRUSTIR_ITER_SEQ), [Expr::bvar(2), int_add1_e(1)]),
        );
        assert!(matches!(
            iter_step_obligation_verdict(&step, IterStepThm::Val2, Some(&forged)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// F-POLARITY — claiming `mkNone` under the TRUE (`iter_has_next2`) guard is KernelRejected:
    /// the congrArg transport proves `ret2 = mkSome(..)`, and `Some`/`None` are distinct by
    /// `noConfusion`. This pin IS D-ORIENT's teeth.
    #[test]
    fn iter_step_forgery_polarity_kernel_rejected() {
        let step = example_iter_step();
        let (_some, none_ctor) = iter_step_option_ctors_for_test(&step).expect("option ctors");
        let forged = cst(&none_ctor);
        assert!(matches!(
            iter_step_obligation_verdict(&step, IterStepThm::Val2, Some(&forged)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// F-GENCOLLAPSE — the kernel CANNOT prove `iter_seq recv g = iter_seq recv (g+1)`: the two
    /// opaque applications at distinct second keys are never def-eq, so `Eq.refl` fails
    /// `check_type`. This pins that the two-key surface GENUINELY distinguishes generations —
    /// the property the one-arg handle lacks (where `idxElem(iter_region c,0)=…` is rfl).
    #[test]
    fn iter_step_gen_collapse_fails_check_type() {
        let env = crate::trustir_anchor::trustir_env().expect("anchor env");
        let l1 = Level::succ(Level::zero());
        // ∀ recv g, iter_seq recv g = iter_seq recv (g+1).  Under Π recv Π g: recv=1, g=0.
        let lhs = iter_seq_e(1, 0);
        let rhs = Expr::apps(cst(TRUSTIR_ITER_SEQ), [Expr::bvar(1), int_add1_e(0)]);
        let eq = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [int_ty(), lhs.clone(), rhs],
        );
        let statement = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), eq));
        // Forged proof: `λ recv g. Eq.refl Int (iter_seq recv g)` — proves LHS=LHS only.
        let refl =
            Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![l1]), [int_ty(), lhs]);
        let proof = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), refl));
        let tc = TypeChecker::new(&env);
        assert!(
            tc.check_type(&proof, &statement).is_err(),
            "iter_seq recv g = iter_seq recv (g+1) must NOT kernel-check (generations distinct)"
        );
    }

    /// F-STRTYPE — a `str`-family stride pointee never denotes a slice element; the two-key
    /// claim declines (the D6 `&str`→u8 conflation may not reach the primed surface).
    #[test]
    fn iter_step_str_element_declined() {
        let step = SemIterStep { recv_param: 1, element_ty: trust_types::Ty::Str };
        assert!(matches!(
            check_iter_step_refinement(&step),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// NO-NEW-AXIOMS — `iter_seq`/`iter_len` (Opaque) and `iter_has_next2` (Definition) each
    /// carry EMPTY axiom_deps (modulo-3 preserved), the `ptrOffset`/`iter_region` precedent.
    #[test]
    fn iter_step_surface_has_empty_axiom_deps() {
        let env = crate::trustir_anchor::trustir_env().expect("anchor env");
        for name in [
            TRUSTIR_ITER_SEQ,
            crate::trustir_anchor::TRUSTIR_ITER_LEN,
            TRUSTIR_ITER_HAS_NEXT2,
        ] {
            let residue = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} must be a registered decl"));
            assert!(residue.is_empty(), "{name} must have EMPTY axiom_deps, got {residue:?}");
        }
    }

    /// F-BRIDGE (census) — NO declaration mentions BOTH handle families in one term: the
    /// two-key surface (`iter_seq`/`iter_len`/`iter_has_next2`) and the per-certificate
    /// `ret2`/`post2` never reference the one-arg `iter_region`/`iter_has_next`, and vice
    /// versa. A bridge equation (e.g. `iter_region recv ~ iter_seq recv 0`) is axiom-shaped and
    /// would resurrect the refuted elem0=elem1 composition; this pin forbids it structurally.
    #[test]
    fn iter_step_no_bridge_between_handle_families() {
        let (env, _s, _n, _o) = build_iter_step_env(&example_iter_step()).expect("witness env");
        let iter_len = crate::trustir_anchor::TRUSTIR_ITER_LEN;
        let one_arg =
            [Name::from_string(TRUSTIR_ITER_REGION), Name::from_string(TRUSTIR_ITER_HAS_NEXT)];
        let two_key = [
            Name::from_string(TRUSTIR_ITER_SEQ),
            Name::from_string(iter_len),
            Name::from_string(TRUSTIR_ITER_HAS_NEXT2),
        ];
        let const_names_of = |n: &str| -> Vec<Name> {
            let ci = env.get_const(&Name::from_string(n)).expect("decl present");
            let mut names = Vec::new();
            collect_const_names(&ci.type_, &mut names);
            if let Some(v) = &ci.value {
                collect_const_names(v, &mut names);
            }
            names
        };
        // The two-key + per-certificate decls must NOT reference the one-arg family.
        for n in [TRUSTIR_ITER_SEQ, iter_len, TRUSTIR_ITER_HAS_NEXT2, ITER_STEP_RET2, ITER_STEP_POST2]
        {
            let names = const_names_of(n);
            for bad in &one_arg {
                assert!(!names.contains(bad), "decl `{n}` bridges to one-arg family `{bad:?}`");
            }
        }
        // And the one-arg family must NOT reference the two-key family (symmetry).
        for n in [TRUSTIR_ITER_REGION, TRUSTIR_ITER_HAS_NEXT] {
            let names = const_names_of(n);
            for bad in &two_key {
                assert!(!names.contains(bad), "one-arg decl `{n}` bridges to two-key `{bad:?}`");
            }
        }
    }

    // =======================================================================
    // Trust: W19 mutators inc-1 (2026-07-24) — the FIELD-SETTER kernel-witness pins
    // (the T-STEP recipe verbatim, one obligation-pair simpler). All CALL-SITE-INERT.
    // =======================================================================

    /// The pinned example: `set_x(&mut S{x:i64,y:i64}, v)` — recv local 1, field 0,
    /// value local 2, two declared fields, i64 scalar field.
    fn example_field_set() -> SemFieldSet {
        SemFieldSet {
            recv_param: 1,
            field_key: 0,
            value_param: 2,
            all_field_keys: vec![0, 1],
            field_ty: trust_types::Ty::Int { width: 64, signed: true },
        }
    }

    /// POSITIVE — the T-SET / T-FRAME pair kernel-checks modulo 3 (empty axiom_deps).
    #[test]
    fn field_set_refinement_proves_modulo3() {
        assert_eq!(
            check_field_set_refinement(&example_field_set()),
            RefinementVerdict::ProvenModulo3,
            "the recognized single-scalar-field setter's T-SET/T-FRAME proves modulo 3"
        );
    }

    /// T-SET (pol=true) and T-FRAME (pol=false) each individually prove modulo 3.
    #[test]
    fn field_set_both_theorems_prove_individually() {
        let fs = example_field_set();
        assert_eq!(
            field_set_obligation_verdict(&fs, FieldSetThm::Set, None),
            RefinementVerdict::ProvenModulo3
        );
        assert_eq!(
            field_set_obligation_verdict(&fs, FieldSetThm::Frame, None),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// F-CLAIMED-VALUE — T-SET with a claimed RHS = const ≠ v ⇒ `check_type` REJECTS
    /// (the proof's ACTUAL type is `= v`). The fail-closed probe proves the recipe is not
    /// a dressed-up tautology.
    #[test]
    fn field_set_claimed_wrong_value_rejects() {
        let fs = example_field_set();
        let bogus = int_lit(7); // claim `set_post recv k g v = 7`, not def-eq to `v`.
        assert!(matches!(
            field_set_obligation_verdict(&fs, FieldSetThm::Set, Some(&bogus)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// F-CLAIMED-FRAME — T-FRAME with a claimed RHS = v (claiming the frame ALSO equals
    /// the written value, i.e. a whole-receiver CLOBBER) ⇒ `check_type` REJECTS (the
    /// proof's ACTUAL type is `= idx_elem_prime recv k g`). Guards the option-(a) two-env
    /// clobber forgery. At the eq position `∀ recv k g v hg.`, the bound `v` is bvar 1.
    #[test]
    fn field_set_claimed_frame_clobber_rejects() {
        let fs = example_field_set();
        let v_at_eq = Expr::bvar(1);
        assert!(matches!(
            field_set_obligation_verdict(&fs, FieldSetThm::Frame, Some(&v_at_eq)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// F-NONSCALAR (kernel belt) — a non-scalar field type is `KernelRejected` by the
    /// refinement entry (the recognizer's G8 is the primary structural gate).
    #[test]
    fn field_set_nonscalar_field_declined() {
        let mut fs = example_field_set();
        fs.field_ty = trust_types::Ty::Unit;
        assert!(matches!(
            check_field_set_refinement(&fs),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// NO-NEW-AXIOMS — `idx_elem_prime` (Opaque) and `set_key_eq` (Definition → `Int.beq`
    /// Opaque) each carry EMPTY axiom_deps, and the per-certificate `set_post` closes
    /// empty too (modulo-3 preserved), the `idx_elem`/`iter_seq` precedent.
    #[test]
    fn field_set_surface_has_empty_axiom_deps() {
        let env = crate::trustir_anchor::trustir_env().expect("anchor env");
        for name in [MIRSEM_IDX_ELEM_PRIME, MIRSEM_SET_KEY_EQ] {
            let residue = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} must be a registered decl"));
            assert!(residue.is_empty(), "{name} must have EMPTY axiom_deps, got {residue:?}");
        }
        let env2 = build_field_set_env(0).expect("witness env");
        let residue =
            env2.axiom_deps(&Name::from_string(SET_POST)).expect("set_post registered");
        assert!(residue.is_empty(), "set_post must have EMPTY axiom_deps, got {residue:?}");
    }

    /// F-BRIDGE — NO field-setter decl references the LIVE 2-arg `idx_elem` field-read
    /// family: the 3-arg `idx_elem_prime`, `set_key_eq`, and the per-certificate
    /// `set_post` never mention `Trust.MirSem.idx_elem`. A bridge equation
    /// `idx_elem_prime recv k g ~ idx_elem <handle>` is the F12-forbidden cross-
    /// instantiation (the setter analogue of the refuted iter elem0=elem1); this pin
    /// forbids it structurally.
    #[test]
    fn field_set_no_bridge_to_live_idx_elem() {
        let env = build_field_set_env(0).expect("witness env");
        let live_idx_elem = Name::from_string(crate::mirsem::MIRSEM_IDX_ELEM);
        let const_names_of = |n: &str| -> Vec<Name> {
            let ci = env.get_const(&Name::from_string(n)).expect("decl present");
            let mut names = Vec::new();
            collect_const_names(&ci.type_, &mut names);
            if let Some(v) = &ci.value {
                collect_const_names(v, &mut names);
            }
            names
        };
        for n in [MIRSEM_IDX_ELEM_PRIME, MIRSEM_SET_KEY_EQ, SET_POST] {
            let names = const_names_of(n);
            assert!(
                !names.contains(&live_idx_elem),
                "field-setter decl `{n}` bridges to the LIVE 2-arg idx_elem (F12)"
            );
        }
    }

    // =======================================================================
    // Trust: W19 mutators inc-1.5 (2026-07-24) — the CHECKED-RMW kernel-witness pins
    // (the inc-1 field-setter recipe with an arithmetic TRUE minor). All CALL-SITE-INERT.
    // =======================================================================

    /// The pinned example: `bump(&mut S{x:i64,y:i64})` — recv local 1, field 0, `+= 1`,
    /// two declared fields, i64 scalar field. `SemRmwRhs::Const` ⇒ the `v` binder is
    /// vacuous, which is exactly the `bump` fixture's shape.
    fn example_field_rmw() -> SemFieldRmw {
        SemFieldRmw {
            recv_param: 1,
            field_key: 0,
            op: SemRmwOp::Add,
            rhs: SemRmwRhs::Const(1),
            all_field_keys: vec![0, 1],
            field_ty: trust_types::Ty::Int { width: 64, signed: true },
        }
    }

    /// POSITIVE — the checked-RMW T-SET / T-FRAME pair kernel-checks modulo 3.
    #[test]
    fn field_rmw_refinement_proves_modulo3() {
        assert_eq!(
            check_field_rmw_refinement(&example_field_rmw()),
            RefinementVerdict::ProvenModulo3,
            "the recognized checked-RMW setter's T-SET/T-FRAME proves modulo 3"
        );
    }

    /// POSITIVE (all three ops, both right-hand operand forms) — the surface is uniform
    /// over `Int.add`/`Int.sub`/`Int.mul` and over a literal vs a parameter RHS.
    #[test]
    fn field_rmw_all_ops_and_rhs_forms_prove_modulo3() {
        for op in [SemRmwOp::Add, SemRmwOp::Sub, SemRmwOp::Mul] {
            for rhs in [SemRmwRhs::Const(1), SemRmwRhs::Const(-7), SemRmwRhs::Param(2)] {
                let rmw = SemFieldRmw { op, rhs, ..example_field_rmw() };
                assert_eq!(
                    check_field_rmw_refinement(&rmw),
                    RefinementVerdict::ProvenModulo3,
                    "op {op:?} / rhs {rhs:?} must prove modulo 3"
                );
            }
        }
    }

    /// T-SET (pol=true) and T-FRAME (pol=false) each individually prove modulo 3.
    #[test]
    fn field_rmw_both_theorems_prove_individually() {
        let rmw = example_field_rmw();
        assert_eq!(
            field_rmw_obligation_verdict(&rmw, FieldRmwThm::Set, None),
            RefinementVerdict::ProvenModulo3
        );
        assert_eq!(
            field_rmw_obligation_verdict(&rmw, FieldRmwThm::Frame, None),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// Assert a forged claim is rejected BY THE KERNEL (`check_type`), not by the
    /// surrounding plumbing. `field_rmw_obligation_verdict` returns the SAME
    /// `KernelRejected` variant for an env-build failure, an `add_decl` failure, and a
    /// genuine def-eq refusal — so a bare `matches!(.., KernelRejected(_))` would still
    /// pass if the probe silently stopped reaching the type-checker at all. The message
    /// prefix is what distinguishes them.
    #[track_caller]
    fn assert_kernel_type_rejected(v: RefinementVerdict, what: &str) {
        match v {
            RefinementVerdict::KernelRejected(msg) => assert!(
                msg.starts_with("check_type["),
                "{what}: expected a check_type refusal, got a different failure: {msg}"
            ),
            other => panic!("{what}: expected KernelRejected, got {other:?}"),
        }
    }

    /// F-CLAIMED-DELTA — the CENTRAL non-tautology probe for inc-1.5: T-SET with a
    /// claimed RHS of `Int.add (idx_elem_prime recv fld g) 2` when the recognized body
    /// adds ONE ⇒ `check_type` REJECTS. Without this, the arithmetic minor could be any
    /// term at all and the recipe would carry no information about the delta.
    #[test]
    fn field_rmw_claimed_wrong_delta_rejects() {
        let rmw = example_field_rmw();
        let off_by_one = SemFieldRmw { rhs: SemRmwRhs::Const(2), ..rmw.clone() };
        // The claimed term is built at the SAME de-Bruijn depth the honest minor uses.
        let bogus = super::rmw_value_e(&off_by_one, 4, 2, 1);
        assert_kernel_type_rejected(
            field_rmw_obligation_verdict(&rmw, FieldRmwThm::Set, Some(&bogus)),
            "claiming `+2` for a body that adds 1",
        );
    }

    /// OPACITY PIN — `idx_elem_prime` is a `Declaration::Opaque`, and that is what the
    /// ENTIRE content of inc-1.5 rests on. Its registered body is the type-correct
    /// placeholder `λλλ Int.ofNat 0`; if it ever δ-unfolded, the T-SET minor
    /// `Int.add (idx_elem_prime recv fld g) 1` would reduce to `0 + 1 = 1` and the
    /// theorem would collapse from "the post-value is a function of the PRE-value" into
    /// a closed arithmetic tautology — while still type-checking green. Nothing else in
    /// the suite would catch that, so pin the declaration KIND directly.
    #[test]
    fn field_rmw_prestate_selector_is_opaque_and_does_not_unfold() {
        let env = crate::trustir_anchor::trustir_env().expect("anchor env");
        let ci = env
            .get_const(&Name::from_string(MIRSEM_IDX_ELEM_PRIME))
            .expect("idx_elem_prime registered");
        assert!(
            matches!(ci.kind, clean_kernel::ConstantKind::Opaque),
            "idx_elem_prime MUST stay Opaque — a reducible one collapses T-SET to `0+1=1`: \
             {:?}",
            ci.kind
        );
        // Behavioural twin of the kind check: the placeholder body must NOT be reachable
        // by def-eq, i.e. `idx_elem_prime a b c` is NOT def-eq to `Int.ofNat 0`.
        let applied = super::idx_elem_prime_e(0, 0, 0);
        let applied = Expr::lam(bd(), int_ty(), applied);
        let zero = Expr::lam(bd(), int_ty(), int_lit(0));
        let tc = TypeChecker::new(&env);
        assert!(
            !tc.is_def_eq(&applied, &zero),
            "idx_elem_prime must not unfold to its placeholder body"
        );
    }

    /// F-CLAIMED-OP — claiming `Int.sub` for a recognized `Int.add` body ⇒ REJECTED.
    /// (`Int.add`/`Int.sub` are both reducible, so this is a genuine def-eq refusal on
    /// an unconstrained opaque left summand, not a syntactic mismatch.)
    #[test]
    fn field_rmw_claimed_wrong_op_rejects() {
        let rmw = example_field_rmw();
        let subbed = SemFieldRmw { op: SemRmwOp::Sub, ..rmw.clone() };
        let bogus = super::rmw_value_e(&subbed, 4, 2, 1);
        assert_kernel_type_rejected(
            field_rmw_obligation_verdict(&rmw, FieldRmwThm::Set, Some(&bogus)),
            "claiming Int.sub for a body that adds",
        );
    }

    /// F-CLAIMED-PRESTATE — claiming the post-value is the UNCHANGED pre-state
    /// (`idx_elem_prime recv fld g`, i.e. "the RMW did nothing") ⇒ REJECTED. The
    /// complement of F-CLAIMED-DELTA: neither a wrong delta nor NO delta type-checks.
    #[test]
    fn field_rmw_claimed_unchanged_prestate_rejects() {
        let rmw = example_field_rmw();
        let bogus = super::idx_elem_prime_e(4, 3, 2);
        assert_kernel_type_rejected(
            field_rmw_obligation_verdict(&rmw, FieldRmwThm::Set, Some(&bogus)),
            "claiming the post-value equals the unchanged pre-state",
        );
    }

    /// F-CLAIMED-FRAME — T-FRAME with a claimed RHS equal to the INCREMENTED value
    /// (claiming every other field also got bumped — a whole-receiver clobber) ⇒
    /// REJECTED. The inc-1 clobber forgery, at the RMW minor.
    #[test]
    fn field_rmw_claimed_frame_clobber_rejects() {
        let rmw = example_field_rmw();
        let bogus = super::rmw_value_e(&rmw, 4, 2, 1);
        assert_kernel_type_rejected(
            field_rmw_obligation_verdict(&rmw, FieldRmwThm::Frame, Some(&bogus)),
            "claiming the FRAME also got incremented",
        );
    }

    /// F-NONINT (kernel belt) — a non-`Int` field type is `KernelRejected` by the
    /// refinement entry (the recognizer's G8 is the primary structural gate).
    #[test]
    fn field_rmw_nonint_field_declined() {
        let mut rmw = example_field_rmw();
        rmw.field_ty = trust_types::Ty::Bool;
        assert!(matches!(
            check_field_rmw_refinement(&rmw),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// F-WIDTH (belt) — a hand-built witness over a 128-bit field is `KernelRejected` by
    /// the `pub` entry, mirroring the mint gate's G-WIDTH.
    #[test]
    fn field_rmw_belt_rejects_128_bit_field() {
        let rmw = SemFieldRmw {
            field_ty: trust_types::Ty::Int { width: 128, signed: true },
            ..example_field_rmw()
        };
        assert!(matches!(
            check_field_rmw_refinement(&rmw),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// F-LITRANGE (belt) — a hand-built witness carrying a literal outside the FIELD's
    /// declared type is `KernelRejected`.
    ///
    /// Trust: THIS TEST'S RATIONALE CHANGED THE DAY IT WAS WRITTEN, and the change is
    /// worth recording. It originally pinned the `int_lit` TRUNCATION COLLISION — that
    /// `Const(1 << 70)` and `Const(0)` build the byte-identical term — as the reason the
    /// belt exists. Generalizing that same encoder-fidelity concern one lane over turned
    /// up a LIVE FALSE ACCEPT in the grounder, and the fix made the encoder EXACT over
    /// the full `i128` range (`Expr::nat_lit_u128`). So the collision is gone, and this
    /// test caught its own premise expiring — which is the pin doing its job.
    ///
    /// F-LITRANGE survives on an INDEPENDENT justification: a literal outside the
    /// field's declared integer type cannot be that operand's value in any well-formed
    /// lowering, so admitting one would mint a term the body never computes. That reason
    /// never depended on the encoder.
    #[test]
    fn field_rmw_belt_rejects_unencodable_literal() {
        let rmw = SemFieldRmw { rhs: SemRmwRhs::Const(1i128 << 70), ..example_field_rmw() };
        assert!(
            matches!(check_field_rmw_refinement(&rmw), RefinementVerdict::KernelRejected(_)),
            "a literal outside the i64 field's declared range must be rejected by the belt"
        );
        // The collision is GONE — the encoder is exact. Pinned so a regression to a
        // bounded encoder is caught HERE rather than by the next false accept.
        let zero = SemFieldRmw { rhs: SemRmwRhs::Const(0), ..example_field_rmw() };
        assert_ne!(
            super::rmw_value_e(&rmw, 4, 2, 1),
            super::rmw_value_e(&zero, 4, 2, 1),
            "`+= 2^70` and `+= 0` must build DISTINCT terms — if they ever collide again, \
             the 2026-07-24 grounder false accept is reachable once more"
        );
    }

    /// NO-NEW-AXIOMS — the per-certificate `rmw_post` closes with EMPTY `axiom_deps`,
    /// and so do the three prelude arithmetic constants it names (`Int.add`/`sub`/`mul`
    /// are reducible Definitions, never `Axiom`s). Modulo-3 preserved.
    #[test]
    fn field_rmw_surface_has_empty_axiom_deps() {
        let env = crate::trustir_anchor::trustir_env().expect("anchor env");
        for name in ["Int.add", "Int.sub", "Int.mul"] {
            let residue = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} must be a registered decl"));
            assert!(residue.is_empty(), "{name} must have EMPTY axiom_deps, got {residue:?}");
        }
        for op in [SemRmwOp::Add, SemRmwOp::Sub, SemRmwOp::Mul] {
            let rmw = SemFieldRmw { op, ..example_field_rmw() };
            let env2 = super::build_field_rmw_env(&rmw).expect("witness env");
            let residue =
                env2.axiom_deps(&Name::from_string(super::RMW_POST)).expect("rmw_post registered");
            assert!(residue.is_empty(), "rmw_post must have EMPTY axiom_deps, got {residue:?}");
        }
    }

    /// F-BRIDGE — NO checked-RMW decl references the LIVE 2-arg `idx_elem` field-read
    /// family. This is the pin that matters MOST for inc-1.5: the RMW's pre-state read
    /// `(*self).x` IS a real field read, so `rmw_post`'s TRUE minor is the natural place
    /// to smuggle in a bridge from the 3-arg (generation-keyed) `idx_elem_prime` to the
    /// live 2-arg (untimed)
    /// `idx_elem`. It is mapped to `idx_elem_prime recv <fld> g` and nothing else.
    #[test]
    fn field_rmw_no_bridge_to_live_idx_elem() {
        let env = super::build_field_rmw_env(&example_field_rmw()).expect("witness env");
        let live_idx_elem = Name::from_string(crate::mirsem::MIRSEM_IDX_ELEM);
        let ci = env.get_const(&Name::from_string(super::RMW_POST)).expect("decl present");
        let mut names = Vec::new();
        collect_const_names(&ci.type_, &mut names);
        if let Some(v) = &ci.value {
            collect_const_names(v, &mut names);
        }
        assert!(
            !names.contains(&live_idx_elem),
            "checked-RMW decl `{}` bridges to the LIVE 2-arg idx_elem (F12)",
            super::RMW_POST
        );
        // ...and it DOES name the primed 3-arg opaque (the pin is not vacuous).
        assert!(
            names.contains(&Name::from_string(MIRSEM_IDX_ELEM_PRIME)),
            "rmw_post must key its pre-state read on the 3-arg idx_elem_prime"
        );
    }

    #[test]
    fn integer_cast_payload_reduces_to_rust_integer_as_results() {
        let env = crate::trustir_anchor::trustir_env().expect("anchor env");
        let tc = TypeChecker::new(&env);
        for (source, width, signed, expected) in [
            (-1, 8, false, 255),
            (255, 8, true, -1),
            (256, 8, false, 0),
            (-129, 8, true, 127),
            (i128::MIN, 8, false, 0),
        ] {
            let actual = int_cast_expr(&SemOperand::Const(source), width, signed, 0)
                .expect("supported integer cast expression");
            assert!(
                tc.is_def_eq(&actual, &int_lit(expected)),
                "cast {source} -> {}{width} must reduce to {expected}",
                if signed { 'i' } else { 'u' }
            );
        }
    }

    #[test]
    fn adt_return_two_nested_arms_use_distinct_internal_carriers() {
        let mut r = example_half_promotion();
        r.else_arm.payload =
            Some(SemAdtPayload::NullaryNested { enum_name: "Error".to_string(), variant: 2 });

        let mut env = crate::trustir_anchor::trustir_env().expect("anchor env");
        let (_, _, then_nested, else_nested, _) =
            register_outer_enum(&mut env, &r).expect("both nested carriers register");
        assert_ne!(
            then_nested, else_nested,
            "different variants of one nested enum must not reuse the first arm's constructor"
        );
        assert_eq!(check_adt_return_refinement(&r), RefinementVerdict::ProvenModulo3);
    }

    /// FAIL-CLOSED probe (adversarial probe (a): wrong-variant-tag misdenotation) —
    /// claim the guarded return equals the ELSE arm's value (`Ok(cast(src))`) even though the
    /// guard is TRUE (`src < 0`), i.e. the TRUE answer is `Err(Error::Underflow)`. The
    /// `congrArg`-transport proof's ACTUAL type is `select = then_val` regardless of
    /// what is claimed, so a claimed RHS not def-eq to `then_val` (the `Ok`/`Err`
    /// constructors are DISTINCT by inductive `noConfusion`, never unifiable) makes
    /// `check_type` reject — the kernel genuinely catches a wrong-variant claim, not a
    /// dressed-up tautology (see [`build_refinement`]'s doc for why "swap the arms and
    /// keep the same guard" is NOT a valid probe: that produces a DIFFERENT but still
    /// internally-consistent, still-provable statement).
    #[test]
    fn adt_return_refinement_fail_closed_wrong_variant_claim() {
        let r = example_half_promotion();
        let wrong_rhs = else_value_for_test(&r).expect("else-arm value builds");
        assert!(
            matches!(
                check_adt_return_refinement_claimed(&r, Some(&wrong_rhs)),
                RefinementVerdict::KernelRejected(_)
            ),
            "claiming the ELSE arm's value under a TRUE guard must be rejected by the kernel"
        );
    }

    #[test]
    fn adt_return_false_arm_wrong_claim_is_kernel_rejected() {
        let r = example_half_promotion();
        let wrong_rhs = then_value_for_test(&r).expect("then-arm value builds");
        let (env, statement, proof) =
            build_refinement_else(&r, Some(&wrong_rhs)).expect("false-arm obligation builds");
        let tc = TypeChecker::new(&env);
        assert!(
            tc.check_type(&proof, &statement).is_err(),
            "the false-arm proof must reject a claim for the true-arm constructor"
        );
    }

    // -----------------------------------------------------------------------
    // 3-outcome guard chain (gap-queue #2 follow-up #1, 2026-07-08).
    // -----------------------------------------------------------------------

    use crate::mirsem::SemAdtReturn3;

    /// The canonical `from_signed!`-shape: `Err(if src < i8::MIN as i16 {
    /// Underflow } else if src > i8::MAX as i16 { Overflow } else { return
    /// Ok(src as i8); })` — matching the REAL `cast` 0.3.0 fixture
    /// (`_64::<impl From<i16> for i8>::cast`).
    fn example_from_signed() -> SemAdtReturn3 {
        SemAdtReturn3 {
            cond1: SemCondTree::Leaf(SemCond {
                op: SemCmpOp::Lt,
                a: SemOperand::Var(0),
                b: SemOperand::Const(-128),
            }),
            cond2: SemCondTree::Leaf(SemCond {
                op: SemCmpOp::Gt,
                a: SemOperand::Var(0),
                b: SemOperand::Const(127),
            }),
            arm_a: SemAdtArm {
                variant: 1,
                payload: Some(SemAdtPayload::NullaryNested {
                    enum_name: "Error".to_string(),
                    variant: 3,
                }),
            },
            arm_b: SemAdtArm {
                variant: 1,
                payload: Some(SemAdtPayload::NullaryNested {
                    enum_name: "Error".to_string(),
                    variant: 2,
                }),
            },
            arm_c: SemAdtArm {
                variant: 0,
                payload: Some(SemAdtPayload::IntCast {
                    source: SemOperand::Var(0),
                    width: 8,
                    signed: true,
                }),
            },
            enum_name: "core::result::Result".to_string(),
        }
    }

    #[test]
    fn adt_return3_refinement_modulo3() {
        assert_eq!(
            check_adt_return3_refinement(&example_from_signed()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// ADVERSARIAL: the TWO nested `Error` payloads (arm A: `Underflow`=3, arm B:
    /// `Overflow`=2) must NOT collapse to the same claimed value — a real risk
    /// this witness's registration specifically guards against (module doc's
    /// "OUTER-ENUM REGISTRATION NOTE": a naive shared-name registration would
    /// silently reuse arm A's nested constructor for arm B too). Cross-claiming
    /// arm A's value for arm B's obligation must be `KernelRejected`.
    #[test]
    fn adt_return3_refinement_fail_closed_cross_arm_claim() {
        let r = example_from_signed();
        // Build arm A's OWN closed value (depth 1, matching `build_bc`'s `arm_x_e2`
        // convention closely enough for a wrong-claim probe — any depth-1 term
        // that is NOT def-eq to arm B's real value serves the same purpose).
        let mut env = crate::trustir_anchor::trustir_env().expect("trustir env builds");
        let (ctor_a, _ctor_b, _ctor_c, nested_a, _nested_b, _nested_c, _name) =
            register_outer_enum3(&mut env, &r).expect("registration succeeds");
        let wrong_b = arm_value_expr(&ctor_a, &r.arm_a.payload, nested_a.as_ref(), 2)
            .expect("arm A's value builds");
        assert!(
            matches!(
                check_adt_return3_refinement_claimed(&r, [None, Some(&wrong_b), None]),
                RefinementVerdict::KernelRejected(_)
            ),
            "claiming arm A's value for arm B's obligation must be rejected by the kernel"
        );
    }

    // -----------------------------------------------------------------------
    // Trust: OPAQUE-CHAIN ADT-RETURN (M6 Tier-1 SHAPE_GAP, 2026-07-10).
    // -----------------------------------------------------------------------

    use crate::mirsem::{
        SemAdtReturnOpaque, SemChainVal, SemOpaqueArm, SemOpaqueCond, SemOpaqueStep,
    };

    /// The `Abstractor::fold_fvar_opt` Family-D shape: 2 steps (Bool sentinel
    /// guard + Int `ek` payload), `StepBool(0)` guard, `Some(Step(1))`/`None`.
    fn example_opaque_fold_fvar() -> SemAdtReturnOpaque {
        SemAdtReturnOpaque {
            steps: vec![
                SemOpaqueStep { callee: "__trust_total_clone".into(), bool_typed: true },
                SemOpaqueStep { callee: "expr::kind::ek".into(), bool_typed: false },
            ],
            cond: SemOpaqueCond::StepBool(0),
            then_arm: SemOpaqueArm { variant: 1, payload: Some(SemChainVal::Step(1)) },
            else_arm: SemOpaqueArm { variant: 0, payload: None },
            enum_name: "std::option::Option".to_string(),
        }
    }

    /// The `Lifter::fold_bvar_opt` Family-B shape: REAL `Ge(idx, self.start)`
    /// guard over (param, entry field read), 2 Int steps.
    fn example_opaque_fold_bvar() -> SemAdtReturnOpaque {
        SemAdtReturnOpaque {
            steps: vec![
                SemOpaqueStep { callee: "expr::checked_add_u32".into(), bool_typed: false },
                SemOpaqueStep { callee: "expr::kind::ek".into(), bool_typed: false },
            ],
            cond: SemOpaqueCond::Cmp {
                op: SemCmpOp::Ge,
                a: SemOperand::Var(1),
                b: SemOperand::Field(Box::new(SemOperand::Var(0)), 0),
            },
            then_arm: SemOpaqueArm { variant: 1, payload: Some(SemChainVal::Step(1)) },
            else_arm: SemOpaqueArm { variant: 0, payload: None },
            enum_name: "std::option::Option".to_string(),
        }
    }

    #[test]
    fn adt_return_opaque_refinement_modulo3_stepbool_guard() {
        assert_eq!(
            check_adt_return_opaque_refinement(&example_opaque_fold_fvar()),
            RefinementVerdict::ProvenModulo3
        );
    }

    #[test]
    fn adt_return_opaque_refinement_modulo3_cmp_guard() {
        assert_eq!(
            check_adt_return_opaque_refinement(&example_opaque_fold_bvar()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// FAIL-CLOSED probe (mission probe (a): wrong-variant claim) — claiming the
    /// ELSE arm's value (`None`) under a TRUE guard must be `KernelRejected`
    /// (the `congrArg` transport's actual type is `select = Some(step)`; `None`
    /// is a DISTINCT constructor, never def-eq).
    #[test]
    fn adt_return_opaque_fail_closed_wrong_variant_claim() {
        for r in [example_opaque_fold_fvar(), example_opaque_fold_bvar()] {
            let wrong = opaque_else_value_for_test(&r).expect("else value builds");
            assert!(
                matches!(
                    check_adt_return_opaque_refinement_claimed(&r, Some(&wrong)),
                    RefinementVerdict::KernelRejected(_)
                ),
                "claiming the ELSE arm's value under a TRUE guard must be KernelRejected"
            );
        }
    }

    /// FAIL-CLOSED probe (mission probe (c): ctor arg swapped) — claiming
    /// `Some(<the OTHER step>)` (the guard's own Bool step instead of the
    /// payload step) or `Some(<a wrong entry operand>)` must be
    /// `KernelRejected`: the ∀-bound binders are DISTINCT bvars, never def-eq.
    #[test]
    fn adt_return_opaque_fail_closed_swapped_payload_claim() {
        let r = example_opaque_fold_bvar();
        for wrong_payload in [
            SemChainVal::Step(0),
            SemChainVal::Operand(SemOperand::Var(1)),
            SemChainVal::Operand(SemOperand::Field(Box::new(SemOperand::Var(0)), 7)),
        ] {
            let wrong = opaque_then_value_with_payload_for_test(&r, &wrong_payload)
                .expect("wrong-payload value builds");
            assert!(
                matches!(
                    check_adt_return_opaque_refinement_claimed(&r, Some(&wrong)),
                    RefinementVerdict::KernelRejected(_)
                ),
                "claiming Some(<swapped arg>) must be KernelRejected: {wrong_payload:?}"
            );
        }
    }

    /// FAIL-CLOSED: a malformed shape (a `StepBool` guard naming a non-Bool /
    /// out-of-range step) must be `KernelRejected` at witness-build time, not
    /// silently accepted.
    #[test]
    fn adt_return_opaque_fail_closed_malformed_guard_step() {
        let mut r = example_opaque_fold_fvar();
        r.cond = SemOpaqueCond::StepBool(1); // ek's Int step — not Bool.
        assert!(matches!(
            check_adt_return_opaque_refinement(&r),
            RefinementVerdict::KernelRejected(_)
        ));
        let mut r2 = example_opaque_fold_fvar();
        r2.cond = SemOpaqueCond::StepBool(9); // out of range.
        assert!(matches!(
            check_adt_return_opaque_refinement(&r2),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// ADVERSARIAL: claiming arm C's (Ok) value for arm A's (Err, guard1=true)
    /// obligation — a wrong-variant misdenotation across the OUTER split — must
    /// be `KernelRejected`.
    #[test]
    fn adt_return3_refinement_fail_closed_wrong_outer_variant_claim() {
        let r = example_from_signed();
        let mut env = crate::trustir_anchor::trustir_env().expect("trustir env builds");
        let (_ctor_a, _ctor_b, ctor_c, _nested_a, _nested_b, nested_c, _name) =
            register_outer_enum3(&mut env, &r).expect("registration succeeds");
        let wrong_a = arm_value_expr(&ctor_c, &r.arm_c.payload, nested_c.as_ref(), 1)
            .expect("arm C's value builds");
        assert!(
            matches!(
                check_adt_return3_refinement_claimed(&r, [Some(&wrong_a), None, None]),
                RefinementVerdict::KernelRejected(_)
            ),
            "claiming arm C's value for arm A's obligation must be rejected by the kernel"
        );
    }

    // =====================================================================
    // Trust: SCALAR SENTINEL-SELECT (cmp-mono-select, 2026-07-16) kernel tests.
    // =====================================================================

    /// The `<u8 as Ord>::min` shape: guard-TRUE (SwitchInt `otherwise`) arm
    /// returns param op-index 1 (`other`); guard-FALSE (value-0) arm returns 0
    /// (`self`). The guard Bool is UNINTERPRETED (no value claim).
    fn example_scalar_sentinel_select() -> SemScalarSentinelSelect {
        SemScalarSentinelSelect { then_var: 1, else_var: 0, width: 8, signed: false }
    }

    /// POSITIVE: the scalar sentinel-select witness proves modulo 3 (BOTH
    /// `g=true→then` and `g=false→else`), against the REAL clean-kernel.
    #[test]
    fn scalar_sentinel_select_refinement_proves_modulo_3() {
        assert!(
            matches!(
                check_scalar_sentinel_select_refinement(&example_scalar_sentinel_select()),
                RefinementVerdict::ProvenModulo3
            ),
            "the scalar sentinel-select witness must prove modulo 3"
        );
    }

    /// FAIL-CLOSED (guard genuinely consumed): claiming the guard-TRUE arm returns
    /// the ELSE param — a forgery — must be `KernelRejected` (the `congrArg`
    /// transport proves `select = f Bool.true ≡ then_var`, NOT def-eq to
    /// `else_var`).
    #[test]
    fn scalar_sentinel_select_wrong_then_claim_is_kernel_rejected() {
        use crate::mirsem::SemChainVal;
        let r = example_scalar_sentinel_select();
        let wrong =
            chain_val_expr(&SemChainVal::Operand(SemOperand::Var(r.else_var)), 1, 1).unwrap();
        assert!(
            matches!(
                check_scalar_sentinel_select_refinement_claimed(&r, [Some(&wrong), None]),
                RefinementVerdict::KernelRejected(_)
            ),
            "a wrong claimed then-arm (the ELSE param) must be KernelRejected"
        );
    }

    /// FAIL-CLOSED: symmetric probe on the guard-FALSE obligation — claiming the
    /// else arm returns the THEN param must be `KernelRejected`.
    #[test]
    fn scalar_sentinel_select_wrong_else_claim_is_kernel_rejected() {
        use crate::mirsem::SemChainVal;
        let r = example_scalar_sentinel_select();
        let wrong =
            chain_val_expr(&SemChainVal::Operand(SemOperand::Var(r.then_var)), 1, 1).unwrap();
        assert!(
            matches!(
                check_scalar_sentinel_select_refinement_claimed(&r, [None, Some(&wrong)]),
                RefinementVerdict::KernelRejected(_)
            ),
            "a wrong claimed else-arm (the THEN param) must be KernelRejected"
        );
    }

    // -------------------------------------------------------------------
    // ADT PAYLOAD-EXTRACTION SELECT (optres-payload-extract, 2026-07-17) —
    // the value-faithful recursor witness, over the REAL committed dumps +
    // kernel-level forgery probes.
    // -------------------------------------------------------------------

    fn load_payload_dump(def_path: &str) -> trust_types::VerifiableFunction {
        let dir = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/fixtures/optres-payload-extract-2026-07-17/dumps"
        );
        for entry in std::fs::read_dir(dir).expect("dumps dir readable") {
            let path = entry.expect("dir entry").path();
            if path.extension().and_then(|e| e.to_str()) != Some("json") {
                continue;
            }
            let bytes = std::fs::read(&path).expect("read dump");
            if let Ok(f) = serde_json::from_slice::<trust_types::VerifiableFunction>(&bytes) {
                if f.def_path == def_path {
                    return f;
                }
            }
        }
        panic!("no dump with def_path == {def_path}");
    }

    #[test]
    fn payload_extract_option_i32_certifies_modulo_3() {
        let f = load_payload_dump("std::option::Option::<i32>::unwrap_or");
        let s = crate::mirsem::sem_adt_payload_extract_of_discriminant_switch(&f)
            .expect("recognized");
        assert_eq!(
            check_payload_extract_refinement(&s),
            RefinementVerdict::ProvenModulo3,
            "Option::<i32>::unwrap_or's payload extraction + default must certify modulo 3"
        );
    }

    #[test]
    fn payload_extract_result_i32_u8_certifies_modulo_3() {
        // Result's DEFAULT constructor (Err) carries a field — the NONE obligation's
        // recursor minor binds it and still returns the outer `d` (the caller owns
        // the de-Bruijn shift). This is the field-bearing-default-ctor case the
        // Option-only spec sketch did not cover; it MUST certify.
        let f = load_payload_dump("std::result::Result::<i32, u8>::unwrap_or");
        let s = crate::mirsem::sem_adt_payload_extract_of_discriminant_switch(&f)
            .expect("recognized");
        assert_eq!(
            check_payload_extract_refinement(&s),
            RefinementVerdict::ProvenModulo3,
            "Result::<i32,u8>::unwrap_or (field-bearing Err default) must certify modulo 3"
        );
    }

    /// FORGERY PROBE (some→default): claiming the SOME obligation's RHS is the
    /// default `d` instead of the field `x` — `Rec(Some x, d)` ι-reduces to `x`,
    /// and `x`/`d` are DISTINCT bvars ⇒ NOT def-eq ⇒ `KernelRejected`. Proves the
    /// some-minor genuinely READS THE PAYLOAD, not the default.
    #[test]
    fn payload_extract_some_to_default_is_kernel_rejected() {
        let f = load_payload_dump("std::option::Option::<i32>::unwrap_or");
        let s = crate::mirsem::sem_adt_payload_extract_of_discriminant_switch(&f)
            .expect("recognized");
        let (d, _xf) = payload_extract_some_probe_bvars(&s).expect("probe bvars build");
        assert!(
            matches!(
                check_payload_extract_refinement_claimed(&s, [Some(&d), None], false),
                RefinementVerdict::KernelRejected(_)
            ),
            "claiming SOME returns the default `d` (not the field `x`) must be KernelRejected"
        );
    }

    /// FORGERY PROBE (swapped minor): building the some-minor as `λx. d` (ignores
    /// the field, returns the default) while keeping the honest RHS `x` —
    /// `Rec(Some x, d)` now reduces to `d != x` ⇒ `KernelRejected`. Proves the
    /// value-faithfulness of the `bvar(0)` field read.
    #[test]
    fn payload_extract_swapped_minor_is_kernel_rejected() {
        let f = load_payload_dump("std::option::Option::<i32>::unwrap_or");
        let s = crate::mirsem::sem_adt_payload_extract_of_discriminant_switch(&f)
            .expect("recognized");
        assert!(
            matches!(
                check_payload_extract_refinement_claimed(&s, [None, None], true),
                RefinementVerdict::KernelRejected(_)
            ),
            "a swapped some-minor (returns the default, not the field) must be KernelRejected"
        );
    }

    /// FORGERY PROBE (none→literal): claiming the NONE obligation's RHS is a fresh
    /// Int literal while the LHS reduces to the open bound default `d` — literal !=
    /// open var ⇒ `KernelRejected`.
    #[test]
    fn payload_extract_none_to_literal_is_kernel_rejected() {
        let f = load_payload_dump("std::option::Option::<i32>::unwrap_or");
        let s = crate::mirsem::sem_adt_payload_extract_of_discriminant_switch(&f)
            .expect("recognized");
        let seven = crate::trustir_anchor::int_lit(7);
        assert!(
            matches!(
                check_payload_extract_refinement_claimed(&s, [None, Some(&seven)], false),
                RefinementVerdict::KernelRejected(_)
            ),
            "claiming NONE returns a concrete literal (not the bound default `d`) must be \
             KernelRejected"
        );
    }

    // -------------------------------------------------------------------
    // DIVERGENCE-GUARDED payload extraction (W-UNWRAP-DIVERGE, 2026-07-17) —
    // the SOME-ONLY witness for `unwrap`/`expect` over the REAL corpus dumps.
    // -------------------------------------------------------------------

    /// The `Option::<i32>::unwrap` SOME obligation (field read) kernel-checks modulo 3
    /// — the divergence-guarded value-faithful payload witness (there is NO None-side
    /// obligation; that arm diverges).
    #[test]
    fn payload_extract_diverging_option_i32_unwrap_certifies_modulo_3() {
        let f = load_payload_dump("std::option::Option::<i32>::unwrap");
        let s = crate::mirsem::sem_adt_payload_extract_diverging_of_discriminant_switch(&f)
            .expect("Option::<i32>::unwrap divergence-guarded extraction recognized");
        assert_eq!(s.extract_variant, 1, "Some is variant 1");
        assert_eq!(s.extract_field_idx, 0);
        assert_eq!(
            check_payload_extract_diverging_refinement(&s),
            RefinementVerdict::ProvenModulo3,
            "unwrap's SOME-side payload ι-reduction must certify modulo 3"
        );
    }

    /// The `Result::<i32,u8>::unwrap` SOME obligation (Ok field read, variant 0) —
    /// the panic arm (Err) reads the Err payload + Refs it before diverging; the
    /// SOME witness is unaffected and MUST certify modulo 3.
    #[test]
    fn payload_extract_diverging_result_i32_u8_unwrap_certifies_modulo_3() {
        let f = load_payload_dump("std::result::Result::<i32, u8>::unwrap");
        let s = crate::mirsem::sem_adt_payload_extract_diverging_of_discriminant_switch(&f)
            .expect("Result::<i32,u8>::unwrap divergence-guarded extraction recognized");
        assert_eq!(s.extract_variant, 0, "Ok is variant 0 (the payload arm)");
        assert_eq!(s.extract_field_idx, 0);
        assert_eq!(
            check_payload_extract_diverging_refinement(&s),
            RefinementVerdict::ProvenModulo3,
            "Result unwrap's SOME-side (Ok) payload ι-reduction must certify modulo 3"
        );
    }

    /// The `Option::<i32>::expect` SOME obligation certifies modulo 3 (the `msg`
    /// parameter and the `expect_failed` panic are irrelevant to the payload witness).
    #[test]
    fn payload_extract_diverging_option_i32_expect_certifies_modulo_3() {
        let f = load_payload_dump("std::option::Option::<i32>::expect");
        let s = crate::mirsem::sem_adt_payload_extract_diverging_of_discriminant_switch(&f)
            .expect("Option::<i32>::expect divergence-guarded extraction recognized");
        assert_eq!(
            check_payload_extract_diverging_refinement(&s),
            RefinementVerdict::ProvenModulo3,
            "expect's SOME-side payload ι-reduction must certify modulo 3"
        );
    }

    /// FORGERY PROBE (c) — some→CONSTANT: claiming the SOME obligation's RHS is a
    /// concrete Int constant instead of the extracted field. `Rec(Some x, d)` ι-reduces
    /// to the OPEN field bvar `x`; a closed literal is NOT def-eq to it ⇒ `KernelRejected`.
    /// Proves the witness genuinely READS THE PAYLOAD, not a fabricated constant.
    #[test]
    fn payload_extract_diverging_some_to_constant_is_kernel_rejected() {
        let f = load_payload_dump("std::option::Option::<i32>::unwrap");
        let s = crate::mirsem::sem_adt_payload_extract_diverging_of_discriminant_switch(&f)
            .expect("recognized");
        let zero = crate::trustir_anchor::int_lit(0);
        assert!(
            matches!(
                check_payload_extract_diverging_refinement_claimed(&s, Some(&zero), false),
                RefinementVerdict::KernelRejected(_)
            ),
            "claiming SOME returns a constant (not the extracted field) must be KernelRejected"
        );
    }

    /// FORGERY PROBE (swapped minor): building the some-minor as `λx. d` (returns the
    /// default, ignores the field) while keeping the honest RHS `x` — the reduct is
    /// `d != x` ⇒ `KernelRejected`. Proves the value-faithfulness of the field read.
    #[test]
    fn payload_extract_diverging_swapped_minor_is_kernel_rejected() {
        let f = load_payload_dump("std::option::Option::<i32>::unwrap");
        let s = crate::mirsem::sem_adt_payload_extract_diverging_of_discriminant_switch(&f)
            .expect("recognized");
        assert!(
            matches!(
                check_payload_extract_diverging_refinement_claimed(&s, None, true),
                RefinementVerdict::KernelRejected(_)
            ),
            "a swapped some-minor (returns the default, not the field) must be KernelRejected"
        );
    }
}

// ---------------------------------------------------------------------------
// Trust: W6 CLOSURE-COMPOSITION kernel-witness tests (increment 1, 2026-07-18).
// ---------------------------------------------------------------------------
#[cfg(test)]
mod w6_map_compose_kernel_tests {
    use super::*;
    use crate::mirsem::{ComposeReturn, SemAdtFilterCompose, SemAdtMapCompose, SemOperand};
    use crate::trustir_anchor::IrOperand;
    use clean_kernel::Name;
    use trust_types::{Ty, VariantDef};

    fn option_i32() -> Ty {
        Ty::adt_enum_with_disc_safety(
            "std::option::Option",
            vec![
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), Ty::Int { width: 32, signed: true })],
                },
            ],
            true,
        )
    }

    fn shape() -> SemAdtMapCompose {
        SemAdtMapCompose {
            kind: ComposeReturn::MapWrap,
            self_ty: option_i32(),
            call_variant: 1,
            none_variant: 0,
            callee: "map_add1::{closure#0}".into(),
            callee_id: 0,
            env_operand: SemOperand::Var(1),
        }
    }

    /// The `and_then` shape over the SAME `Option<i32>` carrier — the flat-return
    /// (`AndThenFlat`) variant: the some-minor is the bare opaque carrier return.
    fn and_then_shape() -> SemAdtMapCompose {
        SemAdtMapCompose { kind: ComposeReturn::AndThenFlat, ..shape() }
    }

    /// The registered constructor consts (`Trust.Adt.<Option>.None` / `.Some`) —
    /// pure functions of the reflected carrier, so they name the SAME consts the
    /// witness's fresh env registers.
    fn ctor_consts() -> (Expr, Expr) {
        let carrier = crate::reflect::reflect_enum(&option_i32()).expect("reflect");
        let none = Expr::const_(Name::from_string(&carrier.constructors[0].name), LevelVec::new());
        let some = Expr::const_(Name::from_string(&carrier.constructors[1].name), LevelVec::new());
        (none, some)
    }

    #[test]
    fn map_compose_kernel_proves_modulo3() {
        let arg = IrOperand::Var(1);
        assert!(
            matches!(check_map_compose_refinement(&shape(), &arg), RefinementVerdict::ProvenModulo3),
            "the two recursor ι-obligations (Some(call_result) + None construction) must prove modulo 3"
        );
    }

    #[test]
    fn swapped_minors_kernel_rejects() {
        let arg = IrOperand::Var(1);
        assert!(
            matches!(
                check_map_compose_refinement_claimed(&shape(), &arg, [None, None], true),
                RefinementVerdict::KernelRejected(_)
            ),
            "swapping the minor bodies must KernelReject both obligations"
        );
    }

    #[test]
    fn some_claim_wrong_variant_kernel_rejects() {
        let arg = IrOperand::Var(1);
        let (none, _some) = ctor_consts();
        // SOME obligation RHS claimed C_none (wrong variant) — not def-eq to the
        // honest C_some(callResult …) reduct.
        assert!(
            matches!(
                check_map_compose_refinement_claimed(&shape(), &arg, [Some(&none), None], false),
                RefinementVerdict::KernelRejected(_)
            ),
            "SOME→C_none wrong-variant claim must KernelReject"
        );
    }

    #[test]
    fn none_claim_wrong_variant_kernel_rejects() {
        let arg = IrOperand::Var(1);
        let (_none, some) = ctor_consts();
        // NONE obligation RHS claimed C_some(0) (wrong variant).
        let some_of_0 = Expr::app(some, crate::trustir_anchor::int_lit(0));
        assert!(
            matches!(
                check_map_compose_refinement_claimed(&shape(), &arg, [None, Some(&some_of_0)], false),
                RefinementVerdict::KernelRejected(_)
            ),
            "NONE→C_some claim must KernelReject"
        );
    }

    #[test]
    fn some_claim_concrete_value_kernel_rejects() {
        let arg = IrOperand::Var(1);
        let (_none, some) = ctor_consts();
        // SOME obligation RHS claimed C_some(42) — a CONCRETE value, never asserted
        // (the honest RHS wraps the opaque `callResult`, not a literal).
        let some_of_42 = Expr::app(some, crate::trustir_anchor::int_lit(42));
        assert!(
            matches!(
                check_map_compose_refinement_claimed(&shape(), &arg, [Some(&some_of_42), None], false),
                RefinementVerdict::KernelRejected(_)
            ),
            "a concrete-value SOME claim must KernelReject (no concrete ret is ever asserted)"
        );
    }

    #[test]
    fn nullary_call_variant_declines() {
        // The CALL variant must carry EXACTLY one Int field; a nullary "Some" is
        // outside the sound fragment (no payload to carry the call result).
        let bad = Ty::adt_enum_with_disc_safety(
            "std::option::Option",
            vec![
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "Some".into(), discriminant: 1, fields: vec![] },
            ],
            true,
        );
        let mut s = shape();
        s.self_ty = bad;
        let arg = IrOperand::Var(1);
        assert!(matches!(
            check_map_compose_refinement(&s, &arg),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// ENV HYGIENE: the composed witness env (call theory + registered Option
    /// carrier) declares ZERO `Trust.MirSem.*` constants, and DOES declare the
    /// trust-ir Call theory + the Option carrier.
    #[test]
    fn composed_env_asserts_zero_mirsem_names() {
        let arg = IrOperand::Var(1);
        let (env, _obl) = build_map_compose(&shape(), &arg, [None, None], false)
            .expect("the witness env must build");
        for n in [
            "Trust.MirSem.Call",
            "Trust.MirSem.call_result",
            "Trust.MirSem.callRefinesContract",
            "Trust.MirSem.Operand",
            "Trust.MirSem.idx_elem",
        ] {
            assert!(
                env.get_const(&Name::from_string(n)).is_none(),
                "the composed witness env must NOT declare {n}"
            );
        }
        // The trust-ir Call theory IS present.
        assert!(env.get_const(&Name::from_string(crate::trustir_call::TRUSTIR_CALL_RESULT)).is_some());
        // The Option carrier inductive IS registered.
        let carrier = crate::reflect::reflect_enum(&option_i32()).expect("reflect");
        assert!(env.get_inductive(&Name::from_string(&carrier.name)).is_some(), "Option carrier registered");
    }

    // ----- W6 increment 2: `and_then` flat-return witness -----

    /// The `and_then` flat-return witness: the some-minor is the bare opaque
    /// carrier return `ret : T` (the call result IS the return), the none-minor
    /// `C_none`. Both recursor ι-obligations close modulo 3 by `Eq.refl`.
    #[test]
    fn and_then_flat_kernel_proves_modulo3() {
        let arg = IrOperand::Var(1);
        assert!(
            matches!(
                check_map_compose_refinement(&and_then_shape(), &arg),
                RefinementVerdict::ProvenModulo3
            ),
            "the and_then flat some/none ι-obligations must prove modulo 3"
        );
    }

    /// FAIL-CLOSED: swapping the minor bodies (none↦the opaque return, call↦C_none)
    /// makes the honest `Eq.refl` reduct not def-eq to the statement — KernelReject.
    #[test]
    fn and_then_flat_swapped_minors_kernel_rejects() {
        let arg = IrOperand::Var(1);
        assert!(
            matches!(
                check_map_compose_refinement_claimed(&and_then_shape(), &arg, [None, None], true),
                RefinementVerdict::KernelRejected(_)
            ),
            "swapping the and_then minors must KernelReject"
        );
    }

    /// FAIL-CLOSED: claiming the SOME arm returns the CONCRETE `C_some(42)` (rather
    /// than the opaque `ret : T`) is not def-eq to the honest reduct — KernelReject.
    /// Confirms the flat witness makes NO value claim about the closure's return.
    #[test]
    fn and_then_flat_concrete_claim_kernel_rejects() {
        let arg = IrOperand::Var(1);
        let (_none, some) = ctor_consts();
        let some_of_42 = Expr::app(some, crate::trustir_anchor::int_lit(42));
        assert!(
            matches!(
                check_map_compose_refinement_claimed(
                    &and_then_shape(),
                    &arg,
                    [Some(&some_of_42), None],
                    false
                ),
                RefinementVerdict::KernelRejected(_)
            ),
            "a concrete-value SOME claim must KernelReject on the flat lane too"
        );
    }

    /// FAIL-CLOSED: claiming the NONE arm returns `C_some(0)` (wrong variant) is
    /// rejected — the none-minor is `C_none` regardless of the flat return.
    #[test]
    fn and_then_flat_none_wrong_variant_kernel_rejects() {
        let arg = IrOperand::Var(1);
        let (_none, some) = ctor_consts();
        let some_of_0 = Expr::app(some, crate::trustir_anchor::int_lit(0));
        assert!(
            matches!(
                check_map_compose_refinement_claimed(
                    &and_then_shape(),
                    &arg,
                    [None, Some(&some_of_0)],
                    false
                ),
                RefinementVerdict::KernelRejected(_)
            ),
            "NONE→C_some claim must KernelReject on the flat lane"
        );
    }

    // ----- W6 increment 2: `filter` predicate-select witness -----

    fn filter_shape() -> SemAdtFilterCompose {
        SemAdtFilterCompose {
            self_ty: option_i32(),
            some_variant: 1,
            none_variant: 0,
            callee: "filter_pos::{closure#0}".into(),
            callee_id: 0,
            env_operand: SemOperand::Var(1),
        }
    }

    /// The filter predicate-select witness: on Some(x), the return is `Bool.rec
    /// (λ_.T) C_none (C_some x) b` (b an opaque ∀-bound Bool); on None, C_none. Both
    /// ι-obligations close modulo 3 by `Eq.refl`.
    #[test]
    fn filter_kernel_proves_modulo3() {
        assert!(
            matches!(
                check_filter_compose_refinement(&filter_shape()),
                RefinementVerdict::ProvenModulo3
            ),
            "the filter predicate-select some/none ι-obligations must prove modulo 3"
        );
    }

    /// FAIL-CLOSED: flipping the some-minor's `Bool.rec` orientation (true↦None,
    /// false↦Some) is not def-eq to the honest select — KernelReject.
    #[test]
    fn filter_swapped_orientation_kernel_rejects() {
        assert!(
            matches!(
                check_filter_compose_refinement_claimed(&filter_shape(), [None, None], true),
                RefinementVerdict::KernelRejected(_)
            ),
            "a flipped predicate orientation must KernelReject"
        );
    }

    /// FAIL-CLOSED: claiming the SOME arm UNCONDITIONALLY returns `C_some(x)` (i.e.
    /// `C_some` of the field binder, ignoring the predicate) is not def-eq to the
    /// predicate-select honest reduct — KernelReject. Confirms the witness genuinely
    /// conditions on the predicate `b`.
    #[test]
    fn filter_unconditional_some_claim_kernel_rejects() {
        // RHS claim: `C_some x` where x is the SOME statement's payload binder (bvar 0
        // under `Π b Π x`). Not def-eq to `Bool.rec (λ_.T) C_none (C_some x) b`.
        let (_none, some) = ctor_consts();
        let some_of_x = Expr::app(some, Expr::bvar(0));
        assert!(
            matches!(
                check_filter_compose_refinement_claimed(
                    &filter_shape(),
                    [Some(&some_of_x), None],
                    false
                ),
                RefinementVerdict::KernelRejected(_)
            ),
            "an unconditional Some(x) claim must KernelReject (the return conditions on b)"
        );
    }

    /// FAIL-CLOSED: a nullary "Some" carrier declines (no payload to reconstruct).
    #[test]
    fn filter_nullary_some_variant_declines() {
        let bad = Ty::adt_enum_with_disc_safety(
            "std::option::Option",
            vec![
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "Some".into(), discriminant: 1, fields: vec![] },
            ],
            true,
        );
        let mut s = filter_shape();
        s.self_ty = bad;
        assert!(matches!(
            check_filter_compose_refinement(&s),
            RefinementVerdict::KernelRejected(_)
        ));
    }
}

// ---------------------------------------------------------------------------
// Trust: RECORD-WITNESS inc-2 (ok/err DowncastField, 2026-07-22) — the KERNEL
// forgery-probe suite. The DowncastField payload denotes through the UNCHANGED 2-arm
// `Bool.rec`/`congrArg` recipe at a VARIANT-DISJOINT flattened `idxElem` key. The
// MANDATORY DOWNCAST-KEY-DISJOINTNESS probe (a wrong-variant key claim) is the test that
// proves the disjointness is load-bearing: it is VACUOUS under within-variant keys.
// A separate module (kept off the increment-1 record suites).
// ---------------------------------------------------------------------------
#[cfg(test)]
mod record_inc2_kernel_tests {
    use super::*;
    use crate::mirsem::{SemAdtArm, SemAdtPayload, SemAdtReturn, SemCmpOp, SemCond, SemCondTree, SemOperand};

    /// The `Result::ok`-class 2-arm ADT-return whose `Some` arm carries a DowncastField at
    /// `flat_key`: guard `Discriminant(self = Var 0) == 0` (Ok); then = `Some(idxElem(e 0,
    /// flat_key))`; else = `None`. The honest key is 1 (the flattened `__v0_0` slot).
    fn ok_downcast_return(flat_key: u64) -> SemAdtReturn {
        SemAdtReturn {
            cond: SemCondTree::Leaf(SemCond {
                op: SemCmpOp::Eq,
                a: SemOperand::Discriminant(Box::new(SemOperand::Var(0))),
                b: SemOperand::Const(0),
            }),
            then_arm: SemAdtArm {
                variant: 1, // Some
                payload: Some(SemAdtPayload::DowncastField {
                    base_param: 0,
                    flat_key,
                    downcast_variant: 0,
                }),
            },
            else_arm: SemAdtArm { variant: 0, payload: None }, // None
            enum_name: "core::option::Option".to_string(),
        }
    }

    /// MANDATORY DOWNCAST-KEY-DISJOINTNESS probe. The honest ok() DowncastField return
    /// certifies (non-vacuity); a claim at the WRONG variant's flattened key (2 = `__v1_0`,
    /// the Err-payload slot) must be `KernelRejected` (non-tautology). Under WITHIN-VARIANT
    /// keys `⟦(_1 as v#0).0⟧` and `⟦(_1 as v#1).0⟧` would BOTH be `idxElem(e 0, 0)` —
    /// def-eq — and this forgery would kernel-ACCEPT; this probe is VACUOUS there, so it is
    /// the test that proves the flattened-key disjointness is load-bearing.
    #[test]
    fn downcast_wrong_variant_key_claim_is_kernel_rejected() {
        let honest = ok_downcast_return(1);
        assert_eq!(
            check_adt_return_refinement(&honest),
            RefinementVerdict::ProvenModulo3,
            "the honest ok() DowncastField return must certify (non-vacuity)"
        );
        let forged = ok_downcast_return(2); // Some(idxElem(e 0, 2)) — the wrong-variant key.
        let wrong_rhs = then_value_for_test(&forged).expect("forged then-value builds");
        assert!(
            matches!(
                check_adt_return_refinement_claimed(&honest, Some(&wrong_rhs)),
                RefinementVerdict::KernelRejected(_)
            ),
            "a wrong-variant flattened-key `Some` claim must be kernel-REJECTED (non-tautology)"
        );
    }

    /// A wrong-VARIANT-TAG claim (the `None` else-arm value) against the TRUE guard also
    /// rejects — the DowncastField `Some` arm is DISTINCT from `None` by inductive
    /// noConfusion, exactly as the scalar-payload `adt_return` probes assert.
    #[test]
    fn downcast_wrong_variant_tag_claim_is_kernel_rejected() {
        let honest = ok_downcast_return(1);
        let wrong_rhs = else_value_for_test(&honest).expect("else-arm value builds");
        assert!(matches!(
            check_adt_return_refinement_claimed(&honest, Some(&wrong_rhs)),
            RefinementVerdict::KernelRejected(_)
        ));
    }
}
