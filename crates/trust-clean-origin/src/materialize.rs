// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **THE BODY TEMPLATE — §6f's EMITTER HALF** (landing 4).
//!
//! Landings 1, 2 and 3 each recorded the same deferral, in the same words:
//! *"the emitter's six builders were NOT collapsed"*, because *"collapsing the
//! builders is the emitter half of §6f and it cannot be validated on the fast
//! lane; a landing that cannot run x.py must not restructure the code that
//! emits binaries."* (Six was the count when landing 1 wrote it; landings 2 and
//! 3 each added one, and `build_structural_rec_body` plus
//! `build_nat_zero_test_rec_body` make NINE deleted here.) That deferral is what this module retires — not by
//! restructuring the emitter on faith, but by moving the DECISION out of the
//! compiler and onto the fast lane, where it is byte-identity-controlled, and
//! leaving `rustc_mir_transform` with a mechanical interpreter that has no
//! shape knowledge at all.
//!
//! # The split, and why it is the honest one
//!
//! ```text
//!   SelectionRow + CleanOriginPlan
//!         │
//!         │  body_template()        ← HERE. TyCtxt-free. Fast-lane tested.
//!         ▼                            Decides every block, local, operand,
//!   BodyTemplate                       Copy-vs-Move and unwind edge.
//!         │
//!         │  materialize()          ← `clean_origin_mir.rs`. Needs TyCtxt for
//!         ▼                            three things ONLY: carrier→rustc types,
//!   mir::Body                          `DefId` resolution, and `Body::new`.
//! ```
//!
//! Everything a wrong binary could hide in — which block, which local, which
//! operand, `Copy` versus `Move`, the `SwitchInt` polarity, the unwind edge —
//! is decided in this file, which `cargo test -p trust-clean-origin` runs in
//! two seconds. What is left on the compiler side is a translation with one arm
//! per template variant and no branch on any shape.
//!
//! # BYTE-IDENTICAL ACCEPTANCE, and what it does and does not cover
//!
//! The acceptance for this landing is that for every shape the nine
//! hand-written builders emitted, the template is the SAME body — not an
//! equivalent one.
//! `tests/control_11_materializer_byte_identity.rs` executes that: it renders
//! each template into the `trust_types` MIR vocabulary the extractor produces
//! and compares against the bodies `control_5`..`control_10` measured off the
//! shipped builders, block for block and local for local — including the two
//! dead arm temps R1/R2 leave declared (`_4`/`_9` for `tozero`, `_4`/`_12` for
//! `countdownSum`), `Copy` versus `Move` in every position, and the per-row
//! unwind edge. It then puts the rendered body through the REAL `admit_lowering`
//! — side B's independent reader, side B's producer, and the kernel gate — so
//! a template that drifted is refused on the fast lane rather than in a binary.
//!
//! What that does NOT cover, stated rather than implied: the ~175 lines of
//! [`materialize`](../../../compiler/rustc_mir_transform/src/clean_origin_mir.rs)
//! that turn a template into `mir::Body` are x.py-only and ship unverified by
//! any build, exactly as every `compiler/` edit in landings 1–3 did. The
//! residual risk is a transcription error in a translation with no shape
//! knowledge, and the gate in `build_gated_body` is fatal on it.
//!
//! # The table drives the shape; the plan drives the operands
//!
//! [`body_template`] matches [`MirShape`] EXHAUSTIVELY with no `_ =>` arm, for
//! the reason `table.rs` gives for `MirShape` not being `#[non_exhaustive]`: a
//! realization nobody wrote a skeleton for must be a COMPILE ERROR, never a
//! fall-through into the wrong body. Landing 1 put that error an hour into a
//! bootstrap; it is now two seconds into `cargo check -p trust-clean-origin`.
//! The emitter keeps its own exhaustiveness at the layer it still owns —
//! [`TemplateTerminator`], [`TemplateRvalue`], [`TemplateOperand`],
//! [`TemplateTy`] and [`TemplateCallee`] are equally closed, and a new
//! *realization primitive* is a compile error in `clean_origin_mir.rs`.
//!
//! Inside each arm the row supplies the SKELETON and the plan supplies the
//! OPERANDS. That is why three ladder rungs that were three builders
//! (`Select`, `SelectLiteral`, `SelectOperands`) are one call to
//! [`diamond_body`]: they were never three shapes, only three operand
//! vocabularies over one diamond — the same finding landing 3 recorded on the
//! reflection side, now instantiated on the emission side.
//!
//! # THE UNWIND EDGE IS NOW TAKEN FROM THE ROW
//!
//! H-G's hazard is *"an emitted unwind edge nobody declared"*. Until this
//! landing the edge was hand-written per builder and the row's
//! [`UnwindDiscipline`](crate::table::UnwindDiscipline) merely *described* it —
//! two places one fact could live. Here the emitted edge is DERIVED from
//! `row.unwind`, so `table_controls::h_g_the_unwind_discipline_matches_the_
//! realization` is no longer a description of the emitter but a constraint on
//! it. A row that declares `NoCall` and whose realization emits a call is
//! [`TemplateRefusal::UndeclaredUnwindEdge`] — fail-closed, and unreachable
//! today precisely because H-G passes.
//!
//! # WHAT DID NOT COLLAPSE, and why
//!
//! Nothing in the emission did. Three things stayed on the compiler side
//! because they are genuinely `TyCtxt` facts and not shape decisions:
//!
//! * `carrier_to_rustc_ty` — I4's carrier decision needs `tcx.types.*` and the
//!   `Nat` `DefId` of record. [`TemplateTy`] names the carrier POSITION
//!   (result, parameter `i`, `bool`, `&result`) and the emitter resolves it.
//! * `resolve_core_wrapping_method` / `resolve_bignum_method` — a `DefId` is
//!   resolved from `TyCtxt` facts and AUTHENTICATED there. The template carries
//!   the ONE authenticated identity ([`PrimitiveCallee`]) and nothing else; the
//!   standing rule that side A must not mirror side B's path table is
//!   untouched, because a template still hands over an identity, never a path.
//! * `Body::new` and the phase/table discipline — one construction, once.
//!
//! And one *behavioural* boundary was deliberately NOT moved: the width
//! extraction. `build_select_body` never extracted a machine width (a bare
//! parameter select has no numeral), while its two siblings did. Collapsing all
//! three into one arm that always extracts would add a fatal on a path that
//! does not exist today. The [`MirShape::ComparisonBranch`] arm therefore
//! extracts the width for `SelectLiteral` and `SelectOperands` and NOT for
//! `Select` — the same fatals, on the same inputs, with the same shape labels.

use trust_types::admissible_body::{
    ArithBinOp, ArithExpr, ArithOperand, BeqOperand, PrimitiveCallee, RawBinOpKind, RecBodyExpr,
    SelectCmp,
};

use crate::emit::{CleanOriginPlan, CleanOriginShape, WfLowering};
use crate::table::{CalleeSelector, MirShape, SelectionRow, UnwindDiscipline};

/// The carrier POSITION a template local is typed at.
///
/// Deliberately a position and not a type: the carrier→rustc mapping exists
/// exactly once, in `clean_origin_mir::carrier_to_rustc_ty`, and
/// `check_signature_agrees` guards the one duplication I5 could not avoid. A
/// template that carried a `trust_types::Ty` would be a THIRD spelling of the
/// same decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateTy {
    /// The plan's RESULT carrier — `_0`, every arithmetic temporary, the select
    /// temporary, and (in the recursion lane) the parameter and every arm temp.
    Result,
    /// The plan's `index`-th PARAMETER carrier.
    Param {
        /// 0-based source parameter position.
        index: usize,
    },
    /// `bool` — the comparison's result, and the zero test's.
    Bool,
    /// `&<result carrier>` — the shared borrow the bignum runtime's
    /// by-reference methods take.
    ResultRef,
}

/// One local declaration.
///
/// `immutable` reproduces `LocalDecl::immutable()`, which the shipped builders
/// applied to PARAMETERS ONLY. It is carried explicitly because the extractor
/// cannot see it, so a control comparing extracted bodies alone would be blind
/// to a change here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TemplateLocal {
    /// The carrier position this local is typed at.
    pub ty: TemplateTy,
    /// Whether `LocalDecl::immutable()` is applied.
    pub immutable: bool,
}

/// An operand, in the four spellings the emitted fragment uses.
///
/// **`Copy` versus `Move` is a decision, not a detail.** Every operand the
/// arithmetic and select lanes build is `Copy`, because one parameter may
/// occupy two positions (`a + a`, `if a < b then a else a`); the projection's
/// single use and the recursion lane's reference/temporary consumption are
/// `Move`. Both spellings reach the recognizer, and the recognized shapes the
/// probes hand-build carry exactly these.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateOperand {
    /// `Operand::Copy(Place::from(Local(index)))`.
    Copy(usize),
    /// `Operand::Move(Place::from(Local(index)))`.
    Move(usize),
    /// An inline evaluated scalar at the RESULT carrier's rustc type and the
    /// carrier's encoded width. Nothing needs evaluation, so `required_consts`
    /// stays honestly empty and nothing can promote.
    ResultScalar {
        /// The value, already range-checked on the sealed plan.
        value: u128,
        /// The result carrier's encoded width in bits.
        width: u32,
    },
    /// An inline evaluated scalar at `u64` — the bignum runtime's `from_u64`
    /// argument, which is NOT at the result carrier (the result is `Nat`).
    U64Scalar(u64),
    /// **§6f LANDING 6** — an inline evaluated scalar at `bool`
    /// (`tcx.types.bool`, `Scalar::from_bool`), the right-hand side of the
    /// `== Bool.true` lift in [`MirShape::BoolDecisionBranch`].
    ///
    /// It is a NEW REALIZATION PRIMITIVE, and landing 4 made that a compile
    /// error in `rustc_mir_transform::clean_origin_mir::materialize`'s
    /// wildcard-free match ON PURPOSE — landing 5 measured the demand for it
    /// and declined to add it, because a lane that cannot run `x.py` must not
    /// break the compiler's closed match mid-type-check. This landing pays that
    /// cost with the constraint lifted.
    ///
    /// Neither existing scalar could spell it and the reason is typing, not
    /// taste: [`Self::ResultScalar`] is at the result carrier (`u{w}`) and
    /// [`Self::U64Scalar`] at `u64`, and comparing a `bool` local against
    /// either is ill-typed MIR. Like both of them it is an INLINE evaluated
    /// scalar, so `required_consts` stays honestly empty and nothing can
    /// promote.
    BoolScalar(bool),
}

/// The right-hand side of a template assignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateRvalue {
    /// `Rvalue::Use(operand, WithRetag::Yes)`.
    ///
    /// `WithRetag::Yes` is what `rustc_mir_build` emits for every ordinary
    /// `Rvalue::Use`, so a Clean-origin body is spelled the way a hand-written
    /// `fn fst(x, y) -> u64 { x }` is spelled. That is not cosmetic: side B is
    /// produced by reading this MIR back, and the fewer respects in which a
    /// Clean-origin body differs from an ordinary one, the fewer places a
    /// reader can behave differently on it than on the bodies it was written
    /// for. It is uniform across every shipped shape, which is why it is not a
    /// field.
    Use(TemplateOperand),
    /// `Rvalue::BinaryOp(<cmp>, (left, right))` — the select diamond's test.
    Compare {
        /// The comparison.
        cmp: SelectCmp,
        /// Left operand.
        left: TemplateOperand,
        /// Right operand.
        right: TemplateOperand,
    },
    /// **§6f LANDING 7** — `Rvalue::BinaryOp(<op>, (left, right))` at the
    /// RESULT carrier: `&`, `|`, `/`, `%`.
    ///
    /// # It is a NEW REALIZATION PRIMITIVE, and landing 4 made that a compile
    /// error on purpose
    ///
    /// `rustc_mir_transform::clean_origin_mir::materialize` matches this enum
    /// with no wildcard, so this variant does not build until the compiler
    /// side is written — the same cost `TemplateOperand::BoolScalar` carried
    /// in landing 6, paid the same way and reported the same way.
    ///
    /// # Why [`Self::Compare`] could not spell it
    ///
    /// Typing, not taste. `Compare` is parameterised by `SelectCmp`, whose
    /// three values are all RELATIONS: the rvalue it builds is `bool`-typed
    /// and its destination is a `bool` local. `_0` here is at the result
    /// carrier `u{w}`, and assigning a `bool` rvalue to it is ill-typed MIR.
    /// The two are the same `Rvalue::BinaryOp` constructor at the MIR level
    /// and two different decisions at this one, which is exactly the
    /// distinction this vocabulary exists to keep visible.
    ///
    /// # NO overflow check, NO div-by-zero assert
    ///
    /// `BitAnd`/`BitOr` cannot fail. `Div`/`Rem` can, and the invariant that
    /// they do not is upstream of this file: `recognise_raw_binop_expr`
    /// refuses to plan a `Div`/`Rem` whose right operand is not a strictly
    /// positive numeral, and the FROZEN producer independently refuses to
    /// reflect one. See [`crate::table::MirShape::RawBinOp`] for the full
    /// accounting of why there is no `Assert` terminator to add.
    RawBin {
        /// The operator.
        op: RawBinOpKind,
        /// Left operand.
        left: TemplateOperand,
        /// Right operand.
        right: TemplateOperand,
    },
    /// `Rvalue::Ref(re_erased, BorrowKind::Shared, Place::from(Local(index)))`.
    SharedRef(usize),
}

/// One statement: an assignment to a bare local.
///
/// There is no projection in the emitted fragment — every place is a bare
/// local — and keeping that unrepresentable is deliberate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TemplateStatement {
    /// The local written.
    pub place: usize,
    /// What is written into it.
    pub rvalue: TemplateRvalue,
}

/// Who a template call calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateCallee {
    /// The ONE authenticated identity. The emitter resolves a `DefId` from it
    /// (by METHOD NAME, then authentication from `TyCtxt` facts) and side B
    /// classifies the path the extractor independently re-renders through the
    /// same identity — which closes the "emit says sub, side B says add" hole
    /// without either side asserting what the other will see.
    Primitive(PrimitiveCallee),
    /// The def being built — `Operand::function_handle` for its own `DefId`,
    /// no lookup. Not a primitive, so it has no authenticated identity: the
    /// recognizer matches it against `func.def_path` and the kernel re-decides
    /// the argument.
    SelfDef,
}

/// The unwind edge an emitted call carries.
///
/// Two variants, not three: an emitted call always has an edge. The row's
/// three-valued [`UnwindDiscipline`] is the DECLARATION, and
/// [`TemplateRefusal::UndeclaredUnwindEdge`] is what happens when a row
/// declares `NoCall` and its realization emits a call anyway.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateUnwind {
    /// `UnwindAction::Unreachable` — the callee cannot unwind (the core
    /// wrapping primitives).
    Unreachable,
    /// `UnwindAction::Continue` — the callee can abort (the bignum runtime's
    /// allocation, and the self-call's stack).
    Continue,
}

impl TemplateUnwind {
    /// The row-level discipline this edge realizes.
    #[must_use]
    pub fn discipline(self) -> UnwindDiscipline {
        match self {
            Self::Unreachable => UnwindDiscipline::Unreachable,
            Self::Continue => UnwindDiscipline::Continue,
        }
    }
}

/// A block terminator, in the four spellings the emitted fragment uses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TemplateTerminator {
    /// `TerminatorKind::Return`.
    Return,
    /// `TerminatorKind::Goto { target }`.
    Goto(usize),
    /// `TerminatorKind::SwitchInt` over exactly two targets, built as
    /// `SwitchTargets::static_if(0, zero, otherwise)`.
    ///
    /// **THE POLARITY TRAP, named where the data is.**
    /// `SwitchTargets::static_if(v, v_target, otherwise)` puts `v`'s target
    /// FIRST and `otherwise` LAST. Getting the argument order wrong silently
    /// emits max where the island wrote min, or the succ arm where the island
    /// wrote the base case. Naming the two targets `zero` and `otherwise`
    /// rather than `then`/`else` is the point: the diamond's `zero` target is
    /// the ELSE arm (comparison false) and the zero test's `zero` target is the
    /// SUCC arm (`is_zero` false). The gate, not this comment, is what makes a
    /// swapped emission unshippable, and
    /// `-Ztrust-clean-origin-mutate-emitter` exercises it end-to-end.
    SwitchIntZero {
        /// The discriminant read.
        discr: TemplateOperand,
        /// The block reached when the discriminant is `0`.
        zero: usize,
        /// The block reached otherwise.
        otherwise: usize,
    },
    /// `TerminatorKind::Call` with `CallSource::Misc`, no generic arguments,
    /// and a bare-local destination.
    Call {
        /// Who is called.
        callee: TemplateCallee,
        /// The arguments, in order.
        args: Vec<TemplateOperand>,
        /// The local written.
        dest: usize,
        /// The block returned to.
        target: usize,
        /// The unwind edge, derived from the selected row.
        unwind: TemplateUnwind,
    },
}

/// One basic block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TemplateBlock {
    /// Statements, in order.
    pub stmts: Vec<TemplateStatement>,
    /// The terminator. Never absent: a block with no terminator is a hole a
    /// patching pass has to close, which is where the R1 emitter's
    /// `RET_SENTINEL` hazard lived.
    pub terminator: TemplateTerminator,
}

/// **The complete description of one Clean-origin body**, in block order.
///
/// Block `k` of [`Self::blocks`] is `bb{k}`; local `k` of [`Self::locals`] is
/// `_{k}`. Both orders are load-bearing and both are compared byte for byte by
/// `tests/control_11_materializer_byte_identity.rs` — including locals that are
/// DECLARED AND DEAD, which the recursion lane leaves behind whenever
/// `lower_arm` re-points an arm's last call at `_0` after its temporary was
/// already allocated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BodyTemplate {
    /// Local declarations, `_0` first.
    pub locals: Vec<TemplateLocal>,
    /// Basic blocks, `bb0` first.
    pub blocks: Vec<TemplateBlock>,
    /// The number of parameters — `_1 ..= _{arg_count}`.
    pub arg_count: usize,
}

impl BodyTemplate {
    /// Every call in this body, as `(block index, callee, unwind)`.
    ///
    /// Exists for the emitter-side half of H-G: the control asserts that every
    /// emitted edge is the one the SELECTED ROW declares, which is the property
    /// that turns `table_controls::h_g_…` from a description of the emitter
    /// into a constraint on it.
    #[must_use]
    pub fn calls(&self) -> Vec<(usize, TemplateCallee, TemplateUnwind)> {
        self.blocks
            .iter()
            .enumerate()
            .filter_map(|(index, block)| match &block.terminator {
                TemplateTerminator::Call { callee, unwind, .. } => Some((index, *callee, *unwind)),
                _ => None,
            })
            .collect()
    }
}

/// Why no template could be built. Every variant is a COMPILER DEFECT: each
/// names an invariant `plan_clean_origin_body` is required to have sealed, or a
/// disagreement between the table and this file. None of them is reachable from
/// anything a user writes, and none of them has a degraded mode — the emitter
/// turns each into a fatal diagnostic and emits nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TemplateRefusal {
    /// The selected row's declared MIR realization is not the one this file
    /// builds for the planned shape. Table/emitter drift.
    RealizationDisagrees,
    /// The plan's result carrier is not an unsigned machine width, for a shape
    /// whose numerals need one.
    NonMachineResultCarrier {
        /// The shape label, as the shipped fatal spells it (`ConstantUint`,
        /// `WrappingBinOp`, `Composed`, `SelectLiteral`, `SelectOperands`).
        shape: &'static str,
        /// The carrier that was found instead.
        carrier: trust_types::Ty,
    },
    /// A `Composed` plan flattened to fewer than two call steps, or its root
    /// was not the last step.
    DegenerateComposedTree {
        /// How many steps it flattened to.
        steps: usize,
    },
    /// A recursive plan reached the emitter outside the single-parameter /
    /// predecessor class.
    RecursionOutsideFragment,
    /// **§6f LANDING 7** — a `Div`/`Rem` plan reached the emitter with a right
    /// operand that is not a strictly positive numeral.
    ///
    /// The ONLY refusal in this file whose subject is a SOUNDNESS invariant
    /// rather than a structural one, and it is stated as its own variant for
    /// that reason: every other variant means "the emitter cannot build this",
    /// and this one means "building this would emit a body that PANICS where
    /// the Clean declaration returns a value". Clean's `UInt{N}.div`/`.mod`
    /// are total (`x / 0 = 0`, `x % 0 = x`); Rust's `/`/`%` are not.
    ///
    /// Unreachable while `plan_clean_origin_body` holds its divisor rule, and
    /// fail-closed if it ever stops.
    PanickingDivisor,
    /// The selected row's realization emits a call but the row declares
    /// [`UnwindDiscipline::NoCall`]. Unreachable while
    /// `table_controls::h_g_the_unwind_discipline_matches_the_realization`
    /// passes; fail-closed if it ever stops.
    UndeclaredUnwindEdge,
}

impl TemplateRefusal {
    /// The diagnostic the emitter reports, verbatim.
    ///
    /// The text lives here rather than in `clean_origin_mir.rs` so it is on the
    /// fast lane with the decision that produces it —
    /// `control_11`'s `half_9` pins each string. `name` is the Clean
    /// declaration, `row` the selected row and `shape` the planned shape;
    /// every message ends in the report request, because every one of these is
    /// a compiler defect and nothing the user writes changes it.
    #[must_use]
    pub fn note(&self, name: &str, row: &SelectionRow, shape: &CleanOriginShape) -> String {
        match self {
            Self::RealizationDisagrees => format!(
                "internal: the plan for Clean declaration `{name}` selected the row `{}`, \
                 whose declared MIR realization ({:?}) is not the one this emitter builds \
                 for the planned shape ({shape:?}). The instruction-selection table and the \
                 emitter have drifted apart, and an emitted body cannot rest on that. \
                 NOTHING WAS EMITTED. This is a compiler defect — please report it.",
                row.name, row.mir,
            ),
            Self::NonMachineResultCarrier { shape: label, carrier } => format!(
                "internal: a {label} plan carries result carrier `{carrier:?}`, which \
                 `plan_clean_origin_body` is required to refuse. This is a compiler defect. \
                 Please report it."
            ),
            Self::DegenerateComposedTree { steps } => format!(
                "internal: a Composed plan flattened to {steps} call step(s), which \
                 `plan_clean_origin_body` is required to refuse. This is a compiler defect. \
                 Please report it."
            ),
            Self::RecursionOutsideFragment => "internal: a recursive Clean-origin plan \
                 reached the emitter outside the single-parameter/predecessor class \
                 `plan_clean_origin_body` is required to enforce. This is a compiler defect. \
                 Please report it."
                .to_owned(),
            Self::PanickingDivisor => format!(
                "internal: the plan for Clean declaration `{name}` selected the row `{}`, a \
                 division whose right operand is not a strictly positive numeral. Clean's \
                 `UInt{{N}}.div`/`.mod` are TOTAL (`x / 0 = 0`, `x % 0 = x`) while Rust's \
                 `/`/`%` PANIC at a zero divisor, so the body this plan asks for would \
                 compute a DIFFERENT function from the declaration it was minted for. \
                 `plan_clean_origin_body` is required to refuse it. NOTHING WAS EMITTED. \
                 This is a compiler defect — please report it.",
                row.name,
            ),
            Self::UndeclaredUnwindEdge => format!(
                "internal: the plan for Clean declaration `{name}` selected the row `{}`, \
                 whose realization ({:?}) emits a call while the row declares the unwind \
                 discipline `NoCall`. The emitted edge is taken FROM the row, so there is no \
                 edge to emit and NOTHING WAS EMITTED. This is a compiler defect — a row and \
                 its realization disagree, which \
                 `table_controls::h_g_the_unwind_discipline_matches_the_realization` exists \
                 to prevent. Please report it.",
                row.name, row.mir,
            ),
        }
    }
}

/// **THE ONE BODY BUILDER.** The selected row supplies the SKELETON; the plan
/// supplies the OPERANDS.
///
/// The outer match is over [`MirShape`] and is EXHAUSTIVE WITH NO WILDCARD, so
/// a realization nobody wrote a skeleton for is a compile error here — on the
/// fast lane, two seconds into the edit. The inner match re-checks that the
/// planned shape is one the row's realization actually describes; a
/// disagreement is [`TemplateRefusal::RealizationDisagrees`], which is the
/// emitter-side half of the shape-drift hazard a general emitter opens (the
/// fast lane's `h_c_shared_mir_realizations_are_declared_and_separated` proves
/// no two rows are realized indistinguishably, and this proves the row a plan
/// selected is the one that gets built).
///
/// # Errors
///
/// Every variant of [`TemplateRefusal`] is a compiler defect; see its docs.
pub fn body_template(
    row: &SelectionRow,
    plan: &CleanOriginPlan,
) -> Result<BodyTemplate, TemplateRefusal> {
    match row.mir {
        // ── the whole-body operand copy: `_0 = move _{i+1}; return` ─────────
        //
        // For `Projection` this is the d01 shape the kernel identifies by
        // definitional equality. For `InductiveProjection` the MIR is
        // intentionally IDENTICAL, and the recursive side A is admitted only by
        // a closed, axiom-free structural-induction proof which the
        // post-emission gate re-earns. Two rungs, one row, one template — §6f's
        // ladder-not-a-boundary claim in its smallest instance.
        MirShape::OperandCopy => match plan.shape() {
            CleanOriginShape::Projection { projected }
            | CleanOriginShape::InductiveProjection { projected } => {
                // The `+1` is the return place occupying local 0. `projected`
                // is the 0-based SOURCE parameter, already inverted out of its
                // de Bruijn index by `plan_clean_origin_body` — and an
                // inversion mistake here is exactly the one-construct
                // mistranslation `control_3`'s `half_2` injects and requires
                // the gate to catch.
                Ok(single_assignment_body(plan, TemplateOperand::Move(arg(*projected))))
            }
            _ => Err(TemplateRefusal::RealizationDisagrees),
        },

        // ── the whole-body inline scalar: `_0 = const v_u{w}; return` ───────
        //
        // ARITY-AGNOSTIC, and that is the soundness-relevant shape rather than
        // a simplification: `AdmissibleBody::ConstantUint` ERASES the arity on
        // the way back (`fragment_widening_probes::probe_e3`), so the arity is
        // bound on side B and NOWHERE else — `admit_lowering` compares
        // `extracted.body.arg_count` against `plan.signature.arity()` before
        // any reflection runs, and the reflection's own lambda count is that
        // same `arg_count`. A special case here would be a third place the
        // arity is decided, and a third place is how the original defect (a
        // nullary mint against a unary declaration) happened.
        MirShape::InlineScalar => match plan.shape() {
            CleanOriginShape::ConstantUint { value } => {
                let width = machine_width(plan, "ConstantUint")?;
                Ok(single_assignment_body(
                    plan,
                    TemplateOperand::ResultScalar { value: *value, width },
                ))
            }
            _ => Err(TemplateRefusal::RealizationDisagrees),
        },

        // ── the wrapping call chain ─────────────────────────────────────────
        //
        // ONE skeleton for TWO rungs, and the identity is exact rather than
        // approximate: `WrappingBinOp` IS the one-step chain. The shipped
        // `build_wrapping_binop_body` emitted `bb0: _0 = Call(op, [l, r]) ->
        // bb1; bb1: Return`, which is precisely what the composed builder emits
        // when the tree flattens to a single node — same blocks, same locals
        // (no temporaries), same destination, same target. Two builders existed
        // for one shape at two sizes.
        MirShape::Call(CalleeSelector::WrappingAtSignatureWidth(row_op)) => {
            let unwind = call_unwind(row)?;
            match plan.shape() {
                CleanOriginShape::WrappingBinOp { op, left, right } => {
                    if *op != row_op {
                        return Err(TemplateRefusal::RealizationDisagrees);
                    }
                    let width = machine_width(plan, "WrappingBinOp")?;
                    let steps = vec![Step {
                        op: *op,
                        left: StepOperand::Leaf(leaf(*left, width)),
                        right: StepOperand::Leaf(leaf(*right, width)),
                    }];
                    Ok(call_chain_body(plan, &steps, width, unwind))
                }
                CleanOriginShape::Composed { expr } => {
                    match expr {
                        ArithExpr::Bin { op, .. } if *op == row_op => {}
                        _ => return Err(TemplateRefusal::RealizationDisagrees),
                    }
                    let width = machine_width(plan, "Composed")?;
                    let mut steps = Vec::new();
                    let root = flatten(expr, width, &mut steps);
                    let n_steps = steps.len();
                    // The plan is required to carry 2..=COMPOSED_MAX_OPS nodes;
                    // a degenerate tree reaching the emitter is a defect, and
                    // emitting a fallback body for it is the wrong-binary
                    // outcome. (The root being the LAST step is post-order by
                    // construction; it is checked anyway because `_0`'s writer
                    // depends on it.)
                    if n_steps < 2
                        || !matches!(root, StepOperand::Step(index) if index == n_steps - 1)
                    {
                        return Err(TemplateRefusal::DegenerateComposedTree { steps: n_steps });
                    }
                    Ok(call_chain_body(plan, &steps, width, unwind))
                }
                _ => Err(TemplateRefusal::RealizationDisagrees),
            }
        }

        // ── the whole-body raw binary operator (§6f landing 7) ──────────────
        //
        // `_0 = <op>(l, r); return` — ONE block, ONE statement, no call and no
        // branch. It is [`single_assignment_body`]'s skeleton with a different
        // rvalue, and it is written through the SAME helper for that reason:
        // the locals, the block count and the terminator are one decision, and
        // a second copy of them is a second place they could drift.
        //
        // The DIVISOR RULE is re-asserted here rather than assumed. The sealed
        // plan is the decision, and `plan_clean_origin_body` has already
        // required a `Div`/`Rem` right operand to be a strictly positive
        // numeral — so a violation reaching this point is table/emitter drift,
        // and emitting a body for it would be the wrong-binary outcome this
        // whole landing is organised around. It fails closed with the SAME
        // refusal a realization disagreement gets, because that is what it is:
        // the plan and the emitter disagreeing about what may be built.
        MirShape::RawBinOp(row_op) => match plan.shape() {
            CleanOriginShape::RawBinOp { op, left, right } => {
                if *op != row_op {
                    return Err(TemplateRefusal::RealizationDisagrees);
                }
                if op.panics_at_zero_right_operand()
                    && !matches!(right, ArithOperand::Const(divisor) if *divisor > 0)
                {
                    return Err(TemplateRefusal::PanickingDivisor);
                }
                let width = machine_width(plan, "RawBinOp")?;
                Ok(BodyTemplate {
                    locals: signature_locals(plan),
                    blocks: vec![TemplateBlock {
                        stmts: vec![TemplateStatement {
                            place: 0,
                            rvalue: TemplateRvalue::RawBin {
                                op: *op,
                                left: leaf(*left, width),
                                right: leaf(*right, width),
                            },
                        }],
                        terminator: TemplateTerminator::Return,
                    }],
                    arg_count: plan.signature().arity(),
                })
            }
            _ => Err(TemplateRefusal::RealizationDisagrees),
        },

        // ── the comparison diamond ──────────────────────────────────────────
        //
        // ONE skeleton for THREE rungs. Landing 3 recorded the reflection-side
        // finding — *"`ite` at `<` is `ite` at `<` whether its arms are
        // parameters or numerals … what moved is the ARMS, and an arm is
        // DATAFLOW"* — and deliberately did not act on it in the emitter,
        // because acting on it there is this landing. The three shipped
        // builders differed in nothing but which of three operand vocabularies
        // filled four positions.
        MirShape::ComparisonBranch(row_cmp) => match plan.shape() {
            CleanOriginShape::Select { cmp, cmp_left, cmp_right, then_param, else_param } => {
                if *cmp != row_cmp {
                    return Err(TemplateRefusal::RealizationDisagrees);
                }
                // NO width extraction: all four positions are parameters, so
                // the shipped `build_select_body` never destructured the result
                // carrier and never had that fatal. Preserved exactly.
                Ok(diamond_body(
                    plan,
                    *cmp,
                    TemplateOperand::Copy(arg(*cmp_left)),
                    TemplateOperand::Copy(arg(*cmp_right)),
                    TemplateOperand::Copy(arg(*then_param)),
                    TemplateOperand::Copy(arg(*else_param)),
                ))
            }
            CleanOriginShape::SelectLiteral { cmp, cmp_param, literal, then_param, else_param } => {
                if *cmp != row_cmp {
                    return Err(TemplateRefusal::RealizationDisagrees);
                }
                let width = machine_width(plan, "SelectLiteral")?;
                Ok(diamond_body(
                    plan,
                    *cmp,
                    TemplateOperand::Copy(arg(*cmp_param)),
                    TemplateOperand::ResultScalar { value: *literal, width },
                    TemplateOperand::Copy(arg(*then_param)),
                    TemplateOperand::Copy(arg(*else_param)),
                ))
            }
            CleanOriginShape::SelectOperands { cmp, cmp_left, cmp_right, then_arm, else_arm } => {
                if *cmp != row_cmp {
                    return Err(TemplateRefusal::RealizationDisagrees);
                }
                let width = machine_width(plan, "SelectOperands")?;
                // A numeral on the comparison's LEFT is unrepresentable here by
                // construction — the plan vocabulary keeps `cmp_left` a
                // parameter — and that is a MEASURED boundary
                // (`landing3_selection_probes::l3_p6`: the shape does not
                // elaborate at all), not a cautious one.
                Ok(diamond_body(
                    plan,
                    *cmp,
                    TemplateOperand::Copy(arg(*cmp_left)),
                    leaf(*cmp_right, width),
                    leaf(*then_arm, width),
                    leaf(*else_arm, width),
                ))
            }
            _ => Err(TemplateRefusal::RealizationDisagrees),
        },

        // ── the TWO-STEP `==` diamond (§6f landing 6) ───────────────────────
        //
        // The same four-block diamond with ONE extra statement in the entry
        // block, and that statement is the whole landing. `a == b` and `a = b`
        // denote the same branch condition, so until this landing both emitted
        // one `BinOp::Eq` and one `SwitchInt` — side B, which reads only the
        // emitted body, could not tell them apart, while the KERNEL can and
        // does (l5_p3: the island refuses even `rfl` between the two `ite`s).
        // The gate therefore refused a correct body.
        //
        // The fix direction the discipline takes is that the EMITTER moves to
        // meet the reader: the emitted body now transcribes the tree the
        // elaborator actually built — a `Bool` DECISION, its lift to a
        // proposition by `= Bool.true`, and only then the branch — so what side
        // B reads back IS what it reflects.
        MirShape::BoolDecisionBranch => match plan.shape() {
            CleanOriginShape::SelectBeq { cmp_left, cmp_right, then_arm, else_arm } => {
                let width = machine_width(plan, "SelectBeq")?;
                Ok(beq_diamond_body(
                    plan,
                    &[],
                    true,
                    DecisionOperand::Leaf(TemplateOperand::Copy(arg(*cmp_left))),
                    DecisionOperand::Leaf(leaf(*cmp_right, width)),
                    leaf(*then_arm, width),
                    leaf(*else_arm, width),
                ))
            }
            // §6f LANDING 8 — the SAME skeleton with the two coordinates
            // landing 6 fixed now supplied by the plan. There is no second
            // builder and no seventh skeleton: a computed operand is one extra
            // STATEMENT at the top of the entry block, and the lift's polarity
            // is one operand inside a statement that was already there.
            //
            // Every prefix temporary is APPENDED after the three locals landing
            // 6 allocated, so a `SelectBeq` template is byte-identical to what
            // it was — which is what `control_11`'s byte-identity acceptance
            // requires of a landing that touches this function at all.
            CleanOriginShape::SelectBeqGeneral {
                scrutinee,
                cmp_left,
                cmp_right,
                then_arm,
                else_arm,
            } => {
                let width = machine_width(plan, "SelectBeqGeneral")?;
                let arg_count = plan.signature().arity();
                // `_0` ret, `_1..=_n` params, `_{n+1}` select temp, `_{n+2}`
                // decision, `_{n+3}` lift — then the computed temporaries, in
                // LEFT-then-RIGHT order, which is the order the entry block's
                // statements appear in and therefore the order side B resolves
                // them in.
                let mut prefix: Vec<PrefixStep> = Vec::new();
                let mut decision_operand =
                    |operand: &BeqOperand| -> Result<DecisionOperand, TemplateRefusal> {
                        Ok(match operand {
                            BeqOperand::Param(index) => {
                                DecisionOperand::Leaf(TemplateOperand::Copy(arg(*index)))
                            }
                            BeqOperand::Const(value) => {
                                DecisionOperand::Leaf(TemplateOperand::ResultScalar {
                                    value: *value,
                                    width,
                                })
                            }
                            BeqOperand::RawBin { op, left, right } => {
                                // THE DIVISOR RULE, re-asserted where the
                                // instruction is created. The sealed plan has
                                // already required it; a violation reaching here is
                                // plan/emitter drift, and emitting a trapping
                                // division for a TOTAL declaration is the
                                // wrong-binary outcome this lane is organised
                                // around. Same refusal as the whole-body shape,
                                // because it is the same defect.
                                if op.panics_at_zero_right_operand()
                                    && !matches!(right, ArithOperand::Const(d) if *d > 0)
                                {
                                    return Err(TemplateRefusal::PanickingDivisor);
                                }
                                let temp = arg_count + 4 + prefix.len();
                                prefix.push(PrefixStep {
                                    temp,
                                    rvalue: TemplateRvalue::RawBin {
                                        op: *op,
                                        left: leaf(*left, width),
                                        right: leaf(*right, width),
                                    },
                                });
                                DecisionOperand::Computed(temp)
                            }
                        })
                    };
                let left = decision_operand(cmp_left)?;
                let right = decision_operand(cmp_right)?;
                Ok(beq_diamond_body(
                    plan,
                    &prefix,
                    *scrutinee,
                    left,
                    right,
                    leaf(*then_arm, width),
                    leaf(*else_arm, width),
                ))
            }
            _ => Err(TemplateRefusal::RealizationDisagrees),
        },

        // ── the zero-test recursion contract ────────────────────────────────
        //
        // ONE skeleton for BOTH recursive rungs, which the shipped emitter
        // already was (`build_structural_rec_body` was a one-line call into
        // `build_nat_zero_test_rec_body`) and which is a MEASUREMENT rather
        // than a shortcut: the emitted body is built from one runtime
        // vocabulary, at one carrier, at one arity, over one closed value
        // vocabulary — there is nothing for a second emitter to emit
        // differently, and two emitters for one contract can only drift, while
        // the recognizer that reads the bytes back is likewise one
        // (`recognize_wf_nat_rec` delegates to `recognize_structural_rec`).
        //
        // What is NOT shared, and where the lanes actually separate: side A (a
        // `Nat.rec` spine versus a `WellFounded.fix` spine, read by two
        // recognizers in `emit.rs`), the termination evidence the plan demands,
        // the REFLECTION (R1 maps values through the recursor's case
        // substitution, R2 through the functional's own binders) and the GATE
        // (per-defining-equation versus the F layer, with the borrow and the
        // closure audit only on the latter). A widening of this arm widens both
        // lanes and must be re-measured against both reflections in the same
        // change.
        MirShape::ZeroTestBranch => {
            let unwind = call_unwind(row)?;
            // R1 stays single-parameter and passes a one-element argument list;
            // R2 carries one per parameter, with the measure position read off
            // the plan. The two lanes reach ONE template builder, which is what
            // keeps them from drifting about the MIR contract they share.
            let (zero_value, nonzero_value, rec_args, measure_index, guarded_is_pred) =
                match plan.shape() {
                    CleanOriginShape::StructuralNatRec { base, step, rec_arg } => {
                        (base, step, std::slice::from_ref(rec_arg), 0, true)
                    }
                    CleanOriginShape::WellFoundedNatRec {
                        zero_value,
                        nonzero_value,
                        rec_args,
                        measure_index,
                        lowering,
                    } => (
                        zero_value,
                        nonzero_value,
                        rec_args.as_slice(),
                        *measure_index,
                        // R3d: the argument at the GUARDED position is the
                        // emitted predecessor at phase 2 and an ordinary value
                        // at phase 3, where the recursion runs on the measure's
                        // VALUE and side A carries the decrease proof. The MIR
                        // skeleton is identical either way — `ArmLowerer`
                        // lowers `Pred` and a general `Sub` through the same
                        // `Nat::sub` call — so this is the only line the
                        // lowering reaches in the materializer.
                        matches!(lowering, WfLowering::OnParameter),
                    ),
                    _ => return Err(TemplateRefusal::RealizationDisagrees),
                };
            // The plan is the sealed decision: re-assert the invariants the arm
            // lowering depends on rather than silently emitting around them.
            let structural = matches!(plan.shape(), CleanOriginShape::StructuralNatRec { .. });
            if plan.signature().arity() != rec_args.len()
                || (structural && plan.signature().arity() != 1)
                || measure_index >= rec_args.len()
                || (guarded_is_pred && rec_args[measure_index] != RecBodyExpr::Pred)
            {
                return Err(TemplateRefusal::RecursionOutsideFragment);
            }
            Ok(zero_test_rec_template(zero_value, nonzero_value, rec_args, measure_index, unwind))
        }

        // These realizations belong to rows that are NODES inside a recursion
        // arm, framed by a scheme row — no whole-body plan may select one, and
        // a plan that did would be table/emitter drift. Fail closed rather than
        // guess a skeleton.
        MirShape::Call(CalleeSelector::Fixed(_)) | MirShape::SelfCall => {
            Err(TemplateRefusal::RealizationDisagrees)
        }
    }
}

// ═══════════════════════════ the skeletons ═════════════════════════════════

/// `_0` is the return place; `_1 ..= _n` are the parameters, immutable exactly
/// as `local_decls_for_sig` makes them for a shim. At arity 0 the chain is empty
/// and the body is one local — a nullary `fn() -> uN`.
fn signature_locals(plan: &CleanOriginPlan) -> Vec<TemplateLocal> {
    std::iter::once(TemplateLocal { ty: TemplateTy::Result, immutable: false })
        .chain(
            (0..plan.signature().arity())
                .map(|index| TemplateLocal { ty: TemplateTy::Param { index }, immutable: true }),
        )
        .collect()
}

/// One block: `_0 = <operand>; return`. Serves the projection rungs and the
/// constant body.
fn single_assignment_body(plan: &CleanOriginPlan, operand: TemplateOperand) -> BodyTemplate {
    BodyTemplate {
        locals: signature_locals(plan),
        blocks: vec![TemplateBlock {
            stmts: vec![TemplateStatement { place: 0, rvalue: TemplateRvalue::Use(operand) }],
            terminator: TemplateTerminator::Return,
        }],
        arg_count: plan.signature().arity(),
    }
}

/// One flattened binary node.
struct Step {
    op: ArithBinOp,
    left: StepOperand,
    right: StepOperand,
}

/// A step's operand: a leaf, or the RESULT OF AN EARLIER STEP — which is what
/// makes a dangling intermediate unrepresentable here too.
enum StepOperand {
    Leaf(TemplateOperand),
    Step(usize),
}

/// Flatten an arithmetic tree POST-ORDER (left subtree, right subtree, then the
/// node).
///
/// Post-order makes the read-back exact: each temporary is written once and
/// consumed once, so the recognizer's substitution through its environment
/// reconstructs precisely the tree that was flattened here, and the structural
/// comparison in `admit_lowering` is then direct equality.
fn flatten(expr: &ArithExpr, width: u32, steps: &mut Vec<Step>) -> StepOperand {
    match expr {
        ArithExpr::Operand(operand) => StepOperand::Leaf(leaf(*operand, width)),
        ArithExpr::Bin { op, left, right } => {
            let left = flatten(left, width, steps);
            let right = flatten(right, width, steps);
            steps.push(Step { op: *op, left, right });
            StepOperand::Step(steps.len() - 1)
        }
    }
}

/// The linear wrapping-call chain — one `Call` per tree node in post-order,
/// each non-root node writing a fresh temporary, the root writing `_0`, then
/// `Return`. For `fun a b => (a + b) * a`:
///
/// ```text
/// bb0: _3 = Call(u64::wrapping_add, [copy _1, copy _2]) -> bb1
/// bb1: _0 = Call(u64::wrapping_mul, [copy _3, copy _1]) -> bb2
/// bb2: Return
/// ```
///
/// Temporary for NON-ROOT step `k` is local `arg_count + 1 + k`; the root (step
/// `n - 1`) writes the return place and gets no temporary. Every temporary is at
/// the RESULT carrier — the plan's checks guarantee every position shares the
/// one width.
fn call_chain_body(
    plan: &CleanOriginPlan,
    steps: &[Step],
    width: u32,
    unwind: TemplateUnwind,
) -> BodyTemplate {
    let arg_count = plan.signature().arity();
    let n_steps = steps.len();
    let temp = |step: usize| arg_count + 1 + step;

    let locals = signature_locals(plan)
        .into_iter()
        .chain((0..n_steps - 1).map(|_| TemplateLocal { ty: TemplateTy::Result, immutable: false }))
        .collect();

    let operand = |o: &StepOperand| match o {
        StepOperand::Leaf(leaf) => *leaf,
        StepOperand::Step(k) => TemplateOperand::Copy(temp(*k)),
    };

    let mut blocks: Vec<TemplateBlock> = Vec::with_capacity(n_steps + 1);
    for (k, step) in steps.iter().enumerate() {
        let is_root = k == n_steps - 1;
        blocks.push(TemplateBlock {
            stmts: Vec::new(),
            terminator: TemplateTerminator::Call {
                // The ONE authenticated identity at the SIGNATURE's width.
                // Width is never a second field.
                callee: TemplateCallee::Primitive(
                    CalleeSelector::WrappingAtSignatureWidth(step.op).at_width(width),
                ),
                args: vec![operand(&step.left), operand(&step.right)],
                dest: if is_root { 0 } else { temp(k) },
                target: k + 1,
                unwind,
            },
        });
    }
    blocks.push(TemplateBlock { stmts: Vec::new(), terminator: TemplateTerminator::Return });

    BodyTemplate { locals, blocks, arg_count }
}

/// The four-block O0 diamond `recognize_select` was written for, years before
/// this lane:
///
/// ```text
/// bb0: _{n+2} = Cmp(<left>, <right>); switchInt(_{n+2}) -> [0: bb2, otherwise: bb1]
/// bb1: _{n+1} = <then>; goto bb3        // otherwise == the TRUE arm
/// bb2: _{n+1} = <else>; goto bb3        // 0 == the FALSE arm
/// bb3: _0 = copy _{n+1}; return
/// ```
///
/// See [`TemplateTerminator::SwitchIntZero`] for the polarity trap this
/// encodes. With one arm a parameter and the other a numeral the two arms are
/// DIFFERENT INSTRUCTIONS, so a swapped `SwitchTargets` is a visibly different
/// body rather than two indices exchanged — `control_10`'s `half_3` is its net.
fn diamond_body(
    plan: &CleanOriginPlan,
    cmp: SelectCmp,
    cmp_left: TemplateOperand,
    cmp_right: TemplateOperand,
    then_arm: TemplateOperand,
    else_arm: TemplateOperand,
) -> BodyTemplate {
    let arg_count = plan.signature().arity();
    // `_0` ret, `_1..=_n` params, `_{n+1}` the select temp at the result
    // carrier, `_{n+2}` the bool the comparison writes.
    let select_temp = arg_count + 1;
    let cmp_local = arg_count + 2;

    let locals = signature_locals(plan)
        .into_iter()
        .chain([
            TemplateLocal { ty: TemplateTy::Result, immutable: false },
            TemplateLocal { ty: TemplateTy::Bool, immutable: false },
        ])
        .collect();

    let arm = |value: TemplateOperand| TemplateBlock {
        stmts: vec![TemplateStatement { place: select_temp, rvalue: TemplateRvalue::Use(value) }],
        terminator: TemplateTerminator::Goto(3),
    };

    BodyTemplate {
        locals,
        blocks: vec![
            TemplateBlock {
                stmts: vec![TemplateStatement {
                    place: cmp_local,
                    rvalue: TemplateRvalue::Compare { cmp, left: cmp_left, right: cmp_right },
                }],
                terminator: TemplateTerminator::SwitchIntZero {
                    discr: TemplateOperand::Copy(cmp_local),
                    // 0 (comparison FALSE) -> bb2 (else); otherwise -> bb1.
                    zero: 2,
                    otherwise: 1,
                },
            },
            arm(then_arm),
            arm(else_arm),
            TemplateBlock {
                stmts: vec![TemplateStatement {
                    place: 0,
                    rvalue: TemplateRvalue::Use(TemplateOperand::Copy(select_temp)),
                }],
                terminator: TemplateTerminator::Return,
            },
        ],
        arg_count,
    }
}

/// **§6f LANDING 6 — the TWO-STEP diamond**, the emitted realization of a
/// branch condition written `a == b`:
///
/// ```text
/// bb0: _{n+2} = Eq(<left>, <right>)            // the bool DECISION
///      _{n+3} = Eq(copy _{n+2}, const true)    // the LIFT to a proposition
///      switchInt(copy _{n+3}) -> [0: bb2, otherwise: bb1]
/// bb1: _{n+1} = <then>; goto bb3               // otherwise == the TRUE arm
/// bb2: _{n+1} = <else>; goto bb3               // 0 == the FALSE arm
/// bb3: _0 = copy _{n+1}; return
/// ```
///
/// Everything below `bb0` is [`diamond_body`]'s contract, byte for byte —
/// including the polarity trap [`TemplateTerminator::SwitchIntZero`] names —
/// which is deliberate: the arms and the join are one contract and side B reads
/// them with one function
/// (`trust_types::admissible_body::select_arms_and_join`).
///
/// # THE COST, stated where the extra instruction is created
///
/// This body carries ONE MORE COMPARISON and ONE MORE `bool` local than the
/// propositional `a = b` spelling, and it **survives into the binary**. That is
/// not a hedge: `optimized_mir` returns a Clean-origin body at its very top,
/// BEFORE `run_optimization_passes` (the gate's subject is the body that
/// function returns, so a pass rewriting it afterwards would put un-gated code
/// in the binary — `compiler/rustc_mir_transform/src/lib.rs`, and
/// `docs/TCB.md`'s Clean-origin runtime-body row states the same thing), and
/// `mir_for_ctfe` does the same. No MIR pass ever sees it, so nothing folds
/// `Eq(_d, const true)` into `_d` at the MIR level. Whether LLVM folds it
/// downstream is a backend question this lane does not measure and does not
/// claim.
///
/// The alternative — emitting the one-step body and letting side A tell the
/// gate which of two side-B spellings to compare against — is cheaper by one
/// instruction and was REFUSED in landing 5: a spelling bit taken from side A
/// is a bit the kernel structurally cannot refuse, in the one place the double
/// fault `docs/TCB.md` rests on. One comparison is the price of the kernel
/// deciding rather than being told.
/// **§6f LANDING 8** — one COMPUTED decision operand: a raw-binop statement at
/// the head of the entry block, and the temporary it writes.
struct PrefixStep {
    /// The local the statement writes. Allocated after landing 6's three.
    temp: usize,
    /// The raw binary operation. Always [`TemplateRvalue::RawBin`]; the field
    /// is the rvalue rather than the parts so this file has exactly one place
    /// that builds one.
    rvalue: TemplateRvalue,
}

/// **§6f LANDING 8** — a decision operand, as the diamond builder needs it.
///
/// A LEAF is an operand the decision reads directly. A COMPUTED one names a
/// [`PrefixStep`]'s temporary, and it is a distinct variant rather than a bare
/// `TemplateOperand::Copy` so the builder cannot silently read a temp nothing
/// wrote.
enum DecisionOperand {
    Leaf(TemplateOperand),
    Computed(usize),
}

impl DecisionOperand {
    fn operand(&self) -> TemplateOperand {
        match self {
            Self::Leaf(operand) => *operand,
            Self::Computed(temp) => TemplateOperand::Copy(*temp),
        }
    }
}

fn beq_diamond_body(
    plan: &CleanOriginPlan,
    prefix: &[PrefixStep],
    scrutinee: bool,
    cmp_left: DecisionOperand,
    cmp_right: DecisionOperand,
    then_arm: TemplateOperand,
    else_arm: TemplateOperand,
) -> BodyTemplate {
    let arg_count = plan.signature().arity();
    // `_0` ret, `_1..=_n` params, `_{n+1}` the select temp at the result
    // carrier, `_{n+2}` the DECISION bool, `_{n+3}` the LIFTED bool. The select
    // temp keeps its position from `diamond_body` so the two shapes' arm and
    // join blocks are identical; the second bool is appended, which is where a
    // new local belongs.
    //
    // §6f LANDING 8: a COMPUTED operand's temporary is appended AFTER all
    // three, at `_{n+4}` and up. That ordering is what makes a landing-6
    // `SelectBeq` template byte-identical to the one landing 6 shipped — the
    // acceptance `control_11` states for this file — rather than merely
    // equivalent to it.
    let select_temp = arg_count + 1;
    let decision = arg_count + 2;
    let lifted = arg_count + 3;

    let locals = signature_locals(plan)
        .into_iter()
        .chain([
            TemplateLocal { ty: TemplateTy::Result, immutable: false },
            TemplateLocal { ty: TemplateTy::Bool, immutable: false },
            TemplateLocal { ty: TemplateTy::Bool, immutable: false },
        ])
        // Every computed temporary is at the RESULT carrier: the operands of a
        // `==` decision are carrier-typed, which is also what makes side B's
        // width anchor able to see a skew.
        .chain(prefix.iter().map(|_| TemplateLocal { ty: TemplateTy::Result, immutable: false }))
        .collect();

    let arm = |value: TemplateOperand| TemplateBlock {
        stmts: vec![TemplateStatement { place: select_temp, rvalue: TemplateRvalue::Use(value) }],
        terminator: TemplateTerminator::Goto(3),
    };

    // The entry block: the computed operands, then the decision, then the lift.
    let mut entry: Vec<TemplateStatement> = prefix
        .iter()
        .map(|step| TemplateStatement { place: step.temp, rvalue: step.rvalue })
        .collect();
    entry.push(TemplateStatement {
        place: decision,
        rvalue: TemplateRvalue::Compare {
            cmp: SelectCmp::Eq,
            left: cmp_left.operand(),
            right: cmp_right.operand(),
        },
    });
    // THE LIFT. Its constant is the DECLARATION's polarity, transcribed: `true`
    // for `a == b`, `false` for `(a == b) = false`. Flipping it is the
    // complementary function with every arm, index and width still correct —
    // which is why side B matches the constant exactly, why `control_13`
    // injects that mutant against the `true` shape and `control_15` against the
    // `false` one, and why the arms are NEVER swapped to express a negation.
    entry.push(TemplateStatement {
        place: lifted,
        rvalue: TemplateRvalue::Compare {
            cmp: SelectCmp::Eq,
            left: TemplateOperand::Copy(decision),
            right: TemplateOperand::BoolScalar(scrutinee),
        },
    });

    BodyTemplate {
        locals,
        blocks: vec![
            TemplateBlock {
                stmts: entry,
                terminator: TemplateTerminator::SwitchIntZero {
                    // The branch reads the LIFTED bool. Reading the decision
                    // here would emit the one-step body wearing a dead
                    // statement, which side B refuses.
                    discr: TemplateOperand::Copy(lifted),
                    // 0 (the lifted proposition FALSE) -> bb2 (else).
                    zero: 2,
                    otherwise: 1,
                },
            },
            arm(then_arm),
            arm(else_arm),
            TemplateBlock {
                stmts: vec![TemplateStatement {
                    place: 0,
                    rvalue: TemplateRvalue::Use(TemplateOperand::Copy(select_temp)),
                }],
                terminator: TemplateTerminator::Return,
            },
        ],
        arg_count,
    }
}

/// The block index every arm root targets until the `Return` block exists.
///
/// **A plain sentinel, and the hazard it used to carry is gone.** The shipped
/// emitter patched `BasicBlock::from_u32(0xFFFF_FF00)` — deliberately NOT
/// `u32::MAX`, because `BasicBlock`'s `newtype_index` asserts
/// `value <= 0xFFFF_FF00` at CONSTRUCTION and a max-valued sentinel panics the
/// compiler before it can ever be patched (measured on the first
/// structural-rec fixture run). A template block index is an ordinary `usize`
/// with no such constraint, and the materializer only ever converts PATCHED
/// indices, so the constraint cannot be tripped at all.
const RET_SENTINEL: usize = usize::MAX;

/// **The zero-test recursion contract**, shared by R1 and R2:
///
/// ```text
/// bb0:   _2 = &_1;  Call(Nat::is_zero, [move _2]) -> _3: bool, bb1
/// bb1:   switchInt(move _3) [(0, succ_start)] otherwise zero_start
/// zero…: the base chain (from_u64 / add / value copies), root writes _0
/// succ…: _o = from_u64(1); _k = sub(&_1, &_o); ONE Call to THE DEF'S OWN
///        DefId with [move _k]; then the step chain, root writes _0
/// ret:   Return
/// ```
///
/// SWITCH POLARITY: `is_zero` TRUE routes to the zero arm — so the `0` (false)
/// target is the SUCC arm and `otherwise` is the ZERO arm, the mirror of the
/// diamond's trap.
///
/// `_1` is typed at the RESULT carrier rather than at `Param { index: 0 }`,
/// which is what the shipped emitter did (`nat_ty` for both) and is preserved
/// byte for byte. The two agree for every plan that can reach here — the sealed
/// plan's `check_structural_nat_signature` puts the single parameter and the
/// result at the same bignum carrier — but reproducing the spelling rather than
/// "improving" it is the whole discipline of a byte-identity landing.
///
/// Exposed publicly because it is the unit `control_11` measures the R2 shape
/// on: `body_template` reaches it only through a `WellFoundedNatRec` plan, and
/// building one of those needs a kernel-checked `WellFounded.fix` declaration
/// (`control_8`'s hundred-line environment) that adds no byte-level evidence
/// this function does not already carry.
#[must_use]
pub fn zero_test_rec_template(
    zero_value: &RecBodyExpr,
    nonzero_value: &RecBodyExpr,
    rec_args: &[RecBodyExpr],
    measure_index: usize,
    unwind: TemplateUnwind,
) -> BodyTemplate {
    let arity = rec_args.len().max(1);
    let measure_local = measure_index + 1;
    let zero_ref = arity + 1;
    let zero_bool = arity + 2;
    // Locals: _0 ret, _1.._N params (immutable), then the is_zero ref and the
    // bool; arm temps are allocated behind them. At arity 1 that is
    // `_0, _1, _2, _3` — R2's numbering, byte for byte.
    let mut locals = vec![TemplateLocal { ty: TemplateTy::Result, immutable: false }];
    locals.extend(
        (0..arity).map(|_| TemplateLocal { ty: TemplateTy::Result, immutable: true }),
    );
    locals.push(TemplateLocal { ty: TemplateTy::ResultRef, immutable: false });
    locals.push(TemplateLocal { ty: TemplateTy::Bool, immutable: false });
    let mut blocks: Vec<TemplateBlock> = Vec::new();

    // bb0: `_r = &_m; is_zero(move _r) -> _b, bb1`, where `_m` is the MEASURE
    // parameter — the recognizer reads the measure back out of exactly this
    // borrow, so a body that tested a parameter other than the one it descends
    // on would read back with a different `measure_index` and fail the
    // structural comparison against the plan.
    blocks.push(TemplateBlock {
        stmts: vec![TemplateStatement {
            place: zero_ref,
            rvalue: TemplateRvalue::SharedRef(measure_local),
        }],
        terminator: TemplateTerminator::Call {
            callee: TemplateCallee::Primitive(PrimitiveCallee::NatIsZero),
            args: vec![TemplateOperand::Move(zero_ref)],
            dest: zero_bool,
            target: 1,
            unwind,
        },
    });
    // bb1 is the switch; its targets are known only once the arms are built, so
    // it is pushed as a placeholder and REPLACED below. (The shipped emitter
    // left the terminator `None` here — a hole a later pass had to close. A
    // template block always has a terminator, so the hole is unrepresentable.)
    blocks.push(TemplateBlock { stmts: Vec::new(), terminator: TemplateTerminator::Return });

    // Zero arm, then succ arm — each a linear region of appended blocks.
    let zero_start = blocks.len();
    ArmLowerer {
        locals: &mut locals,
        blocks: &mut blocks,
        pending: Vec::new(),
        unwind,
        rec_args: rec_args.to_vec(),
        measure_local,
    }
    .lower_arm(zero_value, false);
    let succ_start = blocks.len();
    ArmLowerer {
        locals: &mut locals,
        blocks: &mut blocks,
        pending: Vec::new(),
        unwind,
        rec_args: rec_args.to_vec(),
        measure_local,
    }
    .lower_arm(nonzero_value, true);
    let ret_index = blocks.len();
    blocks.push(TemplateBlock { stmts: Vec::new(), terminator: TemplateTerminator::Return });

    // `is_zero` FALSE (0) -> the succ arm, otherwise (TRUE) -> the zero arm.
    blocks[1].terminator = TemplateTerminator::SwitchIntZero {
        discr: TemplateOperand::Move(zero_bool),
        zero: succ_start,
        otherwise: zero_start,
    };
    // Patch the RET sentinels.
    for block in &mut blocks {
        match &mut block.terminator {
            TemplateTerminator::Call { target, .. } | TemplateTerminator::Goto(target)
                if *target == RET_SENTINEL =>
            {
                *target = ret_index;
            }
            _ => {}
        }
    }

    BodyTemplate { locals, blocks, arg_count: arity }
}

/// Lowers one [`RecBodyExpr`] tree into a linear chain of call blocks, each
/// targeting the next pushed block; the ROOT write targets the RET SENTINEL,
/// patched once every arm is built. Reference temporaries are accumulated as
/// statements on the block whose call consumes them — the recognizer resolves
/// them from the same block.
struct ArmLowerer<'a> {
    locals: &'a mut Vec<TemplateLocal>,
    blocks: &'a mut Vec<TemplateBlock>,
    pending: Vec<TemplateStatement>,
    unwind: TemplateUnwind,
    /// The self-call's arguments, by 0-based SOURCE parameter position.
    rec_args: Vec<RecBodyExpr>,
    /// The LOCAL the measure parameter occupies (`measure_index + 1`).
    measure_local: usize,
}

impl ArmLowerer<'_> {
    fn fresh(&mut self, ty: TemplateTy) -> usize {
        self.locals.push(TemplateLocal { ty, immutable: false });
        self.locals.len() - 1
    }

    fn borrow(&mut self, of: usize) -> usize {
        let reference = self.fresh(TemplateTy::ResultRef);
        self.pending
            .push(TemplateStatement { place: reference, rvalue: TemplateRvalue::SharedRef(of) });
        reference
    }

    /// Push one call block: pending ref statements ride along, the target is
    /// the NEXT block to be pushed (linear chain) unless this is the arm root,
    /// which targets the sentinel.
    fn push_call(
        &mut self,
        callee: TemplateCallee,
        args: Vec<TemplateOperand>,
        dest: usize,
        is_root: bool,
    ) {
        let target = if is_root { RET_SENTINEL } else { self.blocks.len() + 1 };
        let stmts = std::mem::take(&mut self.pending);
        self.blocks.push(TemplateBlock {
            stmts,
            terminator: TemplateTerminator::Call {
                callee,
                args,
                dest,
                target,
                unwind: self.unwind,
            },
        });
    }

    /// Lower one node into the local that holds its value. `in_succ_arm` gates
    /// `Pred`/`Rec`, which the plan already confines there.
    fn lower(&mut self, node: &RecBodyExpr, in_succ_arm: bool) -> usize {
        match node {
            RecBodyExpr::Decreasing => self.measure_local,
            // R3a — a threaded parameter is the local `arg(i)` holds. The
            // `Decreasing` arm above is the same rule at the measure position;
            // the two are separate arms only because the measure's local is
            // carried rather than recomputed.
            &RecBodyExpr::Param(source_index) => arg(source_index),
            RecBodyExpr::NatConst(value) => {
                let dest = self.fresh(TemplateTy::Result);
                self.push_call(
                    TemplateCallee::Primitive(PrimitiveCallee::NatFromU64),
                    vec![TemplateOperand::U64Scalar(*value)],
                    dest,
                    false,
                );
                dest
            }
            RecBodyExpr::Pred => {
                assert!(in_succ_arm, "plan invariant: Pred is succ-arm-only");
                // one = from_u64(1); k = sub(&_m, &one)
                let one = self.lower(&RecBodyExpr::NatConst(1), in_succ_arm);
                let param_ref = self.borrow(self.measure_local);
                let one_ref = self.borrow(one);
                let dest = self.fresh(TemplateTy::Result);
                self.push_call(
                    TemplateCallee::Primitive(PrimitiveCallee::NatSub),
                    vec![TemplateOperand::Move(param_ref), TemplateOperand::Move(one_ref)],
                    dest,
                    false,
                );
                dest
            }
            RecBodyExpr::Rec => {
                assert!(in_succ_arm, "plan invariant: Rec is succ-arm-only");
                // THE SELF-CALL: every argument is lowered from the RECOGNIZED
                // `rec_args`, in SOURCE order, so the emitted dataflow IS the
                // identity the kernel re-checks (gate step 6) — including the
                // decreasing one, which is `Pred` at the measure position and
                // is not special-cased here. At arity 1 that is the single
                // `Pred` operand R2 emitted.
                let rec_args = std::mem::take(&mut self.rec_args);
                assert!(
                    !rec_args.is_empty(),
                    "plan invariant: a self-call carries one argument per parameter, and a \
                     recursion has at least one — an empty argument list here would mean this \
                     lowering re-entered its own `Rec` arm, which the plan's \
                     `count(&Rec) == 1` and the reflector's `rec_args` check both forbid"
                );
                let mut operands = Vec::with_capacity(rec_args.len());
                for argument in &rec_args {
                    operands.push(TemplateOperand::Move(self.lower(argument, in_succ_arm)));
                }
                self.rec_args = rec_args;
                let dest = self.fresh(TemplateTy::Result);
                self.push_call(TemplateCallee::SelfDef, operands, dest, false);
                dest
            }
            // `+`, `*` and R3b's general `-` lower to the SAME call chain —
            // operands first, then a shared borrow of each, then one
            // authenticated bignum call — and differ only in which
            // `PrimitiveCallee` names it. Keeping one arm is what makes that a
            // fact rather than a claim: there is no second place the operand
            // order or the borrow discipline can diverge between the three.
            //
            // The SHARED BORROW is what makes repeated parameters free here:
            // `a - (a - b)` borrows `_2` twice and clones nothing. The
            // emitter's only MOVE of a parameter is a bare parameter at a
            // self-call argument, which is why the plan's duplication rule is
            // move-aware rather than a use count (see `emit.rs`).
            RecBodyExpr::Add(left, right)
            | RecBodyExpr::Mul(left, right)
            | RecBodyExpr::Sub(left, right)
            | RecBodyExpr::Rem(left, right) => {
                // EXHAUSTIVE BY HAND, and the `_` that used to sit on the last
                // row is gone deliberately (§R8). A catch-all here maps every
                // FUTURE binary node to whichever callee happened to be last —
                // adding `Rem` to the pattern above while `_ => NatSub` stood
                // would have emitted `Nat::sub` for `a % b`: a wrong binary,
                // produced silently, in the one place the operand-order and
                // callee-identity discipline is supposed to be a fact rather
                // than a claim. `control_21` (c) is the mutation that catches
                // exactly this, and it fails if this match is ever loosened.
                let callee = match node {
                    RecBodyExpr::Add(..) => PrimitiveCallee::NatAdd,
                    RecBodyExpr::Mul(..) => PrimitiveCallee::NatMul,
                    RecBodyExpr::Sub(..) => PrimitiveCallee::NatSub,
                    RecBodyExpr::Rem(..) => PrimitiveCallee::NatRem,
                    RecBodyExpr::Rec
                    | RecBodyExpr::Pred
                    | RecBodyExpr::Decreasing
                    | RecBodyExpr::NatConst(_)
                    | RecBodyExpr::Param(_) => {
                        unreachable!("the outer pattern admits only binary bignum nodes")
                    }
                };
                let left = self.lower(left, in_succ_arm);
                let right = self.lower(right, in_succ_arm);
                let left_ref = self.borrow(left);
                let right_ref = self.borrow(right);
                let dest = self.fresh(TemplateTy::Result);
                self.push_call(
                    TemplateCallee::Primitive(callee),
                    vec![TemplateOperand::Move(left_ref), TemplateOperand::Move(right_ref)],
                    dest,
                    false,
                );
                dest
            }
        }
    }

    /// Lower a whole arm: the root value lands in `_0` and the arm's last block
    /// targets the RET sentinel. A call-produced root is re-pointed at `_0`
    /// directly; a place root (`Decreasing`, or a temp) becomes
    /// `_0 = move <place>; goto RET`.
    fn lower_arm(&mut self, root: &RecBodyExpr, in_succ_arm: bool) {
        let value = self.lower(root, in_succ_arm);
        if let Some(last) = self.blocks.last_mut()
            && let TemplateTerminator::Call { dest, target, .. } = &mut last.terminator
            && *dest == value
            && self.pending.is_empty()
        {
            // The root was the last call: write `_0` and go straight to
            // Return, exactly the contract's `Call target bb_ret` form.
            *dest = 0;
            *target = RET_SENTINEL;
            // The temp allocated for it stays DECLARED AND DEAD — harmless,
            // and keeping the lowering uniform beats special-casing the
            // declaration away. It is also load-bearing evidence: the succ
            // arm's numbering starts past it, which `control_11` and
            // `control_7`/`control_8` all pin (`_4`/`_9` for `tozero`,
            // `_4`/`_12` for `countdownSum`).
            return;
        }
        let mut stmts = std::mem::take(&mut self.pending);
        stmts.push(TemplateStatement {
            place: 0,
            rvalue: TemplateRvalue::Use(TemplateOperand::Move(value)),
        });
        self.blocks
            .push(TemplateBlock { stmts, terminator: TemplateTerminator::Goto(RET_SENTINEL) });
    }
}

// ═══════════════════════════ small shared decisions ════════════════════════

/// The local a 0-based SOURCE parameter occupies. The `+1` is the return place
/// occupying local 0.
const fn arg(index: usize) -> usize {
    index + 1
}

/// An arithmetic leaf as an operand.
///
/// `Copy`, not `Move`: `a + a` names one local twice. A numeral is an inline
/// `Const::Val` scalar — nothing needs evaluation, so `required_consts` stays
/// honestly empty and nothing can promote.
fn leaf(operand: ArithOperand, width: u32) -> TemplateOperand {
    match operand {
        ArithOperand::Param(index) => TemplateOperand::Copy(arg(index)),
        ArithOperand::Const(value) => TemplateOperand::ResultScalar { value, width },
    }
}

/// The unsigned machine width the plan's RESULT carrier encodes at.
///
/// **The width is never a second field.** `plan_clean_origin_body` has already
/// required every signature position to carry at one unsigned machine width and
/// every numeral to be in range on the sealed plan, so a non-machine result here
/// is table/emitter drift, not user input.
fn machine_width(plan: &CleanOriginPlan, shape: &'static str) -> Result<u32, TemplateRefusal> {
    match plan.return_ty() {
        trust_types::Ty::Int { width, signed: false } => Ok(*width),
        other => Err(TemplateRefusal::NonMachineResultCarrier { shape, carrier: other.clone() }),
    }
}

/// The unwind edge a row's emitted calls carry, taken FROM the row.
fn call_unwind(row: &SelectionRow) -> Result<TemplateUnwind, TemplateRefusal> {
    match row.unwind {
        UnwindDiscipline::Unreachable => Ok(TemplateUnwind::Unreachable),
        UnwindDiscipline::Continue => Ok(TemplateUnwind::Continue),
        UnwindDiscipline::NoCall => Err(TemplateRefusal::UndeclaredUnwindEdge),
    }
}
