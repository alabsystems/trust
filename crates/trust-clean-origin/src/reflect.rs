// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **THE RECURSIVE-DESCENT REFLECTOR** — §6f landing 1.
//!
//! One descent over side B's reading, driven by [`crate::table`], replacing the
//! per-shape dispatch that used to be spread across three hand-written
//! recursions:
//!
//! | was | is |
//! |---|---|
//! | `emit.rs::render_wrapping_binop` + `render_composed` (a string descent over `ArithExpr`) | [`render_arith_tree`] / [`render_arith_single_op`], one operator vocabulary read from the table |
//! | `reflect_rec.rs::render` (an `Expr` descent over `RecBodyExpr`, three sites) | [`render_rec_node`], six sites |
//! | `reflect_wf.rs::render` (a SECOND `Expr` descent over the SAME vocabulary, three more sites) | — same function |
//! | `emit.rs::admit_lowering`'s `match &recognised { … }` producer dispatch | [`producer_call_for`] |
//!
//! # What is deliberately NOT unified
//!
//! **Side A's reading and side B's reading stay two authorships.** The double
//! fault `docs/TCB.md` rests on is *"a rendering bug alone is caught
//! structurally, a recognition bug alone is caught by the kernel"*, and it
//! works because `emit.rs` reads the KERNEL TERM and
//! `trust_types::admissible_body` independently reads the EMITTED MIR. This
//! module reflects side B's reading only. It never sees the plan, it is never
//! given the plan, and `trust_types` cannot name it. See
//! [`crate::table`]'s module docs for the three checked reasons the table does
//! not collapse the fault.
//!
//! **The frozen producers still produce.** For an
//! [`crate::table::ReflectSpec::ElabSurface`] row this module builds the
//! producer's INPUT — a `p{i}`-positional rendering, or a tuple of parameter
//! indices — and hands it to `trust_spec_elab`'s `admit_*` family, whose output
//! `Expr` is read back out of a scratch environment. A Rust descent that built
//! that `Expr` itself would be co-authorship and would retire frozen-R's
//! pedigree without saying so; the whole reason side B is credible for the
//! arithmetic and select rows is that it passes through the elaborator's own
//! parser and typing, written for the opposite direction.
//!
//! # The de Bruijn layout is a TYPE, never table data
//!
//! [`Site`] is a closed enum whose indices are fixed per variant. That is the
//! discipline `reflect_rec`'s `Case` and `reflect_wf`'s `Site` each established
//! separately, for the reason both module headers give: the binder shape is
//! what the gate compares against side A's own minor premises, so a wrong index
//! is a wrong verdict, and here it is unrepresentable. A row can say *which
//! constant* a node names; it can never say *at which index* a binder sits.

use std::collections::BTreeSet;

use clean_kernel::{Expr, Name};
use trust_types::admissible_body::{
    AdmissibleBody, ArithBinOp, ArithExpr, ArithOperand, RawBinOpKind, RecBodyExpr, SelectCmp,
};

use crate::emit::WfLowering;
use crate::table::{
    CarrierClass, ElabToken, ReflectSpec, SelectionRow, cmp_label, no_selection_row, row,
};

/// Which recursion family a refusal is about. Only affects prose — the
/// rendering itself is one function.
#[derive(Clone, Copy)]
pub(crate) enum RecFamily {
    /// R1 — `Nat.rec`, gated per defining equation.
    Structural,
    /// R2 — `WellFounded.fix`, gated at the F layer.
    WellFounded,
}

impl RecFamily {
    fn label(self) -> &'static str {
        match self {
            Self::Structural => "structural",
            Self::WellFounded => "well-founded",
        }
    }
}

/// **The self-call under construction, and the binder telescope it sits in.**
///
/// R3a (2026-08-26). Before the arity widening the WF sites' indices were
/// literal constants (`x = bvar 2`, `rec = bvar 1`) and the self-call carried a
/// single argument. Both are functions of the ARITY once a recursion may thread
/// parameters beside the one it descends on, so the constants moved here — into
/// one value, derived once, that every WF site reads.
///
/// **This is not a caller supplying an index.** The module header's discipline
/// is that a row may say which constant a node names and never at which index a
/// binder sits; that is unchanged. What a caller supplies is the SHAPE of the
/// recursion — how many parameters it has and which one is the measure, both
/// read off the emitted body by `recognize_wf_nat_rec` — and the indices are
/// then computed here, in one place, by [`Self::measure_bvar`],
/// [`Self::rec_bvar`] and [`Self::other_bvar`]. A wrong arity is a wrong
/// verdict exactly as a wrong index was, and it is caught in exactly the same
/// place: the gate type-checks side B at side A's own functional type and then
/// asks the kernel for defeq.
///
/// The layout is MEASURED, not assumed — `r7_arity_widening_probes` q1 reads it
/// out of the elaborator's own lowering for `addAcc` (measure at source
/// position 0), `addAcc2` (measure at position 1) and `countdownSum` (arity 1,
/// the R2 baseline, which this reproduces index for index):
///
/// ```text
/// F = fun (x : Nat) (rec : (y : Nat) → Nat.lt y x → Nat^(N-1) → Nat)
///        (others : Nat)^(N-1) => dite … (fun h => …) (fun _ => …)
///
/// under a branch binder:   x = bvar (N+1)   rec = bvar N
///                          the j-th OTHER parameter = bvar (N-1-j)
/// self-call:               rec <decreasing> <proof> <others, in source order>
/// ```
/// **R3d — the layout is a function of the LOWERING too.** Phase 3's telescope
/// is `n, rec, p⃗, hm` (`arity + 3` binders) against phase 2's `x, rec,
/// threaded…` (`arity + 1`), so every index below moves and the self-call
/// carries two more arguments. Measured on the elaborated `gcdB`
/// (`gcd_phase3_probes` p2): at arity 2, under the branch binder, `rec` is
/// `#4`, `a` is `#3`, `b` is `#2` and `hm` is `#1`.
#[derive(Clone, Copy)]
pub(crate) struct RecCall<'a> {
    /// The self-call's arguments, indexed by 0-based SOURCE parameter
    /// position. R1 passes a one-element slice; R2 passes `WfRecBody::rec_args`.
    pub args: &'a [RecBodyExpr],
    /// How many parameters the recursion has.
    pub arity: usize,
    /// Which 0-based source parameter the ZERO TEST decides. At phase 2 that is
    /// also the measure; at phase 3 it is an ordinary parameter and the
    /// recursion variable is the measure's value.
    pub measure_index: usize,
    /// Which well-founded lowering the functional being rendered is in. R1
    /// passes `OnParameter` and never reads it — a structural recursor has no
    /// `WellFounded.fix` spine at all.
    pub lowering: WfLowering,
}

impl RecCall<'_> {
    /// R1's context: one parameter, which is necessarily the measure.
    pub(crate) fn unary(arg: &RecBodyExpr) -> RecCall<'_> {
        RecCall {
            args: std::slice::from_ref(arg),
            arity: 1,
            measure_index: 0,
            lowering: WfLowering::OnParameter,
        }
    }

    /// The GUARDED parameter's index under a WF branch binder.
    fn measure_bvar(self) -> u32 {
        let index = match self.lowering {
            WfLowering::OnParameter => self.arity + 1,
            WfLowering::OnMeasureValue => self.arity + 1 - self.measure_index.min(self.arity),
        };
        u32::try_from(index).unwrap_or(u32::MAX)
    }

    /// The recursive slot's index under a WF branch binder.
    fn rec_bvar(self) -> u32 {
        let index = match self.lowering {
            WfLowering::OnParameter => self.arity,
            WfLowering::OnMeasureValue => self.arity + 2,
        };
        u32::try_from(index).unwrap_or(u32::MAX)
    }

    /// The course-of-values HYPOTHESIS `hm`'s index under a WF branch binder —
    /// phase 3 only. It is the functional's innermost binder, so `bvar 0` at
    /// the body and `bvar 1` under the branch, which is where every rendering
    /// site in this module sits.
    fn hypothesis_bvar(self) -> u32 {
        1
    }

    /// The 0-based SOURCE parameter indices this recursion threads beside its
    /// measure, in source order — the order the functional binds them in and
    /// the order the self-call passes them in.
    pub(crate) fn other_indices(self) -> impl Iterator<Item = usize> {
        (0..self.arity).filter(move |index| *index != self.measure_index)
    }

    /// A non-measure parameter's index under a WF branch binder, or `None` when
    /// `source_index` is out of range or names the guarded parameter (which has
    /// its own spelling and must never arrive here — see `RecBodyExpr::Param`).
    fn other_bvar(self, source_index: usize) -> Option<u32> {
        if source_index >= self.arity || source_index == self.measure_index {
            return None;
        }
        match self.lowering {
            WfLowering::OnParameter => {
                let position = self.other_indices().position(|index| index == source_index)?;
                u32::try_from(self.arity - 1 - position).ok()
            }
            // Phase 3 binds EVERY parameter, in source order, so the index is
            // the same formula the guarded one uses — there is no privileged
            // binder to skip over.
            WfLowering::OnMeasureValue => u32::try_from(self.arity + 1 - source_index).ok(),
        }
    }
}

/// The de Bruijn context of one rendering site.
///
/// A CLOSED vocabulary, with the indices fixed per variant rather than supplied
/// by a caller. The three `Rec*` sites are `reflect_rec`'s former `Case`; the
/// three `Wf*` sites are `reflect_wf`'s former `Site`; merging them changed no
/// index, and the mutation controls at both layers (`control_7`, `control_8`)
/// plus the two probe batteries (`r1_equation_probes`, `r2_wf_equation_probes`)
/// are what pin that. R3a made the three `Wf*` sites' indices a function of the
/// recursion's ARITY (see [`RecCall`]); at arity 1 every one of them is the
/// constant it was.
#[derive(Clone, Copy)]
pub(crate) enum Site {
    /// R1, `n := 0`: no binders in scope, and the term is closed.
    RecZero,
    /// R1, `n := Nat.succ k`, under the recursor's OWN minor-premise binders
    /// `k` (outer, `bvar 1`) and `ih` (inner, `bvar 0`). Matching the
    /// recursor's shape is what leaves the gate's per-case comparison with
    /// nothing to unfold (probe s3).
    RecSuccValue,
    /// R1, the self-call argument as a function of the case binder alone:
    /// `k = bvar 0`, and NO `ih` — an argument computed from the call's own
    /// result is not a structural recursion. Probe s4 is the identity this
    /// term feeds.
    RecSuccArg,
    /// R2, the `dite` ELSE branch — the value when the measure IS zero.
    /// `x = bvar (N+1)`; `bvar 2` at `N = 1`, the index R2 shipped.
    WfZero,
    /// R2, the `dite` THEN branch — the value when the measure is NONZERO.
    /// `x = bvar (N+1)`, `rec = bvar N`. The only site where the recursive
    /// occurrence has a reading on the WF lane.
    WfNonzero,
    /// R2, the self-call ARGUMENT, at the same layout as [`Self::WfNonzero`]
    /// because that is where the call sits.
    WfRecArg,
}

impl Site {
    /// How a refusal names this site to a reader. Derived from the site rather
    /// than passed alongside it, so the label cannot disagree with the site.
    pub(crate) fn position(self) -> &'static str {
        match self {
            Self::RecZero => "zero-case value",
            Self::RecSuccValue => "succ-case value",
            Self::RecSuccArg | Self::WfRecArg => "self-call argument",
            Self::WfZero => "zero-arm value",
            Self::WfNonzero => "nonzero-arm value",
        }
    }

    /// The parameter of the recursion, under this site's binders.
    ///
    /// R1's sites substitute the CONSTRUCTOR (`n := 0` / `n := Nat.succ k`),
    /// because the recursor's minor premises are stated that way; R2's sites
    /// name the functional's own parameter binder. Both are the case analysis
    /// the kernel itself performs, not a simplification this module chose.
    fn parameter(self, ctx: RecCall<'_>, named: &mut BTreeSet<&'static str>) -> Expr {
        match self {
            Self::RecZero => Expr::nat_lit(0),
            Self::RecSuccValue => Expr::app(cnst("Nat.succ", named), Expr::bvar(1)),
            Self::RecSuccArg => Expr::app(cnst("Nat.succ", named), Expr::bvar(0)),
            // `bvar 2` at arity 1, which is the index R2 shipped.
            Self::WfZero | Self::WfNonzero | Self::WfRecArg => Expr::bvar(ctx.measure_bvar()),
        }
    }

    /// Whether a NON-MEASURE parameter has a reading here. Only the WF sites
    /// have a binder telescope to read one out of; R1's recursor minor premises
    /// bind the case variable and the induction hypothesis and nothing else.
    fn has_other_parameters(self) -> bool {
        matches!(self, Self::WfZero | Self::WfNonzero | Self::WfRecArg)
    }

    /// Whether the recursive occurrence has a reading here.
    fn binds_recursive_result(self) -> bool {
        matches!(self, Self::RecSuccValue | Self::WfNonzero)
    }

    /// Whether the predecessor has a reading here. It is confined to the
    /// non-zero arm: under a parameter the case split just reported ZERO there
    /// is nothing to take the predecessor OF.
    fn has_predecessor(self) -> bool {
        matches!(self, Self::RecSuccValue | Self::RecSuccArg | Self::WfNonzero | Self::WfRecArg)
    }
}

/// The ONE way a rendering names a kernel constant, recording the name so the
/// environment preflight can be demand-driven.
///
/// `&'static str` is load-bearing, not incidental: it is what makes the defined
/// constant's name — an ordinary borrowed `&str` — unrenderable, which is §6e's
/// prohibition. Probe s2 measures that the constant-citing spelling is VACUOUS
/// as a gate (it admits a diverging off-by-one body), so here it is
/// unconstructible rather than merely absent. The table's
/// [`ReflectSpec::KernelConst`] payload is `&'static str` for exactly this
/// reason: a row cannot smuggle a runtime name in.
pub(crate) fn cnst(constant: &'static str, named: &mut BTreeSet<&'static str>) -> Expr {
    named.insert(constant);
    Expr::const_(Name::interned(constant), vec![])
}

/// The row a recognized recursion-arm node selects, or a NAMED refusal.
///
/// Requirement 3 of the landing, at the reflector: a node the table has no row
/// for cites the missing row by the coordinates a row is keyed on, never a
/// silent `None`. Today the vocabulary is closed and this cannot miss; the
/// refusal exists so that widening `RecBodyExpr` without adding a row is a
/// legible failure rather than a fall-through.
fn rec_node_row(node: &RecBodyExpr) -> Result<&'static SelectionRow, String> {
    let (name, head) = match node {
        RecBodyExpr::Rec => ("nat.self", "the recursive occurrence"),
        RecBodyExpr::Pred => ("nat.sub", "Nat.sub _ 1"),
        RecBodyExpr::Decreasing => ("nat.param", "the recursion parameter"),
        RecBodyExpr::NatConst(_) => ("nat.lit", "a Nat numeral"),
        RecBodyExpr::Add(..) => ("nat.add", "Nat.add"),
        RecBodyExpr::Mul(..) => ("nat.mul", "Nat.mul"),
        // R3b: the GENERAL `-` selects the same row the predecessor does, for
        // the reason `Param` selects the same row `Decreasing` does — one
        // constant, one MIR realization, two operand shapes. A second row
        // would put an operand shape into the table.
        RecBodyExpr::Sub(..) => ("nat.sub", "Nat.sub"),
        // §R8: `%` gets its OWN row, unlike the `Sub`/`Pred` pair above. Those
        // two share `nat.sub` because they name one constant and one MIR
        // realization; `Rem` names a DIFFERENT constant (`Nat.mod`) through a
        // DIFFERENT callee (`Nat::rem`), so sharing would be the aliasing this
        // file's header forbids.
        RecBodyExpr::Rem(..) => ("nat.mod", "Nat.mod"),
        // R3a: a NON-MEASURE parameter selects the SAME row the measure does.
        // Deliberately not a row of its own — `nat.param` is `BinderSite`, and
        // this file's header rule is that a row may say which constant a node
        // names and never at which index a binder sits. `Decreasing` and
        // `Param(i)` differ in exactly that index, which is `RecCall`'s to
        // compute; a second row would put a binder position into the table.
        RecBodyExpr::Param(_) => ("nat.param", "the recursion parameter"),
    };
    row(name).ok_or_else(|| no_selection_row(head, CarrierClass::BignumNat))
}

/// Render one recognized recursion-arm node at its site, or refuse
/// (fail-closed) when the node has no reading there.
///
/// Deliberately the DUMB rendering: each node spells what the MACHINE computes,
/// and every identification with side A's spelling is the KERNEL's decision,
/// never this function's. The measurement table for every node is in
/// [`crate::reflect_rec`]'s and [`crate::reflect_wf`]'s module docs, which are
/// unchanged — this function renders exactly what those two rendered.
///
/// `rec_arg` is only read at a site that binds the recursive result AND whose
/// family renders the argument inline (R2's functional puts it in the `rec`
/// slot). R1 renders the argument at its own [`Site::RecSuccArg`] site, which
/// is why the gate can compare it against `fun k => bvar 0`.
pub(crate) fn render_rec_node(
    family: RecFamily,
    name: &str,
    node: &RecBodyExpr,
    site: Site,
    ctx: RecCall<'_>,
    named: &mut BTreeSet<&'static str>,
) -> Result<Expr, String> {
    let position = site.position();
    let family_label = family.label();
    let selected = rec_node_row(node)?;

    match node {
        // THE RECURSIVE OCCURRENCE. `ReflectSpec::BinderSite`: the row carries
        // no term, the SITE does — R1's recursor `ih`, R2's functional `rec`
        // slot with the decrease sentinel. The defined constant appears
        // nowhere, at either.
        RecBodyExpr::Rec => {
            if !site.binds_recursive_result() {
                return Err(format!(
                    "cannot reflect the {family_label} recursion emitted for `{name}`: its \
                     {position} reads the self-call RESULT, which has no reading there — the \
                     recursive result exists only under the recursion's own binder in the \
                     non-zero arm, and an argument computed from the call's own result is not \
                     a {family_label} recursion. This is a producer-chain defect, not a user \
                     error, and there is no degraded rendering: either the emitter placed the \
                     self-call outside the non-zero arm, or the recognizer read it into the \
                     wrong field. Please report it."
                ));
            }
            debug_assert!(matches!(selected.reflect, ReflectSpec::BinderSite));
            match family {
                // The recursor's OWN `ih` binder — the abstract-ih form.
                RecFamily::Structural => Ok(Expr::bvar(0)),
                // The functional's OWN `rec` binder, applied to the argument
                // and to the decrease-slot SENTINEL. Side B cannot author a
                // decrease proof even by accident: the sentinel resolves to
                // nothing and the gate borrows side A's.
                RecFamily::WellFounded => match ctx.lowering {
                    // PHASE 2 — `rec <decreasing> <slot> <others, in SOURCE
                    // order>`, the spine `r7` q1 measured, at arity 1 the
                    // two-argument one R2 shipped. The other arguments are
                    // ordinary VALUES: they carry no termination weight, they
                    // are decided by the gate's type check at side A's
                    // functional type and by the kernel defeq, and side B still
                    // writes only the sentinel in the one slot that IS a proof.
                    WfLowering::OnParameter => {
                        let Some(decreasing) = ctx.args.get(ctx.measure_index) else {
                            return Err(format!(
                                "cannot reflect the {family_label} recursion emitted for `{name}`: its \
                                 self-call carries {} argument(s) with the measure at position {}, so \
                                 the decreasing argument has no slot to be read from. This is a \
                                 producer-chain defect; please report it.",
                                ctx.args.len(),
                                ctx.measure_index
                            ));
                        };
                        let mut spine = Vec::with_capacity(ctx.args.len() + 1);
                        spine.push(render_rec_node(
                            family,
                            name,
                            decreasing,
                            Site::WfRecArg,
                            ctx,
                            named,
                        )?);
                        spine.push(cnst(crate::gate::DECREASE_SLOT_SENTINEL, named));
                        for source_index in ctx.other_indices() {
                            let Some(argument) = ctx.args.get(source_index) else {
                                return Err(format!(
                                    "cannot reflect the {family_label} recursion emitted for `{name}`: \
                                     its self-call has no argument for source parameter \
                                     {source_index}, which the functional binds. This is a \
                                     producer-chain defect; please report it."
                                ));
                            };
                            spine.push(render_rec_node(
                                family,
                                name,
                                argument,
                                Site::WfRecArg,
                                ctx,
                                named,
                            )?);
                        }
                        Ok(Expr::apps(Expr::bvar(ctx.rec_bvar()), spine))
                    }
                    // PHASE 3 (R3d) — `rec <measure> <hm> <p⃗ in SOURCE order>
                    // <slot>`. THREE of those five positions are things MIR
                    // does not contain and side B therefore may not author:
                    //
                    //   * the MAJOR PREMISE is the measure at the enclosing
                    //     parameters — a term written by `termination_by`, of
                    //     which the emitted body holds no trace. Side B writes
                    //     `MEASURE_SLOT_SENTINEL` and the gate borrows side A's.
                    //   * `hm` is the functional's OWN hypothesis binder. Side B
                    //     can and does author that: it is a de Bruijn reference,
                    //     not a term about the program.
                    //   * the DECREASE PROOF, exactly as at phase 2.
                    //
                    // What side B authors is what the emitted body determines:
                    // the `arity` source arguments, in source order.
                    WfLowering::OnMeasureValue => {
                        let mut spine = Vec::with_capacity(ctx.args.len() + 3);
                        spine.push(cnst(crate::gate::MEASURE_SLOT_SENTINEL, named));
                        spine.push(Expr::bvar(ctx.hypothesis_bvar()));
                        for source_index in 0..ctx.arity {
                            let Some(argument) = ctx.args.get(source_index) else {
                                return Err(format!(
                                    "cannot reflect the {family_label} recursion emitted for `{name}`: \
                                     its self-call has no argument for source parameter \
                                     {source_index}, which the functional binds. This is a \
                                     producer-chain defect; please report it."
                                ));
                            };
                            spine.push(render_rec_node(
                                family,
                                name,
                                argument,
                                Site::WfRecArg,
                                ctx,
                                named,
                            )?);
                        }
                        spine.push(cnst(crate::gate::DECREASE_SLOT_SENTINEL, named));
                        Ok(Expr::apps(Expr::bvar(ctx.rec_bvar()), spine))
                    }
                },
            }
        }
        // The emitted predecessor is `trust_bignum::Nat::sub(&n, &1)`. Its
        // MIR-faithful reflection is `Nat.sub <parameter> 1` — NEVER pre-reduced
        // to the case binder, because reducing here would decide the
        // recursive-argument identity in Rust instead of at the kernel, which
        // is the authority this producer must not have (probe s6).
        RecBodyExpr::Pred => {
            if !site.has_predecessor() {
                return Err(format!(
                    "cannot reflect the {family_label} recursion emitted for `{name}`: its \
                     {position} computes the predecessor, which has no reading there — the \
                     emitted contract confines the predecessor to the non-zero arm, and under \
                     a parameter the case split just reported ZERO there is nothing to take \
                     the predecessor OF. This is a producer-chain defect, not a user error: \
                     the recognizer confines `Pred` to that arm, so a `Pred` here means the \
                     arm walk or the emitter disagreed with the zero-test polarity. Please \
                     report it."
                ));
            }
            let ReflectSpec::KernelConst(constant) = selected.reflect else {
                return Err(row_reflect_spec_defect(selected, position));
            };
            Ok(Expr::apps(cnst(constant, named), [site.parameter(ctx, named), Expr::nat_lit(1)]))
        }
        // The recursion parameter under its case substitution. `BinderSite`
        // again: the substitution is the KERNEL's case analysis, and it lives
        // in `Site`, never in a row.
        RecBodyExpr::Decreasing => {
            debug_assert!(matches!(selected.reflect, ReflectSpec::BinderSite));
            Ok(site.parameter(ctx, named))
        }
        // R3a — a NON-MEASURE parameter, at the index the functional's binder
        // telescope puts it at. `BinderSite` again, and the same rule: the
        // substitution is the KERNEL's, the index is `RecCall`'s, and no row
        // knows either.
        &RecBodyExpr::Param(source_index) => {
            debug_assert!(matches!(selected.reflect, ReflectSpec::BinderSite));
            if !site.has_other_parameters() {
                return Err(format!(
                    "cannot reflect the {family_label} recursion emitted for `{name}`: its \
                     {position} names source parameter {source_index}, which has no reading \
                     there — a structural recursor's minor premise binds the case variable and \
                     the induction hypothesis and nothing else, so there is no binder for a \
                     threaded parameter to be read out of. This is a producer-chain defect, not \
                     a user error, and there is no degraded rendering. Please report it."
                ));
            }
            let Some(index) = ctx.other_bvar(source_index) else {
                return Err(format!(
                    "cannot reflect the {family_label} recursion emitted for `{name}`: its \
                     {position} names source parameter {source_index} under a recursion of \
                     arity {} whose measure is parameter {}. Either the index is out of range, \
                     or it names the MEASURE — which is spelled `Decreasing`, never \
                     `Param({})`, because one position with two spellings would let the \
                     structural comparison in `admit_lowering` pass or fail on a naming \
                     accident. This is a producer-chain defect; please report it.",
                    ctx.arity, ctx.measure_index, ctx.measure_index
                ));
            };
            Ok(Expr::bvar(index))
        }
        // Numerals as kernel literals (probe s7's bridge to the island's
        // `OfNat.ofNat` surface spelling).
        &RecBodyExpr::NatConst(value) => {
            let ReflectSpec::KernelNatLiteral = selected.reflect else {
                return Err(row_reflect_spec_defect(selected, position));
            };
            Ok(Expr::nat_lit(value))
        }
        // `+` as the row's kernel constant (probe s8's bridge to the surface
        // `HAdd.hAdd` spelling), `*` as `nat.mul`'s (probe q7's bridge to
        // `HMul.hMul`), and R3b's general `-` as `nat.sub`'s (probe m1's
        // bridge to `HSub.hSub`). THIS is the recursive descent: the operands
        // are rendered by the same function at the same site. The three share
        // an arm because they differ in exactly one thing — the constant the
        // ROW names — and splitting them would create a second place a binary
        // arithmetic node's operand order could be got wrong.
        //
        // Operand ORDER is load-bearing in a way it was not before R3b: `+`
        // and `*` are commutative at `Nat`, so a transposed rendering of those
        // two is invisible to the kernel. `-` is NOT (m1 refuses
        // `a - b = Nat.sub b a`), which makes this one arm the place a
        // transposition would now be caught — and makes the swapped-operand
        // row of `control_17` a genuine refutation rather than a vacuous one.
        // §R8 adds `Rem` to this arm rather than beside it. The arm renders
        // `<row's constant> left right` and nothing else, so it is correct for
        // `%` for the same reason it is correct for `-`: the CONSTANT comes
        // from the row (`nat.mod` ⇒ `Nat.mod`), never from this match, and the
        // operands are rendered in source order. `%` is non-commutative like
        // `-`, so `control_21`'s swapped-operand row is a genuine refutation
        // here too — `q1` refuses `a % b = Nat.mod b a`.
        RecBodyExpr::Add(left, right)
        | RecBodyExpr::Mul(left, right)
        | RecBodyExpr::Sub(left, right)
        | RecBodyExpr::Rem(left, right) => {
            let ReflectSpec::KernelConst(constant) = selected.reflect else {
                return Err(row_reflect_spec_defect(selected, position));
            };
            Ok(Expr::apps(
                cnst(constant, named),
                [
                    render_rec_node(family, name, left, site, ctx, named)?,
                    render_rec_node(family, name, right, site, ctx, named)?,
                ],
            ))
        }
    }
}

/// A row whose [`ReflectSpec`] does not match the node it was selected for.
/// Unreachable while the table and this descent agree; it exists so that a
/// future edit to one and not the other is a NAMED refusal rather than a
/// wrong term.
fn row_reflect_spec_defect(selected: &SelectionRow, position: &str) -> String {
    format!(
        "INTERNAL: selection row `{}` declares the reflection `{:?}`, which is not the one \
         the reflector's {position} arm renders. The instruction-selection table and the \
         reflector have drifted apart. This is a compiler-correctness defect and nothing \
         emitted may rest on it. Please report it.",
        selected.name, selected.reflect
    )
}

// ── the non-recursive lane: the FROZEN producers' inputs ───────────────────

/// The input of a frozen `trust_spec_elab` producer.
///
/// This module builds these; it never builds the resulting `Expr`. See the
/// module docs on why that separation IS frozen-R's pedigree.
pub(crate) enum ProducerCall {
    /// `trust_spec_elab::admit_projection_function`.
    Projection {
        /// 0-based source parameter.
        param: usize,
    },
    /// `trust_spec_elab::admit_expr_function`, over a `p{i}`-positional
    /// rendering.
    ExprRendering(String),
    /// `trust_spec_elab::admit_select_function`.
    Select {
        /// The comparison, in the ELABORATOR's vocabulary (translated at this
        /// boundary, exactly as `clean_island::admit_function_into` does it).
        cmp: trust_spec_elab::SelectCmp,
        /// Comparison's left parameter.
        cmp_left: usize,
        /// Comparison's right parameter.
        cmp_right: usize,
        /// Parameter returned when the comparison holds.
        then_param: usize,
        /// Parameter returned otherwise.
        else_param: usize,
    },
    /// `trust_spec_elab::admit_select_operands_function` — the §6f landing 3
    /// GENERAL select route, whose comparison right-hand side and both arms
    /// are operands.
    SelectOperands {
        /// The comparison, in the elaborator's vocabulary.
        cmp: trust_spec_elab::SelectCmp,
        /// Comparison's left parameter.
        cmp_left: usize,
        /// Comparison's right operand.
        cmp_right: trust_spec_elab::SelectOperand,
        /// The value when the comparison holds.
        then_arm: trust_spec_elab::SelectOperand,
        /// The value otherwise.
        else_arm: trust_spec_elab::SelectOperand,
    },
    /// `trust_spec_elab::admit_select_beq_function` — the §6f landing 6 `==`
    /// route, whose condition is a `Bool`-level decision lifted by
    /// `= Bool.true`. It carries no comparison: the shape is the second
    /// SPELLING of equality, not a fourth comparison.
    SelectBeq {
        /// The decision's left parameter.
        cmp_left: usize,
        /// The decision's right operand.
        cmp_right: trust_spec_elab::SelectOperand,
        /// The value when the decision holds.
        then_arm: trust_spec_elab::SelectOperand,
        /// The value otherwise.
        else_arm: trust_spec_elab::SelectOperand,
    },
    /// `trust_spec_elab::admit_select_beq_operands_function` — the §6f landing
    /// 8 GENERAL `==` route: a COMPUTED decision operand, and the lift's
    /// polarity.
    SelectBeqGeneral {
        /// The `Bool` constant the decision is lifted against.
        scrutinee: bool,
        /// The decision's left operand.
        cmp_left: trust_spec_elab::SelectBeqOperand,
        /// The decision's right operand.
        cmp_right: trust_spec_elab::SelectBeqOperand,
        /// The value when the lifted proposition holds.
        then_arm: trust_spec_elab::SelectOperand,
        /// The value otherwise.
        else_arm: trust_spec_elab::SelectOperand,
    },
    /// `trust_spec_elab::admit_select_literal_function`.
    SelectLiteral {
        /// The comparison, in the elaborator's vocabulary.
        cmp: trust_spec_elab::SelectCmp,
        /// Comparison's left parameter.
        cmp_param: usize,
        /// The numeral on the comparison's RIGHT.
        literal: u128,
        /// Parameter returned when the comparison holds.
        then_param: usize,
        /// Parameter returned otherwise.
        else_param: usize,
    },
    /// **W6 (Rust-calls-Clean)** — `trust_spec_elab::admit_comparison_function`,
    /// the FROZEN E6 producer that mints `Decidable.decide <prop> <inst>` for a
    /// comparison returned as `Bool`. Reached through the shared
    /// [`producer_call_for`] chain (side B reads
    /// [`AdmissibleBody::ComparisonBool`]), because that reading is ALREADY in
    /// the E6 kernel-import direction — so serving it here exposes nothing new.
    Comparison {
        /// The comparison, in the elaborator's vocabulary.
        cmp: trust_spec_elab::SelectCmp,
        /// The comparison's left operand.
        cmp_left: trust_spec_elab::CmpOperand,
        /// The comparison's right operand.
        cmp_right: trust_spec_elab::CmpOperand,
    },
}

/// A recognized body the table has no row for. Carries the v7/D3 text.
#[derive(Debug)]
pub(crate) struct RowMiss {
    /// The named refusal, citing the missing row by its coordinates.
    pub(crate) note: String,
}

/// Select the row for a recognized NON-RECURSIVE body and build its frozen
/// producer's input, or cite the missing row by name.
///
/// This replaces `admit_lowering`'s per-shape `match &recognised { … }`. What
/// it does NOT replace is the reading that produced `recognised`: that is
/// `trust_types::admissible_body`'s, table-independent, and the whole point.
pub(crate) fn producer_call_for(
    recognised: &AdmissibleBody,
) -> Result<(&'static SelectionRow, ProducerCall), RowMiss> {
    match recognised {
        AdmissibleBody::Projection { param } => {
            let selected = require_row("param", "a parameter projection", CarrierClass::AnyExact)?;
            expect_elab(selected, ElabToken::Projection)?;
            Ok((selected, ProducerCall::Projection { param: *param }))
        }
        AdmissibleBody::Arithmetic { op, left, right } => {
            let selected = arith_row(*op)?;
            Ok((selected, ProducerCall::ExprRendering(render_arith_single_op(*op, *left, *right)?)))
        }
        AdmissibleBody::Composed { expr } => {
            // The ROOT row of the tree; every node re-selects its own row
            // inside the descent.
            let root_op = match expr {
                ArithExpr::Bin { op, .. } => *op,
                ArithExpr::Operand(_) => {
                    return Err(RowMiss {
                        note: no_selection_row(
                            "a bare operand as a whole composed body",
                            CarrierClass::MachineUInt,
                        ),
                    });
                }
            };
            let selected = arith_row(root_op)?;
            Ok((selected, ProducerCall::ExprRendering(render_arith_tree(expr)?)))
        }
        AdmissibleBody::Select { cmp, cmp_left, cmp_right, then_param, else_param } => {
            let selected = select_row(*cmp)?;
            Ok((
                selected,
                ProducerCall::Select {
                    cmp: elaborator_cmp(*cmp),
                    cmp_left: *cmp_left,
                    cmp_right: *cmp_right,
                    then_param: *then_param,
                    else_param: *else_param,
                },
            ))
        }
        AdmissibleBody::SelectLiteral { cmp, cmp_param, literal, then_param, else_param } => {
            let selected = select_row(*cmp)?;
            Ok((
                selected,
                ProducerCall::SelectLiteral {
                    cmp: elaborator_cmp(*cmp),
                    cmp_param: *cmp_param,
                    literal: *literal,
                    then_param: *then_param,
                    else_param: *else_param,
                },
            ))
        }
        // §6f LANDING 2 — SERVED. Landing 1 refused here, citing probe_e3's
        // diagnosis: the defect was the arity-erasing
        // `ConstantUint -> admit_constant_function` ROUTING, not definitional
        // equality. This is the repair, and it is a ROUTING change only:
        // `landing2_selection_probes::l2_p1` measured that at ZERO parameters
        // the two producers mint the SAME kernel term, so nothing is given up
        // by going through the expr producer — and the expr producer takes its
        // arity from `extracted.body.arg_count`, which is what makes ONE route
        // serve the nullary body and the ignored-binder body alike.
        //
        // The row is `uint.lit`, reached through its SECOND side-A route
        // (`KernelSelector::CarrierNumeralBody`): an operand numeral and a
        // whole-body numeral are one vocabulary item in two positions, and the
        // position is dataflow, which this module does not own — side B told
        // them apart before this line ran, off different MIR.
        &AdmissibleBody::ConstantUint { value, .. } => {
            let selected = require_row("uint.lit", "a constant body", CarrierClass::MachineUInt)?;
            expect_elab(selected, ElabToken::Numeral)?;
            // Rendered by the SAME function that renders a numeral in operand
            // position, not by a second `to_string()` here. One vocabulary item
            // means one rendering; two would be the place an operand numeral
            // and a body numeral could start disagreeing about spelling.
            let rendering = render_arith_operand(ArithOperand::Const(value))?;
            Ok((selected, ProducerCall::ExprRendering(rendering)))
        }
        // W6 (Rust-calls-Clean): the comparison-to-`Bool` value. Reflected
        // through the FROZEN `admit_comparison_function` (E6's own producer),
        // which mints `Decidable.decide <prop> <inst>` — definitionally equal to
        // the `decide`/`BEq.beq` the island wrote. The row is
        // `comparison.{lt,le,eq}`; the operands cross into the elaborator's
        // vocabulary the same way a select's do.
        AdmissibleBody::ComparisonBool { cmp, left, right } => {
            let selected = comparison_row(*cmp)?;
            Ok((
                selected,
                ProducerCall::Comparison {
                    cmp: elaborator_cmp(*cmp),
                    cmp_left: elaborator_cmp_operand(*left),
                    cmp_right: elaborator_cmp_operand(*right),
                },
            ))
        }
        // The E6 recognizer shapes the frozen-producer table has no row for
        // yet (the per-field/bool-binary/checked-arith series). Fail closed by
        // citing the missing row, exactly as every other unselected shape
        // does — recognition is not emission, and a shape this table cannot
        // emit must decline rather than guess.
        AdmissibleBody::ConstantInt { .. }
        | AdmissibleBody::FieldProjection { .. }
        | AdmissibleBody::BoolBinary { .. }
        | AdmissibleBody::CheckedArithmetic { .. }
        | AdmissibleBody::GuardedNarrow { .. }
        | AdmissibleBody::AggregateFields { .. }
        | AdmissibleBody::WidenedEq { .. } => Err(RowMiss {
            note: no_selection_row(
                "an E6 shape outside the frozen-producer table",
                CarrierClass::AnyExact,
            ),
        }),
    }
}

/// **§6f landing 3** — select the row for a GENERAL select reading and build
/// its producer's input.
///
/// A separate entry point for the same reason side B's reader has one: the
/// general reading is deliberately not an `AdmissibleBody` value, so it cannot
/// arrive through [`producer_call_for`], and the E6 kernel-import direction —
/// which consumes `AdmissibleBody` and nothing else — cannot reach either.
///
/// The ROW is the same row a bare-parameter select selects. That is the whole
/// finding: the arms are dataflow, and the table selects vocabulary.
pub(crate) fn producer_call_for_general_select(
    recognised: &trust_types::admissible_body::GeneralSelectBody,
) -> Result<(&'static SelectionRow, ProducerCall), RowMiss> {
    let selected = select_row(recognised.cmp)?;
    Ok((
        selected,
        ProducerCall::SelectOperands {
            cmp: elaborator_cmp(recognised.cmp),
            cmp_left: recognised.cmp_left,
            cmp_right: elaborator_operand(recognised.cmp_right),
            then_arm: elaborator_operand(recognised.then_arm),
            else_arm: elaborator_operand(recognised.else_arm),
        },
    ))
}

/// **§6f landing 6** — select the row for a `==` select reading and build its
/// producer's input.
///
/// A separate entry point for the same reason side B's reader has one: the
/// reading is deliberately not an `AdmissibleBody` value, so it cannot arrive
/// through [`producer_call_for`], and the E6 kernel-import direction — which
/// consumes `AdmissibleBody` and nothing else — cannot reach it either.
///
/// Unlike [`producer_call_for_general_select`] this selects a DIFFERENT row
/// from the propositional select's, and that is the landing: the arms are
/// dataflow (landing 3), but the CONDITION is a kernel term, and a different
/// kernel term with a different emitted realization is a different row.
pub(crate) fn producer_call_for_beq_select(
    recognised: &trust_types::admissible_body::BeqSelectBody,
) -> Result<(&'static SelectionRow, ProducerCall), RowMiss> {
    let selected = require_row(
        "select.beq",
        "`ite` at a `Bool`-level `==` decision",
        CarrierClass::MachineUInt,
    )?;
    expect_elab(selected, ElabToken::SelectBeq)?;
    Ok((
        selected,
        ProducerCall::SelectBeq {
            cmp_left: recognised.cmp_left,
            cmp_right: elaborator_operand(recognised.cmp_right),
            then_arm: elaborator_operand(recognised.then_arm),
            else_arm: elaborator_operand(recognised.else_arm),
        },
    ))
}

/// **§6f LANDING 8** — select the row for a GENERAL `==` select reading and
/// build its producer's input.
///
/// A separate entry point for the same reason side B's reader has one, and it
/// selects the SAME ROW landing 6's `==` reading selects. That is the finding
/// rather than a convenience: what changed is an operand vocabulary and a lift
/// constant, both of which side B reads out of the emitted bytes, and neither
/// of which moves the realization ([`crate::table::MirShape::BoolDecisionBranch`]
/// is still realized by exactly one row). Landing 3 established the pattern for
/// an operand — `ite` at `<` is one row whatever fills its arms — and this is
/// the same statement one layer inside the condition.
///
/// The COMPUTED operand's rendering is built here by exactly the two functions
/// [`producer_call_for_raw_binop`] uses ([`render_arith_operand`] and
/// [`raw_operator_token`], the latter reading the token from the selected ROW
/// rather than from a match in this file), so the operand a general select
/// reflects and the operand a whole-body raw binop reflects are one rendering
/// through one frozen producer.
pub(crate) fn producer_call_for_beq_general_select(
    recognised: &trust_types::admissible_body::GeneralBeqSelectBody,
) -> Result<(&'static SelectionRow, ProducerCall), RowMiss> {
    let selected = require_row(
        "select.beq",
        "`ite` at a `Bool`-level `==` decision",
        CarrierClass::MachineUInt,
    )?;
    expect_elab(selected, ElabToken::SelectBeq)?;
    Ok((
        selected,
        ProducerCall::SelectBeqGeneral {
            scrutinee: recognised.scrutinee,
            cmp_left: elaborator_beq_operand(recognised.cmp_left)?,
            cmp_right: elaborator_beq_operand(recognised.cmp_right)?,
            then_arm: elaborator_operand(recognised.then_arm),
            else_arm: elaborator_operand(recognised.else_arm),
        },
    ))
}

/// One general-`==` decision operand, translated at the crate boundary into the
/// ELABORATOR's vocabulary.
///
/// The two leaves go across as leaves; a computed node goes across as the
/// SURFACE RENDERING the frozen `elab_term` elaborates — never as a term. That
/// is what keeps the computed subterm inside frozen-R's pedigree: this file
/// hands the producer its input, and the producer's own parser and typing build
/// the `Expr`.
fn elaborator_beq_operand(
    operand: trust_types::admissible_body::BeqOperand,
) -> Result<trust_spec_elab::SelectBeqOperand, RowMiss> {
    use trust_types::admissible_body::BeqOperand;
    Ok(match operand {
        BeqOperand::Param(index) => trust_spec_elab::SelectBeqOperand::Param(index),
        BeqOperand::Const(value) => trust_spec_elab::SelectBeqOperand::Literal(value),
        BeqOperand::RawBin { op, left, right } => {
            trust_spec_elab::SelectBeqOperand::Computed(format!(
                "{} {} {}",
                render_arith_operand(left)?,
                raw_operator_token(op)?,
                render_arith_operand(right)?
            ))
        }
    })
}

/// **§6f LANDING 7** — select the row for a RAW-BINOP reading and build its
/// producer's input.
///
/// A separate entry point for the same reason side B's reader has one: the
/// reading is deliberately not an `AdmissibleBody` value, so it cannot arrive
/// through [`producer_call_for`], and the E6 kernel-import direction — which
/// consumes `AdmissibleBody` and nothing else — cannot reach it either. Here
/// that is not merely hygiene: `AdmissibleBody`'s exclusion of the raw-binop
/// spelling is a pinned provenance boundary
/// (`binop_provenance_pins_never_admit`), and this landing does not move it.
///
/// The producer is the FROZEN [`trust_spec_elab::admit_expr_function`] — the
/// same one the arithmetic and numeral rows route to. Nothing new was written
/// to serve these operators, because `elab_term` has elaborated `&`/`|`/`^`
/// through `Nat.land`/`Nat.lor`/`Nat.xor`, `/`/`%` through the TOTAL
/// `Nat.div`/`Nat.mod`, and a literal `>>` through `Nat.div` by `2^k` since
/// long before this lane existed. That is what lets
/// these rows ride frozen-R's pedigree and carry no `docs/TCB.md` row of their
/// own.
pub(crate) fn producer_call_for_raw_binop(
    recognised: &trust_types::admissible_body::RawBinOpBody,
) -> Result<(&'static SelectionRow, ProducerCall), RowMiss> {
    let selected = raw_binop_row(recognised.op)?;
    Ok((
        selected,
        ProducerCall::ExprRendering(format!(
            "{} {} {}",
            render_arith_operand(recognised.left)?,
            raw_operator_token(recognised.op)?,
            render_arith_operand(recognised.right)?
        )),
    ))
}

/// The row a raw-binop operator selects, from the TABLE — never from a literal
/// in this function, exactly as [`arith_row`] is.
fn raw_binop_row(op: RawBinOpKind) -> Result<&'static SelectionRow, RowMiss> {
    crate::table::raw_binop_rows(CarrierClass::MachineUInt)
        .find(|(_, candidate)| *candidate == op)
        .map(|(selected, _)| selected)
        .ok_or_else(|| RowMiss {
            note: no_selection_row(raw_binop_head_label(op), CarrierClass::MachineUInt),
        })
}

fn raw_binop_head_label(op: RawBinOpKind) -> &'static str {
    match op {
        RawBinOpKind::BitAnd => "a bitwise `&`",
        RawBinOpKind::BitOr => "a bitwise `|`",
        RawBinOpKind::BitXor => "a bitwise `^`",
        RawBinOpKind::Div => "a division `/`",
        RawBinOpKind::Rem => "a remainder `%`",
        RawBinOpKind::Shr => "a right shift `>>`",
    }
}

/// The surface operator token a raw-binop row hands the frozen producer.
/// Read from the row's [`ElabToken`], never from a match in the renderer —
/// [`operator_token`]'s discipline, for the same reason.
fn raw_operator_token(op: RawBinOpKind) -> Result<&'static str, RowMiss> {
    let selected = raw_binop_row(op)?;
    match selected.reflect {
        ReflectSpec::ElabSurface(ElabToken::RawOperator(RawBinOpKind::BitAnd)) => Ok("&"),
        ReflectSpec::ElabSurface(ElabToken::RawOperator(RawBinOpKind::BitOr)) => Ok("|"),
        ReflectSpec::ElabSurface(ElabToken::RawOperator(RawBinOpKind::BitXor)) => Ok("^"),
        ReflectSpec::ElabSurface(ElabToken::RawOperator(RawBinOpKind::Div)) => Ok("/"),
        ReflectSpec::ElabSurface(ElabToken::RawOperator(RawBinOpKind::Rem)) => Ok("%"),
        // The frozen `elab_term` mints `>>` only at a literal amount below the
        // width, as `{C}.ofNat (Nat.div ({C}.toNat x) 2^k)` — the reading the
        // kernel identifies with Lean's `{C}.shiftRight` (`l7_p12`).
        ReflectSpec::ElabSurface(ElabToken::RawOperator(RawBinOpKind::Shr)) => Ok(">>"),
        _ => Err(RowMiss {
            note: format!(
                "INTERNAL: selection row `{}` was selected for a raw binary operator but \
                 declares the reflection `{:?}`. The table and the reflector have drifted \
                 apart. Please report it.",
                selected.name, selected.reflect
            ),
        }),
    }
}

/// One operand, translated at the crate boundary into the ELABORATOR's
/// vocabulary — exactly as [`elaborator_cmp`] translates the comparison, and
/// for the same reason: the two crates' enums are separate types on purpose,
/// so the translation is one visible function rather than a shared definition
/// that would couple side B's producer to side B's reader.
fn elaborator_operand(operand: ArithOperand) -> trust_spec_elab::SelectOperand {
    match operand {
        ArithOperand::Param(index) => trust_spec_elab::SelectOperand::Param(index),
        ArithOperand::Const(value) => trust_spec_elab::SelectOperand::Literal(value),
    }
}

fn require_row(
    name: &'static str,
    head: &'static str,
    carrier: CarrierClass,
) -> Result<&'static SelectionRow, RowMiss> {
    row(name).ok_or_else(|| RowMiss { note: no_selection_row(head, carrier) })
}

fn expect_elab(selected: &'static SelectionRow, token: ElabToken) -> Result<(), RowMiss> {
    if selected.reflect == ReflectSpec::ElabSurface(token) {
        return Ok(());
    }
    Err(RowMiss {
        note: format!(
            "INTERNAL: selection row `{}` declares the reflection `{:?}`, not the frozen \
             producer `{token:?}` the reflector routes it to. The table and the reflector \
             have drifted apart; nothing emitted may rest on it. Please report it.",
            selected.name, selected.reflect
        ),
    })
}

/// The row an arithmetic operator selects, from the TABLE — never from a
/// literal in this function.
fn arith_row(op: ArithBinOp) -> Result<&'static SelectionRow, RowMiss> {
    crate::table::arith_operator_rows(CarrierClass::MachineUInt)
        .find(|(_, candidate)| *candidate == op)
        .map(|(selected, _)| selected)
        .ok_or_else(|| RowMiss {
            note: no_selection_row(arith_head_label(op), CarrierClass::MachineUInt),
        })
}

fn select_row(cmp: SelectCmp) -> Result<&'static SelectionRow, RowMiss> {
    crate::table::ROWS
        .iter()
        .find(|candidate| candidate.reflect == ReflectSpec::ElabSurface(ElabToken::Select(cmp)))
        .ok_or_else(|| RowMiss {
            note: no_selection_row(
                &format!("`ite` at {}", cmp_label(cmp)),
                CarrierClass::MachineUInt,
            ),
        })
}

/// **W6 (Rust-calls-Clean)** — the row a comparison-to-`Bool` selects, from the
/// TABLE by its `ElabToken`, never from a literal here.
fn comparison_row(cmp: SelectCmp) -> Result<&'static SelectionRow, RowMiss> {
    crate::table::ROWS
        .iter()
        .find(|candidate| candidate.reflect == ReflectSpec::ElabSurface(ElabToken::Comparison(cmp)))
        .ok_or_else(|| RowMiss {
            note: no_selection_row(
                &format!("a comparison to `Bool` at {}", cmp_label(cmp)),
                CarrierClass::MachineUInt,
            ),
        })
}

/// One comparison-to-`Bool` operand, translated at the crate boundary into the
/// ELABORATOR's `CmpOperand` vocabulary — the same translation a select
/// operand takes, one shape simpler (a comparison operand is never computed).
fn elaborator_cmp_operand(
    operand: trust_types::admissible_body::CmpOperand,
) -> trust_spec_elab::CmpOperand {
    match operand {
        trust_types::admissible_body::CmpOperand::Param(index) => {
            trust_spec_elab::CmpOperand::Param(index)
        }
        trust_types::admissible_body::CmpOperand::Const(value) => {
            trust_spec_elab::CmpOperand::Const(value)
        }
        trust_types::admissible_body::CmpOperand::NegConst(magnitude) => {
            trust_spec_elab::CmpOperand::NegConst(magnitude)
        }
    }
}

fn arith_head_label(op: ArithBinOp) -> &'static str {
    match op {
        ArithBinOp::Add => "a wrapping `+`",
        ArithBinOp::Sub => "a wrapping `-`",
        ArithBinOp::Mul => "a wrapping `*`",
    }
}

fn elaborator_cmp(cmp: SelectCmp) -> trust_spec_elab::SelectCmp {
    match cmp {
        SelectCmp::Lt => trust_spec_elab::SelectCmp::Lt,
        SelectCmp::Le => trust_spec_elab::SelectCmp::Le,
        SelectCmp::Eq => trust_spec_elab::SelectCmp::Eq,
    }
}

/// The surface operator token an arithmetic row hands the frozen producer.
/// Read from the row's [`ElabToken`], never from a match in the renderer.
fn operator_token(op: ArithBinOp) -> Result<&'static str, RowMiss> {
    let selected = arith_row(op)?;
    match selected.reflect {
        ReflectSpec::ElabSurface(ElabToken::ArithOperator(ArithBinOp::Add)) => Ok("+"),
        ReflectSpec::ElabSurface(ElabToken::ArithOperator(ArithBinOp::Sub)) => Ok("-"),
        ReflectSpec::ElabSurface(ElabToken::ArithOperator(ArithBinOp::Mul)) => Ok("*"),
        _ => Err(RowMiss {
            note: format!(
                "INTERNAL: selection row `{}` was selected for an arithmetic operator but \
                 declares the reflection `{:?}`. The table and the reflector have drifted \
                 apart. Please report it.",
                selected.name, selected.reflect
            ),
        }),
    }
}

/// One LEAF of an arithmetic rendering, through its own row: `param` renders
/// positionally, `uint.lit` renders the raw numeral.
fn render_arith_operand_into(operand: ArithOperand, out: &mut String) -> Result<(), RowMiss> {
    use std::fmt::Write as _;
    match operand {
        ArithOperand::Param(index) => {
            let selected = require_row("param", "a parameter", CarrierClass::AnyExact)?;
            expect_elab(selected, ElabToken::Projection)?;
            let _ = write!(out, "p{index}");
            Ok(())
        }
        ArithOperand::Const(value) => {
            let selected = require_row("uint.lit", "a numeral", CarrierClass::MachineUInt)?;
            expect_elab(selected, ElabToken::Numeral)?;
            let _ = write!(out, "{value}");
            Ok(())
        }
    }
}

fn render_arith_operand(operand: ArithOperand) -> Result<String, RowMiss> {
    let mut out = String::new();
    render_arith_operand_into(operand, &mut out)?;
    Ok(out)
}

/// The `clean_island::admit_function_into` rendering of a recognized single-op
/// body: `lhs op rhs`, positional `p{i}` names and raw literals, NOT
/// parenthesized.
///
/// The single-op and composed spellings differ, deliberately and measurably:
/// the composed one is fully parenthesized so precedence can never reshape the
/// tree the spec parser reconstructs (probe_f pins `((p0 + p1) * p0)`), while
/// the single-op one has nothing to reshape. Both take ONLY side B's reading.
pub(crate) fn render_arith_single_op(
    op: ArithBinOp,
    left: ArithOperand,
    right: ArithOperand,
) -> Result<String, RowMiss> {
    let mut out = String::new();
    render_arith_operand_into(left, &mut out)?;
    out.push(' ');
    out.push_str(operator_token(op)?);
    out.push(' ');
    render_arith_operand_into(right, &mut out)?;
    Ok(out)
}

fn render_arith_tree_into(expr: &ArithExpr, out: &mut String) -> Result<(), RowMiss> {
    match expr {
        ArithExpr::Operand(operand) => render_arith_operand_into(*operand, out),
        ArithExpr::Bin { op, left, right } => {
            out.push('(');
            render_arith_tree_into(left, out)?;
            out.push(' ');
            let token = operator_token(*op)?;
            out.push_str(token);
            out.push(' ');
            render_arith_tree_into(right, out)?;
            out.push(')');
            Ok(())
        }
    }
}

/// The `clean_island::admit_function_into` rendering of a recognized composed
/// tree: FULLY PARENTHESIZED, one row selected per node. Recursion depth is the
/// tree depth, bounded by `COMPOSED_MAX_OPS` through the structural plan match.
pub(crate) fn render_arith_tree(expr: &ArithExpr) -> Result<String, RowMiss> {
    let mut out = String::new();
    render_arith_tree_into(expr, &mut out)?;
    Ok(out)
}

#[cfg(test)]
mod tests {
    //! The descent's own coverage: that lifting the operator vocabulary into
    //! the table did not move a single character of the two renderings the
    //! probes pin.

    use super::{
        ArithBinOp, ArithExpr, ArithOperand, RecCall, render_arith_single_op, render_arith_tree,
    };

    fn bin(op: ArithBinOp, left: ArithExpr, right: ArithExpr) -> ArithExpr {
        ArithExpr::Bin { op, left: Box::new(left), right: Box::new(right) }
    }

    fn param(index: usize) -> ArithExpr {
        ArithExpr::Operand(ArithOperand::Param(index))
    }

    #[test]
    fn the_single_op_rendering_is_unparenthesised_and_positional() {
        let rendered =
            render_arith_single_op(ArithBinOp::Add, ArithOperand::Param(0), ArithOperand::Param(1))
                .expect("the row exists");
        assert_eq!(rendered, "p0 + p1");
    }

    #[test]
    fn the_single_op_rendering_carries_a_raw_literal() {
        let rendered =
            render_arith_single_op(ArithBinOp::Sub, ArithOperand::Param(0), ArithOperand::Const(1))
                .expect("the row exists");
        assert_eq!(rendered, "p0 - 1");
    }

    /// `probe_f`'s exact spelling. If lifting the operator table changed
    /// precedence handling this is where it shows.
    #[test]
    fn the_composed_rendering_is_fully_parenthesised() {
        let tree = bin(ArithBinOp::Mul, bin(ArithBinOp::Add, param(0), param(1)), param(0));
        assert_eq!(render_arith_tree(&tree).expect("the rows exist"), "((p0 + p1) * p0)");
    }

    #[test]
    fn every_operator_renders_through_its_own_row() {
        for (op, token) in [(ArithBinOp::Add, "+"), (ArithBinOp::Sub, "-"), (ArithBinOp::Mul, "*")]
        {
            let rendered = render_arith_tree(&bin(op, param(0), param(1))).expect("rows exist");
            assert_eq!(rendered, format!("(p0 {token} p1)"));
        }
    }

    /// **H-F, the reflector's half: the descent is TOTAL over the product of
    /// the node vocabulary and the site vocabulary.**
    ///
    /// One general descent replacing five per-shape recognizer arms is only an
    /// improvement if it cannot fall through. Every `(node, site)` pair must
    /// either render or produce a NAMED refusal that says which position it is
    /// about and which declaration — never a panic, never a silent `Ok` of a
    /// term nobody intended. The pairs that must REFUSE are the arm-confinement
    /// facts the two producers each state separately: the recursive result and
    /// the predecessor exist only in the non-zero arm.
    #[test]
    fn the_descent_is_total_over_every_node_at_every_site() {
        use std::collections::BTreeSet;

        use super::{RecBodyExpr, RecFamily, Site, render_rec_node};

        let nodes = [
            RecBodyExpr::Rec,
            RecBodyExpr::Pred,
            RecBodyExpr::Decreasing,
            RecBodyExpr::NatConst(7),
            RecBodyExpr::Add(Box::new(RecBodyExpr::Decreasing), Box::new(RecBodyExpr::Rec)),
        ];
        let lanes = [
            (RecFamily::Structural, Site::RecZero, false),
            (RecFamily::Structural, Site::RecSuccValue, true),
            (RecFamily::Structural, Site::RecSuccArg, false),
            (RecFamily::WellFounded, Site::WfZero, false),
            (RecFamily::WellFounded, Site::WfNonzero, true),
            (RecFamily::WellFounded, Site::WfRecArg, false),
        ];

        let mut refused = 0usize;
        for node in &nodes {
            for &(family, site, arm_binds_recursion) in &lanes {
                let mut named = BTreeSet::new();
                let outcome =
                    render_rec_node(family, "probe", node, site, RecCall::unary(&RecBodyExpr::Pred), &mut named);
                let reads_recursion = node.contains(&RecBodyExpr::Rec);
                let reads_predecessor = node.contains(&RecBodyExpr::Pred);
                let zero_arm = matches!(site, Site::RecZero | Site::WfZero);
                let must_refuse =
                    (reads_recursion && !arm_binds_recursion) || (reads_predecessor && zero_arm);

                match outcome {
                    Ok(_) => assert!(
                        !must_refuse,
                        "{node:?} at {} rendered, but that arm has no reading for it",
                        site.position()
                    ),
                    Err(detail) => {
                        assert!(
                            must_refuse,
                            "{node:?} at {} must render: {detail}",
                            site.position()
                        );
                        assert!(
                            detail.contains(site.position()),
                            "a refusal must name the position it is about: {detail}"
                        );
                        assert!(
                            detail.contains("`probe`"),
                            "a refusal must name the declaration it is about: {detail}"
                        );
                        assert!(
                            detail.contains("report it"),
                            "a producer-chain defect must say so (v7/D3): {detail}"
                        );
                        refused += 1;
                    }
                }
            }
        }
        // EXACTLY ten, counted rather than bounded so a rendering that quietly
        // starts accepting an out-of-arm node is a failure, not a looser pass:
        // `Rec` and the `Add` that contains it each refuse at the four sites
        // that do not bind the recursion (8), and `Pred` refuses at the two
        // zero arms (2).
        assert_eq!(
            refused, 10,
            "the arm-confinement refusals must fire exactly where the two producers each say \
             they do; a different count means the descent's arm confinement moved"
        );
    }

    /// Every constant the descent can name must be recorded, so the
    /// demand-driven environment preflight in each producer sees exactly what
    /// the term needs — never more (which would over-reject) and never less
    /// (which would surface as an opaque kernel refusal about a term nobody
    /// wrote).
    #[test]
    fn every_named_constant_is_recorded_for_the_preflight() {
        use std::collections::BTreeSet;

        use super::{RecBodyExpr, RecFamily, Site, render_rec_node};

        let mut named = BTreeSet::new();
        render_rec_node(
            RecFamily::Structural,
            "probe",
            &RecBodyExpr::Add(Box::new(RecBodyExpr::Decreasing), Box::new(RecBodyExpr::Pred)),
            Site::RecSuccValue,
            RecCall::unary(&RecBodyExpr::Pred),
            &mut named,
        )
        .expect("an in-fragment succ value renders");
        assert!(named.contains("Nat.add"), "the `+` row's constant must be recorded: {named:?}");
        assert!(named.contains("Nat.sub"), "the predecessor row's constant must be recorded");
        assert!(named.contains("Nat.succ"), "the case substitution's constructor must be recorded");

        // A body with no `Add` must NOT demand `Nat.add`: the preflight is
        // demand-driven, and over-demanding refuses environments a body does
        // not need.
        let mut lean = BTreeSet::new();
        let _ = render_rec_node(
            RecFamily::Structural,
            "probe",
            &RecBodyExpr::NatConst(0),
            Site::RecZero,
            RecCall::unary(&RecBodyExpr::Pred),
            &mut lean,
        )
        .expect("a literal zero case renders");
        assert!(lean.is_empty(), "a bare literal names no constant at all: {lean:?}");
    }
}
