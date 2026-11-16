//! Trust (D1 increment 0, 2026-09-23): ERROR TRANSPARENCY (ET) of a user
//! formatting impl, required at every formatting sink that panics on `Err`.
//!
//! ## The false accept this closes (F1), measured on stage-1 `de437e35d`
//!
//! ```text
//! impl fmt::Display for E { fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result { Err(fmt::Error) } }
//! ```
//!
//! This impl is PANIC-FREE, so it passed the shared evidence bar
//! (`dyn_dispatch_reliance::dyn_target_is_verified_panic_free`) that the packer
//! gate's verified-impl fallback (`fmt_trait_impl_is_verified_panic_free`,
//! added by `618a1910e7`) and the `to_string` arm read. Every one of these then
//! built rc=0 on the default lane and exited 101 at runtime:
//!
//! | program                              | runtime panic site                     |
//! |--------------------------------------|----------------------------------------|
//! | `println!("{}", E)`                  | `std/src/io/mod.rs:636`                |
//! | `format!("{}", E)`                   | `alloc/src/fmt.rs:655`                 |
//! | `E.to_string()`                      | `alloc/src/string.rs:2943`             |
//! | `fn main() -> Result<(), E> { Err(E) }` (a `Debug` twin) | `io/mod.rs:636` via `Termination::report` |
//!
//! The println/format/to_string runs carried an advisory whose note said the
//! `_print` panic "can dispatch into no user code" — false for this program:
//! the panic is std's own `expect`-style reaction to a user formatter that
//! returned `Err` while its writer did not fail. The `Termination` run carried
//! no row at all (a local `E` does not reach FOREIGN user code, so the entry
//! row never minted).
//!
//! ## What ET means, and why panic-freedom does not imply it
//!
//! std's formatting sinks assume a formatter returns `Err` ONLY when its writer
//! (or a nested formatter) did. `io::Write::write_fmt`, `alloc::fmt::format`
//! and `<T as ToString>::to_string` each check that and PANIC otherwise. So a
//! sink that panics on `Err` is panic-free only if every formatter it drives is
//! (a) panic-free and (b) error-transparent. The shared bar decides (a); this
//! module decides (b). The shared bar is deliberately NOT changed: its other
//! consumers (Φ's per-impl discharge, the C-FLOW case split, the `write_fmt`
//! reduction, the drop-glue premise) do not panic on a returned `Err`.
//!
//! ## Refusal-only
//!
//! Every use of this module is a new CONJUNCT on an existing acceptance
//! predicate, or a new standalone refusal. Nothing here is ever OR-ed into an
//! acceptance, an excusal, or a tolerance, and nothing here marks any row
//! proved. If ET is wrong in the permissive direction the result is the
//! pre-existing behaviour; if it is wrong in the strict direction the result is
//! over-refusal.
//!
//! ## Version 0 of the recognizer: "every return value is `Ok(())`"
//!
//! An impl is ET here only if every value that can reach its return place is
//! the `Result::Ok` variant, read off the impl's own optimized MIR:
//! * each write of `_0` is a whole-place `Assign` of the `Ok` aggregate, of a
//!   constant that const-eval destructures to the `Ok` variant, or of a
//!   copy/move of a non-argument local every one of whose writes satisfies the
//!   same rule (bounded chase, cycles refused);
//! * no tracked local is borrowed or address-taken (a pointer could write it),
//!   written through a projection, `SetDiscriminant`ed, a call destination, an
//!   asm output, or `Deinit`ed;
//! * the body has no `TailCall` (a `become` returns the callee's result without
//!   writing `_0`).
//!
//! Anything else — including every writer-forwarding impl
//! (`f.write_str(..)`, `write!(f, ..)`, `?`) — is NOT ET under version 0. That
//! refuses nothing new in practice: such impls fail the shared bar today on
//! their writer rows. The writer-relative increments widen the recognizer, not
//! this conjunct.
//!
//! ## Version 1 (D1 increment 1, 2026-09-25): writer-forwarding sources
//!
//! Increment 1 admits impls whose only unproved edges are their writer
//! (`fmt_writer_relative`), so the recognizer now also accepts, as a write of a
//! tracked `Result` local (every write must still be one of these):
//! * the DESTINATION of a call to core's `Formatter::write_str` (inherent) or
//!   `<Formatter as fmt::Write>::{write_str, write_char}` — each returns exactly
//!   `self.buf.write_str(..)` / `self.buf.write_char(..)` (`core/src/fmt/mod.rs`,
//!   premise P2 in docs/TCB.md) — whose receiver is the body's OWN `&mut
//!   Formatter` parameter, PINNED (never reassigned, never borrowed as a whole,
//!   never written through), directly or through one reborrow local;
//! * an `Err` — a literal/aggregate, or core's `from_residual` with both error
//!   types `fmt::Error` (so the reflexive `From` is core's) — ONLY in a block every
//!   predecessor of which is a `switchInt` over the discriminant of a transparent
//!   `Result` (reaching the block on `Err` only) or of core's `Try::branch` of one
//!   (on `Break` only). That is `?` at `-O0` (`from_residual`) and at `-O2` (the
//!   inlined `const Err`). The residual is a ZST folded to a constant, so the
//!   SHAPE alone cannot tell `?` from a spontaneous `Err` — the control flow is
//!   the evidence, and `f.write_str("x")?; Err(fmt::Error)` is refused because
//!   its `Err` sits on the `Continue`/`Ok` edge.
//! `write_fmt` and every other `Formatter` method stay unrecognized.
//!
//! ## Version 2 (D1 increment 2, 2026-09-25): `#[derive(Debug)]`'s helpers
//!
//! Also accepted, as a write of a tracked `Result` local: the destination of a
//! call to one of core's inherent `Formatter::debug_{tuple,struct}_field{1..5}_
//! finish` / `debug_{tuple,struct}_fields_finish` (what the derive expands to)
//! whose receiver is the pinned formatter parameter — AND only when every LOCAL
//! formatting impl this body's admitted nested-formatter edges can reach is
//! error-transparent itself (read off the writer-relative facts its bundle
//! recorded; recursion is guarded, and re-entry refuses). Each helper returns the
//! builder's `result`, which is `Err` only when a `write_str` on the receiver —
//! or on core's `PadAdapter` over it (`{:#?}`), which forwards its inner writer's
//! `Err` — or a nested value's `fmt` returned `Err` (`core/src/fmt/builders.rs`,
//! premise P2). The other admitted nested targets — core's `&T` forwarding impl
//! and sysroot impls at foundational types — are transparent by premise P1.
//! A hand-written builder chain (`f.debug_tuple(..).field(..).finish()`) is NOT
//! recognized: the `DebugTuple` methods are not in this list.
//!
//! FAIL-CLOSED on: a non-`Item` instance (shim, virtual), a NON-LOCAL def that
//! this compilation does not re-derive (a foreign instance may have no MIR, and
//! an undeclared dependency's MIR is not the verdict authority here; a declared
//! one with encoded MIR is read under the same recognizer since D4-A — see
//! `foreign_rederivation`), a def with no MIR, a body whose MIR query would
//! cycle, and a return type that is not `Result`.

use rustc_attr_ir::lang_items::LangItem;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    AggregateKind, BasicBlock, Body, BorrowKind, Const, Local, Location, Operand, Place,
    ProjectionElem, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;
use rustc_span::sym;

use super::{
    PreparedDiagnostic, PreparedDiagnosticChild, PreparedLocatedDiagnostic, dyn_dispatch_reliance,
    fmt_termination_dyn,
};

/// How many local-to-local copies the return-value chase follows before it
/// gives up (fail-closed). Version 0 only ever needs one (`_0 = copy _3`).
const MAX_CHASE_DEPTH: usize = 8;

/// How many `Result<Result<.., E2>, E1>` layers the entry `Termination` check
/// peels before failing closed.
const MAX_TERMINATION_NESTING: usize = 8;

/// Is this formatting-impl instance ERROR-TRANSPARENT — can it return `Err` only
/// when its own `Formatter`'s writer did? See the module docs (recognizer
/// version 1). `false` is the fail-closed answer for every shape not recognized.
pub(super) fn impl_is_error_transparent<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> bool {
    let ty::InstanceKind::Item(def_id) = instance.def else {
        return false;
    };
    item_is_error_transparent(tcx, def_id)
}

thread_local! {
    /// Trust (D1 increment 2): formatting impls whose error transparency is being
    /// decided up this thread's stack. Version 2 recurses into the local impls a
    /// nested-formatter edge can reach; re-entry REFUSES (a cycle of formatters
    /// is not shown transparent by assuming it).
    static ERROR_TRANSPARENCY_IN_PROGRESS: std::cell::RefCell<FxHashSet<DefId>> =
        std::cell::RefCell::new(FxHashSet::default());
}

/// [`impl_is_error_transparent`] for an `InstanceKind::Item` — the recognizer
/// only ever reads the item's own MIR, so the instance's arguments never
/// mattered. Guarded against re-entry (see `ERROR_TRANSPARENCY_IN_PROGRESS`).
fn item_is_error_transparent(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !ERROR_TRANSPARENCY_IN_PROGRESS.with(|set| set.borrow_mut().insert(def_id)) {
        return false;
    }
    let verdict = item_is_error_transparent_inner(tcx, def_id);
    ERROR_TRANSPARENCY_IN_PROGRESS.with(|set| {
        set.borrow_mut().remove(&def_id);
    });
    verdict
}

fn item_is_error_transparent_inner(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    // A foreign instance: its MIR may be absent (no `-Zalways-encode-mir`), and
    // even when present it is not what this crate's verdicts are about — UNLESS
    // (D4-A, 2026-09-24) it is a declared dependency body this compilation
    // re-derives, in which case the SAME recognizer reads its encoded MIR and
    // must still find only `Ok(())`. The foreign arm never relaxes the rule; it
    // only lets it run (`xcrate_fmt_dep.rs`, revision `err_dep`).
    if !super::foreign_rederivation::body_is_local_or_rederivable(tcx, def_id)
        || !tcx.is_mir_available(def_id)
    {
        return false;
    }
    if super::optimized_mir_query_would_cycle(tcx, def_id) {
        return false;
    }
    let lang_items = tcx.lang_items();
    let (Some(ok_variant), Some(err_variant)) =
        (lang_items.get(LangItem::ResultOk), lang_items.get(LangItem::ResultErr))
    else {
        return false;
    };
    let body = tcx.instance_mir(ty::InstanceKind::Item(def_id));
    body_is_error_transparent(tcx, body, ok_variant, err_variant)
}

fn body_is_error_transparent<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    ok_variant: DefId,
    err_variant: DefId,
) -> bool {
    let ty::Adt(ret_adt, _) = body.return_ty().kind() else {
        return false;
    };
    if !tcx.is_diagnostic_item(sym::Result, ret_adt.did()) {
        return false;
    }
    if body
        .basic_blocks
        .iter()
        .any(|bb| matches!(bb.terminator().kind, TerminatorKind::TailCall { .. }))
    {
        return false;
    }
    // Trust (D1 increment 1, version 1): the body's own `&mut Formatter` parameter,
    // usable as a writer-forwarding receiver only when it is PINNED — never
    // reassigned, never borrowed as a whole, never written through.
    let formatter_param = body
        .args_iter()
        .find(|&local| {
            dyn_dispatch_reliance::ty_is_mut_ref_to_formatter(tcx, body.local_decls[local].ty)
        })
        .filter(|&local| formatter_param_is_pinned(body, local));
    let mut chase = TransparencyChase {
        tcx,
        body,
        ok_variant,
        err_variant,
        formatter_param,
        done: FxHashMap::default(),
        in_progress: FxHashSet::default(),
        nested_formatters_transparent: None,
    };
    chase.local_is_transparent(RETURN_PLACE, 0)
}

/// Is the formatter parameter `param` PINNED: every use of it a read, a move, or
/// a REBORROW of its pointee (`&mut (*f)` / `&(*f)`)? Refused: any write to the
/// parameter itself, any write THROUGH it (`*f = ..`, which would replace the
/// whole `Formatter` and with it the writer), a borrow of the reference itself
/// (`&mut f`, which could re-point it), and any raw borrow.
fn formatter_param_is_pinned<'tcx>(body: &Body<'tcx>, param: Local) -> bool {
    let mut uses = PlaceUses { local: param, uses: Vec::new() };
    uses.visit_body(body);
    uses.uses.iter().all(|(place, context, _)| match context {
        PlaceContext::NonUse(_) => true,
        PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow) => false,
        PlaceContext::NonMutatingUse(
            NonMutatingUseContext::SharedBorrow | NonMutatingUseContext::FakeBorrow,
        ) => !place.projection.is_empty(),
        PlaceContext::NonMutatingUse(_) => true,
        PlaceContext::MutatingUse(MutatingUseContext::Borrow) => {
            matches!(&place.projection[..], [ProjectionElem::Deref])
        }
        PlaceContext::MutatingUse(_) => false,
    })
}

/// Is `callee` (called with `args`) a core `Formatter` method that returns
/// EXACTLY its writer's result — `Formatter::write_str` (inherent, `self.buf.
/// write_str(data)`, `core/src/fmt/mod.rs`) or `<Formatter as fmt::Write>::
/// {write_str, write_char}` (`self.buf.write_str(s)` / `self.buf.write_char(c)`)?
/// That is premise P2 of docs/TCB.md "Formatting premises". `write_fmt` and every
/// other method are deliberately NOT here: they drive nested formatters.
pub(super) fn callee_forwards_to_formatter_writer<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    generic_args: ty::GenericArgs<'tcx>,
) -> bool {
    if !super::crate_is_authentic_core(tcx, callee.krate) {
        return false;
    }
    let Some(name) = tcx.opt_item_name(callee) else {
        return false;
    };
    let is_write_str = name == sym::write_str;
    let is_write_char = name.as_str() == "write_char";
    let is_formatter = |ty: Ty<'tcx>| match ty.kind() {
        ty::Adt(adt, _) => tcx.is_diagnostic_item(sym::Formatter, adt.did()),
        _ => false,
    };
    // (a) the inherent `Formatter::write_str`.
    if let Some(impl_did) = tcx.inherent_impl_of_assoc(callee) {
        let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_normalization();
        return is_write_str && is_formatter(self_ty);
    }
    // (b) `fmt::Write::{write_str, write_char}`, named through the TRAIT method with
    // `Self = Formatter` (how MIR spells it) or through core's impl item itself.
    let (trait_did, self_ty) = if let Some(trait_did) = tcx.trait_of_assoc(callee) {
        let Some(self_ty) = generic_args.types().next() else {
            return false;
        };
        (trait_did, self_ty)
    } else if let Some(impl_did) = tcx.trait_impl_of_assoc(callee) {
        let trait_ref = tcx.impl_trait_ref(impl_did).instantiate_identity().skip_normalization();
        (trait_ref.def_id, trait_ref.self_ty())
    } else {
        return false;
    };
    tcx.is_diagnostic_item(sym::FmtWrite, trait_did)
        && (is_write_str || is_write_char)
        && is_formatter(self_ty)
}

/// Trust (D1 increment 2, version 2): is `callee` one of core's inherent
/// `Formatter` helpers that `#[derive(Debug)]` expands to —
/// `debug_{tuple,struct}_field{1..5}_finish` and `debug_{tuple,struct}_fields_finish`
/// (`core/src/fmt/mod.rs`)? Each builds a `DebugTuple`/`DebugStruct` over the
/// receiver, adds each value with `field`, and returns `finish()`, i.e. the
/// builder's `result`: `Err` only when a `write_str` on the receiver (or on the
/// `PadAdapter` over it, `{:#?}`) or a nested value's `fmt` returned `Err`
/// (`core/src/fmt/builders.rs`, premise P2). Authenticated by crate and by the
/// inherent impl's self type being `Formatter`; the name only disambiguates
/// within authentic core. The nested half is the caller's conjunct.
fn callee_is_debug_builder_helper(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if !super::crate_is_authentic_core(tcx, callee.krate) {
        return false;
    }
    let Some(impl_did) = tcx.inherent_impl_of_assoc(callee) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_normalization();
    let is_formatter = matches!(
        self_ty.kind(),
        ty::Adt(adt, _) if tcx.is_diagnostic_item(sym::Formatter, adt.did())
    );
    is_formatter
        && tcx.opt_item_name(callee).is_some_and(|name| {
            matches!(
                name.as_str(),
                // Trust (mini-port 4c46afa): upstream removed the
                // `debug_tuple_*_finish` helpers; derived `Debug` now
                // routes tuple structs through these struct helpers.
                "debug_struct_field1_finish"
                    | "debug_struct_field2_finish"
                    | "debug_struct_field3_finish"
                    | "debug_struct_field4_finish"
                    | "debug_struct_field5_finish"
                    | "debug_struct_fields_finish"
            )
        })
}

/// Is `callee` core's `<Result<_, fmt::Error> as FromResidual<Result<Infallible,
/// fmt::Error>>>::from_residual` — the `?` desugar's error path, which returns
/// `Err(From::from(e))`, i.e. `Err(e)` through core's reflexive `From`?
fn callee_is_fmt_error_from_residual<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    generic_args: ty::GenericArgs<'tcx>,
) -> bool {
    if tcx.lang_items().get(LangItem::TryTraitFromResidual) != Some(callee) {
        return false;
    }
    let mut types = generic_args.types();
    let (Some(self_ty), Some(residual_ty), None) = (types.next(), types.next(), types.next())
    else {
        return false;
    };
    let result_with_fmt_error = |ty: Ty<'tcx>| match ty.kind() {
        ty::Adt(adt, args) => {
            tcx.is_diagnostic_item(sym::Result, adt.did())
                && args.len() == 2
                && fmt_termination_dyn::ty_is_core_fmt_error(tcx, args.type_at(1))
        }
        _ => false,
    };
    // Both error types are core's `fmt::Error`, so the `From::from` the impl applies
    // is core's reflexive `impl<T> From<T> for T` — never a user conversion.
    result_with_fmt_error(self_ty)
        && result_with_fmt_error(residual_ty)
        && matches!(
            (self_ty.kind(), residual_ty.kind()),
            (ty::Adt(_, self_args), ty::Adt(_, residual_args))
                if self_args.type_at(1) == residual_args.type_at(1)
        )
}

struct TransparencyChase<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    ok_variant: DefId,
    err_variant: DefId,
    formatter_param: Option<Local>,
    done: FxHashMap<Local, bool>,
    in_progress: FxHashSet<Local>,
    /// Trust (D1 increment 2): the cached answer of
    /// [`TransparencyChase::nested_formatters_are_transparent`].
    nested_formatters_transparent: Option<bool>,
}

impl<'a, 'tcx> TransparencyChase<'a, 'tcx> {
    /// Does every value that can be stored in `local` satisfy "`Err` only when the
    /// formatter's writer returned `Err`"? (For a `Result`: an `Ok`, a writer's own
    /// result, or an `Err` reached only on the failure edge of such a result.)
    fn local_is_transparent(&mut self, local: Local, depth: usize) -> bool {
        if depth > MAX_CHASE_DEPTH {
            return false;
        }
        if let Some(&known) = self.done.get(&local) {
            return known;
        }
        // A cycle of copies is refused rather than solved coinductively.
        if !self.in_progress.insert(local) {
            return false;
        }
        let verdict = self.compute(local, depth);
        self.in_progress.remove(&local);
        self.done.insert(local, verdict);
        verdict
    }

    fn compute(&mut self, local: Local, depth: usize) -> bool {
        // An argument's value is written by the caller, not by this body.
        if local != RETURN_PLACE && local.as_usize() <= self.body.arg_count {
            return false;
        }
        let mut uses = PlaceUses { local, uses: Vec::new() };
        uses.visit_body(self.body);
        let mut saw_write = false;
        for (place, context, location) in uses.uses {
            match context {
                PlaceContext::NonUse(_) => {}
                // Reading the value is harmless. Any borrow or address-of could
                // later write the local through a pointer: refuse outright.
                PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::SharedBorrow
                    | NonMutatingUseContext::FakeBorrow
                    | NonMutatingUseContext::RawBorrow,
                ) => return false,
                PlaceContext::NonMutatingUse(_) => {}
                PlaceContext::MutatingUse(MutatingUseContext::Store)
                    if place.projection.is_empty() =>
                {
                    let Some(rvalue) = self.assigned_rvalue(local, location) else {
                        return false;
                    };
                    if !self.rvalue_is_transparent(rvalue, location.block, depth) {
                        return false;
                    }
                    saw_write = true;
                }
                // Trust (version 1): a whole-place CALL destination — a writer's own
                // result, or the `?` desugar's `from_residual` on a failure edge.
                PlaceContext::MutatingUse(MutatingUseContext::Call)
                    if place.projection.is_empty() =>
                {
                    if !self.call_result_is_transparent(local, location, depth) {
                        return false;
                    }
                    saw_write = true;
                }
                // Projection writes, asm outputs, `SetDiscriminant`, `Deinit`,
                // drops, retags, mutable borrows.
                PlaceContext::MutatingUse(_) => return false,
            }
        }
        // A never-written return place means no normal return was recognized:
        // over-refuse rather than reason about divergence.
        saw_write
    }

    /// The rvalue of the whole-place `Assign` to `local` at `location`, or
    /// `None` when the write there is any other statement.
    fn assigned_rvalue(&self, local: Local, location: Location) -> Option<&'a Rvalue<'tcx>> {
        let block = &self.body.basic_blocks[location.block];
        let statement = block.statements.get(location.statement_index)?;
        let StatementKind::Assign(assign) = &statement.kind else {
            return None;
        };
        let (lhs, rvalue) = &**assign;
        (lhs.local == local && lhs.projection.is_empty()).then_some(rvalue)
    }

    fn rvalue_is_transparent(
        &mut self,
        rvalue: &Rvalue<'tcx>,
        block: BasicBlock,
        depth: usize,
    ) -> bool {
        match rvalue {
            Rvalue::Use(Operand::Constant(constant), _) => {
                match self.const_result_variant(&constant.const_) {
                    Some(variant) if variant == self.ok_variant => true,
                    // An `Err` literal is transparent only where it can run solely
                    // after some transparent result was observed to be an error.
                    Some(variant) if variant == self.err_variant => {
                        self.block_is_failure_edge(block, depth)
                    }
                    _ => false,
                }
            }
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
                if place.projection.is_empty() =>
            {
                self.local_is_transparent(place.local, depth + 1)
            }
            Rvalue::Aggregate(kind, _) => match **kind {
                AggregateKind::Adt(adt_did, variant, ..) => {
                    if !self.tcx.is_diagnostic_item(sym::Result, adt_did) {
                        return false;
                    }
                    let variant_did = self.tcx.adt_def(adt_did).variant(variant).def_id;
                    if variant_did == self.ok_variant {
                        true
                    } else if variant_did == self.err_variant {
                        self.block_is_failure_edge(block, depth)
                    } else {
                        false
                    }
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// The `Result` variant an EVALUATED `Result` constant holds. Unevaluated and
    /// type-system constants fail closed (over-refusal only).
    fn const_result_variant(&self, constant: &Const<'tcx>) -> Option<DefId> {
        let Const::Val(value, ty) = *constant else {
            return None;
        };
        let ty::Adt(adt, _) = ty.kind() else {
            return None;
        };
        if !self.tcx.is_diagnostic_item(sym::Result, adt.did()) || ty.has_non_region_param() {
            return None;
        }
        let destructured = self.tcx.try_destructure_mir_constant_for_user_output(value, ty)?;
        destructured.variant.map(|variant| adt.variant(variant).def_id)
    }

    /// Trust (version 1): the call whose destination is `local` at `location`.
    fn call_result_is_transparent(
        &mut self,
        local: Local,
        location: Location,
        depth: usize,
    ) -> bool {
        let body: &'a Body<'tcx> = self.body;
        let data = &body.basic_blocks[location.block];
        if location.statement_index != data.statements.len() {
            return false;
        }
        let TerminatorKind::Call { func, args, destination, .. } = &data.terminator().kind else {
            return false;
        };
        if destination.local != local || !destination.projection.is_empty() {
            return false;
        }
        let Some((callee, generic_args)) = func.const_fn_def() else {
            return false;
        };
        if callee_forwards_to_formatter_writer(self.tcx, callee, generic_args) {
            return args.first().is_some_and(|arg| self.operand_is_root_formatter(&arg.node));
        }
        if callee_is_fmt_error_from_residual(self.tcx, callee, generic_args) {
            return self.block_is_failure_edge(location.block, depth);
        }
        // Trust (D1 increment 2, version 2): a `derive(Debug)` builder helper on
        // the pinned formatter, when every nested formatter it can drive is
        // transparent too.
        if callee_is_debug_builder_helper(self.tcx, callee) {
            return args.first().is_some_and(|arg| self.operand_is_root_formatter(&arg.node))
                && self.nested_formatters_are_transparent();
        }
        false
    }

    /// Trust (D1 increment 2, version 2): is every LOCAL formatting impl this
    /// body's admitted nested-formatter edges can reach error-transparent itself?
    /// Read off the writer-relative facts its bundle recorded
    /// (`fmt_writer_relative::recorded_nested_local_targets`); no recorded facts
    /// answers `false`. The other admitted target kinds — core's `&T` forwarding
    /// impl and a sysroot impl at a foundational type — are transparent by
    /// premise P1 (docs/TCB.md "Formatting premises").
    fn nested_formatters_are_transparent(&mut self) -> bool {
        if let Some(known) = self.nested_formatters_transparent {
            return known;
        }
        let root = self.body.source.def_id();
        let verdict =
            super::fmt_writer_relative::recorded_nested_local_targets(self.tcx.sess, root)
                .is_some_and(|targets| {
                    targets.iter().all(|&target| item_is_error_transparent(self.tcx, target))
                });
        self.nested_formatters_transparent = Some(verdict);
        verdict
    }

    /// Is `operand` the body's own pinned `&mut Formatter` parameter — directly,
    /// or through ONE local that is a reborrow `&mut (*f)` or copy of it?
    fn operand_is_root_formatter(&self, operand: &Operand<'tcx>) -> bool {
        let Some(param) = self.formatter_param else {
            return false;
        };
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return false;
        };
        if !place.projection.is_empty() {
            return false;
        }
        place.local == param || self.local_is_reborrow_of(place.local, param)
    }

    /// `local` is written exactly once, as `&mut (*param)` or a copy/move of
    /// `param`, and is otherwise only read or moved.
    fn local_is_reborrow_of(&self, local: Local, param: Local) -> bool {
        if local == RETURN_PLACE || local.as_usize() <= self.body.arg_count {
            return false;
        }
        let mut uses = PlaceUses { local, uses: Vec::new() };
        uses.visit_body(self.body);
        let mut writes = 0usize;
        for (place, context, location) in uses.uses {
            match context {
                PlaceContext::NonUse(_) => {}
                PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::Copy | NonMutatingUseContext::Move,
                ) if place.projection.is_empty() => {}
                PlaceContext::MutatingUse(MutatingUseContext::Store)
                    if place.projection.is_empty() =>
                {
                    writes += 1;
                    let pinned_source = match self.assigned_rvalue(local, location) {
                        Some(Rvalue::Ref(_, BorrowKind::Mut { .. }, source)) => {
                            source.local == param
                                && matches!(&source.projection[..], [ProjectionElem::Deref])
                        }
                        Some(Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _)) => {
                            source.local == param && source.projection.is_empty()
                        }
                        _ => false,
                    };
                    if !pinned_source {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        writes == 1
    }

    /// Trust (version 1): is `block` reached ONLY along the failure edge of a
    /// `switchInt` over the discriminant of a transparent `Result` (`Err`) or of a
    /// `ControlFlow` produced by `Try::branch` of one (`Break`)? Then any `Err` it
    /// writes is the propagation of an error a writer returned (the `?` desugar,
    /// at `-O0` through `from_residual` and at `-O2` as an inlined `Err`
    /// constant). Every predecessor must be such a switch, `block` must be its
    /// target for the failure value only, and never its `otherwise`.
    fn block_is_failure_edge(&mut self, block: BasicBlock, depth: usize) -> bool {
        let body: &'a Body<'tcx> = self.body;
        let predecessors = &body.basic_blocks.predecessors()[block];
        if predecessors.is_empty() {
            return false;
        }
        for &pred in predecessors.iter() {
            let TerminatorKind::SwitchInt { discr, targets } =
                &body.basic_blocks[pred].terminator().kind
            else {
                return false;
            };
            let Some(discr_place) = discr.place() else {
                return false;
            };
            if !discr_place.projection.is_empty() {
                return false;
            }
            let Some(scrutinee) = self.discriminant_source(discr_place.local, pred) else {
                return false;
            };
            let Some(failure_value) = self.failure_discriminant(scrutinee, depth) else {
                return false;
            };
            if targets.otherwise() == block {
                return false;
            }
            let mut reached = false;
            for (value, target) in targets.iter() {
                if target == block {
                    if value != failure_value {
                        return false;
                    }
                    reached = true;
                }
            }
            if !reached {
                return false;
            }
        }
        true
    }

    /// The local `d` is written exactly once, in `block`, as `discriminant(x)` of a
    /// whole local `x`, and is otherwise only read: returns `x`.
    fn discriminant_source(&self, d: Local, block: BasicBlock) -> Option<Local> {
        if d == RETURN_PLACE || d.as_usize() <= self.body.arg_count {
            return None;
        }
        let mut uses = PlaceUses { local: d, uses: Vec::new() };
        uses.visit_body(self.body);
        let mut source = None;
        for (place, context, location) in uses.uses {
            match context {
                PlaceContext::NonUse(_) => {}
                PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::Copy
                    | NonMutatingUseContext::Move
                    | NonMutatingUseContext::Inspect,
                ) if place.projection.is_empty() => {}
                PlaceContext::MutatingUse(MutatingUseContext::Store)
                    if place.projection.is_empty() =>
                {
                    if source.is_some() || location.block != block {
                        return None;
                    }
                    let Rvalue::Discriminant(scrutinee) = self.assigned_rvalue(d, location)? else {
                        return None;
                    };
                    if !scrutinee.projection.is_empty() {
                        return None;
                    }
                    source = Some(scrutinee.local);
                }
                _ => return None,
            }
        }
        source
    }

    /// The switch value that means FAILURE for `scrutinee`: `Err`'s discriminant
    /// for a transparent `Result`, `Break`'s for a `ControlFlow` that is
    /// `Try::branch` of a transparent `Result`. `None` for anything else.
    fn failure_discriminant(&mut self, scrutinee: Local, depth: usize) -> Option<u128> {
        let ty::Adt(adt, _) = *self.body.local_decls[scrutinee].ty.kind() else {
            return None;
        };
        if self.tcx.is_diagnostic_item(sym::Result, adt.did()) {
            if !self.local_is_transparent(scrutinee, depth + 1) {
                return None;
            }
            let index = adt.variant_index_with_id(self.err_variant);
            return Some(adt.discriminant_for_variant(self.tcx, index).val);
        }
        let break_variant = self.tcx.lang_items().get(LangItem::ControlFlowBreak)?;
        if self.tcx.parent(break_variant) != adt.did() {
            return None;
        }
        if !self.control_flow_branches_a_transparent_result(scrutinee, depth + 1) {
            return None;
        }
        let index = adt.variant_index_with_id(break_variant);
        Some(adt.discriminant_for_variant(self.tcx, index).val)
    }

    /// `cf` is written exactly once, as the destination of core's `Try::branch` on
    /// a `Result`, whose argument is a whole transparent local; otherwise `cf` is
    /// only read (its discriminant, or a field of it).
    fn control_flow_branches_a_transparent_result(&mut self, cf: Local, depth: usize) -> bool {
        if depth > MAX_CHASE_DEPTH || cf == RETURN_PLACE || cf.as_usize() <= self.body.arg_count {
            return false;
        }
        let branch_fn = self.tcx.lang_items().get(LangItem::TryTraitBranch);
        let mut uses = PlaceUses { local: cf, uses: Vec::new() };
        uses.visit_body(self.body);
        let mut branched: Option<Local> = None;
        for (place, context, location) in uses.uses {
            match context {
                PlaceContext::NonUse(_) => {}
                PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::Copy
                    | NonMutatingUseContext::Move
                    | NonMutatingUseContext::Inspect
                    | NonMutatingUseContext::PlaceMention,
                ) => {}
                PlaceContext::MutatingUse(MutatingUseContext::Call)
                    if place.projection.is_empty() =>
                {
                    if branched.is_some() {
                        return false;
                    }
                    let data = &self.body.basic_blocks[location.block];
                    let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
                        return false;
                    };
                    let Some((callee, generic_args)) = func.const_fn_def() else {
                        return false;
                    };
                    if branch_fn != Some(callee) {
                        return false;
                    }
                    let self_is_result = generic_args.types().next().is_some_and(|self_ty| {
                        matches!(
                            self_ty.kind(),
                            ty::Adt(adt, _) if self.tcx.is_diagnostic_item(sym::Result, adt.did())
                        )
                    });
                    if !self_is_result || args.len() != 1 {
                        return false;
                    }
                    let (Operand::Copy(source) | Operand::Move(source)) = &args[0].node else {
                        return false;
                    };
                    if !source.projection.is_empty() {
                        return false;
                    }
                    branched = Some(source.local);
                }
                _ => return false,
            }
        }
        match branched {
            Some(result) => self.local_is_transparent(result, depth + 1),
            None => false,
        }
    }
}

/// Every place occurrence whose base local is `local`, with the ORIGINAL
/// context (overriding `visit_place` keeps a borrow of a projection visible as
/// a borrow, where `super_place` would rewrite it to `Projection`).
struct PlaceUses<'tcx> {
    local: Local,
    uses: Vec<(Place<'tcx>, PlaceContext, Location)>,
}

impl<'tcx> Visitor<'tcx> for PlaceUses<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if place.local == self.local {
            self.uses.push((*place, context, location));
        }
    }
}

/// Resolve `<ty as trait>::fmt` to a concrete instance, or `None`. The same
/// resolution `fmt_trait_impl_is_verified_panic_free` performs; used here ONLY
/// to name the refusal in a diagnostic, never to decide one.
fn resolve_fmt_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_def_id: DefId,
    formatted: Ty<'tcx>,
) -> Option<ty::Instance<'tcx>> {
    let method_def_id = tcx
        .associated_items(trait_def_id)
        .in_definition_order()
        .find(|item| item.opt_name() == Some(sym::fmt))
        .map(|item| item.def_id)?;
    let args = tcx.mk_args(&[formatted.into()]);
    if args.has_non_region_param() {
        return None;
    }
    let instance =
        ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), method_def_id, args)
            .ok()??;
    matches!(instance.def, ty::InstanceKind::Item(_)).then_some(instance)
}

/// DIAGNOSTIC ONLY: when a formatting sink in this body was refused and one of
/// the formatted types has an impl that is NOT error-transparent, the note that
/// names it. The refusal's own header speaks of panic-freedom; without this note
/// an impl that IS panic-free (`Err(fmt::Error)`) would be refused under a
/// message that reads as false. Decides nothing.
pub(super) fn error_opacity_note<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Option<String> {
    let display_trait = tcx.get_diagnostic_item(sym::Display);
    for bb in body.basic_blocks.iter() {
        let Some(terminator) = &bb.terminator else { continue };
        let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) =
            &terminator.kind
        else {
            continue;
        };
        let Some((def_id, generic_args)) = func.const_fn_def() else { continue };
        let trait_def_id = if super::is_fmt_rt_argument_packer(tcx, def_id) {
            super::fmt_packer_bound_trait(tcx, def_id)
        } else if super::callee_is_to_string_dispatch(tcx, def_id) {
            display_trait
        } else {
            None
        };
        let Some(trait_def_id) = trait_def_id else { continue };
        for ty in generic_args.types() {
            if super::ty_is_foundational_display(tcx, ty) {
                continue;
            }
            let Some(instance) = resolve_fmt_method(tcx, trait_def_id, ty) else { continue };
            // Trust (2026-09-25): a formatter that is THIS body, whose verification is
            // on this stack, or that sits in a recursion cycle was never examined — the
            // recognizer declines it rather than risk re-entering its `optimized_mir` —
            // so "not recognized as error-transparent" would be a false statement about
            // it. `formatting_cycle_note` names that edge instead.
            if formatter_verdict_is_declined(tcx, body, instance.def_id()) {
                continue;
            }
            if !super::foreign_rederivation::body_is_local_or_rederivable(tcx, instance.def_id())
                || impl_is_error_transparent(tcx, instance)
            {
                continue;
            }
            let label = with_no_trimmed_paths!(tcx.def_path_str(instance.def_id()));
            return Some(error_opacity_note_text(&label));
        }
    }
    None
}

/// Is `impl_def_id` the body being published, or one `optimized_mir_query_would_cycle`
/// answers for — its `optimized_mir` (and so its verification) is on this stack, or it
/// is a member of a static recursion cycle? Every verdict reader declines such a target
/// (`dyn_dispatch_reliance::target_admits_independent_verdict`: the self-discharge and
/// query-cycle conjuncts; `item_is_error_transparent_inner`: the query-cycle guard), so
/// a note must not describe it as examined.
fn formatter_verdict_is_declined(tcx: TyCtxt<'_>, body: &Body<'_>, impl_def_id: DefId) -> bool {
    impl_def_id == body.source.def_id() || super::optimized_mir_query_would_cycle(tcx, impl_def_id)
}

/// Trust (2026-09-25). DIAGNOSTIC ONLY — decides nothing. When a formatting sink in
/// this body was refused and a value it formats reaches a formatting impl that is
/// this very body, one whose verification is on this stack (the impls format each
/// other: `A` -> `B` -> `A`), or a member of a static recursion cycle, the note that
/// says which.
///
/// Such an edge is refused by construction: its verdict would have to be read while it
/// is still being decided, which is circular (and was, before the in-progress mark
/// covered publication, an E0391 query-cycle abort). Without this note the refusal
/// reads "panic-freedom was not established" about an impl whose verdict was never
/// asked for.
pub(super) fn formatting_cycle_note<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Option<String> {
    let display_trait = tcx.get_diagnostic_item(sym::Display);
    for bb in body.basic_blocks.iter() {
        let Some(terminator) = &bb.terminator else { continue };
        let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) =
            &terminator.kind
        else {
            continue;
        };
        let Some((def_id, generic_args)) = func.const_fn_def() else { continue };
        let trait_def_id = if super::is_fmt_rt_argument_packer(tcx, def_id) {
            super::fmt_packer_bound_trait(tcx, def_id)
        } else if super::callee_is_to_string_dispatch(tcx, def_id) {
            display_trait
        } else {
            None
        };
        let Some(trait_def_id) = trait_def_id else { continue };
        for ty in generic_args.types() {
            if super::ty_is_foundational_display(tcx, ty) {
                continue;
            }
            let Some(instance) = resolve_fmt_method(tcx, trait_def_id, ty) else { continue };
            let impl_def_id = instance.def_id();
            if !formatter_verdict_is_declined(tcx, body, impl_def_id) {
                continue;
            }
            let label = with_no_trimmed_paths!(tcx.def_path_str(impl_def_id));
            // Say WHICH reason declined it: the two oracle halves are different facts.
            let whose = if impl_def_id == body.source.def_id() {
                "is this very impl: it formats a value of its own type, so its verdict would \
                 rest on the one being decided here"
            } else if super::optimized_mir_verify_in_progress(impl_def_id) {
                "is being verified further up this stack: the formatting impls format each \
                 other, so its verdict would rest on the one being decided here"
            } else {
                "is a member of a recursion cycle: it and a function it calls reach each \
                 other"
            };
            return Some(format!(
                "recursive formatting: `{label}` {whose}. No verdict is read for that edge (it \
                 is refused, never assumed): recursion carries no termination or panic-freedom \
                 argument this verifier can check here"
            ));
        }
    }
    None
}

/// Trust (D4 increment A, 2026-09-24). DIAGNOSTIC ONLY: when a formatting sink in
/// this body was refused and one of the formatted types has a DEPENDENCY impl,
/// the note that says what happened to it — which re-derivation conjunct
/// declined it, or that it was re-derived here and what the shared bar said. A
/// dependency body's own verification never surfaces a diagnostic of its own,
/// so without this note every cross-crate refusal reads alike. Decides nothing,
/// and charges no re-derivation budget (`peek`).
pub(super) fn foreign_formatter_note<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Option<String> {
    let display_trait = tcx.get_diagnostic_item(sym::Display);
    for bb in body.basic_blocks.iter() {
        let Some(terminator) = &bb.terminator else { continue };
        let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) =
            &terminator.kind
        else {
            continue;
        };
        let Some((def_id, generic_args)) = func.const_fn_def() else { continue };
        let trait_def_id = if super::is_fmt_rt_argument_packer(tcx, def_id) {
            super::fmt_packer_bound_trait(tcx, def_id)
        } else if super::callee_is_to_string_dispatch(tcx, def_id) {
            display_trait
        } else {
            None
        };
        let Some(trait_def_id) = trait_def_id else { continue };
        for ty in generic_args.types() {
            if super::ty_is_foundational_display(tcx, ty) {
                continue;
            }
            let Some(instance) = resolve_fmt_method(tcx, trait_def_id, ty) else { continue };
            let impl_def_id = instance.def_id();
            if impl_def_id.is_local() {
                continue;
            }
            let label = with_no_trimmed_paths!(tcx.def_path_str(impl_def_id));
            if let Some(decline) =
                super::foreign_rederivation::peek_foreign_rederivation(tcx, impl_def_id)
            {
                return Some(format!(
                    "dependency impl `{label}` was not re-derived in this compilation: it {}",
                    decline.reason()
                ));
            }
            let verdict = super::dyn_dispatch_reliance::target_decline_reason(
                tcx,
                instance,
                body.source.def_id(),
            );
            return Some(format!(
                "dependency impl `{label}` was re-derived in this compilation from its crate's \
                 encoded MIR (no dependency verdict is ever read); the shared panic-freedom \
                 bar's answer for it: {verdict}"
            ));
        }
    }
    None
}

fn error_opacity_note_text(label: &str) -> String {
    format!(
        "error transparency: `{label}` is not recognized as returning `Err` only when its \
         `Formatter`'s writer did. std's formatting sinks (`println!`/`eprint!` through \
         `io::Write::write_fmt`, `format!`, `ToString::to_string`, and `main`'s \
         `Termination::report`) PANIC when a formatter returns `Err` while the writer did not \
         fail, so a panic-free impl is not enough there. This compiler currently recognizes \
         an impl as error-transparent only when every value it can return is `Ok(())`, the \
         result of its own `Formatter`'s `write_str`/`write_char`, an error such a call \
         returned (propagated by `?`), or the result of a `#[derive(Debug)]` helper whose \
         nested formatters are all transparent"
    )
}

/// Trust (D1 increment 0): the hidden `Termination` sink of `main`.
///
/// `lang_start` calls `<R as Termination>::report` on `main`'s return value;
/// for `R = Result<T, E>` that runs `io::attempt_print_to_stderr(format_args!(
/// "Error: {err:?}"))` → `io::Write::write_fmt`, which PANICS when `E`'s `Debug`
/// returns `Err` spontaneously (`std/src/io/mod.rs:636`). None of this is a
/// terminator in `main`'s MIR, so the packer gate never sees it.
///
/// Returns the offending error type when `main`'s return type — peeled through
/// nested `Result<Result<..>, _>` Ok-types — carries an `E` that is neither
/// foundational (P1: a sysroot impl at a `ty_is_foundational_display` type
/// returns `Err` only if its writer did) nor a formatting impl passing the
/// SAME predicate the packer arm reads (`fmt_trait_impl_is_verified_panic_free`:
/// the shared panic-freedom bar AND this module's ET).
///
/// `None` when this body is not the `EntryFnType::Main` entry or its return
/// type is not `Result`. An error type is skipped — deliberately — when it
/// reaches FOREIGN or DYNAMIC user code AND names no local definition
/// (`Box<dyn Error>`, `io::Error`, `dep::E`; never `E(io::Error)`, `Box<E>`,
/// `dep::W<E>`, and never decided for the whole return type at once): that
/// `Termination::report` dispatch is already published as its own
/// policy-B runtime-checked row by `entry_termination_dispatch_rows` (reported,
/// CONDITIONAL, fatal under `certify`), whose statement — the report dispatches
/// into code this compilation does not verify — covers an opaque `Err` from
/// that code as much as a panic in it. See the deviation note in the D1
/// increment-0 docs text.
pub(super) fn entry_termination_error_opaque_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Option<Ty<'tcx>> {
    let def_id = body.source.def_id();
    let Some((entry_def_id, rustc_session::config::EntryFnType::Main { .. })) = tcx.entry_fn(())
    else {
        return None;
    };
    if entry_def_id != def_id || body.source.promoted.is_some() {
        return None;
    }
    let typing_env = ty::TypingEnv::post_analysis(tcx, def_id);
    let ret_ty =
        tcx.normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(body.return_ty()));
    let Some(debug_trait) = tcx.get_diagnostic_item(sym::Debug) else {
        return Some(ret_ty);
    };
    // Trust (D1 increment 0 review, 2026-09-23): the deferral to the entry row is
    // decided PER ERROR TYPE, never for the whole return type. A whole-type early
    // return let a local `Err`-returning `Debug` through whenever ANY part of the
    // return type reached foreign code — measured on stage-1 `de437e35d`:
    // `struct E(io::Error)` with `Debug` returning `Err(fmt::Error)` and
    // `main -> Result<(), E>` built rc=0 and exited 101; `main ->
    // Result<Result<(), E>, io::Error>` (same `E`, no field) ICEd and, with X2
    // fixed, would have built rc=0 on the conditional row and exited 101. The
    // row's own statement ("a foreign or dynamic type this compilation does not
    // verify") is false for a `Debug` impl this crate owns.
    let mut memo: FxHashMap<Ty<'tcx>, bool> = FxHashMap::default();
    let mut current = ret_ty;
    for _ in 0..MAX_TERMINATION_NESTING {
        let ty::Adt(adt, args) = current.kind() else {
            return None;
        };
        if !tcx.is_diagnostic_item(sym::Result, adt.did()) {
            return None;
        }
        let err_ty = args.type_at(1);
        // DEFERRED to `entry_termination_dispatch_rows` only when this error type
        // reaches foreign/dynamic code AND names no local definition at all, so
        // (orphan rules) its `Debug` impl cannot be this crate's.
        let deferred_to_entry_row = error_layer_defers_to_entry_row(tcx, err_ty, &mut memo);
        if !deferred_to_entry_row
            && !super::ty_is_foundational_display(tcx, err_ty)
            && !super::fmt_trait_impl_is_verified_panic_free(tcx, body, debug_trait, err_ty)
        {
            return Some(err_ty);
        }
        current = args.type_at(0);
    }
    Some(current)
}

/// Is this `Result` error layer of `main`'s return type DEFERRED to the policy-B
/// entry row — it reaches foreign/dynamic code AND names no local definition?
/// Shared with `fmt_termination_dyn` (D1 residual, 2026-09-24), which holds the
/// LOCAL formatting code such a layer can dispatch into to the sink bar, so the
/// two can never disagree about which layers are deferred.
pub(super) fn error_layer_defers_to_entry_row<'tcx>(
    tcx: TyCtxt<'tcx>,
    err_ty: Ty<'tcx>,
    memo: &mut FxHashMap<Ty<'tcx>, bool>,
) -> bool {
    // Trust (IOERROR-PAYLOAD-1, 2026-10-27): withheld, as in
    // `entry_termination_dispatch_rows`, so the two still agree (`withheld`).
    !ty_mentions_local_definition(err_ty)
        && super::dyn_error_payload::withheld(|| {
            super::ty_reaches_foreign_user_code(tcx, err_ty, memo)
        })
}

/// Does `ty` name a definition of THIS crate anywhere in its type tree (an ADT,
/// function item, closure/coroutine, extern type, or a trait object's trait)?
/// Fail-closed: an unrevealed alias counts as local. Only a `false` here lets
/// [`entry_termination_error_opaque_ty`] defer an error type to the entry row.
fn ty_mentions_local_definition<'tcx>(ty: Ty<'tcx>) -> bool {
    ty.walk().filter_map(|arg| arg.as_type()).any(|t| match *t.kind() {
        ty::Adt(adt, _) => adt.did().is_local(),
        ty::FnDef(did, _)
        | ty::Closure(did, _)
        | ty::CoroutineClosure(did, _)
        | ty::Coroutine(did, _)
        | ty::CoroutineWitness(did, _)
        | ty::Foreign(did) => did.is_local(),
        ty::Dynamic(preds, _) => {
            preds.principal_def_id().is_some_and(|did| did.is_local())
                || preds.auto_traits().any(|did| did.is_local())
        }
        ty::Alias(..) | ty::Param(_) | ty::Bound(..) | ty::Placeholder(_) | ty::Infer(_) => true,
        _ => false,
    })
}

/// Strict-lane refusal for [`entry_termination_error_opaque_ty`]. The caller
/// gates it on the fail-closed, non-memory-safe lane (the same lanes the packer
/// gate's `println!` refusal fires in).
pub(super) fn abort_on_entry_termination_error_opacity<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) {
    if let Some(diagnostic) = prepare_entry_termination_error_opacity(tcx, body, func_path) {
        diagnostic.emit(tcx);
    }
}

pub(super) fn prepare_entry_termination_error_opacity<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) -> Option<PreparedLocatedDiagnostic> {
    let Some(err_ty) = entry_termination_error_opaque_ty(tcx, body) else {
        // Trust (D1 residual, 2026-09-24): no non-deferred layer is refused, but a
        // DEFERRED layer (`Box<dyn Error>`, `io::Error`, ...) can still dispatch
        // into this crate's formatting code; see `fmt_termination_dyn`.
        return super::fmt_termination_dyn::prepare_entry_termination_dyn_formatter_reach(
            tcx, body, func_path,
        );
    };
    let err_label = with_no_trimmed_paths!(err_ty.to_string());
    let span = body.span;
    let header = format!(
        "Trust full verification failed for `{func_path}`: `main` returns an error of type \
         `{err_label}`, which `<_ as Termination>::report` formats with `Debug`, and that \
         `Debug` impl is not established panic-free and error-transparent"
    );
    let mut children = vec![PreparedDiagnosticChild::Note(
        "on `Err`, std's `Termination::report` writes `Error: {err:?}` to stderr through \
         `io::Write::write_fmt`, which PANICS (\"a formatting trait implementation returned an \
         error when the underlying stream did not\") when the `Debug` impl returns `Err` while \
         stderr did not fail. That call is in `lang_start`, not in `main`, so no row of `main` \
         covers it. The error type must be foundational (a primitive, `str`, `String`, ...) or \
         have a `Debug` impl verified panic-free in this crate that returns `Err` only when its \
         writer did"
            .into(),
    )];
    if let Some(debug_trait) = tcx.get_diagnostic_item(sym::Debug)
        && let Some(instance) = resolve_fmt_method(tcx, debug_trait, err_ty)
        && super::foreign_rederivation::body_is_local_or_rederivable(tcx, instance.def_id())
        && !impl_is_error_transparent(tcx, instance)
    {
        let label = with_no_trimmed_paths!(tcx.def_path_str(instance.def_id()));
        children.push(PreparedDiagnosticChild::Note(error_opacity_note_text(&label)));
    }
    Some(PreparedLocatedDiagnostic {
        span,
        diagnostic: PreparedDiagnostic { aborting: true, header, children },
    })
}
