//! Trust rung 1, §(c) for ONE absent std callee: core's DEFAULT
//! `fmt::Write::write_fmt` body, entered with an `Arguments` that
//! `Arguments::from_str` built.
//!
//! `write!(w, "literal")` lowers to two MIR calls —
//! `Arguments::from_str("literal")` then `<W as fmt::Write>::write_fmt(&mut w,
//! args)`. The second names a core body the bundler cannot lower (its chain runs
//! through `NonNull`/`usize` transmutes and a raw byte-template loop), so it
//! rides the bridge's fail-closed absent-callee arm and the caller can never be
//! proved panic-free. That is the correct DEFAULT — `write_fmt` in general drives
//! arbitrary user `Display`/`Debug` impls, any of which may panic.
//!
//! ## The reduction this module certifies
//!
//! For an `Arguments` built by `from_str`, the general case does not arise. Read
//! the three core bodies (`library/core/src/fmt/mod.rs`, this tree):
//!
//! * `from_str(s)` stores `template = s.as_ptr()` and `args = s.len() << 1 | 1`,
//!   so `as_str()`'s `bits & 1 == 1` test is TRUE BY CONSTRUCTION and it returns
//!   `Some(s)`.
//! * `write_fmt` is `self.spec_write_fmt(args)`, and BOTH `SpecWriteFmt` impls
//!   are `if let Some(s) = args.as_statically_known_str() { self.write_str(s) }
//!   else { write(self, args) }`. `as_statically_known_str` is `as_str()` gated
//!   on `is_val_statically_known`, whose result is UNSPECIFIED — so both arms
//!   must be taken as reachable.
//! * `write(output, fmt)` opens with `if let Some(s) = fmt.as_str() { return
//!   output.write_str(s); }` — the SAME `as_str()`, not intrinsic-gated. The raw
//!   template loop and its `Argument::fmt` fn-pointer dispatch are BELOW that
//!   early return and are unreachable for a `from_str` value.
//!
//! So on either arm the call performs EXACTLY ONE `<Self as Write>::write_str(recv,
//! s)` and returns its result; everything else it executes is a transmute, a bit
//! test, `str::from_utf8_unchecked`/`slice::from_raw_parts`,
//! `is_val_statically_known`, and (on the second arm) an `&mut W -> &mut dyn Write`
//! unsizing. None of those can panic and none of them allocate. The call's
//! panic-freedom is therefore EQUIVALENT to `write_str`'s — not weaker, not
//! assumed.
//!
//! ## Why this is not a totality allowlist
//!
//! `write_fmt` is never modeled total. The reduction only names WHICH body the
//! obligation transfers to, and that body must then discharge it on its own
//! evidence: `dyn_target_is_verified_panic_free` — the same INDEPENDENT-verdict
//! bar C-FLOW's case split uses, and the same one `#[trust::panic_free]` uses per
//! impl. A `write_str` that is `todo!()`, `#[trust::skip]`ped,
//! `#[trust::assume_total]`, foreign, cyclic, or simply unproved fails that bar
//! and the site keeps its fail-closed absent-callee obligation, byte-for-byte as
//! before this rule existed. This is the "the driven body carries its own
//! obligation" discipline the native-TLS and `LocalKey::try_with` entries in
//! `is_trusted_panic_free_absent_callee` already run on.
//!
//! ## The discharge channel is a STRING, and that string is MANY-TO-ONE
//!
//! Read this before touching any gate below. The bridge discharges an
//! absent-callee row by testing `dyn_contract_total_callees.contains(callee)`
//! (`trust-ir-bridge/src/lower.rs`), where `callee` is
//! `trust_mir_extract::func_operand_name` of the call. That name is NOT an
//! injective callee identity WITHIN one crate:
//!
//! * `func_operand_name` renders `def_path_str_with_args` (or, for a
//!   devirtualized call, `def_path_str` of the resolved local impl item), and a
//!   def path OMITS `DefPathData` disambiguators.
//! * `direct_call_def_path` — the one place that repair could live — only
//!   disambiguates duplicate CRATE names (`__trust_crate@<stable-crate-id>`) and
//!   duplicate generic ARGUMENTS in such a crate graph. Neither fires inside a
//!   single crate.
//!
//! So two DIFFERENT block-scoped `struct S`, declared in two different blocks of
//! ONE function, render the SAME key. MEASURED on this tree: the two
//! `<render::S as core::fmt::Write>::write_fmt` calls of
//! `tests/ui/trust/static_str_write_fmt_key_alias_site_stays_closed.rs` produce
//! one key, and an earlier revision of this module — which resolved gate 4
//! against `sites[0]` alone — discharged that key from the FIRST `S`'s
//! panic-free `write_str` while the SECOND `S`'s `write_str` was `panic!()`.
//! Compiled and run, that program was proved panic-free and then panicked.
//!
//! Everything below is therefore keyed by the CHANNEL name and decided over the
//! WHOLE group under it:
//!
//! * every site in the group must independently pass gates 2, 3 and 4 — one
//!   site's evidence is never evidence for its neighbour, and
//! * if ANY other bundled call renders to the same key, the key is refused
//!   outright (gate 0), because that call was never examined by this rule at
//!   all.
//!
//! This is a property of `func_operand_name`, not of this module, and the SIBLING
//! `dyn` rule in `dyn_dispatch_reliance` inherited exactly the same hole through
//! exactly the same string — measured, and closed in the same commit as this
//! text. Gate 0's ledger therefore lives on `DynDispatchBundleFacts` as
//! `CallKeyLedger` and serves both lanes: it records which lane, if either,
//! certified each bundled call, and a lane may insert a key only when every call
//! under that key is a certified site OF THAT LANE. ANY future rule that
//! discharges obligations by inserting a `func_operand_name` string into an
//! authenticated set inherits the same hole, and must either join that ledger,
//! group all-or-nothing the way both lanes now do, or strengthen the key itself.
//! The finding is recorded on `direct_call_def_path` in `trust-mir-extract` as
//! well.
//! Strengthening it here is not possible: the key must be byte-identical to the
//! one the bridge already computed for the row being discharged, so the fix
//! would have to change `func_operand_name` for every one of its consumers
//! (contract-summary registration, expected-absent classification, the assumed-
//! total and ABI sets) at once.
//!
//! ## Every gate, and what each one closes
//!
//! 0. NO other call in the bundle renders to this callee key. Sites are grouped
//!    by the channel key; the shared `CallKeyLedger` records which lane
//!    certified each bundled call, and a key is discharged here only when EVERY
//!    call under it is a certified site of THIS rule. This is what stops an
//!    aliased key from carrying a discharge to a call this rule never certified
//!    — including a call that declined at gate 1 (an impl that OVERRIDES
//!    `write_fmt`, whose devirtualized name renders in the very same
//!    `<T as core::fmt::Write>::write_fmt` shape), a `dyn` site the other lane
//!    owns, and an indirect or unresolvable call that has no body at all.
//! 1. The call's resolved instance is `InstanceKind::Item(D)` with
//!    `trait_of_assoc(D) == FmtWrite` — i.e. resolution landed on the TRAIT's
//!    default body. An impl that OVERRIDES `write_fmt` resolves to its own impl
//!    item, whose `trait_of_assoc` is `None`, and declines. This is what makes a
//!    foreign `impl Write for Foo { fn write_fmt(..) { panic!() } }` unable to
//!    ride the rule, and it cannot be spelled by a user (a same-named user trait
//!    is not the `FmtWrite` diagnostic item).
//! 2. EVERY call site under that callee key is `from_str`-backed. The discharge
//!    channel is keyed by the bridge's callee STRING, and one monomorphic
//!    `<W as Write>::write_fmt` serves both `write!(w, "lit")` and
//!    `write!(w, "{x}")`. Discharging a name on the strength of one site would
//!    silently cover the other; a single unbacked site declines the whole name.
//! 3. The `Arguments` operand is a local with exactly ONE definition in the whole
//!    body, that definition is a call to `Arguments::from_str`, it dominates the
//!    use, and the local is never borrowed (so nothing can rewrite it through a
//!    pointer) and is not a parameter.
//! 4. EVERY site under that key resolves its OWN `<Self as Write>::write_str` to
//!    a CONCRETE `Item` body that passes the independent-verdict bar. A `dyn`
//!    Self resolves `Virtual` and declines. Per site for the gate-2 reason: the
//!    key is shared, the receivers under it need not be, and one receiver's
//!    proof says nothing about another's body.
//!
//! ## Safety only
//!
//! Like the two `dyn` certificates, this discharges a CALL obligation. A call
//! instruction is not a panic instruction, so the innermost frame of any
//! panicking execution raised it from its own body, which its own proof covered.
//! It says nothing about termination and must never be extended to it.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::{BasicBlock, Body, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;
use rustc_span::{Spanned, sym};

use super::dyn_dispatch_reliance::{
    CallKeyLedger, dyn_target_is_verified_panic_free, target_decline_reason,
};

/// One observed call to core's default `fmt::Write::write_fmt`.
struct WriteFmtCallSite<'tcx> {
    /// The EXACT identity the bridge will see for this callee — the same
    /// `func_operand_name` spelling its absent-callee row is keyed by.
    call_key: String,
    /// The receiver's `Self` type, taken from the resolved instance rather than
    /// from the operand, so an autoref/reborrow cannot skew it.
    self_ty: Ty<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    /// Did the `Arguments` operand at THIS site come from `Arguments::from_str`?
    from_str_backed: bool,
}

/// Every `write_fmt` site in one verification bundle.
///
/// GATE 0's veto set is NOT here: it lives on `DynDispatchBundleFacts` as
/// [`CallKeyLedger`], because the aliasing it guards against is a property of
/// `func_operand_name` and therefore of EVERY lane that inserts one of those
/// strings, not of this rule.
#[derive(Default)]
pub(crate) struct StaticStrWriteFmtFacts<'tcx> {
    sites: Vec<WriteFmtCallSite<'tcx>>,
}

impl<'tcx> StaticStrWriteFmtFacts<'tcx> {
    pub(crate) fn is_empty(&self) -> bool {
        self.sites.is_empty()
    }

    /// Classify ONE bundled `Call` terminator: record it as a site of this rule
    /// and answer `true`, or answer `false` and leave the caller to file its key
    /// in gate 0's veto ledger.
    ///
    /// Called from the `dyn` facts' body walk rather than from a walk of its
    /// own. That walk is the one place every bundled body — including the
    /// B-lane's instantiated foreign ones — is in hand, AND it is the walk that
    /// classifies `dyn` sites, so having both lanes classify each call exactly
    /// once in one pass is what makes "every bundled call is accounted for"
    /// checkable by reading a single loop.
    ///
    /// `typing_env` must be the environment the body's own call sites resolve
    /// in — `post_analysis` for a body taken as-is, `fully_monomorphized` for one
    /// the B-lane instantiated.
    pub(super) fn observe_call(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        block_id: BasicBlock,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
    ) -> bool {
        let Some(fmt_write) = tcx.get_diagnostic_item(sym::FmtWrite) else { return false };
        match certified_write_fmt_site(tcx, fmt_write, body, typing_env, block_id, func, args) {
            Some(site) => {
                self.sites.push(site);
                true
            }
            None => false,
        }
    }

    /// Decide every observed site and write the discharged call identities into
    /// `out`. A callee absent from `out` keeps the bridge's fail-closed
    /// absent-callee obligation, byte-for-byte as before this rule existed.
    ///
    /// The caller holds the reliance re-entrancy guard, so the
    /// `trust_proof_results` forcing below cannot open a query cycle this module
    /// does not already decline.
    pub(super) fn resolve_reliance(
        &self,
        tcx: TyCtxt<'tcx>,
        root_def_id: DefId,
        out: &mut FxHashSet<String>,
        probe: bool,
        call_keys: &CallKeyLedger,
    ) {
        // A/B measurement switch, DEFAULT ON. Setting it restores the exact
        // pre-rule behavior. There is no setting of this variable that admits
        // anything: the only direction available is LESS proof.
        if std::env::var_os("TRUST_NO_STATIC_STR_WRITE_FMT").is_some() {
            return;
        }
        let Some(fmt_write) = tcx.get_diagnostic_item(sym::FmtWrite) else { return };
        // Group by the identity the discharge channel is keyed by. EVERY gate
        // below is then decided over the WHOLE group, because inserting the key
        // discharges every call the bridge renders to it — not the one site that
        // happened to be examined.
        let mut by_callee: FxHashMap<&str, Vec<&WriteFmtCallSite<'tcx>>> = FxHashMap::default();
        for site in &self.sites {
            by_callee.entry(site.call_key.as_str()).or_default().push(site);
        }
        for (call_key, sites) in by_callee {
            let count = sites.len();
            // GATE 0 — key injectivity, which `func_operand_name` does NOT have
            // inside one crate (module header). A key that also names a call
            // this rule never certified — including one the `dyn` lane certified
            // instead — is refused: the discharge cannot be aimed at a subset of
            // the calls the string covers, and the other lane's evidence is not
            // this reduction's evidence.
            if !call_keys.only_write_fmt_sites(call_key) {
                if probe {
                    eprintln!(
                        "TRUST_DYN_RELIANCE_PROBE: write_fmt site={call_key} ({count} site(s)) \
                         => kept (callee key ALIASES a bundled call this rule did not certify)"
                    );
                }
                continue;
            }
            // GATES 2, 3 and 4, EVERY ONE OF THEM PER SITE. The key is shared by
            // the whole group; the receivers under it need not be, and neither
            // need the `Arguments` operands. One site's evidence is therefore
            // never evidence for its neighbour — the reasoning gate 2 was
            // already written down with, now applied to gate 4 as well. An
            // earlier revision resolved gate 4 against `sites[0]` alone and was
            // MEASURED proving a program that panics (module header).
            let mut refusal: Option<String> = None;
            for site in &sites {
                // GATES 2 + 3.
                if !site.from_str_backed {
                    refusal = Some(
                        "a call site's Arguments is not `Arguments::from_str`-backed".to_string(),
                    );
                    break;
                }
                // GATE 4 — this site's OWN reduction target and its own
                // INDEPENDENT verdict. The bar is shared verbatim with the `dyn`
                // case split rather than re-derived.
                let Some(target) = resolve_write_str(tcx, fmt_write, site) else {
                    refusal = Some(with_no_trimmed_paths!(format!(
                        "no concrete `write_str` body for receiver {}",
                        site.self_ty
                    )));
                    break;
                };
                if !dyn_target_is_verified_panic_free(tcx, target, root_def_id) {
                    // Render the BAR'S OWN reason, not a fixed word: this lane
                    // shares the bar with the `dyn` case split, so a conjunct
                    // added there (e.g. the assumption-root gate) has to be
                    // observable HERE too or it cannot be falsified in this lane.
                    //
                    // BEHIND `probe`, matching the `dyn` lane. `target_decline_reason`
                    // re-runs the whole bar to name the conjunct that fired, and the
                    // string it builds is consumed ONLY by the probe `eprintln!`
                    // below. Gated here rather than at that consumer so an ordinary
                    // compile skips the second bar evaluation, not just the print.
                    refusal = Some(if probe {
                        with_no_trimmed_paths!(format!(
                            "reduction target {} {}",
                            tcx.def_path_str(target.def_id()),
                            target_decline_reason(tcx, target, root_def_id),
                        ))
                    } else {
                        // `Some` is the decision; the text is probe-only diagnostics.
                        String::new()
                    });
                    break;
                }
            }
            if let Some(reason) = refusal {
                if probe {
                    eprintln!(
                        "TRUST_DYN_RELIANCE_PROBE: write_fmt site={call_key} ({count} site(s)) \
                         => kept ({reason})"
                    );
                }
                continue;
            }
            if probe {
                eprintln!(
                    "TRUST_DYN_RELIANCE_PROBE: write_fmt site={call_key} ({count} site(s)) \
                     => DISCHARGED (every site reduces to its own proved `write_str`)"
                );
            }
            out.insert(call_key.to_string());
        }
    }
}

/// The [`WriteFmtCallSite`] for one call terminator, or `None` when this rule
/// does not certify that call.
///
/// `None` is the FAIL-CLOSED answer twice over: the call gets no discharge of
/// its own, AND its callee key joins gate 0's veto set, so it also blocks any
/// aliased key a certified site would otherwise have discharged.
#[allow(clippy::too_many_arguments)]
fn certified_write_fmt_site<'tcx>(
    tcx: TyCtxt<'tcx>,
    fmt_write: DefId,
    body: &Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    block_id: BasicBlock,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
) -> Option<WriteFmtCallSite<'tcx>> {
    let (callee_def_id, gen_args) = func.const_fn_def()?;
    let instance = ty::Instance::try_resolve(tcx, typing_env, callee_def_id, gen_args).ok()??;
    // GATE 1. `Item` on the TRAIT's own `write_fmt` is core's default body. An
    // impl override resolves to the impl item (whose `trait_of_assoc` is `None`)
    // and never reaches here.
    let ty::InstanceKind::Item(resolved) = instance.def else { return None };
    if tcx.opt_item_name(resolved) != Some(sym::write_fmt) {
        return None;
    }
    if tcx.trait_of_assoc(resolved) != Some(fmt_write) {
        return None;
    }
    // `Write::write_fmt` takes only `Self`; anything else means the trait moved
    // under this rule and the audited reduction no longer applies.
    if instance.args.len() != 1 {
        return None;
    }
    let self_ty = instance.args.first().and_then(|arg| arg.as_type())?;
    Some(WriteFmtCallSite {
        call_key: trust_mir_extract::func_operand_name(tcx, func),
        self_ty,
        args: instance.args,
        // GATE 3.
        from_str_backed: args.len() == 2
            && operand_is_arguments_from_str(tcx, body, block_id, &args[1].node),
    })
}

/// The `<Self as fmt::Write>::write_str` body this site's obligation reduces to.
///
/// `None` unless resolution names a CONCRETE body: a `dyn` receiver resolves
/// `Virtual`, a specialization may leave `Ok(None)`, and either is a target this
/// reduction cannot check.
fn resolve_write_str<'tcx>(
    tcx: TyCtxt<'tcx>,
    fmt_write: DefId,
    site: &WriteFmtCallSite<'tcx>,
) -> Option<ty::Instance<'tcx>> {
    let write_str = tcx
        .associated_items(fmt_write)
        .in_definition_order()
        .find(|item| item.opt_name() == Some(sym::write_str))?
        .def_id;
    // `write_str` has the same generics as `write_fmt` (`Self` only), so the
    // site's own args are already the demanded instantiation.
    if site.args.len() != 1 || site.args.has_non_region_param() {
        return None;
    }
    let instance =
        ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), write_str, site.args)
            .ok()??;
    match instance.def {
        ty::InstanceKind::Item(_) => Some(instance),
        _ => None,
    }
}

/// Does `operand`, read at `use_block`, necessarily hold a value that
/// `Arguments::from_str` produced?
///
/// Deliberately structural and single-definition rather than a dataflow: the
/// shape this must recognize is the one `format_args!("literal")` always emits,
/// and every shape it cannot account for must decline. The soundness argument for
/// reading "one definition" as "the value at the use" is the ordinary MIR one: a
/// local with a single value-definition that DOMINATES the use, that is never
/// borrowed, and that is not a parameter, holds either that definition's value or
/// uninit at the use — and reading uninit is UB the program does not have.
fn operand_is_arguments_from_str<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    use_block: BasicBlock,
    operand: &Operand<'tcx>,
) -> bool {
    let Some(from_str) = tcx.get_diagnostic_item(sym::FmtArgumentsFromStr) else { return false };
    let place = match operand {
        Operand::Copy(place) | Operand::Move(place) => place,
        // A constant `Arguments` carries no witnessed provenance, and a
        // `RuntimeChecks` operand is a compiler-synthesized flag bundle that is
        // not an `Arguments` at all. Both decline: this match stays EXHAUSTIVE so
        // a future operand kind is a compile error rather than a silent hole.
        Operand::Constant(_) | Operand::RuntimeChecks(_) => return false,
    };
    if !place.projection.is_empty() {
        return false;
    }
    let local = place.local;
    // The return place and the parameters are written from OUTSIDE this body.
    if local.as_usize() <= body.arg_count {
        return false;
    }

    let mut definition: Option<BasicBlock> = None;
    let mut storage_live: Option<BasicBlock> = None;
    for (block_id, block) in body.basic_blocks.iter_enumerated() {
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(assign) => {
                    let (assigned, rvalue) = &**assign;
                    // Any statement-level write to the local is a second
                    // definition this rule will not reason about.
                    if assigned.local == local {
                        return false;
                    }
                    // A borrow could rewrite the local behind our back. All three
                    // reference-forming rvalues, so a future one added beside
                    // them is the only way this can go stale — and the exhaustive
                    // match below makes that a compile error, not a silent hole.
                    match rvalue {
                        Rvalue::Ref(_, _, borrowed)
                        | Rvalue::Reborrow(_, _, borrowed)
                        | Rvalue::RawPtr(_, borrowed) => {
                            if borrowed.local == local {
                                return false;
                            }
                        }
                        Rvalue::Use(..)
                        | Rvalue::Repeat(..)
                        | Rvalue::ThreadLocalRef(..)
                        | Rvalue::Cast(..)
                        | Rvalue::BinaryOp(..)
                        | Rvalue::UnaryOp(..)
                        | Rvalue::Discriminant(..)
                        | Rvalue::Aggregate(..)
                        | Rvalue::CopyForDeref(..)
                        | Rvalue::WrapUnsafeBinder(..) => {}
                    }
                }
                StatementKind::SetDiscriminant { place, .. } => {
                    if place.local == local {
                        return false;
                    }
                }
                // A second `StorageLive` resets the local to uninit; keep only the
                // shape where storage is established once, before the definition.
                StatementKind::StorageLive(live) => {
                    if *live == local {
                        if storage_live.is_some() {
                            return false;
                        }
                        storage_live = Some(block_id);
                    }
                }
                _ => {}
            }
        }
        match &block.terminator().kind {
            TerminatorKind::Call { func, destination, .. } => {
                if destination.local == local {
                    if !destination.projection.is_empty() || definition.is_some() {
                        return false;
                    }
                    let Some((callee_def_id, _)) = func.const_fn_def() else { return false };
                    if callee_def_id != from_str {
                        return false;
                    }
                    definition = Some(block_id);
                }
            }
            // Neither shape appears in a `format_args!` body, and both can write a
            // local without naming it in a form this walk reads. Fail closed
            // instead of enumerating their operand kinds.
            TerminatorKind::InlineAsm { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop => return false,
            _ => {}
        }
    }

    let Some(definition) = definition else { return false };
    if let Some(storage_live) = storage_live
        && !body.basic_blocks.dominators().dominates(storage_live, definition)
    {
        return false;
    }
    body.basic_blocks.dominators().dominates(definition, use_block)
}
