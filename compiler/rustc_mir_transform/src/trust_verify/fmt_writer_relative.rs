//! Trust (D1 increment 1, 2026-09-25): the WRITER-RELATIVE (WR) verdict class for
//! formatting impls whose only unproved edges are their own `Formatter`'s writer.
//!
//! ## The class, and the program that motivates it
//!
//! ```text
//! pub struct Port(pub u16);
//! impl fmt::Display for Port {
//!     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str("port") }
//! }
//! ```
//!
//! (`tests/idiomatic-rust-sample/i10_newtype_display.rs`.) Measured BEFORE on the
//! stage-1 snapshot `4e9fe36bf`: rc=1, "an unproved assumption-panic row — a
//! generic absent callee — keeps the function fail-closed", the row naming
//! `<dyn core::fmt::Write as core::fmt::Write>::write_str`. That refusal is
//! CORRECT as an absolute claim — the impl really panics when its caller hands it
//! a panicking writer (`write!(Boom, "{}", Port(1))` exits 101) — and it is also
//! a refusal of writing anything at all from a formatting impl.
//!
//! D1 (decided 2026-09-23, `docs/DECISION_QUEUE.md`) keeps the absolute claim
//! refused and adds a CONDITIONAL one: such an impl is panic-free RELATIVE TO its
//! `Formatter`'s writer. Its writer rows stay unproved (`runtime-checked`, no
//! evidence), it compiles as a reported conditional pass under the default policy,
//! `-Ztrust-policy=certify` still refuses it, and the premise is discharged where
//! std supplies the writer: `println!`/`eprintln!` (stdout/stderr), `format!` and
//! `to_string` (`String`), and `main`'s `Termination::report` (stderr).
//!
//! ## The impl side (`writer_relative_root`)
//!
//! A root qualifies only when ALL hold (each fail-closed):
//! * [`formatting_impl_root`]: a local `Debug::fmt`/`Display::fmt` impl method
//!   (diagnostic items, owned by authentic resident core), non-generic, no
//!   `#[trust::skip]`/`assume_total`, no authored clause, signature
//!   `(&Self, &mut Formatter<'_>)`;
//! * no `unsafe` outside std (`function_uses_unsafe_outside_std`);
//! * its bundle's writer-relative facts were recorded and name at least one
//!   writer edge (`DynDispatchBundleFacts::writer_relative_facts`: every
//!   `fmt::Write` value came from the `&mut Formatter` parameter — no coercion to
//!   `dyn fmt::Write`, no other poison source, no minted `Formatter` — and no
//!   walked body, the root included, has a panic site that mints no row
//!   (G-MEMBER));
//! * to EXCUSE a row, additionally: no co-folded masked fail-closed source
//!   (`function_has_masked_fail_closed_dispatch`) and no unresolved indirect call.
//!
//! Only an unproved ABSENT-CALLEE row naming one of the writer-edge keys is
//! excused, and only from the fail-closed assumption-panic decision in
//! `abort_on_full_verification_failure`. Every folded site is judged on its own
//! (`transport_rows_with_fold_sites`), so a co-folded vanilla or print row keeps
//! its own treatment and any other row keeps the function fail-closed.
//!
//! ## The sink side (`fmt_impl_is_writer_relative_panic_free`)
//!
//! The WR bar is the SHARED evidence bar (`trait_panic_free`'s single
//! implementation) with one excuse plugged in: an unproved row may be excused iff
//! it is a writer-edge absent-callee row (conjunct 3, over the fold-expanded rows)
//! or a `runtime-checked` disposition whose VC names a writer edge (conjunct 4).
//! Every other conjunct — including the assumption-root gate — is unchanged, and
//! the same pre-conjuncts as `dyn_target_is_verified_panic_free` are asked
//! (`target_admits_independent_verdict`). ZERO vanilla rows: a `println!` inside a
//! `Display` leaves an unexcused `_print` row — a call whose panic is std's
//! `print` failing, not the writer's — so the bar refuses it. (It does NOT
//! panic by re-entering stdout, measured 2026-09-25: stdout's lock is
//! reentrant and its `RefCell` borrow is per write; the rule rests on the
//! non-writer row, not on a crash.)
//!
//! It is read ONLY through `fmt_termination_dyn::formatter_sink_basis`, i.e. by
//! the formatting sinks. `dyn_target_is_verified_panic_free` — the bar Φ, C-FLOW,
//! C-SEALED, the `write_fmt` reduction and the drop-glue premise read — is NOT
//! changed and never reads a WR verdict, so no lane can mistake a conditional
//! verdict for panic-freedom. Nothing here enters `dyn_contract_total_callees` or
//! any proven registry (`register_proven_panic_free` still needs every row
//! proved).
//!
//! ## Where the premise is discharged (and where it is not)
//!
//! * `ToString::to_string` and `main`'s `Termination::report`: the writer is
//!   alloc's `String` / std's stderr by construction of the dispatch those arms
//!   recognize.
//! * The packer arm (`println!`/`format!`): a `format_args!` value can be handed to
//!   ANY consumer, so a formatter admitted on the WR basis additionally requires
//!   that every call in the body taking a `fmt::Arguments` is std's
//!   `_print`/`_eprint` or alloc's `fmt::format`
//!   ([`body_formats_only_into_recognized_sinks`]). This is refusal-only.
//! * A DIRECT call into a WR impl from a body that is not itself a WR root (the
//!   critique's `wr_direct_call_formatter_new_dep_writer`: `S.fmt(&mut
//!   Formatter::new(&mut dep::F, ..))`) is NOT a sink: the callee is bundled into
//!   the caller, its writer edge is charged to the CALLER as an unproved absent
//!   callee, and the caller is not a WR root, so no excuse applies and the row
//!   stays fatal (measured BEFORE: that row names `Formatter::write_str` in the
//!   caller and is refused). A caller that is itself a WR root carries the same
//!   premise to ITS sink. When the caller's writer is a verified local writer,
//!   C-FLOW discharges the edge in the caller's own bundle as before.
//!
//! ## Refusal-only outside the one excuse
//!
//! The only acceptance this module adds is (a) the excuse of writer-edge rows in
//! a qualifying root's own fail-closed decision and (b) the WR basis at the
//! sinks. Every other use here is a conjunct on an acceptance or an added
//! refusal. `certify` fails every WR root (its rows are not proved).
//!
//! ## Increment 2 (2026-09-25): nested formatters — `#[derive(Debug)]`
//!
//! ```text
//! #[derive(Debug)]
//! pub enum ConfigError { Missing(&'static str), Invalid { key: &'static str, got: u32 } }
//! ```
//!
//! (`tests/idiomatic-rust-sample/i01_*.rs`.) The derive expands to core's
//! `Formatter::debug_{tuple,struct}_field*_finish(f, "Name", &self.0 as &dyn
//! Debug, ..)`. Measured BEFORE on the stage-1 snapshot `43b8fe6ab`: rc=1, rows
//! `<dyn core::fmt::Write>::write_str` (the writer — already the class) and
//! `<dyn core::fmt::Debug as core::fmt::Debug>::fmt` (a NESTED FORMATTER: core's
//! `DebugTuple::field` calls `value.fmt(f)`), and the writer-relative facts were
//! refused on five counts, each now answered on its own evidence
//! (`DynDispatchBundleFacts::writer_relative_facts`):
//!
//! * the nested-formatter edge: excused only when C-FLOW's enumeration of the
//!   `dyn Debug` values in the bundle is complete and EVERY target is core's
//!   `&T` forwarding impl (peeled), a sysroot impl at a foundational type
//!   (premise P1, pre-existing), or a local formatting impl that passes the
//!   absolute or the writer-relative bar with recorded facts of its own
//!   (`dyn_dispatch_reliance::nested_formatter_target_admitted`). One refused
//!   site refuses the class;
//! * the `Formatter` those nested formatters receive (the "unbundled callee"
//!   poison on `fmt::Write`): accepted exactly when every nested site is;
//! * `{:#?}`: core wraps the writer in its private `PadAdapter` — a coercion to
//!   `dyn fmt::Write`, a `Formatter` minted by `PadAdapter::wrap`, and a constant
//!   `None::<&mut PadAdapter>` (MEASURED: the `None` arm of `Option::insert`'s
//!   inlined `as_mut().unwrap_unchecked()` in `PadAdapter::wrap`; the predicted
//!   `None::<PadAdapter>` slot is an aggregate, not a constant). Each is admitted
//!   ONLY for core's `PadAdapter` (authenticated by crate) — the constant also
//!   only when its evaluated value holds no pointer at all — whose one
//!   construction site and whose `write_str`/`write_char` (`builders.rs:20-50`:
//!   forward to the wrapped writer after optional indentation, `Err` only from
//!   it) are premise P2;
//! * G-MEMBER met `Option::insert`'s `unwrap_unchecked` inside `PadAdapter::wrap`:
//!   a UB-check member whose non-unwinding abort fires only on a violated
//!   sysroot `unsafe` precondition. It is not counted (premise P-UB), and the
//!   exemption is VOID when any walked non-sysroot body uses `unsafe` — a belt
//!   only: P-UB rests on the root's own `unsafe` rows being Level 0 errors and a
//!   verify-off dependency call being fail-closed (docs/TCB.md);
//! * G-MEMBER also met `drop(value_fmt)` in the generic `DebugTuple::field_with`
//!   and its closure, instantiated at `DebugTuple::field`'s reference-capturing
//!   closure: a `Drop` of a concrete type with no drop glue runs no code and is
//!   not counted (`drop_runs_no_code`);
//! * the total `caller_location` intrinsic that UB-check member calls is an
//!   excusable key too, only beside a writer or nested-formatter key.
//!
//! Error transparency gains the derive helpers (recognizer version 2,
//! `fmt_error_transparency`), conditioned on every local nested target being
//! transparent itself.
//!
//! LIVE since 2026-09-25 (branch `d1i2-live`): as first committed the class never
//! fired — the `Option<&mut PadAdapter>` constant kept the forged `Constant`
//! poison (refusing `write_poisoned_beyond_formatter_param` and
//! `write_forge_poisoned`), and the no-op closure drops above refused G-MEMBER.
//! Both were measured with `TRUST_DYN_RELIANCE_PROBE` (which now names each
//! G-MEMBER site and each skipped no-op drop) before being answered.
//!
//! The mask: `<Formatter as fmt::Write>::{write_str, write_char}` in a WR root is
//! no longer counted as a masked source ([`writer_relative_body_has_masked_source`]).
//! That, not `?`, was what refused `f.write_str("a")?; f.write_char('b')`
//! (measured: the `write_str` twin of the same `?` program built on the
//! snapshot), and it refused `f.write_char(c)` alone.
//!
//! 96a18b (P-SPLIT): upstream rewrote `debug_struct_field{1..5}_finish` to
//! split ONE concatenated names string, putting `unwrap_failed` and the char
//! searcher's split machinery into the walked bundle. G-MEMBER does not count
//! those authenticated bodies, under per-call MIR evidence recorded during
//! the walk (constant finisher names of the right arity, constant power-of-two
//! alignments, sysroot-only `encode_utf8_raw` callers —
//! `dyn_dispatch_reliance::names_split_member_kind`), and the machinery's own
//! absent-callee fold sites recorded from machinery bodies
//! (`WriterRelativeFacts::names_split_callee_keys`) are judged by the shared
//! bar's excuse exactly as writer edges are. The premise and its void
//! conditions (the P-UB belt) are docs/TCB.md P-SPLIT; the negative is
//! `runtime_align_is_aligned_to` in the derive rails.
//!
//! 1.101 (ff7c30e): upstream rewrote the machinery AGAIN — the tuple
//! finishers are deleted, every form routes through
//! `debug_struct_field{1..5}_finish`, and those now forward to
//! `debug_struct_fields_finish`, whose named arm holds the unwraps (split by
//! `split_str_by_space`, a byte-level `split`). P-SPLIT's evidence chain
//! follows the move: the root-side names check accepts the zero-separator
//! tuple form (that arm reaches no unwrap) or at least the finisher's arity
//! of separators, and `debug_struct_fields_finish` is a member only through
//! the finisher-forwarding call shape (`fields_finish_call_discharged`). A
//! DIRECT root call into it — the >5-named-fields derive shape — carries no
//! finisher evidence and stays refused, as it was when this body's
//! since-deleted `assert_eq!` was the stated reason; the >5 boundary is now
//! the class's, not the body's, and widening it is a decision of its own.
//!
//! P-UB for ABSENT UB-check members (2026-11-08): the same 1.101 shape walks
//! `<Split<'_, u8, _> as Iterator>::next` (and `slice_contains`), whose inlined
//! `slice::Iter::new` calls `<*mut T>::add::precondition_check`. The bundler
//! declines every `core::ptr::` body, so that check is absent and mints an
//! absent-callee marker — the aggregate's FIRST marked site — which the shared
//! bar refused (`fmt_writer_relative_derive.rs#nested_local` and five sink
//! revisions RED on stage-1 `39d11b38d7`), while the root's own decision
//! tolerated it as a vanilla sysroot callee. P-UB rests on the check's identity,
//! not on walking it, so such a key is recorded
//! (`WriterRelativeFacts::ub_check_callee_keys`: an authenticated
//! `precondition_check`, not walked, called only by plain calls from walked
//! sysroot bodies with no trait object in or out, the key rendered by no other
//! call, none under the P-UB belt) and judged by the bar exactly as a P-SPLIT
//! key. The `panic_nounwind` entries are not in this set: absent, one of them IS
//! the abort.
//!
//! What stays refused, by design: a generic `impl<T: Debug> Debug for W<T>`; a
//! field whose `Debug` panics, is `Err`-returning (at a sink), is a trait object,
//! or sits inside a non-foundational sysroot container (`Vec<LocalT>`); a derive
//! over more than five named fields (a direct `debug_struct_fields_finish`
//! call carries no finisher evidence); and every hand-written builder chain (`f.debug_tuple(
//! "x").field(..).finish()`), which error transparency does not recognize.

use rustc_attr_ir::lang_items::LangItem;
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def::DefKind;
use rustc_middle::mir::trust_proof::{TrustDisposition, TrustStatus};
use rustc_middle::mir::{Body, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_session::Session;
use rustc_span::def_id::DefId;
use rustc_span::sym;
use trust_types::{TransportObligationResult, VcKind};

use super::{dyn_dispatch_reliance, fmt_error_transparency, trait_panic_free};

/// Is `def_id` a formatting-impl ROOT the writer-relative class may speak about:
/// a LOCAL `fmt` method of an impl of core's `Debug` or `Display` (by diagnostic
/// item, owned by authentic resident core), with no type or const generics
/// anywhere (impl included), no `#[trust::skip]`/`#[trust::assume_total]`, no
/// authored contract clause, and the signature `fn fmt(&self, f: &mut
/// Formatter<'_>)`?
pub(super) fn formatting_impl_root(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !def_id.is_local() || tcx.def_kind(def_id) != DefKind::AssocFn {
        return false;
    }
    if tcx.opt_item_name(def_id) != Some(sym::fmt) {
        return false;
    }
    let Some(impl_did) = tcx.trait_impl_of_assoc(def_id) else {
        return false;
    };
    let trait_did = tcx.impl_trait_ref(impl_did).instantiate_identity().skip_normalization().def_id;
    if !(tcx.is_diagnostic_item(sym::Debug, trait_did)
        || tcx.is_diagnostic_item(sym::Display, trait_did))
    {
        return false;
    }
    // Trust (identity-anchor sweep, 2026-09-28): and the trait is AUTHENTIC
    // core's (`crate_is_authentic_core`: owner of `Sized` AND resident in this
    // compiler's own sysroot). The diagnostic item names WHICH trait; it is a
    // source attribute, and a whole-`core` substitute (`#![no_core]` +
    // `#![compiler_builtins]`, crate name `core`, `--extern core=`) owns `Debug`,
    // `Display`, `Formatter` and `FmtWrite` in the one graph where no real `core`
    // is loaded. MEASURED on stage-1 `trustc` at `246ceb451e5`
    // (`tests/ui/trust/fmt_writer_relative_fmtwrite_core_substitution_impostor_refuted.rs`):
    // its `impl Display` writing through `f.buf.write_str` built under `strict`
    // with this class's conditional-pass note, a premise about a `Formatter`
    // writer that is not core's. This conjunct is the class's first, so it closes
    // the root side and the sink side (`fmt_impl_is_writer_relative_panic_free`)
    // together; the anchors below are belts.
    if !super::crate_is_authentic_core(tcx, trait_did.krate) {
        return false;
    }
    if tcx.generics_of(def_id).requires_monomorphization(tcx) {
        return false;
    }
    if super::item_has_trust_skip_attr(tcx, def_id)
        || super::item_has_trust_attr(tcx, def_id, "assume_total")
    {
        return false;
    }
    if dyn_dispatch_reliance::body_carries_authored_clause(tcx, def_id) {
        return false;
    }
    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
    let inputs = sig.inputs();
    inputs.len() == 2 && dyn_dispatch_reliance::ty_is_mut_ref_to_formatter(tcx, inputs[1])
}

/// Trust (D1 increment 2): what one bundle of a formatting-impl root recorded for
/// the writer-relative class (`DynDispatchBundleFacts::writer_relative_facts`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct WriterRelativeFacts {
    /// Every call key whose UNPROVED absent-callee row the class may excuse:
    /// the writer edges (`<dyn fmt::Write>::{write_str, write_char}`), the
    /// admitted NESTED-FORMATTER edges (`<dyn fmt::Debug|Display>::fmt`, every
    /// enumerated target panicking only through its writer), and — only beside
    /// one of those — the total `caller_location` intrinsic. Empty = the class
    /// applies to nothing (a body with no writer edge).
    pub(super) excusable_keys: FxHashSet<String>,
    /// The LOCAL formatting impls an admitted nested-formatter edge can dispatch
    /// to. Error transparency at the sink requires each of them to be
    /// transparent too (`fmt_error_transparency`, version 2).
    pub(super) nested_local_targets: Vec<DefId>,
    /// Trust (96a18b, P-SPLIT): rendered absent-callee keys minted INSIDE
    /// authentic core's names-split derive machinery walked in this bundle
    /// (`SplitInternal::next` over a `char` pattern, the char searcher's
    /// `unwrap_failed`), each discharged by the walk's per-call evidence
    /// before these facts were recorded (docs/TCB.md P-SPLIT). The shared
    /// bar's excuse judges a fold site naming one exactly as it judges a
    /// writer edge. Empty when no names-split member was walked.
    pub(super) names_split_callee_keys: FxHashSet<String>,
    /// Trust (P-UB, absent UB-check members, 2026-11-08): rendered keys of
    /// authentic sysroot `precondition_check`s that walked SYSROOT bodies of
    /// this bundle call but the bundle does not walk (the bundler declines every
    /// `core::ptr::` body, so `<*mut T>::add::precondition_check`, reached from
    /// the inlined `slice::Iter::new`, is always absent), and that no other call
    /// renders. P-UB covers such a check exactly as it covers a walked one: its
    /// only panic is the non-unwinding abort of a violated sysroot `unsafe`
    /// precondition. Empty under the P-UB belt (a walked non-sysroot body uses
    /// `unsafe`). Read only by the shared bar's excuse ([`WriterEdgeExcuse`]);
    /// the root's own decision does not read it.
    pub(super) ub_check_callee_keys: FxHashSet<String>,
}

/// Publish one verification's writer-relative facts for `root`. A root verified
/// more than once keeps its facts only if every verification produced the
/// SAME ones; any disagreement, or any `None`, leaves `None` (refused).
pub(super) fn record_writer_relative_facts(
    sess: &Session,
    root: DefId,
    facts: Option<WriterRelativeFacts>,
) {
    super::with_crate_verification_state(sess, |state| {
        let merged = match state.writer_relative_facts.remove(&root) {
            None => facts,
            Some(previous) => match (previous, facts) {
                (Some(previous), Some(current)) if previous == current => Some(previous),
                _ => None,
            },
        };
        state.writer_relative_facts.insert(root, merged);
    });
}

/// Trust (D1 increment 2): the recorded writer-relative facts of `root`, or
/// `None` (never recorded, or refused). `Some` with empty keys still says the
/// bundle mints no `Formatter`, coerces no writer of its own, and takes every
/// writer from its own `&mut Formatter` parameter — which is what a
/// nested-formatter target must show (`dyn_dispatch_reliance::
/// nested_formatter_target_admitted`).
pub(super) fn recorded_writer_relative_facts(
    sess: &Session,
    root: DefId,
) -> Option<WriterRelativeFacts> {
    super::with_crate_verification_state(sess, |state| {
        state.writer_relative_facts.get(&root).cloned().flatten()
    })
}

/// The recorded excusable keys of `root`, or `None` (never recorded, or
/// refused).
fn recorded_writer_edge_keys(sess: &Session, root: DefId) -> Option<FxHashSet<String>> {
    recorded_writer_relative_facts(sess, root).map(|facts| facts.excusable_keys)
}

/// Trust (96a18b, P-SPLIT; P-UB absent UB-check members, 2026-11-08): the keys a
/// recorded premise OTHER than the writer discharges for `root` — P-SPLIT's
/// names-split machinery callees and P-UB's absent UB-check members — or empty
/// (never recorded, or refused). What [`writer_edge_rows_excused`] takes as its
/// `split_keys`. (Replaces `recorded_names_split_callee_keys`, whose two
/// readers, both in [`WriterEdgeExcuse`], now read the union.)
fn recorded_premise_discharged_keys(sess: &Session, root: DefId) -> FxHashSet<String> {
    let Some(facts) = recorded_writer_relative_facts(sess, root) else {
        return FxHashSet::default();
    };
    let mut keys = facts.names_split_callee_keys;
    // A set union: no visit order changes it.
    #[allow(rustc::potential_query_instability)]
    keys.extend(facts.ub_check_callee_keys);
    keys
}

/// Trust (D1 increment 2): the local formatting impls `root`'s admitted
/// nested-formatter edges can reach, or `None` when `root` recorded no
/// writer-relative facts. Read by error transparency (version 2).
pub(super) fn recorded_nested_local_targets(sess: &Session, root: DefId) -> Option<Vec<DefId>> {
    recorded_writer_relative_facts(sess, root).map(|facts| facts.nested_local_targets)
}

/// Trust (D1 increment 2): the fold-mask question (`function_has_masked_fail_
/// closed_dispatch`) asked of a WRITER-RELATIVE root, with one class of call not
/// counted: core's `<Formatter as fmt::Write>::{write_str, write_char}` (and the
/// inherent `Formatter::write_str`, which the scan never counted) —
/// `fmt_error_transparency::callee_forwards_to_formatter_writer`.
///
/// WHY THAT CALL IS NOT A MASKED SOURCE HERE. The scan counts it because its
/// `Self` type, `Formatter`, holds `buf: &mut dyn Write` — a trait object, so the
/// instantiation "reaches foreign user code" (`callee_instantiation_reaches_
/// foreign_user_code`). In a writer-relative root that code IS the writer: core's
/// body is exactly `self.buf.write_str(s)` / `self.buf.write_char(c)`
/// (`core/src/fmt/mod.rs`, `impl Write for Formatter`, premise P2), its body is
/// walked into the bundle, and its one foreign edge is the `<dyn Write>` writer
/// edge that carries a row of its own — judged per folded site, so it cannot hide
/// anything. Measured BEFORE (stage-1 `43b8fe6ab`): `f.write_char('b')` alone,
/// and `f.write_str("a")?; f.write_char('b')` (`write_char_q`), were refused by
/// exactly this mask (`TRUST_MASK_TRACE: masked fail-closed source at _0 =
/// <Formatter<'_> as Write>::write_char(..)`), while the `write_str` twin of the
/// same `?` program built — the `?` sites were never the cause.
///
/// The same holds, one level down, for the writer edge ITSELF when MIR inlining
/// has put it in the root's own body (`<dyn fmt::Write>::write_str(buf, ..)` at
/// `-O2`; memo risk 3): its receiver's provenance is what the bundle facts
/// establish for every `dyn fmt::Write` in the bundle, the root included, and its
/// row is the writer-edge row.
///
/// Every other terminator is judged exactly as before.
pub(super) fn writer_relative_body_has_masked_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> bool {
    super::function_has_masked_fail_closed_dispatch_except(tcx, body, |kind| {
        let TerminatorKind::Call { func, .. } = kind else {
            return false;
        };
        func.const_fn_def().is_some_and(|(callee, generic_args)| {
            fmt_error_transparency::callee_forwards_to_formatter_writer(tcx, callee, generic_args)
                || callee_is_virtual_writer_edge(tcx, callee, generic_args)
        })
    })
}

/// Trust (D1 increment 2): is this call `<dyn core::fmt::Write as
/// fmt::Write>::{write_str, write_char}` — the writer edge, spelled through the
/// REAL `fmt::Write` trait (diagnostic item) with `Self` a `dyn fmt::Write`?
///
/// Trust (identity-anchor sweep, 2026-09-28): "REAL" is the diagnostic item AND
/// authentic resident core (`authentic_core_diagnostic_item`); a whole-`core`
/// substitute's `FmtWrite` is not core's writer trait, and its virtual call stays
/// a masked source.
fn callee_is_virtual_writer_edge<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    generic_args: ty::GenericArgs<'tcx>,
) -> bool {
    let Some(fmt_write) = super::authentic_core_diagnostic_item(tcx, sym::FmtWrite) else {
        return false;
    };
    if tcx.trait_of_assoc(callee) != Some(fmt_write) {
        return false;
    }
    let Some(name) = tcx.opt_item_name(callee) else {
        return false;
    };
    (name == sym::write_str || name.as_str() == "write_char")
        && matches!(
            generic_args.types().next().map(|self_ty| *self_ty.kind()),
            Some(ty::Dynamic(preds, ..)) if preds.principal_def_id() == Some(fmt_write)
        )
}

/// Is `row` an UNPROVED absent-callee row naming one of `edge_keys`?
///
/// `pub(super)` only so the compact-slot parity test (`trust_verify::tests`) can ask it of
/// a compacted row beside the full one: it is one of the readers `premise_transport_row`
/// keeps fields for.
pub(super) fn row_names_writer_edge(
    row: &TransportObligationResult,
    edge_keys: &FxHashSet<String>,
) -> bool {
    super::transport_row_is_unproved_absent_callee(row)
        && super::absent_callee_path_of_row(row).is_some_and(|path| edge_keys.contains(path))
}

/// [`WriterEdgeExcuse`]'s answer to conjunct 3, from the facts it reads off the session:
/// the writer-edge keys the root's bundle recorded and the marked sites folded into its
/// panic-freedom aggregate (`None` when the ledger has no entry for the root).
///
/// Trust (memory, 2026-11-01): split out of `assumption_panic_rows_excused` so that
/// everything this excuse reads of a ROW is a session-free function the compact-slot
/// parity test can ask of a full and a compacted slice alike (adversarial review of
/// COMPACT-SLOT-PAYLOAD-1, finding 2). The session reads stay in the impl; nothing
/// changed in what is decided.
///
/// Trust (P-UB, absent UB-check members, 2026-11-08): `split_keys` is every key a
/// recorded premise other than the writer discharges — P-SPLIT's machinery callees
/// and P-UB's absent UB-check members (`recorded_premise_discharged_keys`). This
/// function judges both sets alike; which keys qualify is decided where they are
/// recorded (`DynDispatchBundleFacts::writer_relative_facts`).
pub(super) fn writer_edge_rows_excused(
    transport_results: &[TransportObligationResult],
    edge_keys: &FxHashSet<String>,
    split_keys: &FxHashSet<String>,
    fold_sites: Option<&[String]>,
) -> bool {
    // Trust: the class requires a recorded writer edge, independently of any
    // names-split machinery. Keep the caller's pre-compaction refusal here.
    if edge_keys.is_empty() {
        return false;
    }
    // FAIL CLOSED when a row stands for a fold but its sites are not on
    // record. The session ledger is keyed by path and an entry can be
    // REMOVED (a later synthesis for the same path that fails, or records
    // no marked site). Reading "no entry" as "nothing folded" would excuse
    // a vanilla or print site folded behind a writer-edge representative —
    // the one acceptance in the tree that depends on this ledger
    // (adversarial review of D1 increment 1, 2026-09-25).
    if fold_sites.is_none() && transport_results.iter().any(super::transport_row_stands_for_fold) {
        return false;
    }
    // Trust: ZERO sites outside the recorded writer and P-SPLIT keys in the fold,
    // whatever their class. The
    // assumption-panic test below asks only about the fatal classes; a
    // demotable `alloc::fmt::format` extern call, an assumed-total callee or a
    // vanilla routine folded beside a writer edge would otherwise ride under
    // the writer edge whenever it is the representative, which depends on
    // statement order.
    if let Some(sites) = fold_sites
        && !sites.iter().all(|site| {
            text_names_writer_edge(site, edge_keys) || text_names_writer_edge(site, split_keys)
        })
    {
        return false;
    }
    let judged = super::transport_rows_with_fold_sites(transport_results, fold_sites);
    !super::transport_rows_have_unexcused_assumption_panic(judged.iter(), |row| {
        row_names_writer_edge(row, edge_keys) || row_names_writer_edge(row, split_keys)
    })
}

/// Does this VC name a writer edge — the absent-callee marker text the bridge
/// mints, parsed exactly as `absent_callee_path_of_row` and
/// `trust_types::l0_refutation::absent_callee_name` parse it?
///
/// The marker is text, and an `Assertion` message can carry user text. That
/// surface is closed for this reader by the class itself: G-MEMBER refuses any
/// bundle with an `Assert` terminator or a diverging call (the only producers of a
/// user-worded assertion message), and an authored clause refuses the root.
/// (D1 increment 2: the diverging calls G-MEMBER no longer counts are a
/// sysroot UB-check member's `panic_nounwind_fmt`, whose message is core's own
/// constant "unsafe precondition(s) violated: ...", and — 96a18b, P-SPLIT —
/// authentic core's names-split machinery, whose assertion messages are
/// likewise core constants. User bodies remain fully counted, so no
/// user-worded message reaches this reader through either exemption.)
fn vc_names_writer_edge(kind: &VcKind, edge_keys: &FxHashSet<String>) -> bool {
    let VcKind::Assertion { message } = kind else {
        return false;
    };
    text_names_writer_edge(message, edge_keys)
}

/// Does this obligation text carry the FATAL absent-callee marker naming one of
/// `edge_keys`? (The expected-absent and assumed-total markers are different
/// texts and never match.)
pub(super) fn text_names_writer_edge(text: &str, edge_keys: &FxHashSet<String>) -> bool {
    let Some(rest) = text.split(super::ABSENT_CALLEE_ASSUMPTION_CALLEE_PREFIX).nth(1) else {
        return false;
    };
    rest.split('`').next().is_some_and(|name| edge_keys.contains(name))
}

/// A qualifying writer-relative root, as seen from its own fail-closed decision.
pub(super) struct WriterRelativeRoot {
    edge_keys: FxHashSet<String>,
    /// No co-folded masked fail-closed source and no unresolved indirect call:
    /// only then may a writer-edge row actually be excused.
    excusable: bool,
    /// Trust (D1 increment 2): this root's own masked-source answer
    /// ([`writer_relative_body_has_masked_source`]), which replaces the plain
    /// scan's in this root's fold-mask conjunct.
    masked_source: bool,
}

impl WriterRelativeRoot {
    /// Trust (D1 increment 2): the masked-source answer for this root — the
    /// plain scan with core's `Formatter`-as-writer calls not counted.
    pub(super) fn masked_source(&self) -> bool {
        self.masked_source
    }

    /// Does `row` name one of this root's writer edges (whether or not it may be
    /// excused)? Used to notice a writer gap at all.
    pub(super) fn names_edge(&self, row: &TransportObligationResult) -> bool {
        row_names_writer_edge(row, &self.edge_keys)
    }

    /// May `row` be excused from the fail-closed assumption-panic decision?
    pub(super) fn excuses(&self, row: &TransportObligationResult) -> bool {
        self.excusable && self.names_edge(row)
    }
}

/// The impl-side question for `body`'s own fail-closed decision. `None` unless
/// `body` is a formatting-impl root with no `unsafe` outside std whose bundle
/// recorded at least one excusable key.
///
/// Trust (D1 increment 2): the masked-source conjunct is computed HERE, as
/// [`writer_relative_body_has_masked_source`], rather than handed in — the one
/// difference from the plain scan is core's `Formatter`-as-writer call, which a
/// writer-relative root's own writer-edge row already accounts for.
pub(super) fn writer_relative_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    unresolved_indirect_call: bool,
) -> Option<WriterRelativeRoot> {
    if body.source.promoted.is_some() {
        return None;
    }
    let def_id = body.source.def_id();
    if !formatting_impl_root(tcx, def_id) || super::function_uses_unsafe_outside_std(tcx, body) {
        return None;
    }
    let edge_keys = recorded_writer_edge_keys(tcx.sess, def_id)?;
    if edge_keys.is_empty() {
        return None;
    }
    let masked_source = writer_relative_body_has_masked_source(tcx, body);
    Some(WriterRelativeRoot {
        edge_keys,
        excusable: !masked_source && !unresolved_indirect_call,
        masked_source,
    })
}

/// The one excuse the writer-relative bar plugs into the shared evidence bar.
/// Its facts are read LAZILY: the bar forces the body's verdict first, and the
/// bundle that verdict builds is what records them.
struct WriterEdgeExcuse<'a> {
    sess: &'a Session,
    root: DefId,
    root_path: String,
}

impl trait_panic_free::RowExcuse for WriterEdgeExcuse<'_> {
    fn assumption_panic_rows_excused(
        &self,
        transport_results: &[TransportObligationResult],
    ) -> bool {
        let Some(edge_keys) = recorded_writer_edge_keys(self.sess, self.root) else {
            return false;
        };
        // EVERY folded site is judged, not the aggregate's representative: the
        // aggregate names only its first marked site.
        let fold_sites = super::session_panic_freedom_fold_sites(self.sess, &self.root_path);
        // Trust: keep main's authenticated P-SPLIT keys when the compact-slot
        // change moves row judgement into a session-free helper.
        // Trust (P-UB, absent UB-check members, 2026-11-08): and P-UB's absent
        // `precondition_check` keys, judged per folded site exactly as the
        // P-SPLIT keys are.
        let split_keys = recorded_premise_discharged_keys(self.sess, self.root);
        if std::env::var_os("TRUST_PF_BAR_TRACE").is_some()
            && let Some(sites) = fold_sites.as_deref()
        {
            for site in sites {
                if !text_names_writer_edge(site, &edge_keys)
                    && !text_names_writer_edge(site, &split_keys)
                {
                    eprintln!("[PF_BAR] non-writer fold site for {}: {site}", self.root_path);
                }
            }
        }
        writer_edge_rows_excused(transport_results, &edge_keys, &split_keys, fold_sites.as_deref())
    }

    fn disposition_excused(
        &self,
        vc_kind: Option<&VcKind>,
        disposition: &TrustDisposition,
    ) -> bool {
        let Some(edge_keys) = recorded_writer_edge_keys(self.sess, self.root) else {
            return false;
        };
        // Trust (96a18b, P-SPLIT): the aggregate's VC names its FIRST marked
        // site, which the names-split rewrite can make a machinery callee
        // rather than a writer edge. Every site of that fold was already
        // judged in `assumption_panic_rows_excused`; a representative naming
        // a recorded machinery callee is discharged by the same evidence.
        // Trust (P-UB, absent UB-check members, 2026-11-08): so is one naming an
        // absent UB-check member — the 1.101 finishers make it the FIRST marked
        // site (`<Split<'_, u8, _> as Iterator>::next`'s inlined `Iter::new`).
        let split_keys = recorded_premise_discharged_keys(self.sess, self.root);
        matches!(disposition.status, TrustStatus::RuntimeChecked)
            && vc_kind.is_some_and(|kind| {
                vc_names_writer_edge(kind, &edge_keys)
                    || (!split_keys.is_empty() && vc_names_writer_edge(kind, &split_keys))
            })
    }
}

/// THE WRITER-RELATIVE BAR: is `instance` a formatting impl that is panic-free
/// relative to its `Formatter`'s writer? Read only by
/// `fmt_termination_dyn::formatter_sink_basis` (the formatting sinks). See the
/// module docs.
pub(super) fn fmt_impl_is_writer_relative_panic_free<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    root_def_id: DefId,
) -> bool {
    let ty::InstanceKind::Item(def_id) = instance.def else {
        return false;
    };
    if instance.args.has_non_region_param() {
        return false;
    }
    // The SAME pre-conjuncts the absolute bar asks, in the same order.
    if !dyn_dispatch_reliance::target_admits_independent_verdict(tcx, def_id, root_def_id) {
        return false;
    }
    if !formatting_impl_root(tcx, def_id) {
        return false;
    }
    let body = tcx.instance_mir(instance.def);
    // Trust (D1 increment 2): the root-side masked-source answer
    // (`writer_relative_body_has_masked_source`), the same one its own decision
    // used — the two sides of the class never disagree about the mask.
    if super::function_uses_unsafe_outside_std(tcx, body)
        || writer_relative_body_has_masked_source(tcx, body)
        || super::function_has_unresolved_indirect_call(tcx, body)
    {
        return false;
    }
    let excuse = WriterEdgeExcuse {
        sess: tcx.sess,
        root: def_id,
        root_path: trust_mir_extract::safe_def_path_str(tcx, def_id),
    };
    trait_panic_free::instance_discharges_panic_freedom_modulo(tcx, instance.def, &excuse).is_ok()
        // Positive evidence that the class applies at all (the modulo bar passes
        // vacuously for a body with nothing to excuse, which the absolute bar has
        // already been asked about).
        && recorded_writer_edge_keys(tcx.sess, def_id).is_some_and(|keys| !keys.is_empty())
}

/// Is `def_id` alloc's `fmt::format` — the function `format!` calls with its
/// `fmt::Arguments`, formatting into a fresh `String`? Crate authenticated by
/// lang-item ownership (`String`) AND artifact residency, never by crate name.
///
/// Trust (R2 residency, 2026-09-28): ownership alone is not identity. A
/// `#![no_std]` graph never loads `alloc`, so a verify-off dependency declaring
/// `#[lang = "String"]` OWNS the anchor, and its own `fmt::format` was accepted
/// here as a std sink for a writer-relative formatter. The impostor CALL was
/// still masked fail-closed by the crate rule of
/// `callee_is_masked_fail_closed_dispatch`, so this was a belt, not a false
/// proof; but the refusal lost its writer-relative sink note. The residency
/// conjunct is the one `crate_is_authentic_{foundational,core,std}` carry. Pin:
/// `tests/ui/trust/fmt_writer_relative_string_lang_item_sink_impostor_refuted.rs`.
fn def_is_alloc_fmt_format(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.lang_items().string().is_some_and(|string| string.krate == def_id.krate)
        && trust_mir_extract::is_real_sysroot_crate(tcx, def_id.krate)
        && tcx.opt_item_name(def_id).is_some_and(|name| name.as_str() == "format")
        && super::def_path_has_module_segment(tcx, def_id, "fmt")
}

/// Trust (D1 increment 1): may a formatter admitted on the WRITER-RELATIVE basis
/// be packed into a `fmt::Arguments` in `body`? Only when every call in `body`
/// that takes a value mentioning `fmt::Arguments` is a sink that supplies a std
/// writer — std's `_print`/`_eprint` (stdout/stderr) or alloc's `fmt::format`
/// (`String`) — and no `Arguments` can leave the body through its signature.
///
/// Refusal-only belt: a consumer that can hand the formatter an arbitrary writer
/// (`fmt::write(&mut w, ..)`, `w.write_fmt(..)`, a user function) already carries
/// a fail-closed row of its own in every shape measured, but the writer-relative
/// premise is discharged by the sink, so the sink is named rather than inferred.
/// Over-refuses at `-O2` where `format!`'s body is inlined; that is accepted.
pub(super) fn body_formats_only_into_recognized_sinks<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> bool {
    let Some(arguments) = tcx.lang_items().get(LangItem::FormatArguments) else {
        return false;
    };
    let mentions_arguments = |ty: Ty<'tcx>| {
        ty.walk()
            .filter_map(|arg| arg.as_type())
            .any(|t| matches!(t.kind(), ty::Adt(adt, _) if adt.did() == arguments))
    };
    if mentions_arguments(body.return_ty())
        || body.args_iter().any(|local| mentions_arguments(body.local_decls[local].ty))
    {
        return false;
    }
    for block in body.basic_blocks.iter() {
        let (TerminatorKind::Call { func, args, .. } | TerminatorKind::TailCall { func, args, .. }) =
            &block.terminator().kind
        else {
            continue;
        };
        if !args.iter().any(|arg| mentions_arguments(arg.node.ty(&body.local_decls, tcx))) {
            continue;
        }
        let Some((callee, _)) = func.const_fn_def() else {
            return false;
        };
        if !(super::def_is_std_print_backend(tcx, callee) || def_is_alloc_fmt_format(tcx, callee)) {
            return false;
        }
    }
    true
}

/// The disclosure note a writer-relative root's advisory carries.
///
/// Trust (D1 increment 2): the note now also names the NESTED-FORMATTER edges
/// (`<dyn core::fmt::Debug>::fmt` inside core's debug builders) the class
/// excuses. The leading phrase is unchanged, so every existing pin still reads it.
pub(super) fn writer_relative_note(func_path: &str) -> String {
    format!(
        "panic-free relative to its `Formatter`'s writer: every unproved row of `{func_path}` \
         is a call through its own `Formatter`'s writer (`<dyn core::fmt::Write>::write_str` / \
         `write_char`) or a nested formatter whose every possible target panics only through \
         that writer (`<dyn core::fmt::Debug>::fmt` in `#[derive(Debug)]`'s builders), which \
         this compilation cannot see. The impl is a CONDITIONAL pass, never proved: it panics \
         exactly when that writer panics. std's formatting sinks (`println!`/`eprintln!`, \
         `format!`, `to_string`, `main`'s error report) supply a std writer and discharge the \
         condition; a writer chosen elsewhere (`write!(my_writer, ..)`, a direct `fmt` call) \
         does not, and stays refused there. Termination is not part of this claim. \
         `-Z trust-policy=certify` refuses this row (D1 increments 1-2; docs/TCB.md \
         \"Formatting premises\")"
    )
}
