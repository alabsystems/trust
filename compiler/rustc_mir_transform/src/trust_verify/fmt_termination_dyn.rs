//! Trust (D1 residual, 2026-09-24): `main`'s `Termination` sink when the error
//! it formats is FOREIGN or DYNAMIC, and what that error can dispatch back into.
//!
//! ## The hole, measured on stage-1 (wave 0 landed, `a8c853de6f`)
//!
//! ```text
//! struct E;
//! impl Debug for E { fn fmt(&self, _: &mut Formatter<'_>) -> fmt::Result { Err(fmt::Error) } }
//! impl Display for E { fn fmt(..) -> fmt::Result { Ok(()) } }
//! impl Error for E {}
//! fn main() -> Result<(), Box<dyn Error>> { Err(Box::new(E)) }
//! ```
//!
//! built rc=0 with ZERO warnings and exited 101 ("a formatting trait
//! implementation returned an error when the underlying stream did not",
//! `std/src/io/mod.rs`). `lang_start` calls `<Result<(), Box<dyn Error>> as
//! Termination>::report`, which writes `Error: {err:?}` to stderr; `Box`'s
//! `Debug` forwards to `<dyn Error as Debug>::fmt`, whose vtable slot is `E`'s
//! own impl. Wave 0's `Termination` check (`fmt_error_transparency::
//! entry_termination_error_opaque_ty`) deliberately DEFERS an error type that
//! reaches foreign/dynamic code and names no local definition to the policy-B
//! entry row — and that row's statement ("dispatches the `Debug`/`Drop` of a
//! foreign or dynamic type this compilation does not verify") is false here:
//! the `Debug` that returned `Err` is this crate's. Same result, all rc=0 then
//! exit 101: `Err(E)?` (the coercion is inside alloc's `From<E> for Box<dyn
//! Error>`), `Err(E.into())`, `Box<dyn Debug>`, `Box<dyn Error + Send + Sync>`,
//! a local generic `fn boxit<T: Error>(t: T) -> Box<dyn Error>`, and
//! `Box::new(fmt::from_fn(|_| Err(fmt::Error)))` as `Box<dyn Debug>` (the
//! offending code is a CLOSURE, not an impl).
//!
//! ## The rule
//!
//! When `main`'s return type carries at least one error layer that is deferred
//! to the entry row, EVERY LOCAL FORMATTING BODY — every local fn, method or
//! closure that takes a `core::fmt::Formatter` (anywhere in a parameter type)
//! and returns a `Result` (or a generic/opaque type that could be one), plus
//! every GENERIC one (a parameter type that could be instantiated to
//! `Formatter`) returning `Result<_, fmt::Error>` or a type that could become
//! it — must
//! pass the SAME predicate the `Termination` and packer sinks read:
//! [`formatter_passes_sink_bar`], the shared panic-freedom bar AND error
//! transparency. Otherwise `main` is refused (strict lanes; same gating as the
//! wave-0 `Termination` check, whose caller this is).
//!
//! Layers that are NOT deferred are wave 0's business and unchanged; foreign and
//! sysroot formatting code reached through a deferred layer keeps the policy-B
//! entry row (reported, CONDITIONAL, fatal under `certify`) exactly as ruled on
//! 2026-09-16 — that row's statement is true of FOREIGN code. What this module
//! removes is its use as cover for LOCAL code.
//!
//! ## Why the candidate set is enumerated from the crate's formatting bodies and
//! not from its coercion sites (the C-FLOW enumeration)
//!
//! The request was "every local type this crate unsize-coerces to `dyn Error` /
//! `dyn Debug`", enumerated from MIR coercion sites. That set is INCOMPLETE as a
//! soundness boundary, measured: `Err(E)?` and `Err(E.into())` coerce `E` inside
//! alloc's generic `From` impl (no coercion in this crate's MIR); `io::Error::new`
//! / `io::Error::other` coerce it inside std; `Vec<E>`'s `Debug` mints a `&dyn
//! Debug` for `E` inside alloc's `debug_list`; a local polymorphic `fn boxit<T:
//! Error>` coerces a type PARAMETER; and `fmt::from_fn` needs no coercion of a
//! local TYPE at all — the dispatched code is a closure. Every one of those
//! built rc=0 and exited 101 (or was already refused for an unrelated row).
//! C-FLOW's enumeration is bundle-local by design and poisons exactly these
//! shapes; closing the gaps would mean re-implementing monomorphization
//! collection over foreign generic bodies.
//!
//! The set enumerated here is a SUPERSET of every local body the dispatch can
//! reach, and needs no coercion argument at all:
//!
//! * A `dyn` vtable whose slot is `Debug::fmt` (or any `fmt` trait method) for a
//!   `Self` that is local dispatches into that `Self`'s impl; by the orphan rules
//!   the impl of a foreign trait for a local type is in this crate.
//! * Foreign/sysroot formatting code reaches local code as a NESTED formatter —
//!   a `fmt`-trait impl (through a vtable, a `debug_*` builder's `&dyn Debug`, or
//!   a packed `fmt::Arguments`) or a `Fn(&mut Formatter) -> fmt::Result` value
//!   (`fmt::from_fn`). Every such body has a `Formatter` parameter and returns
//!   `fmt::Result`, so it is in the set.
//! * A local helper that a local formatting impl calls statically is in that
//!   impl's own bundle, so the impl's bar and ET cover it.
//!
//! So no local code reachable from `Termination::report` escapes the check,
//! whatever the coercion route. The price is over-inclusion (a formatting body
//! the dyn value can never reach is still held to the bar); measured cost below.
//!
//! ## Soundness argument (innermost frame)
//!
//! Suppose `Termination::report` on a deferred layer panics. Either (a) a panic
//! in a frame of foreign/sysroot code — the entry row's policy-B statement, as
//! before; or (b) a panic in a local frame — every local frame reachable from
//! foreign formatting code is a formatting body in the set or in a set member's
//! bundle, and each set member is verified panic-free by the shared bar; or (c)
//! std's own "formatter returned `Err` while the stream did not" panic, which
//! needs some formatter to return `Err` spontaneously: a sysroot one does not
//! (P1, the premise the `println!("{}", 5u32)` tolerance already rests on), a
//! foreign one is (a), and a local one is excluded by ET version 0 (it can
//! return only `Ok(())`).
//!
//! ## Refusal-only
//!
//! This module adds one standalone refusal and one warning. It never excuses a
//! row, never marks anything proved, and never changes the entry row. The one
//! predicate it defines ([`formatter_passes_sink_bar`]) is also what the packer
//! arm and the wave-0 `Termination` check read, so a future widening of the
//! sink bar (the writer-relative increments) reaches this check with no second
//! copy to keep in step.

use rustc_hir::def::DefKind;
use rustc_middle::mir::Body;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::sym;

use super::{
    PreparedDiagnostic, PreparedDiagnosticChild, PreparedLocatedDiagnostic, dyn_dispatch_reliance,
    fmt_error_transparency, fmt_writer_relative,
};

/// How many `Result<Result<.., E2>, E1>` layers are peeled looking for a
/// deferred error type. Mirrors `fmt_error_transparency`'s bound; past it that
/// module's check has already refused `main`.
const MAX_TERMINATION_NESTING: usize = 8;

/// How many further offending bodies the refusal names after the first.
const MAX_NAMED_OFFENDERS: usize = 8;

/// THE formatting-sink predicate: the shared panic-freedom bar
/// (`dyn_dispatch_reliance::dyn_target_is_verified_panic_free`, unchanged) AND
/// error transparency (`fmt_error_transparency::impl_is_error_transparent`).
///
/// ONE definition, read by the packer / `to_string` arm
/// (`fmt_trait_impl_is_verified_panic_free`), by the wave-0 `Termination` check
/// through it, and by this module's dynamic-reach check. A sink that panics on a
/// spontaneous `Err` needs both conjuncts; any future widening (the
/// writer-relative bar) must be made HERE so all three consumers move together.
///
/// Trust (D1 increment 1, 2026-09-25): widened HERE, as this note required, to
/// `(absolute || writer-relative) && ET` — see [`formatter_sink_basis`]. All three
/// consumers are sinks that supply a std writer (stdout/stderr, `String`), which
/// is what discharges the writer-relative premise; the packer arm additionally
/// checks that its `fmt::Arguments` reach only such a sink.
pub(super) fn formatter_passes_sink_bar<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    root_def_id: DefId,
) -> bool {
    formatter_sink_basis(tcx, instance, root_def_id).is_some()
}

/// Trust (D1 increment 1): WHICH panic-freedom bar a formatter passed at a sink.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum SinkBasis {
    /// The shared, absolute bar (`dyn_target_is_verified_panic_free`).
    Absolute,
    /// Only the writer-relative bar (`fmt_writer_relative`): panic-free RELATIVE
    /// TO its `Formatter`'s writer. Sound only where the sink supplies the writer —
    /// a consumer that can hand the formatter an arbitrary writer must refuse it
    /// (the packer arm checks its `fmt::Arguments` consumers for exactly that).
    WriterRelative,
}

/// Trust (D1 increment 1): the formatting-sink predicate with its basis named:
/// `(absolute bar || writer-relative bar) && error transparency`. `None` =
/// refused. The absolute bar is asked FIRST and is unchanged, so every formatter
/// that passed before still passes on the same basis.
pub(super) fn formatter_sink_basis<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    root_def_id: DefId,
) -> Option<SinkBasis> {
    let basis =
        if dyn_dispatch_reliance::dyn_target_is_verified_panic_free(tcx, instance, root_def_id) {
            SinkBasis::Absolute
        } else if fmt_writer_relative::fmt_impl_is_writer_relative_panic_free(
            tcx,
            instance,
            root_def_id,
        ) {
            SinkBasis::WriterRelative
        } else {
            return None;
        };
    let transparent = fmt_error_transparency::impl_is_error_transparent(tcx, instance);
    if std::env::var_os("TRUST_PF_BAR_TRACE").is_some() {
        eprintln!(
            "[PF_BAR] sink basis instance={instance:?} basis={basis:?} error_transparent={transparent}"
        );
    }
    transparent.then_some(basis)
}

/// `main`'s (normalized) return type and every error layer of it that the wave-0
/// check defers to the policy-B entry row. `None` when `body` is not the
/// `EntryFnType::Main` entry.
fn entry_main_deferred_error_layers<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Option<(Ty<'tcx>, Vec<Ty<'tcx>>)> {
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
    let mut memo = Default::default();
    let mut deferred = Vec::new();
    let mut current = ret_ty;
    for _ in 0..MAX_TERMINATION_NESTING {
        let ty::Adt(adt, args) = current.kind() else { break };
        if !tcx.is_diagnostic_item(sym::Result, adt.did()) {
            break;
        }
        let err_ty = args.type_at(1);
        if fmt_error_transparency::error_layer_defers_to_entry_row(tcx, err_ty, &mut memo) {
            deferred.push(err_ty);
        }
        current = args.type_at(0);
    }
    Some((ret_ty, deferred))
}

/// Does `ty` mention `core::fmt::Formatter` anywhere in its type tree?
fn ty_mentions_formatter<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    ty.walk().filter_map(|arg| arg.as_type()).any(|t| {
        matches!(t.kind(), ty::Adt(adt, _) if tcx.is_diagnostic_item(sym::Formatter, adt.did()))
    })
}

/// Is this local body FORMATTING-SHAPED — could foreign formatting code call it
/// as a nested formatter? A `Formatter` in some parameter type, and a return
/// type that is `Result` or could become one (a type parameter or an alias: fail
/// closed toward inclusion). Coroutines and coroutine-closures return futures /
/// resume, never `fmt::Result`, and are not callable as a formatter.
fn local_body_is_formatting_shaped(tcx: TyCtxt<'_>, local: LocalDefId) -> bool {
    let def_id = local.to_def_id();
    let (inputs, output) = match tcx.def_kind(def_id) {
        DefKind::Fn | DefKind::AssocFn => {
            let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
            (sig.inputs().to_vec(), sig.output())
        }
        DefKind::Closure => {
            let closure_ty = tcx.type_of(def_id).instantiate_identity().skip_norm_wip();
            let ty::Closure(_, args) = closure_ty.kind() else { return false };
            let sig = args.as_closure().sig().skip_binder();
            (sig.inputs().to_vec(), sig.output())
        }
        _ => return false,
    };
    let could_be_instantiated = |ty: Ty<'_>| ty.has_non_region_param() || ty.has_aliases();
    // A body that NAMES `Formatter` in a parameter: any `Result` (or a type that
    // could become one) makes it a candidate.
    if inputs.iter().any(|input| ty_mentions_formatter(tcx, *input)) {
        return match output.kind() {
            ty::Adt(adt, _) => tcx.is_diagnostic_item(sym::Result, adt.did()),
            _ => could_be_instantiated(output),
        };
    }
    // A GENERIC body can be instantiated with `Formatter` without naming it
    // (`fn g<W: fmt::Write>(w: &mut W) -> fmt::Result`, handed to
    // `fmt::from_fn(g::<Formatter<'_>>)`). A nested formatter must return exactly
    // `fmt::Result`, so such a body is a candidate when its return type is
    // `Result<_, fmt::Error>` or could be instantiated to it.
    if inputs.iter().any(|input| could_be_instantiated(*input)) {
        return match output.kind() {
            ty::Adt(adt, args) if tcx.is_diagnostic_item(sym::Result, adt.did()) => {
                let err_ty = args.type_at(1);
                ty_is_core_fmt_error(tcx, err_ty) || could_be_instantiated(err_ty)
            }
            ty::Adt(..) => false,
            _ => could_be_instantiated(output),
        };
    }
    false
}

/// Is `ty` exactly `core::fmt::Error` (the error type of `fmt::Result`)? It
/// carries no diagnostic item, so it is matched by crate (`core`) and def path
/// (`fmt::Error`), which a user type cannot spell.
pub(super) fn ty_is_core_fmt_error<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let ty::Adt(adt, _) = ty.kind() else { return false };
    let did = adt.did();
    if tcx.crate_name(did.krate) != sym::core {
        return false;
    }
    let names: Vec<Option<String>> = tcx
        .def_path(did)
        .data
        .iter()
        .map(|segment| segment.data.get_opt_name().map(|name| name.to_string()))
        .collect();
    names == [Some("fmt".to_string()), Some("Error".to_string())]
}

/// Every local formatting-shaped body of this crate, in `mir_keys` order.
/// Restricted to the coverage universe (`trust_coverage_eligible_body`): the
/// excluded bodies are consts/statics, Clean-origin emitter bodies, and
/// statically-dead contract closures, none of which is a callable formatter.
fn local_formatting_bodies(tcx: TyCtxt<'_>) -> Vec<LocalDefId> {
    tcx.mir_keys(())
        .iter()
        .copied()
        .filter(|&local| super::trust_coverage_eligible_body(tcx, local))
        .filter(|&local| local_body_is_formatting_shaped(tcx, local))
        .collect()
}

/// Strict-lane refusal: `main` returns an error layer deferred to the entry row
/// (so its `Termination::report` formats a foreign or dynamic value), and some
/// local formatting body — which that value's formatting can dispatch into —
/// does not pass [`formatter_passes_sink_bar`].
///
/// Called ONLY by `fmt_error_transparency::abort_on_entry_termination_error_opacity`
/// after its own per-layer check found nothing to refuse, so it inherits that
/// check's lane gating (fail-closed and not memory-safe) and never double-reports.
pub(super) fn abort_on_entry_termination_dyn_formatter_reach<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) {
    if let Some(diagnostic) = prepare_entry_termination_dyn_formatter_reach(tcx, body, func_path) {
        diagnostic.emit(tcx);
    }
}

pub(super) fn prepare_entry_termination_dyn_formatter_reach<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) -> Option<PreparedLocatedDiagnostic> {
    let Some((ret_ty, deferred)) = entry_main_deferred_error_layers(tcx, body) else {
        return None;
    };
    if deferred.is_empty() {
        return None;
    }
    let root_def_id = body.source.def_id();
    let offenders: Vec<DefId> = local_formatting_bodies(tcx)
        .into_iter()
        .map(LocalDefId::to_def_id)
        .filter(|&def_id| {
            let instance =
                ty::Instance::new_raw(def_id, ty::GenericArgs::identity_for_item(tcx, def_id));
            !formatter_passes_sink_bar(tcx, instance, root_def_id)
        })
        .collect();
    let Some(&first) = offenders.first() else {
        return None;
    };
    let ret_label = with_no_trimmed_paths!(ret_ty.to_string());
    let deferred_labels: Vec<String> =
        deferred.iter().map(|ty| with_no_trimmed_paths!(format!("`{ty}`"))).collect();
    let first_label = with_no_trimmed_paths!(tcx.def_path_str(first));
    let span = body.span;
    let header = format!(
        "Trust full verification failed for `{func_path}`: `main` returns `{ret_label}`, whose \
         `<_ as Termination>::report` formats the foreign or dynamic error {} with `Debug`, \
         which can dispatch into this crate's formatting code, and `{first_label}` is not \
         established panic-free and error-transparent",
        deferred_labels.join(", "),
    );
    let mut children = vec![
        PreparedDiagnosticChild::SpanNote(
            tcx.def_span(first),
            "this local formatting body can be reached from `main`'s error report".into(),
        ),
        PreparedDiagnosticChild::Note(
            "a foreign or dynamic error value (`Box<dyn Error>`, `Box<dyn Debug>`, `io::Error`, ...) \
             can hold a value of a LOCAL type — through `Box::new`, `?`/`.into()` (std's `From`), \
             `io::Error::new`, a generic helper, or a `fmt::from_fn` closure — and its `Debug` then \
             dispatches into that local code. std's `Termination::report` PANICS (\"a formatting \
             trait implementation returned an error when the underlying stream did not\") when a \
             formatter returns `Err` while stderr did not fail. Since no coercion route can be \
             enumerated completely from this crate's MIR, every local body that takes a \
             `fmt::Formatter` and returns a `Result` is held to the formatting-sink bar: verified \
             panic-free in this crate AND returning `Err` only when its writer did"
                .into(),
        ),
    ];
    if !fmt_error_transparency::impl_is_error_transparent(
        tcx,
        ty::Instance::new_raw(first, ty::GenericArgs::identity_for_item(tcx, first)),
    ) {
        children.push(PreparedDiagnosticChild::Note(format!(
            "error transparency: `{first_label}` is not recognized as returning `Err` only when \
             its `Formatter`'s writer did; this compiler currently recognizes a formatting body as \
             error-transparent only when every value it can return is `Ok(())`, the result of \
             its own `Formatter`'s `write_str`/`write_char`, an error such a call returned \
             (propagated by `?`), or the result of a `#[derive(Debug)]` helper whose nested \
             formatters are all transparent"
        )));
    }
    if offenders.len() > 1 {
        let rest: Vec<String> = offenders[1..]
            .iter()
            .take(MAX_NAMED_OFFENDERS)
            .map(|&def_id| with_no_trimmed_paths!(format!("`{}`", tcx.def_path_str(def_id))))
            .collect();
        let more = offenders.len() - 1 - rest.len();
        children.push(PreparedDiagnosticChild::Note(format!(
            "also not established: {}{}",
            rest.join(", "),
            if more > 0 { format!(" and {more} more") } else { String::new() },
        )));
    }
    children.push(PreparedDiagnosticChild::Note(
        "return `()`, `ExitCode`, or an error type this crate owns whose `Debug` is verified; \
         or make every local formatting body verified panic-free and returning `Ok(())`"
            .into(),
    ));
    Some(PreparedLocatedDiagnostic {
        span,
        diagnostic: PreparedDiagnostic { aborting: true, header, children },
    })
}

/// Trust (D1 residual, 2026-09-24): the policy-B entry-`Termination` row made
/// VISIBLE. It was published to the transport/JSON channel only, so on bare
/// `trustc` a `main` with no other row built with zero warnings while `targo`
/// counted it CONDITIONAL. Diagnostic only: the row, its outcome, and the
/// `certify` refusal are unchanged. The caller skips `certify`, which already
/// refuses this dispatch with an error.
pub(super) fn warn_entry_termination_dispatch_reported<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) {
    prepare_entry_termination_dispatch_warning(tcx, body, func_path).emit(tcx);
}

pub(super) fn prepare_entry_termination_dispatch_warning<'tcx>(
    _tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) -> PreparedLocatedDiagnostic {
    let ret_label = with_no_trimmed_paths!(body.return_ty().to_string());
    let span = body.span;
    let header = format!(
        "Trust verification advisory for `{func_path}`: `main`'s return type \
         `{ret_label}` is dispatched by `lang_start` through `<_ as Termination>::report` \
         into foreign or dynamic code this compilation does not verify"
    );
    let children = vec![PreparedDiagnosticChild::Note(
        "reported gap (policy B): a panic in that `Debug`/`Drop` is a defined abort during \
         error reporting; the row is counted CONDITIONAL and `-Ztrust-policy=certify` \
         refuses it. Local formatting code the value can reach is still held to the \
         formatting-sink bar (a build error otherwise)"
            .into(),
    )];
    PreparedLocatedDiagnostic {
        span,
        diagnostic: PreparedDiagnostic { aborting: false, header, children },
    }
}
