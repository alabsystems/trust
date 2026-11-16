//! Trust: Prepare the original full-verification failure diagnostic as DATA.
//! Predicates, source queries, traces and withheld-verdict effects remain in
//! their original order. This module grants no proof authority or favorable
//! policy outcome; the parent owns the single eventual diagnostic emission.
//! Extracted from immutable commit 28dd079df1f; this checkpoint is UNCOMPILED.

use super::*;

fn prepare_runtime_checked_std_member_withheld<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
    artifacts: &VerificationArtifacts,
    masked_fail_closed_source: bool,
) -> Option<PreparedDiagnostic> {
    const DISPOSITION_NOTE: &str = "the bundled std-member runtime-checked disposition covers \
         std/core/alloc's OWN internal runtime check only (docs/TCB.md): a kept bundle's \
         whole-function panic-freedom row is reported as runtime-checked, so it cannot also \
         stand for user code this function reaches. Options: move that call into the crate \
         that owns the code and verify it there; use a verified local or foundational type; \
         or build with `-Z trust-policy=advisory`";
    let (headline, reason): (&str, Option<String>) = if masked_fail_closed_source {
        (
            "a bundled std/core/alloc member's internal Assert was kept as a runtime check, and \
             this function also reaches code that carries no verdict",
            Some(String::from(
                "it calls into a verify-off dependency, instantiates a std/core/alloc routine at \
                 a dependency's type or a trait object (whose `dyn` dispatch runs code this \
                 compilation does not verify), reifies such a function, or drops a value whose \
                 glue runs such code — `TRUST_MASK_TRACE=1` names the call",
            )),
        )
    } else if function_uses_unsafe_outside_std(tcx, body) {
        (
            "a bundled std/core/alloc member's internal Assert was kept as a runtime check, and \
             this function uses `unsafe` outside std",
            None,
        )
    } else if !function_format_args_all_foundational_display(tcx, body) {
        (
            "a value is formatted through a user `Display`/`Debug` implementation whose \
             panic-freedom was not established",
            None,
        )
    } else if let Some(site) = inlined_sysroot_panic::inlined_foreign_panic_site(tcx, body) {
        // Trust (2026-09-29): the disposition stands for std's OWN internal
        // check; a foreign panic path the MIR inliner copied into THIS body is not
        // one (see `inlined_sysroot_panic`). Refusal-only; at the verifying
        // default it can fire only on a dependency's `#[rustc_force_inline]` fn.
        (
            "a bundled std/core/alloc member's internal Assert was kept as a runtime check, and \
             this body carries a foreign panic path the MIR inliner copied into it",
            Some(inlined_sysroot_panic::inlined_foreign_panic_note(&site)),
        )
    } else if let Some(reach) = fmt_machinery_reach_without_verdict(tcx, body) {
        (
            "a bundled std/core/alloc member's internal Assert was kept as a runtime check, and \
             the formatting machinery this function calls can reach code that carries no verdict",
            Some(reach),
        )
    } else {
        return None;
    };
    let mut diag = PreparedDiagnostic {
            aborting: true,
            header: (format!("Trust full verification failed for `{func_path}`: {headline}")).into(),
            children: Vec::new(),
        };
    if let Some(reason) = reason {
        diag.children.push(PreparedDiagnosticChild::Note((reason).into()));
    }
    diag.children.push(PreparedDiagnosticChild::Note((DISPOSITION_NOTE).into()));
    for member in &artifacts.runtime_checked_std_members {
        diag.children.push(PreparedDiagnosticChild::Note((format!("runtime-checked bundled member `{}`", member.def_path)).into()));
    }
    Some(diag)
}

/// Original source/integrity refusals are not discharged by a row theorem.
/// This classification is process-owned preparation state, never serialized
/// and never a proof. Its source queries and predicates run only once.
#[derive(Debug)]
pub(super) enum NonwaivableFullFailure {
    ForeignDrop,
    UnchargedConsumer,
    NonFoundationalFormatting,
    NativeLoweringIncomplete,
    RuntimeCheckedMember,
    OriginalFloors {
        malformed_native: bool,
        native_authority_integrity: bool,
        masked_source: bool,
        assumption_panic: bool,
        fail_closed_source: bool,
        indirect_call: bool,
        masked_dispatch: bool,
        nonfoundational_format: bool,
        inlined_panic: bool,
        zero_publisher_refusal: bool,
    },
}

enum FullFailureCause {
    Nonwaivable(NonwaivableFullFailure),
    CandidateRowDebt,
}

pub(super) struct PreparedFullFailure {
    diagnostic: PreparedDiagnostic,
    cause: FullFailureCause,
}

/// A live fact about ORIGINAL failure classification, not mathematical
/// authority. Preparing a checked alternative additionally requires complete
/// exact native debt coverage. Selecting it still requires the fresh opaque
/// current-artifact judgment and original stop/clock/row-set checks.
pub(super) struct CandidateRowDebt<'prepared>(&'prepared PreparedFullFailure);

impl PreparedFullFailure {
    fn nonwaivable(cause: NonwaivableFullFailure, diagnostic: PreparedDiagnostic) -> Self {
        Self { diagnostic, cause: FullFailureCause::Nonwaivable(cause) }
    }

    pub(super) fn into_original(self) -> PreparedDiagnostic { self.diagnostic }

    pub(super) fn diagnostic(&self) -> &PreparedDiagnostic { &self.diagnostic }

    pub(super) fn nonwaivable_cause(&self) -> Option<&NonwaivableFullFailure> {
        match &self.cause {
            FullFailureCause::Nonwaivable(cause) => Some(cause),
            FullFailureCause::CandidateRowDebt => None,
        }
    }

    pub(super) fn candidate_row_debt(&self) -> Option<CandidateRowDebt<'_>> {
        match &self.cause {
            FullFailureCause::CandidateRowDebt => Some(CandidateRowDebt(self)),
            FullFailureCause::Nonwaivable(_) => None,
        }
    }
}

pub(super) fn prepare_full_verification_failure<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
    artifacts: &VerificationArtifacts,
    // The tally of the rows this function publishes: its clock count is the
    // engine status note's `timed_out=` (`verifier_status_timed_out_note`).
    published_rows: PublishedRowTally,
    // Trust (2026-10-10, ZERO-ROW-GATE): the publisher's own verdict on a body with
    // zero bridged obligations (`zero_obligation_native_vacuously_clean`); `None`
    // when the body has bridged obligations.
    zero_obligation_vacuously_clean: Option<bool>,
) -> Option<PreparedFullFailure> {
    let summary = &artifacts.proof_results.summary;
    // S4 is computed before every possible successful strict return. Public
    // native Proved rows are claimable only when their exact current compiler
    // rows carry private static authority; this check never rewrites the public
    // run or its counters.
    let native_authority_validation_failures = native_proved_authority_validation_failures(
        tcx.sess,
        artifacts.full_verification.as_ref(),
        &artifacts.results,
        &artifacts.result_bindings,
        &artifacts.proof_authorities,
    );
    // Trust (policy B as ruled, 2026-09-14): which of this function's callees are
    // vanilla-semantics sysroot routines. Consulted by BOTH fail-closed
    // assumption-panic sites below; see `function_vanilla_sysroot_callees`.
    // Trust (2026-09-16, refuted): `Box<i32, dep::DepAlloc>` (allocator_api) has NO
    // `#[global_allocator]` in the graph, so the global-alloc contract discharged
    // "vacuously for `Global`" — while the container's own drop glue calls
    // `<DepAlloc as Allocator>::deallocate`, verify-off user code, and the caller's
    // panic-freedom row came back PROVED. The bridge cannot see this: the
    // extractor's recursion cut lowers `Box` to a by-name `Ty::Adt` with NO fields,
    // so the allocator argument is erased before the drop walk (measured with
    // `TRUST_DROP_WALK_DEBUG=1`: the walk visits `alloc::boxed::Box` and stops).
    // Decided here, where the argument still exists.
    //
    // Narrow on purpose: a FOREIGN ADT (non-local, non-sysroot — a dependency's
    // type) appearing as a type ARGUMENT of a dropped type. A `dyn` payload, a
    // local type and every all-sysroot instantiation are untouched, and a foreign
    // payload carrying its own `Drop` was already refused by
    // `drop_ty_has_masked_fail_closed_glue`. What this adds is the argument with NO
    // `Drop` of its own whose behaviour the container's glue still invokes through
    // a trait — an allocator parameter being the motivating case.
    if let Some(foreign) = body_drops_foreign_adt_argument(tcx, body) {
        return Some(PreparedFullFailure::nonwaivable(
            NonwaivableFullFailure::ForeignDrop,
            PreparedDiagnostic {
            aborting: true,
            header: (format!(
                    "Trust full verification failed for `{func_path}`: this body drops a value \
                     whose type carries `{foreign}`, a type from an unverified dependency, so \
                     the drop glue can run that crate's code (an `Allocator` parameter's \
                     `deallocate`, for instance) with no obligation of this body covering it"
                )).into(),
            children: vec![
            PreparedDiagnosticChild::Note(("the dropped container's own glue is std's, but it dispatches through the \
                 foreign type parameter; options: drop the value in the crate that owns that \
                 type and verify it there, use the default `Global` allocator or a verified \
                 local type, or keep this an honest refusal").into()),
            ],
        }
        ));
    }
    // Trust (2026-09-27): a foreign-reaching closure-driving consumer that no counted
    // row charges — see `foreign_reaching_closure_consumer_edges`. Decided before the
    // zero-inventory return below: such a body often has no row at all.
    //
    // A body whose callable type argument is unresolved
    // (`function_has_unresolved_indirect_call`: `v.iter().any(f)` with `f: &dyn Fn`,
    // a fn pointer, a callable type parameter, through `&`/`&mut`/`Box`) is refused
    // below by that check's own failure, which names the callable; this refusal then
    // stands aside so the specific one is the one reported. Measured when both
    // landed: all eight such revisions of
    // `callable_handed_to_std_through_a_reference.rs` were refused by this generic
    // message ahead of the pinned one. The transport row is published either way.
    let uncharged_consumer_edges =
        uncharged_foreign_closure_consumer_edges(tcx, body, func_path, artifacts);
    if !uncharged_consumer_edges.is_empty() && !function_has_unresolved_indirect_call(tcx, body) {
        return Some(PreparedFullFailure::nonwaivable(
            NonwaivableFullFailure::UnchargedConsumer,
            PreparedDiagnostic {
            aborting: true,
            header: (format!(
                    "Trust full verification failed for `{func_path}`: a closure-driving \
                     consumer call runs code outside the verified closure and the \
                     std/core/alloc TCB, and no obligation charges it"
                )).into(),
            children: vec![
            PreparedDiagnosticChild::Note((format!(
                "uncharged: {}; the native lane lowers such a call to a may-panic marker whose \
                 row is bridge-local, and this body has no counted whole-function \
                 panic-freedom obligation to carry it, so the code it runs (a dependency's \
                 trait impl, a trait object, a type parameter's impl, a foreign closure or \
                 function value) is verified nowhere",
                uncharged_consumer_edges.join(", "),
            )).into()),
            PreparedDiagnosticChild::Note(("options: call the dependency's impl directly (the call is then charged as an \
                 absent callee), use a local or foundational type, or keep this an honest \
                 refusal; `-Z trust-policy=advisory` reports it and continues").into()),
            ],
        }
        ));
    }
    let vanilla_sysroot_callees = {
        // The root-body ledger, UNION the bundle walk's verdicts. Merged HERE
        // and not inside `function_vanilla_sysroot_callees`, because that
        // function's other caller feeds vcgen's non-reentrant callee set, which
        // is computed before this body's bundle exists.
        let charged = with_crate_verification_state(tcx.sess, |state| {
            state.vec_mutator_charged_blocks.get(func_path).cloned()
        });
        let mut merged = function_vanilla_sysroot_callees(tcx, body, charged.as_deref(), true);
        // A key's verdict is the AND of its sightings, which no visit order changes.
        #[allow(rustc::potential_query_instability)]
        for (name, vanilla) in bundle_walk_vanilla_callees(tcx.sess) {
            merged.entry(name).and_modify(|v| *v = *v && vanilla).or_insert(vanilla);
        }
        merged
    };
    // Trust (2026-09-23): every tolerance below judges the FOLD, not its
    // representative row — see `transport_rows_with_fold_sites`.
    let fold_sites = session_panic_freedom_fold_sites(tcx.sess, func_path);
    let judged_rows =
        transport_rows_with_fold_sites(&artifacts.transport_results, fold_sites.as_deref());
    // Trust (refuted 2026-09-16): the bridge folds EVERY absent/foreign panic
    // source of a body into ONE whole-function aggregate row named after a single
    // representative callee, so a tolerated representative (`_print`, or a
    // vanilla sysroot callee) can hide a verify-off dependency call, foreign
    // drop glue, or a sysroot generic instantiated at a foreign type that was
    // co-folded under it (measured: `println!("hi"); dep::boom(3)` and
    // `w.push(1); "3".parse::<dep::P>()` each built exit 0 and panicked in the
    // dependency; the same calls in the other order were refused). Re-derive the
    // masked sources from MIR ONCE here and withhold BOTH tolerances on them.
    let masked_fail_closed_source = function_has_masked_fail_closed_dispatch(tcx, body);
    // Trust (2026-09-14, W1 null twin — the refusal that was riding on the completeness
    // gap): a function that reaches std's print backend with a value formatted through a
    // USER `Display`/`Debug` fails CLOSED whether or not the native lowering failed. The
    // user impl may `panic!`, and its panic edge is not an obligation of this caller — the
    // formatter is reached through the absent `_print`/`_eprint` backend, and the bundled
    // `T::fmt` panic obligations are erased by the ROOT-scope inventory reset — so nothing
    // on the normal path would otherwise refuse it.
    //
    // This gate used to exist ONLY inside the lowering-failure block below, keyed on
    // `native_lowering_failure_is_bundled_std_member_assert_gap_only`. That predicate was a
    // PROXY for "reaches std print dispatch": every `println!` failed to lower on
    // `ReentrantLock::increment_lock_count`'s internal Misaligned/Null asserts, so the block
    // was always entered. The reference-validity discharges (alignment `4db62fdfec`, then
    // the null twin) closed that gap; the bundle lowered cleanly; the block was skipped; and
    // `tests/ui/trust/policy_b/println_user_display_stays_closed.rs` went from FATAL to
    // reported — measured `0 proved, 0 failed, 1 runtime-checked`, exit 0 — on a program
    // whose `S::fmt` divides by zero. The real condition is the transport row for the print
    // backend, which exists on both paths; test that, not the proxy.
    //
    // The general rule this encodes: a refusal keyed on a FAILURE stops protecting anything
    // the moment the failure goes away. Any lane that makes more things lower must enumerate
    // what was keyed on them NOT lowering. Trust (2026-09-29): the inner branch was removed
    // with the lowering-failure tolerance it belonged to; a bundle whose only refused member
    // is an authentic std member's completeness gap now lowers (`runtime_checked_std_member`),
    // and what was keyed on it NOT lowering — the panic-free registries, the premise
    // authenticator, the memory-safe collapse — is enumerated there.
    let dispatches_std_print = judged_rows.iter().any(transport_row_is_std_print_dispatch);
    if dispatches_std_print && !function_format_args_all_foundational_display(tcx, body) {
        let mut diag = PreparedDiagnostic {
            aborting: true,
            header: (format!(
                "Trust full verification failed for `{func_path}`: a value is formatted through a user `Display`/`Debug` implementation whose panic-freedom was not established"
            )).into(),
            children: Vec::new(),
        };
        diag.children.push(PreparedDiagnosticChild::Note(("unlike a foundational std/core/alloc `Display` (for example `<i32 as \
             Display>::fmt`, which runs no user code), an arbitrary user `Display`/`Debug` \
             impl may `panic!` — and its panic edge is not an obligation of this caller \
             (the formatter is reached through the absent std print backend), so it cannot \
             be tolerated. Options: prove the impl panic-free and verify it in its own \
             crate; format a foundational value instead (a primitive, `str`, or `String`); \
             or keep this an honest gap. A derived `Display`/`Debug` is treated the same as \
             a hand-written one").into()));
        // Trust (2026-09-25): name a recursive formatting edge when it is what refused.
        if let Some(note) = fmt_error_transparency::formatting_cycle_note(tcx, body) {
            diag.children.push(PreparedDiagnosticChild::Note((note).into()));
        }
        // Trust (D1 increment 0): name error transparency when it is what refused.
        if let Some(note) = fmt_error_transparency::error_opacity_note(tcx, body) {
            diag.children.push(PreparedDiagnosticChild::Note((note).into()));
        }
        // Trust (D1 increment 1): name an unrecognized consumer of a writer-relative
        // formatter when that is what refused.
        if let Some(note) = writer_relative_sink_refusal_note(tcx, body) {
            diag.children.push(PreparedDiagnosticChild::Note((note).into()));
        }
        // Trust (D4-A, 2026-09-24): name what happened to a DEPENDENCY impl.
        if let Some(note) = fmt_error_transparency::foreign_formatter_note(tcx, body) {
            diag.children.push(PreparedDiagnosticChild::Note((note).into()));
        }
        return Some(PreparedFullFailure::nonwaivable(
            NonwaivableFullFailure::NonFoundationalFormatting,
            diag
        ));
    }
    // Trust (#48): fail closed whenever the native typed-TrustIr lowering did not
    // complete, REGARDLESS of how many public obligations the function has. A
    // lowering failure means an unmodeled construct was present — and after the
    // bridge models the total no-panic calls (`len`, slice iterators, `Ord::min`/
    // `max`/`clamp`, …), a residual failure is dominated by an unmodeled
    // potentially-PANICKING external call (`Option::unwrap`, `u32::pow`) whose
    // panic-freedom the native verifier could not establish. The v1/ay bridge still
    // discharges the vcgen obligations it CAN see (arithmetic/bounds), so a function
    // with a PROVABLE real obligation alongside such a call (e.g.
    // `let x = (a as u32) + 1; x.pow(20)`) would otherwise read as fully proved — a
    // FALSE PROOF, since the call's panic is on no obligation the bridge sees. There
    // is no sound way to certify strict batteries-on verification without complete native
    // evidence, so abort. (The pure case — `summary.total == 0` — is covered here
    // too, before the vacuity gate below.) A remaining TOTAL-but-unmodeled call
    // fails closed conservatively; soundness over permissiveness.
    // Trust (R1-MONO-SUPPRESSION-1): even exact sealed R1 root-row proofs
    // cannot account for the unproduced rows of a discarded native bundle.
    if let Some(run) = artifacts.full_verification.as_ref() {
        if native_run_trust_ir_lowering_failed(run) {
            // Trust (2026-09-29): the policy-B tolerance that used to stand here —
            // which let a lowering failure whose diagnostics were all "a bundled
            // std/core/alloc member was refused for its internal Assert" pass as an
            // advisory — is GONE. It stood in for a DISCARDED bundle: refusing one
            // member dropped every member's rows, so its note ("the only obligation
            // it could not discharge is an internal Assert inside a bundled member")
            // was false whenever the bundle held anything else (a charged
            // `wrapping_div`, a `copy_from_slice` length panic, a dependency reached
            // through core's formatting machinery — all measured exit 0 and
            // panicking). The bundle gate now KEEPS such a member and the root owes
            // a `runtime_checked` row for it (`runtime_checked_std_member`), so its
            // verdict is judged on the success path with every other member's rows
            // intact. A refused member that reaches THIS path is an integrity
            // refusal, a local member, or a non-authentic crate's body, and is fatal
            // below. A sealed R1 proof discharges its own row, never a discarded bundle.
            // A lowering failure means the function was not proved. The
            // memory-safe assumption policy is narrow and cannot weaken a
            // non-demotable strict-verification gate.
            let mut notes = vec![
                "an unmodeled external call (or other unlowerable MIR construct) leaves a panic \
                 path unverified; strict Trust verification requires complete native evidence — \
                 model the call as total, or rewrite it to a verifiable form"
                    .to_string(),
            ];
            // Trust (2026-09-30): this return precedes the indirect-call gate below;
            // name what it refuses too (`uncharged_callable::lowering_failure_gate_notes`).
            notes.extend(uncharged_callable::lowering_failure_gate_notes(tcx, body));
            for diagnostic in run.diagnostics.iter().take(4) {
                notes.push(format!("native full verifier diagnostic: {diagnostic}"));
            }
            let mut diag = PreparedDiagnostic {
            aborting: true,
            header: (format!(
                    "Trust full verification failed for `{func_path}`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established"
                )).into(),
            children: Vec::new(),
        };
            for note in notes {
                diag.children.push(PreparedDiagnosticChild::Note((note).into()));
            }
            // Keep collecting verification results for the rest of the crate.
            // The emitted error still fails the build at the driver checkpoint.
            return Some(PreparedFullFailure::nonwaivable(
            NonwaivableFullFailure::NativeLoweringIncomplete,
            diag
        ));
        }
    }
    // Trust (2026-09-29): the runtime-checked std-member disposition
    // (`runtime_checked_std_member`) stands in for std's OWN internal runtime check
    // and for nothing else — the bar the removed lowering-failure tolerance held,
    // conjunct for conjunct. A kept bundle's rows judge the calls its members make,
    // but not every route into unverified code leaves a row that refuses: the
    // whole-function panic-freedom aggregate folds a dispatch that happens INSIDE a
    // bundled std member, and the default lane reports that aggregate as
    // runtime-checked. MEASURED on this change without this block (stage-1, a
    // release-like std and m3's debug std, strict): `it.count()` on a `&mut dyn
    // Iterator` (the dyn `next` runs inside core's `count`), `fmt::format(a)` of a
    // caller's `fmt::Arguments`, and `filter().count()` beside `drop(io::Error)` or
    // `drop(Waker)` each built exit 0 where the discarded-bundle path had refused
    // them, and the `dyn Iterator` one panicked in the dependency's `next`. So each
    // user-code conjunct of the old tolerance withholds the disposition here.
    // Refusal only: it never accepts anything, and it is reached only when the
    // native lowering completed.
    if !artifacts.runtime_checked_std_members.is_empty()
        && let Some(diagnostic) = prepare_runtime_checked_std_member_withheld(
            tcx,
            body,
            func_path,
            artifacts,
            masked_fail_closed_source,
        )
    {
        return Some(PreparedFullFailure::nonwaivable(
            NonwaivableFullFailure::RuntimeCheckedMember,
            diagnostic
        ));
    }
    // Trust: a function with ZERO real safety obligations is VACUOUSLY fully
    // verified — common for pure-logic functions with no array/arithmetic/unsafe
    // operations (e.g. `fn f(a: i32) -> i32 { if a > 0 { a } else { 0 } }`). The
    // blanket `summary.total == 0 → skipped` failure in `full_verification_failure`
    // wrongly rejected these under strict verification. Accept them ONLY when
    // the native verifier ALSO found nothing outstanding (no real requested
    // obligation and no skipped/unsupported/unknown/timed-out/cancelled/etc.
    // artifact), which distinguishes a genuinely obligation-free function from one
    // whose verification was skipped or crashed — the native run flags the latter.
    // Soundness: a real obligation would surface in `summary.total` OR in the
    // native summary, so this suppresses no genuine gap.
    // Trust: fail-closed on absent-callee/drop-glue panic (revert of d8a9bbc28e /
    // d848dcad97 fail-open; unproven panic MUST fail closed). An UNPROVEN absent-
    // callee / drop-glue `PanicFreedom` row is a genuine undischarged panic
    // obligation (the fail-soft lowering keeps the panic reachable, so it is never
    // `proved`). Compute it up front so the early "nothing to fail on" returns below
    // cannot let it slip through even in the unlikely event the aggregate summary
    // does not surface it: this row alone must keep the function fail-closed.
    // SOUNDNESS: it is never `proved`, so it can never false-refute provably-safe code.
    let has_unproved_assumption_panic = artifacts_have_unproved_assumption_panic(artifacts);
    // Trust (2026-09-19): a call through a RUNTIME CODE ADDRESS is a real,
    // countable coverage gap — `skipped: 1` — not merely a reason to decline an
    // early return. Minting it as a failure rather than bypassing the returns is
    // deliberate and was measured: an earlier cut simply added
    // `&& !function_has_unresolved_indirect_call(..)` to both returns, and a body
    // whose other rows were all PROVED then fell through with an all-zero
    // aggregate and ICE'd on the `debug_assert!(strict_failure_is_fatal(..))`
    // below — the assert was right and the bypass was wrong. Everything past
    // those returns assumes a failure EXISTS; so give it one.
    //
    // BOTH returns need it. Gating only the zero-inventory return was measured
    // INCOMPLETE: `pub fn call(f: Option<fn()>) { if let Some(g) = f { g() } }`
    // carries one PROVED `unreach` row for its `None` arm, so `summary.total == 1`
    // and it never reaches that return at all. It built green against a
    // verify-off dependency's `pub static F: fn() = boom;` and panicked at
    // runtime with exit 101 AFTER the first gate landed.
    // `tests/fn-pointer-witness/fragment/f3_optional_pointer.rs` is that row.
    let indirect_call_failure =
        function_has_unresolved_indirect_call(tcx, body).then_some(FullVerificationFailure {
            failed: 0,
            unknown: 0,
            runtime_checked: 0,
            skipped: 1,
        });
    // Trust (2026-10-10, ZERO-ROW-GATE): the empty-inventory accept now asks the
    // SAME question the transport asked when it chose this body's row
    // (`zero_obligation_vacuously_clean`, from `zero_obligation_native_vacuously_
    // clean`), and refuses whenever the body publishes an `unknown` or timed-out
    // row. Before, it asked only `native_run_is_vacuously_clean`, omitting the
    // publisher's `calls_undischarged` conjunct, and never read `published_rows`:
    // `pub fn f(x: u32, n: u32) -> u32 { x.rotate_left(n) }` published one
    // `unknown` `native-verification-gap` row and exited 0 under strict AND
    // certify. Past this return such a body is refused (`full_verification_failure`
    // is `Some(skipped: 1)` for `summary.total == 0`, and the policy-B tolerance
    // denies an empty result set as `NoRows`). docs/DECISION_QUEUE.md
    // ZERO-ROW-GATE records the ruling; it reverses the 2026-09-16 note below.
    let zero_obligation_accepted =
        zero_obligation_inventory_accepted(zero_obligation_vacuously_clean, published_rows);
    // Every OTHER conjunct of the accept, as it stood before ZERO-ROW-GATE. When it
    // holds and the new conjunct does not, the new conjunct alone decided the
    // refusal: that is when the note below names it.
    let zero_obligation_otherwise_accepted = summary.total == 0
        && !has_unproved_assumption_panic
        && native_authority_validation_failures.is_empty()
        && artifacts.full_verification.as_ref().is_some_and(native_run_is_vacuously_clean)
        && indirect_call_failure.is_none();
    if summary.total == 0 {
        info!(
            "Trust zero-row gate: fn={} publisher_vacuously_clean={:?} published_unknown={} \
             published_timed_out={} otherwise_accepted={} accepted={}",
            func_path,
            zero_obligation_vacuously_clean,
            published_rows.unknown,
            published_rows.timed_out,
            zero_obligation_otherwise_accepted,
            zero_obligation_otherwise_accepted && zero_obligation_accepted,
        );
    }
    if zero_obligation_otherwise_accepted && zero_obligation_accepted {
        inlined_sysroot_panic::trace_early_accept(tcx, body, "no rows");
        return None;
    }
    let zero_obligation_refused_by_publisher_verdict = zero_obligation_otherwise_accepted;
    // Trust (2026-10-10, ZERO-ROW-GATE — SUPERSEDES the 2026-09-16 disposition
    // below). The note below is kept as history; its conclusion is reversed. Two
    // corrections to it:
    //  * the live path of the "EMPTY bridged inventory" hole was THIS FUNCTION'S
    //    FIRST return (the zero-inventory one above), not the second: since
    //    `full_verification_failure` returns `Some(skipped: 1)` for
    //    `summary.total == 0`, the `legacy_failure.is_none()` return below cannot
    //    accept an empty inventory. The first return asked
    //    `native_run_is_vacuously_clean` and not the publisher's
    //    `calls_undischarged`, so a body whose calls no authenticated registry
    //    discharges exited 0 while publishing `outcome: unknown`;
    //  * the "designed discharges" it protected are exactly bodies that published
    //    `unknown` under certify. A gate cannot tell a sound unauthenticated
    //    discharge from an unsound one (the `try_total` user-`Try` false green rode
    //    this same return), so they now FAIL strict/certify until their lane mints
    //    evidence the registries authenticate — the remedy the note itself names
    //    ("the fix belongs on the ROW"). Relabelling the gap row is never the fix.
    // The gate is now keyed on the publisher's own predicate
    // (`zero_obligation_native_vacuously_clean`), so the two cannot diverge.
    //
    // Trust (2026-09-16, MEASURED AND NOT TAKEN — read this before tightening the
    // returns around it).
    //
    // UPDATE 2026-09-19: the hole this describes is CLOSED, but NOT by the gate
    // this note rejects — that one is still rejected, for the reason given
    // below. It was closed by `function_has_unresolved_indirect_call`, which
    // keys on the ABSENCE of a `DefId` at the call rather than on the registry's
    // undischarged set, and therefore separates the hole from every designed
    // discharge structurally (all five are `dyn`/trait dispatches with real
    // `DefId` callees). Everything this note says about
    // `zero_obligation_undischarged_call_funcs` still stands; do not revive it.
    // [SUPERSEDED 2026-10-10 by ZERO-ROW-GATE above: the first return now reads
    // the publisher's predicate, which includes that set.]
    //
    // The `docs/KNOWN_HAZARDS.md` "EMPTY bridged inventory"
    // hole is live and was reproduced here on `pub fn call(f: fn()) { f() }`:
    // exit 0, one `native-verification-gap` row, and no verdict for the call at
    // all (the bridge lowers the fn-pointer call to `CallIndirect` plus its
    // may-panic assert; no engine dispatches it). `core::task::Waker`'s drop
    // rides the same hole through its bundled `Drop` member.
    //
    // A gate keyed on `zero_obligation_undischarged_call_funcs` — the registry's
    // own record of a call nothing discharges — WAS built and measured: it
    // refuses the fn-pointer body correctly and ALSO breaks five of the seven
    // DESIGNED discharges (`dyn_dispatch_reliance_{contract,recursive_field_
    // carrier}_discharges`, `trait_panic_free_impl_discharges`,
    // `native_bundle_std_trait_impl_keeps_existing_model`,
    // `wrapping_refutation_release_identity`), because those bodies' calls are
    // discharged by a reliance CERTIFICATE rather than by an authenticated
    // registry, so the set names them too. That is exactly what the hazard note
    // predicts of any tightening here, and it is why the fix belongs on the ROW:
    // a discharged body must publish its discharging lane's evidence instead of
    // `outcome: unknown`, and only then can a gate here tell the two apart.
    let legacy_failure = full_verification_failure(
        summary,
        &artifacts.transport_results,
        &artifacts.results,
        &artifacts.result_bindings,
        &artifacts.proof_authorities,
    );
    // Trust: `proof_results.summary` is the AUTHORITATIVE per-obligation outcome
    // — it is built from the bridged `results`, gated by `apply_vacuity_gate`,
    // and only counts proofs that pass `convert_result` with an exact private
    // kernel/native authority token. If it shows no gap, the function is fully verified.
    // The native run summary is a PRE-BRIDGE cross-check that cannot see the
    // v1/ay proofs (and whose row-consistency checks would otherwise mis-fire on
    // the excluded admission), so it must not override a clean bridged result.
    if legacy_failure.is_none()
        && !has_unproved_assumption_panic
        && native_authority_validation_failures.is_empty()
        && indirect_call_failure.is_none()
    {
        inlined_sysroot_panic::trace_early_accept(tcx, body, "all rows proved");
        return None;
    }
    let native_failure = native_full_verification_failure(artifacts.full_verification.as_ref());
    let authority_validation_failure = (!native_authority_validation_failures.is_empty())
        .then_some(FullVerificationFailure {
            failed: 0,
            unknown: 0,
            runtime_checked: 0,
            skipped: native_authority_validation_failures.len().min(u32::MAX as usize) as u32,
        });
    let native_failure =
        combine_full_verification_failures(native_failure, authority_validation_failure);
    // Trust: an unproved absent-callee/drop-glue panic must survive even a `None`
    // legacy+native failure (fail-closed), so seed the aggregate with an empty
    // failure it can be combined into rather than early-returning.
    let native_failure = combine_full_verification_failures(native_failure, indirect_call_failure);
    let failure = combine_full_verification_failures(legacy_failure, native_failure).unwrap_or(
        FullVerificationFailure { failed: 0, unknown: 0, runtime_checked: 0, skipped: 0 },
    );

    // `certify` accepts only complete static proof. Under default policy B, a
    // residual coverage gap is still reported as unproved but may remain
    // nonfatal only when every affected row keeps its exact Rust runtime check.
    // Refutations, structural corruption, and rows without a runtime fallback
    // remain fatal. Contract-panic annotations document an intentional
    // reachable panic; they are conditional evidence only in the explicit
    // survey lane and provide no exemption here.
    debug_assert!(strict_failure_is_fatal(failure, true) || has_unproved_assumption_panic);

    // The bridged and native summaries describe overlapping rows. Their
    // category-wise sum above is useful as a conservative fatality aggregate,
    // but it is not a cardinality: adding it would report the same failed row
    // twice. The diagnostic header therefore takes the largest independently
    // authenticated inventory, plus the independent authority/panic floors.
    let unique_failure_count = legacy_failure
        .map_or(0, FullVerificationFailure::total)
        .max(artifacts.full_verification.as_ref().map_or(0, |run| {
            run.summary.requested_obligations.saturating_sub(run.summary.proved) as u32
        }))
        .max(native_authority_validation_failures.len().min(u32::MAX as usize) as u32)
        .max(u32::from(has_unproved_assumption_panic))
        .max(indirect_call_failure.map_or(0, FullVerificationFailure::total));

    // Trust (completeness-gap ruling B): under the DEFAULT policy a residual gap
    // whose every obligation either keeps its runtime check or is an explicitly
    // classified defined-IEEE advisory is reported, not fatal — the emitted
    // program is bit-for-bit vanilla Rust, so failing the build on it buys no
    // safety and costs drop-in. `certify` still demands full static discharge.
    // Any other refutation, unaccounted row, or no-fallback obligation keeps the
    // function fail-closed.
    // Trust (completeness-gap ruling B). Two different things share the
    // `native_authority_validation_failures` list and they must NOT share a fate:
    //
    //  * STRUCTURAL integrity — the native run's derived state does not validate,
    //    or the result/binding/authority carriers are not row-aligned. Then
    //    `artifacts.results` cannot be trusted, so the whole-function fallback
    //    scan below would be reading garbage. Always fatal, under every policy.
    //  * PER-ROW credit absence — a native row claims `Proved` while its compiler
    //    row carries no private static authority. That is the completeness gap
    //    itself, and under B it is reported rather than fatal.
    //
    // Rather than string-match the reasons (fragile, and the exact failure mode
    // this program keeps finding), the structural conditions are recomputed here
    // from the same inputs the validator uses.
    //
    // SAFETY OF TOLERATING THE SECOND CLASS: this function takes
    // `&VerificationArtifacts` and returns `()` — as its own header notes, it
    // "never rewrites the public run or its counters". Downgrading its diagnostic
    // changes the EXIT CODE only. No row is relabelled, no proof credit is
    // granted, and erasure is unaffected because `elide_kernel_certified_checks`
    // licenses on `KernelCertified` authority, which such a row by construction
    // does not carry.
    let native_structurally_sound =
        artifacts.full_verification.as_ref().is_none_or(|run| run.validate_derived_state().is_ok())
            && artifacts.results.len() == artifacts.result_bindings.len()
            && artifacts.results.len() == artifacts.proof_authorities.len();
    let requires_full_discharge =
        tcx.sess.opts.unstable_opts.trust_policy.requires_full_discharge();
    let gap_denial = residual_gap_tolerance_denial(&artifacts.results, tcx.sess.overflow_checks());
    let gap_is_default_nonfatal = gap_denial.is_none();
    // Trust (policy B restoration, 2026-09-10): the fail-closed OVERRIDE keyed on
    // `has_unproved_assumption_panic` must not fire for std `_print`/`_eprint`
    // print-backend rows in a function with no source or inlined `unsafe` — those
    // are runtime-checked completeness gaps (std's defined write-failure panic),
    // exactly what ruling B reports rather than fails. See
    // `transport_row_is_std_print_dispatch`. A generic absent callee (the
    // `read_any` UB shape), `write_fmt`/`fmt::write`, drop glue, and any
    // unsafe-using caller keep the whole override fatal. SOUNDNESS: the excluded
    // row is never `Proved` (reachable-panic marker), so this only lets the
    // ALREADY-TOLERATED runtime-checked disposition stand; it never mints a proof.
    //
    // Trust (2026-09-19): an unresolved INDIRECT call joins this override
    // unconditionally. `trust_types::TRUST_INDIRECT_CALLEE_PATH` — the reserved
    // `@trust-indirect-callee` name extraction stamps on exactly these calls —
    // states the contract: "A consumer that cannot model an open dispatch must
    // fail closed on it exactly as it would on any other callee whose body is
    // absent." This IS that class; it simply has no transport row to recognise,
    // so the row scan below cannot see it.
    //
    // MEASURED, and this placement is the third attempt. Minting a `skipped: 1`
    // failure alone was NOT enough: `pub fn call(f: Option<fn()>) { if let
    // Some(g) = f { g() } }` carries one CERTIFIED row for its `None` arm, so the
    // policy-B demotion right below saw an inventory whose every row keeps its
    // runtime check and demoted the whole thing to a warning — the body stayed
    // exit 0 and still panicked at runtime through a verify-off dependency's
    // `pub static F: fn() = boom;`. The override is where the decision actually
    // lives.
    // Trust (2026-09-20): keep WHICH disjunct matched, not just that one did.
    // Truth value is unchanged — the `||` short-circuit becomes an if/else chain
    // over the same three cases in the same order — and the cause rides along so
    // the note below can NAME it instead of listing four and identifying none.
    // The `unsafe` arm reports itself as the cause because it admits rows the
    // filtered arm excludes, so "which row" would be misleading there.
    // Trust (2026-09-20, second pass): carry the row's own SUBJECT where it has
    // one. The class alone ("drop glue") separates this from an absent callee
    // but not one drop from another, and the neighbours that verify have already
    // excluded the obvious candidates — only the row knows.
    // Trust (D1 increment 1, 2026-09-25): a WRITER-RELATIVE formatting root
    // (`fmt_writer_relative`): a local `Debug`/`Display` impl whose bundle provably
    // takes every `fmt::Write` value from its own `&mut Formatter` parameter. Its
    // writer-edge absent-callee rows — and ONLY those — are excused from the
    // fail-closed decision below, when no masked source and no unresolved
    // indirect call is present. The rows themselves are untouched: they stay
    // unproved and `runtime-checked`, `certify` still refuses them, and no
    // registry or shared bar reads this excuse.
    // Trust (D1 increment 2): the root computes its own masked-source answer
    // (core's `Formatter`-as-writer calls not counted — see
    // `fmt_writer_relative::writer_relative_body_has_masked_source`).
    let writer_relative =
        fmt_writer_relative::writer_relative_root(tcx, body, indirect_call_failure.is_some());
    let row_assumption_panic_cause: Option<String> = if indirect_call_failure.is_some() {
        Some(String::from("an unresolved indirect call"))
    } else if function_uses_unsafe_outside_std(tcx, body) {
        has_unproved_assumption_panic
            .then(|| String::from("an unsafe-using function's own assumption-panic row"))
    } else {
        judged_rows.iter().find_map(|row| {
            if transport_row_is_std_print_dispatch(row)
                    || transport_row_is_vanilla_sysroot_absent_callee(row, &vanilla_sysroot_callees)
                    // Trust (D1 increment 1): a writer edge of a writer-relative
                    // root. Judged per FOLDED site like the two exclusions above,
                    // so a co-folded non-writer row still refuses on its own.
                    || writer_relative.as_ref().is_some_and(|wr| wr.excuses(row))
            {
                return None;
            }
            let class = assumption_panic_row_cause(row)?;
            Some(match drop_glue_assumption_detail(row) {
                Some(subject) => format!("{class} ({subject})"),
                None => String::from(class),
            })
        })
    };
    // Trust (2026-10-13, CALL-REACH-1-D8; DECISION_QUEUE CALL-REACH-1-D8): a call
    // the call-reach walk left OPEN keeps the function fail-closed whichever arm
    // lowered it. An ABSENT callee already does, through the deny arm's fail-closed
    // row (a generic absent callee, above). A BUNDLED sysroot callee is lowered as
    // its own body instead, and the edge the walk opened at — an indirect call such
    // as `LocalKey::try_with`'s `(self.inner)(None)` — becomes that member's havoc
    // row, which reached the whole-function aggregate as runtime-checked and was
    // tolerated: `k.with(|c| c.get())` on a `&'static LocalKey` the caller was
    // handed, or on a dependency's key whose initializer panics, built exit 0.
    // Refusal-only: it can withhold the tolerance and nothing else.
    let fail_closed_assumption_panic_cause = row_assumption_panic_cause.or_else(|| {
        with_crate_verification_state(tcx.sess, |state| {
            state.call_reach_withdrawn.get(func_path).map(|(callee, why)| {
                format!(
                    "a sysroot call whose code the call-reach walk could not close (`{callee}` \
                     {why})"
                )
            })
        })
    });
    let has_fail_closed_assumption_panic = fail_closed_assumption_panic_cause.is_some();
    // Trust (HOLE B / Option Y, fold-safe print grace — 2026-09-14): the std print
    // backend is kept ABSENT from the bundle (`def_is_std_print_backend`), so
    // `main`'s own obligations lower and earn real verdicts. A RUNTIME-value user
    // assert (`assert!(black_box(5) == 7)`) and a runtime format width
    // (`{:width$}`) are RUNTIME-CHECKED obligations: rustc keeps their runtime
    // check and the program has vanilla-Rust semantics, so under the default policy
    // they COMPILE (reported, never proved), with or without a `println!` — exactly
    // as they do without it. The former `print_gap_masks_unproved_own_obligation`
    // gate REFUSED them (over-strict, a drop-in break) and, keyed on
    // `function_has_user_panic_call && !has_proved_own_row`, was ALSO unsound: an
    // UNRELATED proved fact (a constant `arr[1]` bounds row) set `has_proved_own_row`
    // and re-enabled tolerance of an UNRELATED unproved `assert!` — the forbidden
    // "one proved fact launders another unproved one" class. Removed.
    //
    // What DOES have to survive the fold is a FAIL-CLOSED dispatch. The bridge
    // folds every absent/foreign panic source into one whole-function
    // panic-freedom row named after a single representative callee; when a
    // `println!` is present that name is often the tolerated `_print`, hiding a
    // co-folded `write!`-into-a-sink or spoofed-`_print` panic from the row scan in
    // `has_fail_closed_assumption_panic`. Re-derive those from MIR so the print
    // grace covers the std print backend ALONE.
    let has_print_gap = judged_rows.iter().any(transport_row_is_std_print_dispatch);
    // A masked fail-closed CALL (a verify-off dep fn, a sysroot generic at a
    // foreign type) or DROP GLUE folded under a tolerated representative row —
    // `masked_fail_closed_source`, computed once at the top of this function.
    let has_vanilla_gap = judged_rows
        .iter()
        .any(|row| transport_row_is_vanilla_sysroot_absent_callee(row, &vanilla_sysroot_callees));
    // Trust (HOLE — user/dep Display fold-mask via ANY format machinery,
    // 2026-09-14): a value formatted through a NON-FOUNDATIONAL `Display`/`Debug`
    // (a user OR a cross-crate `fmt` impl). Its `fmt` is reached INDIRECTLY
    // through the format machinery (`_print` for `println!`, `alloc::fmt::format`
    // for `format!`) — there is no direct Call in this body for the crate rule to
    // catch and (for a verify-off dep) no bundled obligation — so its panic edge
    // folds into the whole-function panic-freedom aggregate. `main` packs each
    // formatted value with `core::fmt::rt::Argument::new_display`/`new_debug::<T>`,
    // so the non-foundational `T` is detected at the PACKER in THIS body (which
    // also keeps the local case from ever scanning the panicking `fmt` body).
    //
    // This is a STANDALONE positive fail-closed condition, NOT gated on
    // `has_print_gap`: `format!("{}", dep::D(v))` has NO print gap, yet must refuse
    // exactly like the `println!` twin (pin `println_cross_crate_display_refused`).
    // Reaching this seam already means the function has an unproved obligation
    // (abort returns early when fully verified) — and the format machinery is
    // foundational TCB that is never fully discharged, so a non-foundational packer
    // here is always an undischarged user/dep-`fmt` gap. Every tolerated lane
    // formats only foundational scalars/`str`/`String`
    // (`function_format_args_all_foundational_display` is true for them), so this
    // adds no over-refusal.
    let formats_nonfoundational_display = !function_format_args_all_foundational_display(tcx, body);
    // The masked CALL/DROP fold-mask still requires a TOLERATED gap (it is about
    // a co-folded source hidden under a tolerated representative row — the std
    // print backend or, since 2026-09-14, a vanilla sysroot callee).
    // Trust (D1 increment 1): the writer-relative gap joins the tolerated gaps a
    // masked source must not hide behind. REFUSAL-ONLY (critique (c)): this term
    // is conjoined with `masked_fail_closed_source`, which already withholds the
    // writer-relative excuse itself, so it can only turn a tolerance into a
    // refusal — never excuse anything. Pinned by the `masked_dep_call` rails.
    let has_writer_gap =
        writer_relative.as_ref().is_some_and(|wr| judged_rows.iter().any(|row| wr.names_edge(row)));
    // Trust (D1 increment 2): in a writer-relative root the mask is that root's
    // own answer, which does not count core's `<Formatter as fmt::Write>` writer
    // calls (their one foreign edge is the writer edge, judged per folded site).
    // Every other body keeps the plain scan's answer.
    let masked_for_tolerated_gaps =
        writer_relative.as_ref().map_or(masked_fail_closed_source, |wr| wr.masked_source());
    // Trust (2026-09-27): the canonical whole-function panic-freedom AGGREGATE is a
    // fold too, and tolerating it unproved says "every panic here is a runtime check
    // rustc already emits" — false when it folds the may-panic marker of a
    // closure-driving consumer that runs unverified code
    // (`foreign_reaching_closure_consumer_edges`): that edge runs no check at all.
    // Measured on stage-1 436c9eb6d0: `o.unwrap_or_default().0 ^ p.unwrap_or_default()`
    // over `Option<dep::Boom>` (a verify-off `Default` that is
    // `unreachable_unchecked()`) and `Option<u32>` carried one runtime-checked
    // aggregate and built rc=0. Keyed on that edge, not on the coarse masked scan:
    // measured, the coarse scan also withheld the tolerance from `?` into
    // `Box<dyn Error>` and `Result<(), io::Error>::unwrap_or_default` (the fields of
    // `io::Error` hold a trait object), whose folds run std code only.
    let aggregate_folds_unverified_consumer = judged_rows
        .iter()
        .any(|row| transport_row_is_panic_freedom_aggregate(row) && row.outcome != Outcome::Proved)
        && !foreign_reaching_closure_consumer_edges(tcx, body).is_empty();
    let tolerated_gap_masks_fail_closed_dispatch =
        ((has_print_gap || has_vanilla_gap || has_writer_gap) && masked_for_tolerated_gaps)
            || aggregate_folds_unverified_consumer;
    // Trust (D1 increment 1): whether any writer-edge row was excused, and whether
    // EVERY unproved assumption-panic row was one — then the generic tolerated-row
    // note ("can dispatch into no user code") would be false and is withheld in
    // favour of the writer-relative disclosure.
    let writer_rows_excused =
        writer_relative.as_ref().is_some_and(|wr| judged_rows.iter().any(|row| wr.excuses(row)));
    let only_writer_rows_remain = writer_rows_excused
        && judged_rows.iter().all(|row| {
            !transport_row_is_unproved_assumption_panic(row)
                || writer_relative.as_ref().is_some_and(|wr| wr.excuses(row))
        });
    // Trust (2026-09-29): a foreign panic path the explicit MIR inliner copied
    // into this body (`-Zinline-mir=yes`, `-Zmir-opt-level>=2`) — std's panic on
    // a caller value, charged at its call site at `-O0`, or a dependency's,
    // whose call is fail-closed at `-O0` — is not a runtime check the user wrote,
    // so no row of this function may ride ruling B's tolerance. See
    // `inlined_sysroot_panic`. Refusal-only: it can turn a tolerance into a
    // refusal and nothing else.
    let inlined_foreign_panic = inlined_sysroot_panic::inlined_foreign_panic_site(tcx, body);
    let tolerate_default_gap = !requires_full_discharge
        && !has_fail_closed_assumption_panic
        && native_structurally_sound
        && gap_is_default_nonfatal
        && !tolerated_gap_masks_fail_closed_dispatch
        && !formats_nonfoundational_display
        && inlined_foreign_panic.is_none();

    // Freeze NONWAIVABLE source/integrity facts from this ORIGINAL execution.
    // Native row coverage cannot account for source behavior these explicit
    // guards say is uncharged. No message matching or second query decides it.
    let terminal_cause = if !native_structurally_sound
        || !native_authority_validation_failures.is_empty()
        || masked_fail_closed_source
        || has_unproved_assumption_panic
        || has_fail_closed_assumption_panic
        || indirect_call_failure.is_some()
        || tolerated_gap_masks_fail_closed_dispatch
        || formats_nonfoundational_display
        || inlined_foreign_panic.is_some()
        || zero_obligation_refused_by_publisher_verdict
    {
        FullFailureCause::Nonwaivable(NonwaivableFullFailure::OriginalFloors {
            malformed_native: !native_structurally_sound,
            // S4 also rejects exact-binding ambiguity/staleness and current
            // compiler/public verdict disagreement. Derived-state validity
            // alone cannot turn those original failures into row-proof debt.
            // A future dischargeable proof-only category needs a typed exact
            // row result from this SAME original validator execution.
            native_authority_integrity: !native_authority_validation_failures.is_empty(),
            masked_source: masked_fail_closed_source,
            assumption_panic: has_unproved_assumption_panic,
            fail_closed_source: has_fail_closed_assumption_panic,
            indirect_call: indirect_call_failure.is_some(),
            masked_dispatch: tolerated_gap_masks_fail_closed_dispatch,
            nonfoundational_format: formats_nonfoundational_display,
            inlined_panic: inlined_foreign_panic.is_some(),
            zero_publisher_refusal: zero_obligation_refused_by_publisher_verdict,
        })
    } else {
        FullFailureCause::CandidateRowDebt
    };

    // Trust: when the default policy COULD have tolerated this gap but did not,
    // say which condition withheld it. A build that fails where the ruling says
    // it should pass is otherwise indistinguishable from one that fails for a
    // good reason, and "it just fails" is not a diagnosis anyone can act on.
    let tolerance_blocked_by: Option<String> = if requires_full_discharge {
        None // `certify` is meant to fail here; nothing to explain.
    } else if let Some(cause) = fail_closed_assumption_panic_cause {
        // Trust (2026-09-20): NAME the disjunct. This used to list all four and
        // identify none, and the residue of `vec![1, 2, 3]` was misattributed
        // four times off that list before anyone measured it.
        Some(format!(
            "an unproved assumption-panic row — {cause} — keeps the function fail-closed \
             (the other shapes in this class are a generic absent callee, an expected-absent \
             callee, drop glue, an extern call, and any such row in a function that uses \
             `unsafe`)"
        ))
    } else if !native_structurally_sound {
        Some(String::from(
            "the native run's derived state or carrier row-alignment did not validate, so the \
             per-row kinds could not be trusted",
        ))
    } else if tolerated_gap_masks_fail_closed_dispatch {
        Some(String::from(
            "the std stdout/stderr print backend, a vanilla std/core/alloc routine, or the \
             whole-function panic-freedom aggregate kept as a runtime check is a \
             tolerated completeness gap, but this function ALSO carries a fail-closed panic \
             source whose panic-freedom folds invisibly into the same whole-function \
             panic-freedom aggregate — a `write!`/`writeln!` into an unverified sink (its \
             `fmt::Write` impl may `panic!`), a `_print`/`_eprint` that is not std's own \
             stdout/stderr backend, a call into a verify-off dependency (any \
             non-std/core/alloc crate) whose panic-freedom is unproven, a std/core/alloc \
             routine instantiated at a type from such a dependency (`parse::<dep::T>`, \
             `Vec<dep::T>`), or DROP GLUE of a value whose `Drop::drop` is outside the \
             std/core/alloc foundational TCB. The grace covers the tolerated routine alone, \
             not a second unmodeled panic. Options: route the value through a verified \
             sink or a Rust `fn` carrying a proved `ensures`; prove the type's `Drop` \
             panic-free and verify it in its own crate; or build with `-Z trust-policy=advisory`",
        ))
    } else if formats_nonfoundational_display {
        Some(String::from(
            "this function formats a value through a user or dependency `Display`/`Debug` \
             implementation whose `fmt` is not verified panic-free (a `{}`/`{:?}` of a \
             non-foundational type — a `core::fmt::rt::Argument::new_display`/`new_debug::<T>` \
             packer whose `T` is not a primitive, `str`, or `String`). Whether via `println!` \
             or `format!`, that formatter is reached indirectly through the format machinery, \
             so its panic edge folds into the whole-function panic-freedom aggregate; the \
             completeness-gap tolerance covers the foundational format machinery alone, not an \
             arbitrary formatter that may `panic!`. Options: format only foundational values (a \
             primitive, `str`, or `String`); prove the `Display`/`Debug` impl panic-free and \
             verify it in its own crate; or build with `-Z trust-policy=advisory`",
        ))
    } else if let Some(denial) = gap_denial {
        // Trust (2026-10-03): main's `[inlined-panic-path]` row
        // (`inlined_unsafe_evidence`) is an always-SAT assertion, so a body that
        // carries an inlined foreign panic path usually reaches a gap denial too
        // (`RowRefutationHeld`). The denial alone does not say that the
        // counterexample is a std or dependency panic path the MIR inliner copied
        // in, nor that building without the explicit inlining flag is an option, so
        // name the site as well. Diagnostic only: both conditions already withhold
        // the tolerance.
        Some(match &inlined_foreign_panic {
            Some(site) => format!(
                "{}; and {}",
                denial.describe(),
                inlined_sysroot_panic::inlined_foreign_panic_note(site)
            ),
            None => String::from(denial.describe()),
        })
    } else if let Some(site) = &inlined_foreign_panic {
        Some(inlined_sysroot_panic::inlined_foreign_panic_note(site))
    } else {
        None
    };
    // Trust (R1 scan-gap warning gate): this seam, like
    // `report_strict_l0_verification_failure`, is a point where a verdict is
    // actually withheld — record it so the crate-level R1 scan-poison warning may
    // state its cause (see `r1_scan_gap_warning_applies`).
    with_crate_verification_state(tcx.sess, |state| state.l0_verdict_withheld = true);
    let header = if tolerate_default_gap {
        format!(
            "Trust verification advisory for `{func_path}`: {unique_failure_count} obligation(s) were not fully verified"
        )
    } else {
        format!(
            "Trust strict verification failed for `{func_path}`: {unique_failure_count} obligation(s) were not fully verified"
        )
    };
    // Trust: collect the notes once, then emit them on an error (aborting) or a
    // warning (coverage gap) diagnostic — the two `Diag` levels are distinct
    // types and cannot share a binding, so the notes are level-agnostic here.
    let mut notes: Vec<String> = Vec::new();
    // Trust (diagnostic legibility): the native verifier's own reporting —
    // status line, per-request digests, per-obligation evidence and skip
    // reasons — is SEPARATED from the notes a person can act on, and emitted
    // after them.
    //
    // It used to be interleaved, and it is bounded at 1 + 8 + 24 + 8 = 41 notes
    // against a handful of human ones. On the smallest possible failing program
    // — `fn main() { println!("…"); }`, whose only unproved row is panic-freedom
    // for an absent std callee — that put roughly a dozen lines of bundle
    // digests, CHC/PDR strength requirements and TrustIr validation dumps
    // between the reader and the one sentence naming the fix. A first contact
    // with the toolchain that fails on correct code should lead with what to do
    // about it; the engine's internals are for whoever is debugging the engine,
    // and they keep their every byte, just below.
    let mut engine_notes: Vec<String> = Vec::new();
    // Trust (2026-09-25): name a recursive formatting edge when it is what refused.
    if formats_nonfoundational_display
        && let Some(note) = fmt_error_transparency::formatting_cycle_note(tcx, body)
    {
        notes.push(note);
    }
    // Trust (D1 increment 0): name error transparency when it is what refused.
    if formats_nonfoundational_display
        && let Some(note) = fmt_error_transparency::error_opacity_note(tcx, body)
    {
        notes.push(note);
    }
    // Trust (D1 increment 1): likewise an unrecognized consumer of a writer-relative
    // formatter.
    if formats_nonfoundational_display
        && let Some(note) = writer_relative_sink_refusal_note(tcx, body)
    {
        notes.push(note);
    }
    // Trust (D4-A, 2026-09-24): name what happened to a DEPENDENCY impl.
    if formats_nonfoundational_display
        && let Some(note) = fmt_error_transparency::foreign_formatter_note(tcx, body)
    {
        notes.push(note);
    }
    // Trust (2026-09-29): name a `requires`-carrying local function that the
    // indirect-call gate refused as a value (`local_fn_item_is_verified_unconditionally`).
    // Trust (2026-09-30): and a foreign one, or one inside a sysroot closure the MIR
    // inliner built (`uncharged_callable`, residuals L1/L2).
    if indirect_call_failure.is_some() {
        for callee in uncharged_callable::requires_carrying_fn_values(tcx, body) {
            notes.push(uncharged_callable::requires_value_note(&callee));
        }
        // Trust (2026-10-03): and a std/core/alloc item the policy's rule does not
        // account for (`sysroot_callable_item`; empty on the default policy).
        for item in sysroot_callable_item::unaccounted_sysroot_callable_items(tcx, body) {
            notes.push(sysroot_callable_item::unaccounted_sysroot_callable_note(&item));
        }
    }
    // Trust (2026-10-10, ZERO-ROW-GATE): name the empty-inventory refusal. Without
    // it the header reads "1 obligation(s) were not fully verified" over a summary
    // of zero, which says nothing about what to fix.
    if zero_obligation_refused_by_publisher_verdict && zero_obligation_vacuously_clean == Some(true)
    {
        // The belt alone decided: the body is vacuously clean by the publisher's
        // test, but a row it publishes beside `no_obligations` is unproved (an
        // instance-discharge row the callee's verdict left `unknown`, say).
        notes.push(String::from(
            "this function has no obligation of its own, but a row it publishes is `unknown` \
             or timed out, so it is not vacuously verified; a strict or certify build refuses \
             that row exactly as it would an unproved obligation",
        ));
    } else if zero_obligation_refused_by_publisher_verdict {
        notes.push(String::from(
            "this function has no obligation of its own, but it is not vacuously verified: \
             a call it makes is discharged by no authenticated panic-freedom registry (or a \
             consumer call reaches unverified code uncharged), so it publishes an unproved \
             row (outcome `unknown`, a `native-verification-gap` row unless the body carries \
             its own) instead of `no_obligations`; a strict or certify build refuses that \
             row exactly as it would an unproved obligation",
        ));
    }
    notes.push(format!(
        "summary: {} trusted, {} certified, {} failed, {} unknown, {} runtime-checked, {} skipped out of {}",
        summary.trusted,
        summary.certified,
        // Trust: this per-category breakdown must partition `summary.total` and
        // reconcile with the per-obligation evidence, so every count comes from
        // the authoritative `proof_results.summary` (as the sibling "proof
        // results for" debug note does). Drawing failed/unknown/runtime/skipped
        // from `failure` was an accounting bug: `failure` is the fail-closed
        // FATALITY aggregate, and `combine_full_verification_failures` SUMS the
        // legacy (summary-derived) failure with the native re-count of the SAME
        // obligations, so once the native verifier returns rows its per-category
        // fields double-count (e.g. "6 failed, 1 skipped out of 7"). Fatality
        // and the header count still use `failure`; only this display partition
        // changes, so no verdict moves.
        summary.failed,
        summary.unknown,
        summary.runtime_checked,
        summary.total.saturating_sub(summary.accounted()),
        summary.total,
    ));
    for validation_failure in native_authority_validation_failures.iter().take(8) {
        notes.push(format!("native proof-authority validation failed: {validation_failure}"));
    }
    if failure.failed > 0 {
        if tolerate_default_gap
            && artifacts.results.iter().any(|(vc, _)| is_defined_float_advisory(&vc.kind))
        {
            notes.push(
                "the refuted float row is an L1 numerical-hygiene advisory about a defined \
                 IEEE-754 result; it carries no proof credit and remains fatal under \
                 `-Z trust-policy=certify`, but it is not a Rust safety violation"
                    .to_string(),
            );
        } else {
            notes.push(
                "failed obligations, including declared contract panics, are refutations and are \
                 not permitted under strict verification; select -Ztrust-policy=advisory to \
                 record contract-panic conditional evidence"
                    .to_string(),
            );
        }
    }
    if has_unproved_assumption_panic {
        // Trust (I5, ruling v7/D3 — a refusal must carry the fix, with
        // options): the generic note below truthfully describes the std/extern
        // absent-callee class, but it used to be emitted for EVERY absent
        // callee — including a LOCAL Clean-origin function, kernel-defined in
        // this very crate, for which "a std/extern function" is false (the
        // recorded defect on `tests/ui/trust/clean_origin_verify_on.rs`). Name
        // each such callee for what it is, say why its call was still refused,
        // and give the options; keep the generic note exactly for the rows it
        // still truthfully describes.
        let (clean_origin_absent, other_assumption_rows) =
            clean_origin_absent_callees_in_artifacts(tcx, artifacts);
        for (callee, decl) in &clean_origin_absent {
            notes.push(format!(
                "the call to `{callee}` is not a std/extern call: `{callee}` is a local \
                 Clean-origin function, kernel-checked and emitted from the Clean declaration \
                 `{decl}` in this crate's `clean {{ … }}` island. Its call-site semantics are \
                 modeled only for emission-plan shapes the cross-authority summary lane \
                 implements (today: parameter projections, `def f (a : T) (b : T) : T := a`, \
                 and single wrapping `+`/`-`/`*` binary ops over parameters and in-range \
                 numerals at one unsigned machine width, \
                 `def g (a : UInt64) (b : UInt64) : UInt64 := a + b`); \
                 this declaration's shape is not yet modeled, so the call fails closed rather \
                 than guessing. Options: (1) restate the Clean `def` in a modeled shape; \
                 (2) wrap the call in a Rust `fn` carrying an explicit `ensures` contract and \
                 prove that contract; (3) build with `-Z trust-policy=advisory` to record this \
                 gap as a warning until the summary lane models this shape"
            ));
        }
        if clean_origin_absent.is_empty() || other_assumption_rows {
            // Trust (policy B restoration, 2026-09-10 — v7/D3 truthfulness): in the
            // TOLERATED case every remaining assumption-panic row is a std
            // `_print`/`_eprint` backend or (2026-09-14) a vanilla-semantics
            // sysroot routine (see `transport_row_is_std_print_dispatch`,
            // `transport_row_is_vanilla_sysroot_absent_callee` and
            // `has_fail_closed_assumption_panic`), so the old "this is a build
            // error" wording was false. Say what actually happened, per policy.
            if tolerate_default_gap && only_writer_rows_remain {
                // Trust (D1 increment 1): every tolerated assumption row is a writer
                // edge; the writer-relative note below says what they are.
            } else if tolerate_default_gap {
                notes.push(
                    "an unproven panic-freedom obligation for a call into std/core/alloc whose \
                     body is not in the lowered bundle — the stdout/stderr print backend \
                     (`std::io::_print`/`_eprint`, which can still panic on a failed write / \
                     broken pipe) or another sysroot routine instantiated only at foundational \
                     types (`std::env::args`, `str::parse::<u64>`, `Result::expect`): its panic, \
                     if any, is std's own DEFINED behaviour, exactly as vanilla Rust does, and it \
                     can dispatch into no user code. The panic path stays reachable, so this row \
                     is REPORTED, not failed, under the default policy; `-Z trust-policy=certify` \
                     demands full static discharge and fails it"
                        .to_string(),
                );
            } else if requires_full_discharge {
                // Trust (2026-09-26, std-absent-callee): under `certify` the
                // default-policy note below was FALSE twice over — it called the
                // refusal "the fail-closed default" and offered "keep the call within
                // that tolerated class" as the fix, while `certify` refuses that
                // class too. Say what certify requires, then name each absent
                // std/core/alloc callee and exactly why its panic-freedom was not
                // established (the sysroot panic census's report). The note promises
                // those names only when the census has one to give (2026-10-08: a
                // refusal whose row is not an absent-callee row, or whose callee the
                // census never judged, named nothing after saying it would).
                let mut named: Vec<&str> = judged_rows
                    .iter()
                    .filter(|row| transport_row_is_unproved_absent_callee(row))
                    .filter_map(absent_callee_path_of_row)
                    .collect();
                named.sort_unstable();
                named.dedup();
                let census_notes: Vec<String> = named
                    .into_iter()
                    .flat_map(|callee| {
                        sysroot_panic_census::certify_refusal_notes(tcx.sess, callee)
                    })
                    .collect();
                let named_below = if census_notes.is_empty() {
                    ""
                } else {
                    " Each std/core/alloc callee below is named with the reason that did not \
                     happen."
                };
                notes.push(format!(
                    "an unproven panic-freedom obligation for a call to an absent callee (a \
                     function whose body is not in the lowered bundle), or for drop glue, keeps \
                     its panic path reachable, and under `-Z trust-policy=certify` every \
                     unproved row is fatal, including a call into std/core/alloc that the \
                     default policy reports and builds. Its panic-freedom must be established: \
                     for a local callee by its own proved verdict, for a \
                     std/core/alloc callee by the sysroot panic census deriving from the \
                     callee's own MIR that no panic site is reachable.{named_below} Options: \
                     (1) call an API whose panic-freedom is established instead — a \
                     non-panicking std routine, or your own function with a proved contract; \
                     (2) where the callee panics only on some argument values, prefer its \
                     non-panicking form (`checked_*`, `get`, `split_at_checked`, an API \
                     returning `Option`/`Result`): the census judges a std routine for EVERY \
                     argument value, so a guard before the call discharges it only where the \
                     verifier models that routine's panic condition at the call site; (3) the \
                     default policy reports this row as a runtime-checked gap and builds, with \
                     vanilla Rust behaviour"
                ));
                notes.extend(census_notes);
            } else {
                notes.push(
                    "an unproven panic-freedom obligation for a call to an absent callee (a \
                     std/extern function whose body is not in the lowered bundle), or for drop \
                     glue with unproven panic-freedom, could not be established — its panic path \
                     stays reachable, so under the fail-closed default this is a build error. \
                     The default policy tolerates only a sysroot (std/core/alloc) callee \
                     instantiated at foundational types — no closure, trait object, or user \
                     type among its type arguments — because such a call can reach no user \
                     code; a dependency's function, or a std routine handed a user type \
                     (`parse::<MyType>`, `Iterator::map` over a closure) may dispatch into a \
                     user body whose panic this row does not cover. Options: (1) keep the call \
                     within that tolerated class; (2) route the value through a Rust `fn` \
                     carrying an `ensures` contract you prove, or a verified sink; \
                     (3) `-Z trust-policy=advisory` records this gap as a warning and continues"
                        .to_string(),
                );
            }
        }
    }
    // Trust (D1 increment 1): the writer-relative disclosure, on the advisory (and
    // on the `certify` refusal it becomes there).
    if writer_rows_excused && (tolerate_default_gap || requires_full_discharge) {
        notes.push(fmt_writer_relative::writer_relative_note(func_path));
    }
    // Trust (hardened process semantics, 2026-09-14 — v7/D3: a refusal carries
    // the fix): an OPEN `process_semantics` mandate means this compilation never
    // declared its process-signal policy. With one declared the row is
    // discharged by construction (trust-vcgen `generate_hardened_vcs`), so this
    // note can only fire for the platform-agnostic `hardened` profile or a raw
    // profile-less hardened run.
    if installed_process_signal_policy(tcx).is_none()
        && artifacts.results.iter().any(|(vc, result)| {
            !matches!(result, VerificationResult::Proved { .. })
                && matches!(
                    &vc.kind,
                    VcKind::HardenedBoundary { category: HardenedVcCategory::ProcessSemantics, .. }
                )
        })
    {
        notes.push(
            "a hardened `process_semantics` mandate is open because this compilation does not \
             DECLARE its process-signal policy and so assumes Rust's default (SIGPIPE ignored: a \
             write to a closed pipe returns EPIPE and `println!` panics). Options: (1) \
             `-Ztrust-verify-profile=unix_hardened` (what `targo trust build` selects by default) \
             declares Unix-tool semantics — `main` installs SIGPIPE -> SIG_DFL, so a closed pipe \
             terminates the process quietly, as C tools do; (2) declare the policy directly with \
             `-Zon-broken-pipe=kill|error|inherit` (under targo: `RUSTFLAGS=-Zon-broken-pipe=error`), \
             which also discharges the mandate; (3) `--no-hardened` / a non-hardened profile"
                .to_string(),
        );
    }
    if failure.unknown > 0 {
        notes.push("unknown or timed-out obligations are unproved coverage gaps and are not permitted under strict verification".to_string());
    }
    if failure.runtime_checked > 0 && requires_full_discharge {
        notes.push("runtime-checked obligations lack a static proof and are not permitted under `-Z trust-policy=certify`; the default policy reports them and builds (the runtime check rustc emits is retained)".to_string());
    }
    if failure.skipped > 0 {
        notes.push("skipped or unsupported verification artifacts are unproved coverage gaps and are not permitted under strict verification".to_string());
    }
    if let Some(result) = &artifacts.full_verification {
        // The strict lane's SECOND status note for this function: it repeats the
        // `timed_out=` the per-function note already printed, so sum one, never both.
        engine_notes.push(native_verifier_status_note(
            "native full verifier status",
            result,
            published_rows,
        ));
        for diagnostic in result.diagnostics.iter().take(8) {
            engine_notes.push(format!("native full verifier diagnostic: {diagnostic}"));
        }
        for evidence in result.evidence.iter().take(8) {
            for diagnostic in evidence.diagnostics.iter().take(3) {
                engine_notes.push(format!(
                    "native full verifier evidence `{}`: {diagnostic}",
                    evidence.obligation_id
                ));
            }
        }
        for skipped in result.skipped.iter().take(8) {
            engine_notes.push(format!(
                "native full verifier skipped `{}`: {:?}",
                skipped.obligation_id, skipped.reason
            ));
        }
    }
    // Trust: one line saying what the following block IS, so a reader who does
    // not work on the verifier knows they can stop here rather than reading
    // forty notes looking for an instruction that is not in them.
    if !engine_notes.is_empty() {
        engine_notes.insert(
            0,
            format!(
                "--- native verifier detail ({} line(s) below; engine internals, not required to act on this error) ---",
                engine_notes.len()
            ),
        );
    }
    // Trust: relaxing the policy is a truthful suggestion only for a coverage
    // gap backed by structurally valid native state. A refutation is not a gap,
    // and malformed or row-misaligned evidence must remain fail-closed without
    // suggesting a policy bypass.
    let advisory_would_help = advisory_policy_help_applies(
        failure,
        has_unproved_assumption_panic,
        native_structurally_sound,
    );
    // Trust (completeness-gap ruling B): report the gap without failing the build
    // when every obligation keeps its runtime check or is the exact defined-IEEE
    // advisory. The LABEL is unchanged — the rows are still reported unproved and
    // are never relabelled `Proved`; only the exit code differs.
    // `struct_span_warn` and `struct_span_err` yield different `Diag` payload types
    // (`()` vs `ErrorGuaranteed`), so the two levels are emitted separately rather
    // than unified into one binding — the same shape the L0 gate above uses.
    if tolerate_default_gap {
        let mut diag = PreparedDiagnostic {
            aborting: false,
            header: (header).into(),
            children: Vec::new(),
        };
        diag.children.push(PreparedDiagnosticChild::Note(("every unproved obligation here either keeps the runtime check rustc already emits \
             or reports a defined IEEE-754 outcome (infinity/NaN, never panic or UB), so the \
             compiled program has vanilla Rust semantics; reported rather than failed under the \
             default policy. `-Z trust-policy=certify` demands full static discharge and fails \
             on these").into()));
        for note in notes {
            diag.children.push(PreparedDiagnosticChild::Note((note).into()));
        }
        for note in engine_notes {
            diag.children.push(PreparedDiagnosticChild::Note((note).into()));
        }
        return Some(PreparedFullFailure { diagnostic: diag, cause: terminal_cause });
    } else {
        let mut diag = PreparedDiagnostic {
            aborting: true,
            header: (header).into(),
            children: Vec::new(),
        };
        for note in notes {
            diag.children.push(PreparedDiagnosticChild::Note((note).into()));
        }
        if let Some(reason) = tolerance_blocked_by {
            diag.children.push(PreparedDiagnosticChild::Note((format!(
                "the default policy reports rather than fails a gap whose obligations all keep \
                 their runtime checks; that did not apply here because {reason}"
            )).into()));
        }
        // Trust: the ONE actionable line, as `help:` and ahead of the engine
        // dump. rustc renders `help:` distinctly from `note:` and readers are
        // trained to look for it; the same sentence buried mid-way through a
        // note list is not findable, which is how a build error whose remedy
        // WAS printed still read as a dead end.
        if advisory_would_help {
            diag.children.push(PreparedDiagnosticChild::Help(("this build failed on unproved coverage, not on a refutation: to record these \
                 rows as warnings and continue only in non-proof survey mode, build with `-Z \
                 trust-policy=advisory`").into()));
        }
        for note in engine_notes {
            diag.children.push(PreparedDiagnosticChild::Note((note).into()));
        }
        return Some(PreparedFullFailure { diagnostic: diag, cause: terminal_cause });
    }
}
