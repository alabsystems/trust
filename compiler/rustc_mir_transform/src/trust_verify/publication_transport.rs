// Trust: eager original transport capture, followed by DATA-only fitting and
// final emission. Serialized transport is reporting DATA, never proof authority.

use super::*;

pub(super) const MAX_FUNCTION_TRANSPORT_MATERIALIZATION_BYTES: u64 = 32 * 1024 * 1024;

/// The real source-map span is kept live outside serialized transport DATA.
pub(super) struct PreparedFunctionTransport {
    warning_span: rustc_span::Span,
    data: PreparedTransportData,
}

impl PreparedFunctionTransport {
    pub(super) fn result(&self) -> &FunctionTransportResult { self.data.result() }

    pub(super) fn split(self) -> (rustc_span::Span, PreparedTransportData) {
        (self.warning_span, self.data)
    }
}

/// Both framing and emission mode come from this SAME original invocation.
/// Only the already computed filename byte cost is retained, never its source.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
enum CapturedFraming {
    RawStderr,
    JsonDiagnostic { span_file_name_bytes: u64 },
}

impl CapturedFraming {
    fn capture(framing: TransportLineFraming) -> Self {
        match framing {
            TransportLineFraming::RawStderr => Self::RawStderr,
            TransportLineFraming::JsonDiagnostic { span_file_name_bytes } => {
                Self::JsonDiagnostic { span_file_name_bytes }
            }
        }
    }

    fn framing(&self) -> TransportLineFraming {
        match self {
            Self::RawStderr => TransportLineFraming::RawStderr,
            Self::JsonDiagnostic { span_file_name_bytes } => {
                TransportLineFraming::JsonDiagnostic { span_file_name_bytes: *span_file_name_bytes }
            }
        }
    }
}

/// `row_anchor` for a nonempty location is independent of its description.
/// Freeze that exact maintained anchor, including any original degradation.
/// Unlocated/empty-file descriptions are handled by `row_anchor` at final fit.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct LocatedAnchor {
    location: trust_types::SourceSpan,
    anchor: String,
}

/// Authority-free prepared report DATA. No source text, tcx, private proof,
/// live Span, materialization action, or proof/candidate selector is retained.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct PreparedTransportData {
    function_result: FunctionTransportResult,
    framing: CapturedFraming,
    budget: u64,
    fallback_location: Option<trust_types::SourceSpan>,
    anchors: Vec<LocatedAnchor>,
    minted_counts: [usize; 7],
    row_diagnostics_enabled: bool,
}

pub(super) fn prepare_transport_json_with_modeled_facts(
    tcx: TyCtxt<'_>,
    def_id: Option<LocalDefId>,
    func_path: &str,
    obligation_results: &[TransportObligationResult],
    cached: u32,
    modeled_facts: &[String],
    expanded_function_identity: Option<
        &trust_types::expanded_function_identity::ExpandedFunctionIdentity,
    >,
) -> PreparedFunctionTransport {
    // Trust (2026-10-09, review round 86): a body carrying an argument premise
    // (D14 removes rows; D15 discharges them) always publishes an unproved
    // premise row, whatever its other rows are. Without it the authenticated
    // lane passed such a body CONDITIONAL-PASS on its runtime-checked rows with
    // the premise nowhere in the report (`modeled_facts` is not read there).
    let premises: Vec<String> = modeled_facts
        .iter()
        .filter(|fact| argument_premise::is_argument_premise_fact(fact))
        .cloned()
        .collect();
    let with_premise_row: Vec<TransportObligationResult>;
    let obligation_results = if !premises.is_empty()
        && !obligation_results.iter().any(|row| row.kind == ARGUMENT_PREMISE_ROW_KIND)
    {
        with_premise_row = obligation_results
            .iter()
            .cloned()
            .chain(std::iter::once(transport_argument_premise_row(&premises)))
            .collect();
        &with_premise_row[..]
    } else {
        obligation_results
    };
    // Trust (2026-09-30): the SAME tally the human summary line reads
    // (`PublishedRowTally`), so the two surfaces cannot categorize a row
    // differently. Every residual outcome — including one a later toolchain adds —
    // lands in the legacy `unknown` aggregate. It is the bucket that grants
    // nothing, so an unrecognized row can only understate the crate's assurance,
    // never overstate it.
    let TransportRowCounts { proved, failed, unknown, timed_out, skipped, runtime_checked, total } =
        PublishedRowTally::of(obligation_results, None).json_counts();
    let role = tcx.sess.trust_crate_role();
    let package_name = tcx.sess.opts.unstable_opts.trust_verify_package_name.clone();
    let primary_package = role.is_cargo_primary();
    let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
    let mut transported_results = obligation_results.to_vec();
    withdraw_grades_outrunning_outcome(&mut transported_results);
    for result in &mut transported_results {
        if let Some(native) = &mut result.native_trust_ir {
            let mut failures = Vec::new();
            for artifact in &mut native.artifacts {
                if let Err(error) = externalize_native_transport_materialization(tcx.sess, artifact)
                {
                    artifact.materialization = None;
                    failures.push(error);
                }
            }
            for failure in failures {
                native.diagnostics.push(transport_diagnostic(
                    "native_materialization_store_failure",
                    TransportEvidenceDiagnosticSeverity::Error,
                    &failure,
                ));
            }
        }
    }
    // THE COMPILER KNOWS, so the compiler says so. `Session::overflow_checks()`
    // and `Session::ub_checks()` are exact, resolved once for this invocation from
    // `-C overflow-checks` / `-C debug-assertions` / `-Z ub-checks` and the profile
    // behind them, and they are what `VcKind::has_runtime_fallback_in` answers the
    // overflow and unchecked-UB families from. Every obligation in this envelope
    // was minted under THESE settings: `build_transport_results` threads this same
    // `sess.overflow_checks()` into every row it builds, and the pass only ever
    // walks local bodies of this session. So the value is a property of the
    // COMPILATION UNIT, and it is stated once, on the unit's envelope, beside the
    // other per-unit identities there — not restated per obligation, where N
    // copies of one fact could disagree with nowhere to notice.
    //
    // A consumer that cannot see this is left inferring the setting from the flags
    // it appended, which is only sound in a lane that owns them; see
    // `FunctionTransportResult::runtime_checks`. It is deliberately NOT fed into
    // `exact_vc_claim_digest_sha256`, whose `semantics` object already commits
    // `overflow_checks` — this restates that same value in readable form, and
    // changes no digest.
    let runtime_checks = RuntimeCheckEnv::new(tcx.sess.overflow_checks(), tcx.sess.ub_checks());
    let mut counted_native_paths = std::collections::BTreeSet::new();
    let mut materialized_bytes = 0u64;
    for artifact in transported_results.iter().flat_map(|result| {
        result
            .native_trust_ir
            .iter()
            .flat_map(|native| &native.artifacts)
            .chain(result.proof_evidence.iter().flat_map(|proof| &proof.artifacts))
    }) {
        let Some(materialization) = &artifact.materialization else {
            continue;
        };
        if let Some(path) = &materialization.materialized_path {
            if counted_native_paths.insert(path.clone()) {
                materialized_bytes = materialized_bytes.saturating_add(materialization.byte_len);
            }
        } else {
            materialized_bytes = materialized_bytes.saturating_add(materialization.byte_len);
        }
    }
    // Trust (T3 L4, C06a): the withhold is a CAP hit (`trust_types::audit_ledger`; C11e2
    // deletes it).
    if trust_types::audit_ledger::cap_hit_if(
        materialized_bytes > MAX_FUNCTION_TRANSPORT_MATERIALIZATION_BYTES,
        "compiler/rustc_mir_transform/src/trust_verify.rs:MAX_FUNCTION_TRANSPORT_MATERIALIZATION_BYTES",
    ) {
        let message = format!(
            "inline proof materialization totals {materialized_bytes} bytes, exceeding the per-function {MAX_FUNCTION_TRANSPORT_MATERIALIZATION_BYTES}-byte transport cap; exact payloads withheld and publication proof credit disabled"
        );
        for result in &mut transported_results {
            if let Some(native) = &mut result.native_trust_ir {
                for artifact in &mut native.artifacts {
                    artifact.materialization = None;
                }
                native.diagnostics.push(transport_diagnostic(
                    "native_materialization_transport_limit",
                    TransportEvidenceDiagnosticSeverity::Error,
                    &message,
                ));
            }
            if let Some(proof) = &mut result.proof_evidence {
                for artifact in &mut proof.artifacts {
                    artifact.materialization = None;
                }
                proof.diagnostics.push(transport_diagnostic(
                    "proof_materialization_transport_limit",
                    TransportEvidenceDiagnosticSeverity::Error,
                    &message,
                ));
            }
        }
    }
    // Trust (T9): the stable keys are minted over the rows exactly as they are
    // published, after every rewrite above (none of which moves a kind, a
    // location or a description).
    let (stable_ids, mut anchors) = capture_stable_ids(tcx, func_path, &transported_results);
    let source_sha256 = def_id.and_then(|def_id| transport_function_source_digest(tcx, def_id));
    let function_result = FunctionTransportResult {
        stable_ids,
        source_sha256,
        expanded_function_identity: expanded_function_identity.cloned(),
        function: func_path.to_string(),
        package_name,
        crate_name: Some(crate_name),
        primary_package,
        verification_session: tcx
            .sess
            .opts
            .unstable_opts
            .trust_verify_session
            .clone()
            .unwrap_or_default(),
        runtime_checks: Some(runtime_checks),
        // Trust (D2 tier 1): the modeled facts this function's rows rest on.
        modeled_facts: modeled_facts.to_vec(),
        results: transported_results,
        proved,
        failed,
        unknown,
        timed_out,
        skipped,
        runtime_checked,
        // Trust (verify-cache): the authoritative cache-replay count from the
        // summary. The conservative `results` rows above carry these as `unknown`
        // (cross-boundary fail-safe); this surfaces the honest count separately.
        cached: cached as usize,
        total,
        transport_budget: None,
    };


    let framing = transport_line_framing(tcx);
    let budget = transport_line_budget();
    // The original fallback query already obtains exactly this def_span.
    // Reuse its real value for any final budget warning, without querying later.
    let warning_span = def_id.map_or(DUMMY_SP, |def_id| tcx.def_span(def_id));
    let fallback_location =
        def_id.map(|_| source_span_from_rustc_span(tcx, warning_span));
    if let Some(location) = fallback_location.as_ref().filter(|span| !span.file.is_empty()) {
        if !anchors.iter().any(|entry| entry.location == *location) {
            anchors.push(LocatedAnchor {
                location: location.clone(),
                anchor: capture_located_anchor(tcx, location),
            });
        }
    }
    let row_diagnostics_enabled = env_flag_enabled("TRUST_VERIFY_ROW_DIAGNOSTICS");
    PreparedFunctionTransport {
        warning_span,
        data: PreparedTransportData {
            function_result,
            framing: CapturedFraming::capture(framing),
            budget,
            fallback_location,
            anchors,
            minted_counts: [proved, failed, unknown, timed_out, skipped, runtime_checked, total],
            row_diagnostics_enabled,
        },
    }
}

fn capture_stable_ids(
    tcx: TyCtxt<'_>,
    func_path: &str,
    rows: &[TransportObligationResult],
) -> (Vec<String>, Vec<LocatedAnchor>) {
    use trust_types::obligation_identity::{AnchorInput, row_anchor};
    let row_anchors = tcx.sess.with_trust_compiler_state::<TransportSourceIndex, _>(|index| {
        index.refresh(tcx);
        rows.iter().map(|row| {
            let local = row.location.as_ref().and_then(|span| index.files.get(&span.file))
                .map(|(text, lines)| (text.as_str(), lines));
            row_anchor(AnchorInput::of(row.location.as_ref(), &row.description, local))
        }).collect::<Vec<_>>()
    });
    let degraded = row_anchors.iter().filter(|anchor| anchor.degraded).count();
    let mut seen = FxHashSet::default();
    let mut located = Vec::new();
    for (row, anchor) in rows.iter().zip(&row_anchors) {
        if let Some(location) = row.location.as_ref().filter(|span| !span.file.is_empty()) {
            if seen.insert(location.clone()) {
                located.push(LocatedAnchor { location: location.clone(), anchor: anchor.anchor.clone() });
            }
        }
    }
    let anchors = row_anchors.into_iter().map(|anchor| anchor.anchor).collect::<Vec<_>>();
    let ids = local_ids_with_anchors(rows, &anchors);
    tcx.sess.with_trust_compiler_state::<TransportSourceIndex, _>(|index| {
        index.degraded_anchors += degraded;
    });
    let ids = match ids {
        Ok(ids) => ids,
        Err(collision) => {
            tcx.dcx().err(format!(
                "Trust: `{func_path}`: {collision}; its verdicts cannot be compared, so the unit \
                 this function belongs to is not a measurement"
            ));
            Vec::new()
        }
    };
    (ids, located)
}

fn capture_located_anchor(tcx: TyCtxt<'_>, location: &trust_types::SourceSpan) -> String {
    use trust_types::obligation_identity::{AnchorInput, row_anchor};
    tcx.sess.with_trust_compiler_state::<TransportSourceIndex, _>(|index| {
        index.refresh(tcx);
        let local = index.files.get(&location.file).map(|(text, lines)| (text.as_str(), lines));
        // A nonempty located anchor does not inspect this description.
        row_anchor(AnchorInput::of(Some(location), "", local)).anchor
    })
}

fn local_ids_with_anchors(
    rows: &[TransportObligationResult],
    anchors: &[String],
) -> Result<Vec<String>, trust_types::obligation_identity::IdCollision> {
    use trust_types::obligation_identity::{KeyedRow, local_ids, row_discriminator, span_position};
    let discriminators = rows.iter().map(|row| row_discriminator(&row.description)).collect::<Vec<_>>();
    let keyed = rows.iter().zip(anchors).zip(&discriminators).map(|((row, anchor), discriminator)| {
        KeyedRow { kind: &row.kind, anchor, position: span_position(row.location.as_ref()), discriminator }
    }).collect::<Vec<_>>();
    local_ids(&keyed)
}

/// A bounded index over prepared anchors, without a source/session fallback.
/// An unrecognized located row is an incomplete capture, never an external
/// or description-only anchor guessed from a different source context.
struct AnchorIndex<'data> {
    located: FxHashMap<&'data trust_types::SourceSpan, &'data str>,
}

impl<'data> AnchorIndex<'data> {
    fn new(anchors: &'data [LocatedAnchor]) -> Result<Self, String> {
        let mut located = FxHashMap::default();
        for entry in anchors {
            if entry.location.file.is_empty() {
                return Err("a located anchor has an empty file".into());
            }
            if located.insert(&entry.location, entry.anchor.as_str())
                .is_some_and(|previous| previous != entry.anchor.as_str())
            {
                return Err("one captured span has conflicting anchors".into());
            }
        }
        Ok(Self { located })
    }

    fn ids(&self, rows: &[TransportObligationResult]) -> Result<Vec<String>, String> {
        use trust_types::obligation_identity::{AnchorInput, row_anchor};
        let anchors = rows.iter().map(|row| {
            if let Some(location) = row.location.as_ref().filter(|span| !span.file.is_empty()) {
                self.located.get(location).map(|anchor| (*anchor).to_string())
                    .ok_or_else(|| format!("no captured anchor for {}:{}:{}-{}:{}",
                        location.file, location.line_start, location.col_start,
                        location.line_end, location.col_end))
            } else {
                Ok(row_anchor(AnchorInput::of(row.location.as_ref(), &row.description, None)).anchor)
            }
        }).collect::<Result<Vec<_>, String>>()?;
        // Original restatement silently leaves IDs empty on a collision: the
        // eager mint already emitted its exact collision refusal.
        Ok(local_ids_with_anchors(rows, &anchors).unwrap_or_default())
    }
}

pub(super) struct FittedFunctionTransport {
    function_result: FunctionTransportResult,
    fitted: Result<trust_types::transport_budget::FittedTransportLine, serde_json::Error>,
    counts: TransportRowCounts,
    framing: TransportLineFraming,
    budget: u64,
    row_diagnostics_enabled: bool,
    identity_defect: Option<String>,
}

impl PreparedTransportData {
    pub(super) fn result(&self) -> &FunctionTransportResult { &self.function_result }

    /// Construct and fit a DATA alternative while the complete original is
    /// still owned by the caller. The only patch constructor consumes an
    /// actual current-artifact kernel token. This method grants no authority
    /// from saved rows, counts, grades or a successful serializer.
    ///
    /// A single restored body's report may be copied during conversion; no
    /// full verification carrier or all-body report collection is retained.
    /// Any conversion, fit, evidence withdrawal or clock miss leaves the
    /// original envelope and its original policy diagnostics untouched.
    pub(super) fn prepare_calculus_selection(
        &self,
        checked: publication_calculus_transport::PreparedCalculusRows,
        mut still_current: impl FnMut() -> bool,
    ) -> Option<FittedFunctionTransport> {
        if !still_current() { return None; }
        let patches = checked.into_rows();
        if patches.is_empty() { return None; }
        let mut seen = FxHashSet::default();
        seen.try_reserve(patches.len()).ok()?;
        for (index, row) in &patches {
            if !still_current() || !seen.insert(*index)
                || self.function_result.results.get(*index).is_none()
                || row.outcome != Outcome::Proved
            {
                return None;
            }
        }
        let mut selected = self.clone();
        if !still_current() { return None; }
        for (index, row) in patches {
            selected.function_result.results[index] = row;
        }
        // Share the existing whole-function materialization budget with the
        // original native/proof artifacts. Repeated path-backed payloads
        // retain the maintained path deduplication rule; inline bytes count
        // at every actual occurrence. This performs no path read or write.
        let mut paths = std::collections::BTreeSet::new();
        let mut materialized_bytes = 0u64;
        for row in &selected.function_result.results {
            if !still_current() { return None; }
            let artifacts = row.native_trust_ir.iter().flat_map(|native| &native.artifacts)
                .chain(row.proof_evidence.iter().flat_map(|proof| &proof.artifacts));
            for artifact in artifacts {
                if !still_current() { return None; }
                let Some(materialization) = &artifact.materialization else { continue };
                if let Some(path) = materialization.materialized_path.as_deref() {
                    if !paths.insert(path) { continue; }
                }
                materialized_bytes = materialized_bytes.checked_add(materialization.byte_len)?;
                if materialized_bytes > MAX_FUNCTION_TRANSPORT_MATERIALIZATION_BYTES {
                    return None;
                }
            }
        }
        // These are the maintained public tally rules, including every
        // noncandidate and added premise row in the complete denominator.
        let counts = PublishedRowTally::try_of(
            &selected.function_result.results, None, &mut still_current,
        )?.json_counts();
        selected.function_result.proved = counts.proved;
        selected.function_result.failed = counts.failed;
        selected.function_result.unknown = counts.unknown;
        selected.function_result.timed_out = counts.timed_out;
        selected.function_result.skipped = counts.skipped;
        selected.function_result.runtime_checked = counts.runtime_checked;
        selected.function_result.total = counts.total;
        let selected_counts = [counts.proved, counts.failed, counts.unknown, counts.timed_out,
            counts.skipped, counts.runtime_checked, counts.total];
        selected.minted_counts = selected_counts;
        if !still_current() { return None; }
        let fitted = selected.fit();
        if !still_current() || fitted.fitted.is_err() || fitted.identity_defect.is_some() {
            return None;
        }
        let actual = &fitted.function_result;
        if [actual.proved, actual.failed, actual.unknown, actual.timed_out,
            actual.skipped, actual.runtime_checked, actual.total] != selected_counts
        {
            // The existing budget fitter may honestly withdraw evidence or
            // replace the report. Such DATA cannot select compiler success.
            return None;
        }
        Some(fitted)
    }

    /// Only final output consumes the envelope; fitting cannot book a function
    /// or materialize a proof, and it has no source/private proof access.
    fn fit(self) -> FittedFunctionTransport {
        let Self { mut function_result, framing, budget, fallback_location, anchors,
            minted_counts: [proved, failed, unknown, timed_out, skipped, runtime_checked, total],
            row_diagnostics_enabled } = self;
        let framing = framing.framing();
        let index = AnchorIndex::new(&anchors);
        let mut identity_defect = index.as_ref().err().cloned();
        let fitted = replay_audit::fit_function_result(
            &mut function_result, budget, framing, fallback_location,
            &mut |result| {
                let counts = PublishedRowTally::of(&result.results, None).json_counts();
                result.proved = counts.proved;
                result.failed = counts.failed;
                result.unknown = counts.unknown;
                result.timed_out = counts.timed_out;
                result.skipped = counts.skipped;
                result.runtime_checked = counts.runtime_checked;
                result.total = counts.total;
                match index.as_ref().map_err(|error| error.clone()).and_then(|index| index.ids(&result.results)) {
                    Ok(ids) => result.stable_ids = ids,
                    Err(error) => {
                        result.stable_ids.clear();
                        identity_defect = Some(error);
                    }
                }
            },
        );
        let counts = if fitted.is_ok() && identity_defect.is_none() {
            TransportRowCounts { proved: function_result.proved, failed: function_result.failed,
                unknown: function_result.unknown, timed_out: function_result.timed_out,
                skipped: function_result.skipped, runtime_checked: function_result.runtime_checked,
                total: function_result.total }
        } else {
            TransportRowCounts { proved, failed, unknown, timed_out, skipped, runtime_checked, total }
        };
        FittedFunctionTransport { function_result, fitted, counts, framing, budget,
            row_diagnostics_enabled, identity_defect }
    }

    pub(super) fn emit(self, tcx: TyCtxt<'_>, warning_span: rustc_span::Span) {
        self.fit().emit(tcx, warning_span);
    }
}

impl FittedFunctionTransport {
    pub(super) fn emit(self, tcx: TyCtxt<'_>, warning_span: rustc_span::Span) {
        let Self { function_result, fitted, counts, framing, budget,
            row_diagnostics_enabled, identity_defect } = self;
        let func_path = function_result.function.as_str();
        // Trust: debug/test consumers can inspect one exact final public row at a
        // time. A sibling's certificate cannot satisfy a line-anchored aggregate
        // grade check. These are the SAME canonical rows, after all publication
        // rewrites (the transport budget's included); the distinct prefix is never
        // accepted as proof transport.
        let _ = row_diagnostics::write_rows(
            row_diagnostics_enabled,
            &mut std::io::stderr().lock(),
            func_path,
            &function_result.results,
        );

        // The crate summary sums the counts of the envelopes as emitted, so targo's
        // crate accounting reconciles with the function lines it reads. A serialization
        // failure (no line) keeps the minted counts, so the summary disagrees with the
        // lines and targo refuses the unit, as before.
        let TransportRowCounts { proved, failed, unknown, timed_out, skipped, runtime_checked, total } = counts;
        tcx.sess.with_trust_compiler_state::<TransportCrateAccumulator, _>(|summary| {
            summary.functions_analyzed += 1;
            if total > 0 && proved == total {
                summary.functions_verified += 1;
            }
            summary.total_proved += proved;
            summary.total_failed += failed;
            summary.total_unknown += unknown;
            summary.total_timed_out += timed_out;
            summary.total_skipped += skipped;
            summary.total_runtime_checked += runtime_checked;
            summary.total_obligations += total;
        });

        // Trust: emit as a single line. Best-effort: serialization failure is non-fatal
        // since text diagnostics are still emitted.
        if let Some(error) = identity_defect {
            tcx.dcx().err(format!(
                "Trust: `{func_path}`: incomplete prepared transport identity ({error}); its verdicts \
                 cannot be compared, so the unit this function belongs to is not a measurement"
            ));
            return;
        }
        let Ok(fitted) = fitted else {
            return;
        };
        if let Some(disclosure) = &function_result.transport_budget {
            let what = match disclosure.step {
                TransportBudgetStep::WithheldDiagnosticPayloads => format!(
                    "the original-VC snapshots of {} row(s) were withheld; no outcome changed",
                    disclosure.withheld.iter().map(|entry| entry.rows.len()).sum::<usize>()
                ),
                TransportBudgetStep::WithheldProofEvidence => format!(
                    "the proof-evidence payloads of {} row(s) were withheld, and {} row(s) that \
                     claimed a proof or a runtime check without them are published `unknown` or \
                     `failed`",
                    disclosure
                        .withheld
                        .iter()
                        .filter(|entry| entry.field.carries_authority())
                        .flat_map(|entry| entry.rows.iter())
                        .collect::<std::collections::BTreeSet<_>>()
                        .len(),
                    disclosure.demoted_rows.len()
                ),
                TransportBudgetStep::ReportReplaced => format!(
                    "even without its optional evidence it does not fit, so its {} row(s) were \
                     replaced by one fail-closed `{}` row and the function is not verified",
                    disclosure.minted_rows,
                    function_result.results.first().map_or("unknown", |row| row.outcome.as_str()),
                ),
            };
            tcx.dcx()
                .struct_span_warn(
                    warning_span,
                    format!(
                        "Trust: the verification report of `{func_path}` would take {} bytes, over \
                         the {budget}-byte transport line budget; {what}",
                        disclosure.unbounded_line_bytes
                    ),
                )
                .emit();
        }
        emit_transport_payload(tcx, &fitted.payload, framing, budget);
    }
}

fn emit_transport_payload(tcx: TyCtxt<'_>, json: &str, framing: TransportLineFraming, budget: u64) {
    // Trust: (TRANSPORT-LINE-BUDGET-1) no transport line passes the budget, whatever
    // emits it. A function report is fitted before it gets here, so this refuses only a
    // crate-level row (coverage, crate summary) or a function envelope whose identity
    // alone outruns the budget. Such a line is not written, and the compile fails: the
    // unit's report is incomplete, which its consumer must refuse, and the other lines
    // still reach it instead of a closed pipe killing this process.
    let line_bytes = framing.line_bytes(json);
    if line_bytes > budget {
        let kind = serde_json::from_str::<serde_json::Value>(json)
            .ok()
            .and_then(|value| value.get("type").and_then(|kind| kind.as_str()).map(str::to_string))
            .unwrap_or_else(|| "transport".to_string());
        tcx.dcx().err(format!(
            "Trust: a `{kind}` transport line would take {line_bytes} bytes, over the \
             {budget}-byte transport line budget; it is not emitted, so this unit's \
             verification report is incomplete"
        ));
        return;
    }
    let payload = format!("{TRANSPORT_PREFIX}{json}");
    match framing {
        TransportLineFraming::RawStderr => {
            // Raw trustc/driver consumers retain the one-line protocol. Do not
            // also emit a diagnostic here: human diagnostics render a second
            // `note: TRUST_JSON:...` copy and make one logical row look like two.
            eprintln!("{payload}");
        }
        TransportLineFraming::JsonDiagnostic { .. } => {
            // Cargo JSON mode wraps diagnostics in a compiler-message carrying
            // package/target identity. Targo accepts crate-mode evidence only
            // through that envelope, so build-script stderr cannot forge
            // verifier transport. A raw line in this mode would sit outside the
            // Cargo envelope and re-open that provenance ambiguity.
            let mut diagnostic = tcx.dcx().struct_span_note(DUMMY_SP, payload);
            // This code marks a transport envelope, not a version-gated lint;
            // there is no minimum Rust version associated with it.
            diagnostic.is_lint(TRANSPORT_DIAGNOSTIC_CODE.to_string(), false, None);
            // Trust: preserve every transport byte in `message`, while avoiding
            // a rendered duplicate that can exceed the reader's line cap.
            diagnostic.set_json_rendered_message(
                "Trust verification results are available in the structured JSON message",
            );
            diagnostic.emit();
        }
    }
}

#[cfg(test)]
mod tests;
