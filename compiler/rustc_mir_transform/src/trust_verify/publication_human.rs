//! Trust: frozen human-report facts, never proof/grade authority. Capture
//! performs the original private/source-dependent reads once. Rendering reads
//! only owned DATA and a parent-supplied published-row tally; an alternative
//! remains unselected until the parent checks its exact fresh opaque token.

use super::*;

/// No Session, VC, binding, authority or certificate is retained. These are
/// presentation facts only; deserializing them cannot authorize a disposition.
#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct HumanFacts {
    rows: Vec<HumanRow>,
    conditional_on_coroutine_premise: bool,
    // Includes the ORIGINAL certified count and every named premise. The pure
    // renderer only copies these strings; proposed rows never earn a new tier.
    disclosures: Vec<String>,
}

#[derive(serde::Serialize, serde::Deserialize)]
enum HumanRow {
    Proved,
    Assumed(String),
    Failed { reason: String, unproved: bool },
    Unknown { reason: String, proposable: bool },
    RuntimeChecked { reason: String, proposable: bool },
    Timeout(String),
    Other(String),
}

impl HumanRow {
    fn proposable(&self) -> bool {
        matches!(self,
            Self::Unknown { proposable: true, .. }
                | Self::RuntimeChecked { proposable: true, .. }
        )
    }

    fn exclude_proposal(&mut self) {
        match self {
            Self::Unknown { proposable, .. } | Self::RuntimeChecked { proposable, .. } => {
                *proposable = false;
            }
            _ => {}
        }
    }
}

/// Capture every original row and disclosure while the actual original
/// carriers exist. Missing/misaligned authority retains the original honest
/// classification. Nothing here creates or mutates proof authority.
pub(super) fn capture(
    sess: &Session,
    results: &[(VerificationCondition, VerificationResult)],
    result_bindings: &[Option<ResultObligationBinding>],
    proof_authorities: &[Option<ResultProofAuthority>],
    certified: usize,
    conditional_on_coroutine_premise: bool,
) -> Option<HumanFacts> {
    if results.is_empty() { return None; }
    let mut rows = Vec::with_capacity(results.len());
    for (index, (vc, result)) in results.iter().enumerate() {
        let tag = format_vc_kind(&vc.kind);
        let binding = result_bindings.get(index).and_then(Option::as_ref);
        let authority = proof_authorities.get(index).and_then(Option::as_ref);
        let mut row = match result {
            VerificationResult::Proved { .. }
                if authority.is_some_and(|authority| {
                    authority.permits_static_proved_transport_for(index, vc, result, binding)
                }) => HumanRow::Proved,
            VerificationResult::Proved { .. }
                if authority.is_some_and(|authority| {
                    authority.is_definition_entry_assumption_for(index, vc, binding)
                }) => HumanRow::Assumed(format!("[{tag}] {TRUST_ENTRY_ASSUMPTION_REASON}")),
            VerificationResult::Proved { solver, .. } => {
                if has_runtime_check(sess, &vc.kind) {
                    HumanRow::RuntimeChecked {
                        reason: format!(
                            "[{tag}] runtime-checked: solver {solver} reported Proved without exact kernel/native proof authority"
                        ),
                        proposable: true,
                    }
                } else {
                    HumanRow::Unknown {
                        reason: format!(
                            "[{tag}] UNKNOWN ({solver}): Proved label lacked exact kernel/native proof authority"
                        ),
                        proposable: true,
                    }
                }
            }
            VerificationResult::Failed { solver, counterexample, .. } => {
                let cex = counterexample.as_ref()
                    .map(|c| format!("; counterexample: {c}"))
                    .unwrap_or_default();
                let (basis, unproved) = match trust_types::FailureBasis::of_result(result) {
                    Some(basis @ trust_types::FailureBasis::UnprovedFailClosed) => {
                        (format!(": {}", basis.human_label()), true)
                    }
                    _ => (String::new(), false),
                };
                HumanRow::Failed { reason: format!("[{tag}] FAILED ({solver}){basis}{cex}"), unproved }
            }
            VerificationResult::Unknown { solver, reason, .. } => {
                // Preserve the original short-circuit: a held refutation never
                // asks has_runtime_check and is never a proposed proof row.
                let held_refutation = result_is_held_assert_refutation(result);
                if !held_refutation && has_runtime_check(sess, &vc.kind) {
                    HumanRow::RuntimeChecked {
                        reason: format!("[{tag}] runtime-checked: {}", runtime_check_note(&vc.kind)),
                        proposable: true,
                    }
                } else {
                    HumanRow::Unknown {
                        reason: format!("[{tag}] UNKNOWN ({solver}): {reason}"),
                        proposable: !held_refutation,
                    }
                }
            }
            VerificationResult::Timeout { solver, .. } => {
                if has_runtime_check(sess, &vc.kind) {
                    HumanRow::RuntimeChecked {
                        reason: format!("[{tag}] runtime-checked: {}", runtime_check_note(&vc.kind)),
                        proposable: false,
                    }
                } else {
                    HumanRow::Timeout(format!("[{tag}] TIMEOUT ({solver})"))
                }
            }
            _ => HumanRow::Other(format!("[{tag}] unsupported verification result variant")),
        };
        // Conservative DATA eligibility only. Even a misaligned public Proved
        // label cannot turn a recorded assumption/premise into a proposed row.
        // These private field/variant reads confer no authority; the parent
        // still validates each exact original row and its native obligation.
        if binding.is_some_and(|binding| {
            binding.definition_entry_assumption || binding.assumed_total_callee_assumption
        }) || matches!(authority,
            Some(ResultProofAuthority::DefinitionEntryAssumption { .. }
                | ResultProofAuthority::AssumedTotalCalleeAssumption { .. }
                | ResultProofAuthority::EnsuresCitationViewDischarge { .. }
                | ResultProofAuthority::EnsuresCitationUnderRequiresDischarge { .. }
                | ResultProofAuthority::TypeInvariantComposed { .. })
        ) || is_entry_assumption_discharge(result) || is_assumed_total_discharge(result) {
            row.exclude_proposal();
        }
        rows.push(row);
    }

    // The following original disclosure phase keeps the original view/link/
    // invariant authority-query order. Only its final owned text survives.
    let mut diag = PreparedHumanReport { summary: String::new(), notes: Vec::new() };
    // Trust: surface clean's kernel-certified tier by default. A `Certified`
    // obligation was re-proved and RE-CHECKED by the clean CIC kernel with ZERO
    // trust in the SMT solver (the de Bruijn criterion), so the solver is outside
    // the trusted base. This is a strictly stronger guarantee than `proved`
    // (solver-trusted), so we report it explicitly when present. Runtime-check
    // elision remains disabled until this proof also carries exact MIR-Assert
    // identity.
    // Trust (D2 part C): a coroutine resume body's discharges all sit under the
    // bridge's entry `Assume(resume_state ∈ live_states)`, which dominates every
    // block. Advertising them as kernel-certified states a stronger fact than
    // the kernel established: on the exhibit the certified term was an EX FALSO
    // derivation from `resume_state = 0 ∧ resume_state = 1`, whose
    // `axiom_closure: Empty` is literally true of the term (ex falso needs no
    // axiom) and materially misleading about the obligation, because the premise
    // was baked into the hypothesis CONTEXT rather than presented as an axiom.
    // Name the premise instead of the tier.
    if conditional_on_coroutine_premise {
        if certified > 0 {
            diag.note(format!(
                "{certified} obligation(s) were discharged CONDITIONALLY, under the coroutine \
                 resume-state entry assumption injected at function entry — not as unconditional \
                 proof; see the accompanying coroutine executor-protocol row"
            ));
        }
    } else if certified > 0 {
        diag.note(format!(
            "of which {certified} kernel-certified by the clean CIC kernel \
             (zero-trust re-check; runtime-check elision requires exact MIR Assert identity)"
        ));
    }
    // Trust (ref-self I1): the DISCHARGE NOTE owner ruling R1 requires. Such a
    // row is deliberately absent from `certified` above — its disposition is
    // `Trusted`, not `Certified` — so without this note the human surface would
    // simply not mention it, and "a row that is not certified" is not the same
    // statement as "a row that rests on a named assumption".
    // The marker is read OFF THE AUTHORITY rather than restated from the
    // constant, so the note cannot name a view the sealed rows do not carry.
    let view_markers: Vec<&'static str> = proof_authorities
        .iter()
        .enumerate()
        .filter_map(|(index, authority)| {
            let authority = authority.as_ref()?;
            let ResultProofAuthority::EnsuresCitationViewDischarge { view, .. } = authority else {
                return None;
            };
            // Bound to ITS OWN ROW, like the `proved` counter above and unlike
            // a bare variant filter: an authority that does not bind the row it
            // sits on is not a discharge of it, and counting it would print a
            // number the report cannot substantiate.
            let (vc, result) = results.get(index)?;
            let binding = result_bindings.get(index).and_then(Option::as_ref);
            authority
                .permits_static_proved_transport_for(index, vc, result, binding)
                .then_some(*view)
        })
        .collect();
    let view_rows = view_markers.len();
    if let Some(marker) = view_markers.first().copied() {
        diag.note(format!(
            "{view_rows} obligation(s) were discharged through the borrow-erased E6 PARAMETER \
             VIEW (view: {marker}): the Clean-side defining equation, and every `self.<field>` \
             clause binder, name the pointee's scalar field VALUES AT ENTRY. That those values \
             are what the function reads rests on an assumption the compiler does not prove — a \
             live `&T` argument with `T: Freeze` is dereferenceable and its pointee is immutable \
             for the duration of the call (docs/TCB.md, the `EnsuresCitationViewDischarge` row; owner ruling R1). \
             Such a row is NOT kernel-certified, licenses no check elision, and the authenticated \
             `targo trust` lane withholds it. A `&T` into memory something outside Rust's \
             aliasing rules mutates (an mmap'd file, shared memory, MMIO, a raced `static mut`) \
             is out of scope: copy the scalars out and contract a by-value helper instead",
        ));
    }
    // Trust (OR-A1, owner ruling 2026-09-27): the discharge note the ruling
    // requires for a CONDITIONAL row. Like the view row it is absent from
    // `certified` above (its disposition is `Trusted`), and "a row that is not
    // certified" is not the statement "a row that rests on this function's own
    // `requires` through a link the kernel did not check". Read off the SEALED
    // authorities, each bound to its own row, so the note cannot name a link no
    // row carries.
    let conditional_links: Vec<trust_certify::clean_island::RequiresLink> = proof_authorities
        .iter()
        .enumerate()
        .filter_map(|(index, authority)| {
            let authority = authority.as_ref()?;
            let ResultProofAuthority::EnsuresCitationUnderRequiresDischarge { link, .. } =
                authority
            else {
                return None;
            };
            let (vc, result) = results.get(index)?;
            let binding = result_bindings.get(index).and_then(Option::as_ref);
            authority
                .permits_static_proved_transport_for(index, vc, result, binding)
                .then_some(*link)
        })
        .collect();
    if !conditional_links.is_empty() {
        use trust_certify::clean_island::RequiresLink;
        let canonical =
            conditional_links.iter().filter(|link| **link == RequiresLink::KernelCanonical).count();
        let allow_listed = conditional_links.len() - canonical;
        let mut links = Vec::new();
        if canonical > 0 {
            links.push(format!("{canonical} requires-link: kernel-canonical"));
        }
        if allow_listed > 0 {
            links.push(format!("{allow_listed} requires-link: allow-listed"));
        }
        diag.note(format!(
            "{} obligation(s) were discharged by a cited theorem proved UNDER this function's own \
             `requires` ({}): each holds for inputs satisfying the carried preconditions — a \
             caller assumes it only where it establishes them at the call — and says nothing \
             about the rest. Such a row is `Trusted`, not kernel-certified (owner ruling OR-A1, \
             docs/TCB.md, the `EnsuresCitationUnderRequiresDischarge` row): the step from what \
             callers are charged to what the theorem consumed is built by the compiler, not \
             checked by the kernel, so the row licenses no check elision and the authenticated \
             `targo trust` lane withholds it",
            conditional_links.len(),
            links.join(", "),
        ));
        if allow_listed > 0 {
            diag.note(
                "an allow-listed link rests on the arithmetic-free allow-list alone; state each \
                 hypothesis over the lifted carrier (`UInt64.toNat a = UInt64.toNat b`, not \
                 `a = b`) to have the kernel judge it against the reading callers are charged",
            );
        }
    }
    // Trust (TINV step 10.7, TINV-28 amended): the disclosure note of every row proved
    // UNDER a certified type invariant. Such a row counts in `proved` above (it is a
    // disclosed `Trusted` proof) and is absent from `certified`; this note names each
    // premise, read off the sealed token bound to its own row, so the human line cannot
    // say "proved" without saying what the proof assumes.
    let mut tinv_premises: std::collections::BTreeMap<&str, usize> =
        std::collections::BTreeMap::new();
    let mut tinv_rows = 0usize;
    for (index, authority) in proof_authorities.iter().enumerate() {
        let (Some(authority), Some((vc, result))) = (authority.as_ref(), results.get(index)) else {
            continue;
        };
        let binding = result_bindings.get(index).and_then(Option::as_ref);
        if let Some(lines) = authority.type_invariant_disclosure_for(index, vc, result, binding) {
            tinv_rows += 1;
            for line in lines {
                *tinv_premises.entry(line.as_str()).or_insert(0) += 1;
            }
        }
    }
    if tinv_rows > 0 {
        diag.note(type_invariant_terminal_headline(tinv_rows));
        for (line, rows) in &tinv_premises {
            diag.note(format!("{line} ({rows} obligation(s))"));
        }
    }
    Some(HumanFacts {
        rows,
        conditional_on_coroutine_premise,
        disclosures: diag.notes,
    })
}

impl HumanFacts {
    /// Pure presentation. `published_rows` is the parent's tally of the exact
    /// alternative, including added/collapsed policy debt. It is neither
    /// rebuilt from VC counts nor reduced by this renderer. The parent must
    /// preserve that full published denominator and gate selection separately.
    /// Empty proposed indices render the ORIGINAL mode. Nonempty proposals
    /// change only those original per-VC dispositions/reasons, never the
    /// original certified count or unrelated assumption/premise disclosures.
    pub(super) fn render(
        &self,
        published_rows: PublishedRowTally,
        proposed: &[usize],
    ) -> Option<PreparedHumanReport> {
        if self.rows.is_empty() { return None; }
        let mut selected = std::collections::BTreeSet::new();
        for &index in proposed {
            if !self.rows.get(index)?.proposable() || !selected.insert(index) {
                return None;
            }
        }
        let mut proved = 0usize;
        let mut failed = 0usize;
        let mut unknown = 0usize;
        let mut timeout = 0usize;
        let mut runtime_checked = 0usize;
        let mut other = 0usize;
        let mut assumed = 0usize;
        let mut failed_unproved = 0usize;
        let mut reasons: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
        for (index, row) in self.rows.iter().enumerate() {
            if selected.contains(&index) {
                proved += 1;
                continue;
            }
            let reason = match row {
                HumanRow::Proved => { proved += 1; None }
                HumanRow::Assumed(reason) => { assumed += 1; Some(reason) }
                HumanRow::Failed { reason, unproved } => {
                    failed += 1;
                    failed_unproved += usize::from(*unproved);
                    Some(reason)
                }
                HumanRow::Unknown { reason, .. } => { unknown += 1; Some(reason) }
                HumanRow::RuntimeChecked { reason, .. } => { runtime_checked += 1; Some(reason) }
                HumanRow::Timeout(reason) => { timeout += 1; Some(reason) }
                HumanRow::Other(reason) => { other += 1; Some(reason) }
            };
            if let Some(reason) = reason {
                *reasons.entry(reason.clone()).or_insert(0) += 1;
            }
        }
        let conditional_on_coroutine_premise = self.conditional_on_coroutine_premise;
        // D2 part C: in a contract-engaged coroutine body the entry `Assume`
        // dominates every block, so NOTHING here was proved unconditionally.
        // Calling those rows "proved" on the line a developer actually reads is the
        // human-surface half of the same defect the transport stamp closes; name
        // the conditionality in the counter itself rather than only in a note.
        let discharge_label = if conditional_on_coroutine_premise {
            "conditionally discharged (NOT proved)"
        } else {
            "proved"
        };
        // The line counts the rows this function PUBLISHES — the JSON transport's rows —
        // through the one tally both surfaces read (`PublishedRowTally`), in this line's
        // disjoint categories (the JSON's `unknown` is `unknown + timed out + skipped`
        // here; the totals are equal). The VC-level tallies above stay what they were for
        // the per-obligation notes below; when they differ from the published rows and no
        // cause note explains why, a note says so.
        let rows = published_rows;
        let mut summary = format!(
            "Trust verification: {} {discharge_label}, {} failed, {} unknown, {} timed out, \
             {} runtime-checked",
            rows.proved, rows.failed, rows.unknown, rows.timed_out, rows.runtime_checked,
        );
        // Trust: entry `requires` rows are assumed, not proved; they stay in the
        // denominator and are named so the line reconciles with the transport's
        // `skipped`/`assumption:requires` rows.
        if rows.assumed_requires > 0 {
            summary.push_str(&format!(", {} assumed (requires)", rows.assumed_requires));
        }
        if rows.assumed_discharge > 0 {
            summary.push_str(&format!(", {} assumed (instance discharge)", rows.assumed_discharge));
        }
        if rows.skipped > 0 {
            summary.push_str(&format!(", {} skipped", rows.skipped));
        }
        summary.push_str(&format!(" out of {} obligation(s)", rows.total()));
        // Rows the policy layer only ADDED as skipped (D2 part C's coroutine premise)
        // need no note: the line has always named them "skipped".
        let vc_level_differs = (proved, failed, unknown + other, timeout, runtime_checked, assumed)
            != (
                rows.proved,
                rows.failed,
                rows.unknown,
                rows.timed_out,
                rows.runtime_checked,
                rows.assumed_requires,
            )
            // A discharge row has no VC-level counterpart.
            || rows.assumed_discharge > 0;

        // Trust: All results are notes — verification is additive and must NEVER
        // break builds.
        let mut diag = PreparedHumanReport { summary, notes: Vec::new() };
        match rows.cause {
            Some(PublishedRowsCause::NativeLoweringCollapse) => {
                diag.note(
                    "counted over the rows this function publishes: native typed-TrustIr lowering \
                     did not complete, and its unproved rows were collapsed into one \
                     `assumption:native-lowering` row (skipped, NOT proved); the notes below are \
                     the per-obligation results from before that collapse",
                );
            }
            Some(PublishedRowsCause::UnchargedLoweringGap) => {
                diag.note(
                    "counted over the rows this function publishes: native typed-TrustIr lowering \
                     did not complete, and the calls it left uncharged are published as one \
                     `native-verification-gap` row (unknown); the notes below are the \
                     per-obligation results",
                );
            }
            Some(PublishedRowsCause::UnaccountedGap) => {
                diag.note(
                    "counted over the rows this function publishes: the per-obligation results \
                     below do not cover the whole body — a native typed-TrustIr lowering that did \
                     not complete, a call into foreign code that no obligation charges, or an \
                     unresolved indirect call — and each such gap is published as a \
                     `native-verification-gap` row (unknown, NOT proved)",
                );
            }
            None if vc_level_differs => {
                diag.note(
                    "counted over the rows this function publishes (its JSON transport rows): the \
                     policy layer added rows after the per-obligation results below, or reclassified \
                     some of them (a memory-safe assumption, a runtime-checked std member, a \
                     contract-panic or termination row), so their categories can differ from this \
                     line's",
                );
            }
            None => {}
        }
        // Trust (honest label): name the failed rows nothing refuted, so a
        // fail-closed unsafe-operation row is not read as a found violation. The
        // summary line above is unchanged and still counts them as failed.
        if failed_unproved > 0 {
            diag.note(format!(
                "of the per-obligation results below, {failed_unproved} FAILED row(s) are unproved \
                 with NO counterexample: nothing refuted them; they fail closed because the unsafe \
                 operation could not be proved and may not pass unproved (an unmodelled call, a \
                 body that did not lower to native trust-ir, or a solver that returned unknown)"
            ));
        }
        // These are the ORIGINAL captured disclosure strings; proposing a row
        // cannot synthesize a kernel/certified label or a new premise.
        for note in &self.disclosures { diag.note(note.clone()); }
        for (reason, count) in reasons.iter().take(MAX_REPORTED_REASONS) {
            if *count > 1 {
                diag.note(format!("{count}× {reason}"));
            } else {
                diag.note(reason.clone());
            }
        }
        if reasons.len() > MAX_REPORTED_REASONS {
            diag.note(format!(
                "… and {} more distinct reason(s) suppressed (log batching)",
                reasons.len() - MAX_REPORTED_REASONS,
            ));
        }
        Some(diag)
    }
}


// Pure presentation controls, authored UNEXECUTED. These fixtures are DATA,
// not certificates, accepted private authorities or a current compiler proof.
#[cfg(test)]
mod tests {
    use super::*;

    fn tally() -> PublishedRowTally {
        PublishedRowTally {
            cause: None,
            proved: 1,
            failed: 1,
            unknown: 3,
            timed_out: 1,
            runtime_checked: 1,
            assumed_requires: 1,
            assumed_discharge: 1,
            skipped: 2,
            clock_stopped: 1,
        }
    }

    fn facts() -> HumanFacts {
        HumanFacts {
            rows: vec![
                HumanRow::Proved,
                HumanRow::Assumed("[a] original requires assumption".into()),
                HumanRow::Unknown { reason: "[b] UNKNOWN (ay): original open row".into(), proposable: true },
                HumanRow::Unknown { reason: "[b] UNKNOWN (ay): original open row".into(), proposable: true },
                HumanRow::Failed { reason: "[c] FAILED (ay): original fail-closed reason".into(), unproved: true },
                HumanRow::Timeout("[d] TIMEOUT (ay)".into()),
                HumanRow::RuntimeChecked { reason: "[e] original runtime monitor".into(), proposable: true },
                HumanRow::Other("[f] unsupported verification result variant".into()),
            ],
            conditional_on_coroutine_premise: false,
            // Arbitrary already-captured text verifies copy/order behavior;
            // this does not construct the authority that could substantiate it.
            disclosures: vec![
                "of which 1 kernel-certified by the clean CIC kernel (zero-trust re-check; runtime-check elision requires exact MIR Assert identity)".into(),
                "original named premise; not a new candidate certificate".into(),
            ],
        }
    }

    #[test]
    fn original_render_keeps_published_denominator_disclosures_and_batched_reasons() {
        let report = facts().render(tally(), &[]).unwrap();
        assert_eq!(report.summary,
            "Trust verification: 1 proved, 1 failed, 3 unknown, 1 timed out, 1 runtime-checked, 1 assumed (requires), 1 assumed (instance discharge), 2 skipped out of 11 obligation(s)");
        assert_eq!(report.notes, vec![
            "counted over the rows this function publishes (its JSON transport rows): the policy layer added rows after the per-obligation results below, or reclassified some of them (a memory-safe assumption, a runtime-checked std member, a contract-panic or termination row), so their categories can differ from this line's",
            "of the per-obligation results below, 1 FAILED row(s) are unproved with NO counterexample: nothing refuted them; they fail closed because the unsafe operation could not be proved and may not pass unproved (an unmodelled call, a body that did not lower to native trust-ir, or a solver that returned unknown)",
            "of which 1 kernel-certified by the clean CIC kernel (zero-trust re-check; runtime-check elision requires exact MIR Assert identity)",
            "original named premise; not a new candidate certificate",
            "[a] original requires assumption",
            "2× [b] UNKNOWN (ay): original open row",
            "[c] FAILED (ay): original fail-closed reason",
            "[d] TIMEOUT (ay)",
            "[e] original runtime monitor",
            "… and 1 more distinct reason(s) suppressed (log batching)",
        ]);
    }

    #[test]
    fn proposal_changes_only_exact_row_reason_and_never_certified_or_unrelated_debt() {
        let facts = facts();
        let original = facts.render(tally(), &[]).unwrap();
        let mut alternative = tally();
        alternative.proved = 2;
        alternative.unknown = 2;
        assert_eq!(alternative.total(), tally().total());
        let candidate = facts.render(alternative, &[2]).unwrap();
        assert_eq!(candidate.summary,
            "Trust verification: 2 proved, 1 failed, 2 unknown, 1 timed out, 1 runtime-checked, 1 assumed (requires), 1 assumed (instance discharge), 2 skipped out of 11 obligation(s)");
        assert_eq!(candidate.notes.len(), 10);
        assert_eq!(candidate.notes[5], "[b] UNKNOWN (ay): original open row");
        for index in [0, 1, 2, 3, 4, 6, 7, 8, 9] {
            assert_eq!(candidate.notes[index], original.notes[index], "unrelated disclosure/reason {index}");
        }
        let again = facts.render(tally(), &[]).unwrap();
        assert_eq!(again.summary, original.summary);
        assert_eq!(again.notes, original.notes, "rendering never mutates original facts");

        // An original Unknown rendered as runtime-checked can be proposed;
        // its Timeout-derived counterpart below is deliberately ineligible.
        let mut runtime_alternative = tally();
        runtime_alternative.proved = 2;
        runtime_alternative.runtime_checked = 0;
        assert_eq!(runtime_alternative.total(), tally().total());
        let candidate = facts.render(runtime_alternative, &[6]).unwrap();
        assert!(!candidate.notes.iter().any(|s| s.contains("[e] original runtime monitor")));
        assert!(candidate.notes.iter().any(|s| s.contains("of which 1 kernel-certified")));
        assert!(!candidate.notes.iter().any(|s| s.contains("of which 2 kernel-certified")));
    }

    #[test]
    fn invalid_or_protected_proposals_refuse_instead_of_skipping_rows() {
        let mut facts = facts();
        facts.rows.push(HumanRow::Unknown {
            reason: "held refutation or original assumption/premise".into(), proposable: false,
        });
        facts.rows.push(HumanRow::RuntimeChecked {
            reason: "original timeout fallback".into(), proposable: false,
        });
        let mut rows = tally();
        rows.unknown += 1;
        rows.runtime_checked += 1;
        for valid in [vec![], vec![2], vec![3], vec![6], vec![6, 2]] {
            assert!(facts.render(rows, &valid).is_some(), "nonvacuous permitted DATA baseline");
        }
        for invalid in [
            vec![2, 2], vec![usize::MAX], vec![2, usize::MAX],
            vec![0], vec![1], vec![4], vec![5], vec![7], vec![8], vec![9],
        ] {
            assert!(facts.render(rows, &invalid).is_none(), "invalid proposal {invalid:?}");
        }
    }

    #[test]
    fn frozen_human_data_roundtrip_does_not_synthesize_a_favorable_label() {
        let original = facts();
        let bytes = serde_json::to_vec(&original).unwrap();
        let owned: HumanFacts = serde_json::from_slice(&bytes).unwrap();
        let original_report = original.render(tally(), &[]).unwrap();
        let decoded_report = owned.render(tally(), &[]).unwrap();
        assert_eq!(decoded_report.summary, original_report.summary);
        assert_eq!(decoded_report.notes, original_report.notes);
        assert!(owned.render(tally(), &[1]).is_none(), "an assumption stays ineligible after decode");
        let mut unknown_variant = serde_json::to_value(&original).unwrap();
        unknown_variant["rows"][0] = serde_json::json!({"Certified": "not a DATA row constructor"});
        assert!(serde_json::from_value::<HumanFacts>(unknown_variant).is_err());
        let mut extra = serde_json::to_value(&original).unwrap();
        extra["selected_success"] = serde_json::json!(true);
        assert!(serde_json::from_value::<HumanFacts>(extra).is_err());
    }

    #[test]
    fn conditional_and_collapse_disclosures_keep_the_original_scope_and_full_count() {
        let mut facts = facts();
        facts.conditional_on_coroutine_premise = true;
        facts.disclosures = vec![
            "1 obligation(s) were discharged CONDITIONALLY, under the coroutine resume-state entry assumption injected at function entry — not as unconditional proof; see the accompanying coroutine executor-protocol row".into(),
            "original named invariant premise".into(),
        ];
        let mut rows = tally();
        rows.cause = Some(PublishedRowsCause::NativeLoweringCollapse);
        let original = facts.render(rows, &[]).unwrap();
        assert_eq!(original.summary,
            "Trust verification: 1 conditionally discharged (NOT proved), 1 failed, 3 unknown, 1 timed out, 1 runtime-checked, 1 assumed (requires), 1 assumed (instance discharge), 2 skipped out of 11 obligation(s)");
        assert_eq!(original.notes[0],
            "counted over the rows this function publishes: native typed-TrustIr lowering did not complete, and its unproved rows were collapsed into one `assumption:native-lowering` row (skipped, NOT proved); the notes below are the per-obligation results from before that collapse");
        assert!(original.notes[2].contains("discharged CONDITIONALLY"));
        assert_eq!(original.notes[3], "original named invariant premise");
        rows.proved += 1;
        rows.unknown -= 1;
        let candidate = facts.render(rows, &[2]).unwrap();
        assert!(candidate.summary.contains("2 conditionally discharged (NOT proved)"));
        assert!(candidate.summary.ends_with("out of 11 obligation(s)"));
        assert_eq!(&candidate.notes[..4], &original.notes[..4]);
        assert!(!candidate.notes.iter().any(|s| s.contains("kernel-certified")));
        let empty = HumanFacts { rows: Vec::new(), conditional_on_coroutine_premise: false, disclosures: Vec::new() };
        assert!(empty.render(rows, &[]).is_none(), "original empty-results behavior");
    }
}
