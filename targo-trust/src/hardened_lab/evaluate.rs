use std::collections::BTreeMap;

use super::claims::{CLAIMS, ClaimSpec};
use super::report::{
    ClaimMatch, ClaimResult, ClaimTranscriptRequirement, ClaimWalkthroughEvidence,
    WalkthroughExecution,
};
use super::terminal::display_path;
use super::validate::{expected_walkthrough_name, key_values_in_walkthrough};
use crate::source_analysis::{StandaloneVc, VcKind};

pub(super) fn evaluate_claims(
    vcs: &[StandaloneVc],
    walkthroughs: &[WalkthroughExecution],
) -> Vec<ClaimResult> {
    let by_kind = vcs.iter().fold(BTreeMap::<VcKind, Vec<&StandaloneVc>>::new(), |mut acc, vc| {
        acc.entry(vc.kind).or_default().push(vc);
        acc
    });
    let walkthroughs_by_bin = walkthroughs
        .iter()
        .map(|walkthrough| (walkthrough.bin.as_str(), walkthrough))
        .collect::<BTreeMap<_, _>>();

    CLAIMS
        .iter()
        .map(|claim| {
            let matches = by_kind
                .get(&claim.kind)
                .into_iter()
                .flatten()
                .filter(|vc| {
                    vc.function == claim.source_example
                        && claim
                            .required_fragment
                            .map_or(true, |fragment| vc.description.contains(fragment))
                })
                .map(|vc| ClaimMatch {
                    function: vc.function.clone(),
                    file: display_path(&vc.file),
                    description: vc.description.clone(),
                })
                .collect::<Vec<_>>();
            let walkthrough_evidence =
                evaluate_claim_walkthrough_evidence(claim, &walkthroughs_by_bin);
            let analyzer_passed = !matches.is_empty();
            let walkthroughs_passed = !walkthrough_evidence.is_empty()
                && walkthrough_evidence.iter().all(|evidence| evidence.passed);
            let passed = analyzer_passed && walkthroughs_passed;

            ClaimResult {
                id: claim.id,
                category: claim.category,
                report_label: claim.report_label,
                title: claim.title,
                kind: claim.kind,
                standalone_binding: standalone_binding_text(claim),
                required_fragment: claim.required_fragment,
                source_example: claim.source_example,
                source_reference: claim.source_reference,
                passed,
                failure_message: (!passed)
                    .then(|| claim_failure_message(claim, analyzer_passed, walkthroughs_passed)),
                matches,
                walkthrough_evidence,
            }
        })
        .collect()
}

fn evaluate_claim_walkthrough_evidence(
    claim: &ClaimSpec,
    walkthroughs_by_bin: &BTreeMap<&str, &WalkthroughExecution>,
) -> Vec<ClaimWalkthroughEvidence> {
    claim
        .walkthrough_evidence
        .iter()
        .map(|spec| match walkthroughs_by_bin.get(spec.bin).copied() {
            Some(walkthrough) => {
                let walkthrough_name = expected_walkthrough_name(spec);
                let requirements = spec
                    .requirements
                    .iter()
                    .map(|requirement| ClaimTranscriptRequirement {
                        key: requirement.key,
                        value: requirement.value,
                        found: key_values_in_walkthrough(
                            &walkthrough.stdout,
                            walkthrough_name,
                            requirement.key,
                        )
                        .iter()
                        .any(|value| *value == requirement.value),
                    })
                    .collect::<Vec<_>>();
                let missing = requirements
                    .iter()
                    .filter(|requirement| !requirement.found)
                    .map(|requirement| format!("{}={}", requirement.key, requirement.value))
                    .collect::<Vec<_>>();
                let passed = walkthrough.success && missing.is_empty();
                let failure_message = if passed {
                    None
                } else if !walkthrough.success {
                    Some(format!(
                        "walkthrough `{}` did not pass for claim `{}`: {}",
                        spec.bin, claim.id, walkthrough.status
                    ))
                } else {
                    Some(format!(
                        "walkthrough `{}` for claim `{}` is missing transcript requirement(s): {}",
                        spec.bin,
                        claim.id,
                        missing.join(", ")
                    ))
                };
                ClaimWalkthroughEvidence { bin: spec.bin, requirements, passed, failure_message }
            }
            None => ClaimWalkthroughEvidence {
                bin: spec.bin,
                requirements: spec
                    .requirements
                    .iter()
                    .map(|requirement| ClaimTranscriptRequirement {
                        key: requirement.key,
                        value: requirement.value,
                        found: false,
                    })
                    .collect(),
                passed: false,
                failure_message: Some(format!(
                    "required walkthrough `{}` for claim `{}` was not executed",
                    spec.bin, claim.id
                )),
            },
        })
        .collect()
}

pub(super) fn standalone_binding_text(claim: &ClaimSpec) -> String {
    match claim.required_fragment {
        Some(fragment) => format!(
            "{:?} finding bound to `{}` with description containing `{fragment}`",
            claim.kind, claim.source_example
        ),
        None => format!("{:?} finding bound to `{}`", claim.kind, claim.source_example),
    }
}

pub(super) fn claim_failure_message(
    claim: &ClaimSpec,
    analyzer_passed: bool,
    walkthroughs_passed: bool,
) -> String {
    if !analyzer_passed {
        return match claim.id {
            "unsafe-operation" => concat!(
            "expected unsafe-operation inventory evidence bound to `unsafe_ffi_boundary` ",
            "with a trusted-wrapper description; extern FFI declaration evidence alone does not ",
            "satisfy this claim"
            )
            .to_string(),
            "ffi-boundary" => concat!(
            "expected extern FFI declaration evidence bound to the module-level extern block ",
            "with an extern-boundary description; unsafe block/trusted-wrapper evidence alone ",
            "does not satisfy this claim"
            )
            .to_string(),
            _ => format!("expected analyzer evidence matching {}", standalone_binding_text(claim)),
        };
    }

    if !walkthroughs_passed {
        return format!(
            "expected runnable walkthrough transcript evidence matching claim `{}`",
            claim.id
        );
    }

    format!("claim `{}` did not satisfy hardened-lab evidence requirements", claim.id)
}

pub(super) fn is_hardened_kind(kind: VcKind) -> bool {
    matches!(
        kind,
        VcKind::HardenedRawPathApi
            | VcKind::HardenedPathIdentity
            | VcKind::HardenedPermissionChange
            | VcKind::HardenedPermissionCreate
            | VcKind::HardenedPermissionWindow
            | VcKind::HardenedByteLoss
            | VcKind::HardenedUtf8Boundary
            | VcKind::HardenedErrorDiscard
            | VcKind::HardenedPanic
            | VcKind::HardenedTrustBoundary
            | VcKind::HardenedTrustDomainOrder
            | VcKind::HardenedCompatibility
            | VcKind::HardenedProcessSemantics
            | VcKind::HardenedUnsafeOperation
            | VcKind::HardenedFfiBoundary
    )
}

pub(super) fn hardened_finding_label(kind: VcKind) -> Option<&'static str> {
    match kind {
        VcKind::HardenedUnsafeOperation => Some("unsafe_operation"),
        VcKind::HardenedFfiBoundary => Some("ffi_boundary"),
        _ => None,
    }
}
