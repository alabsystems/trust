//! Observe actual Lean checking at the post-typeck verification seam without
//! consulting producer rows. The shared transcript separately records resolver
//! checks; those use different inventories and fresh kernel sessions.
//! This is not an erased-runtime or reachable-body census.
//! A footer covers only the inventoried island checks; consumers must also
//! require the actual compiler exit status and retain every disclosed gap.

use rustc_middle::ty::TyCtxt;
use rustc_session::{Session, trust_lean_census as transcript};
use rustc_span::{FileName, SourceFileHash, SourceFileHashAlgorithm, Span};
use serde_json::{Value, json};

pub(crate) use crate::trust_lean_census_order::CheckPhase;
use crate::trust_lean_census_order::IslandCheckOrder;

#[derive(Default)]
struct CensusState {
    order: IslandCheckOrder,
}

fn sha256(bytes: &[u8]) -> String {
    SourceFileHash::new_in_memory(SourceFileHashAlgorithm::Sha256, bytes)
        .to_string()
        .strip_prefix("sha256=")
        .expect("SHA-256 has an algorithm prefix")
        .to_owned()
}

fn require<T>(sess: &Session, result: Result<T, String>) -> T {
    result.unwrap_or_else(|error| sess.dcx().fatal(format!("Lean island census: {error}")))
}

/// Called before parsing, before either observed kernel session exists.
pub fn prepare(sess: &Session, compiler_version: &str) {
    transcript::prepare(sess, compiler_version);
}

/// Enumerate actual HIR islands, including cfg/expansion/module resolution,
/// before checks at this verification seam. Resolver root-fragment kernel
/// checks/minting and earlier analysis already ran; their rejected populations
/// are not recoverable from HIR. The parser-carried text is bound separately
/// from the exact text eventually consumed by each observed check.
pub(crate) fn inventory(tcx: TyCtxt<'_>) {
    let sess = tcx.sess;
    if sess.opts.unstable_opts.trust_lean_census.is_none() {
        return;
    }
    require(sess, transcript::begin_hir(sess));
    let mut islands = Vec::new();
    for item_id in tcx.hir_crate_items(()).free_items() {
        if tcx.def_kind(item_id.owner_id) != rustc_hir::def::DefKind::GlobalAsm {
            continue;
        }
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::CleanIsland { content_span, text, .. } = item.kind else {
            continue;
        };
        let text = text.as_str();
        islands.push((
            content_span,
            json!({
                "span_lo": content_span.lo().0,
                "span_hi": content_span.hi().0,
                "def_path_hash": format!("{:?}", tcx.def_path_hash(item.owner_id.to_def_id())),
                "parser_text_sha256": sha256(text.as_bytes()),
                "parser_text_bytes": text.len(),
            }),
        ));
    }
    islands.sort_by_key(|(span, _)| (span.lo(), span.hi()));
    let spans = islands.iter().map(|(span, _)| (span.lo().0, span.hi().0)).collect();
    let rows: Vec<_> = islands
        .into_iter()
        .enumerate()
        .map(|(id, (_, mut row))| {
            row["island"] = json!(id);
            row
        })
        .collect();
    require(
        sess,
        sess.with_trust_compiler_state::<CensusState, _>(|state| {
            state.order.inventory(spans)?;
            transcript::record(sess, json!({"event": "inventory", "islands": rows}))?;
            Ok(())
        }),
    );
}

/// Observe the existing admission transition (the walk's post-walk mint and,
/// since TG3, the kernel-only lane's mint), not a new kernel admission path.
/// Its generated constants are explicitly not yet inventoried.
pub(crate) fn program_admissions_boundary(sess: &Session) {
    if sess.opts.unstable_opts.trust_lean_census.is_none() {
        return;
    }
    require(
        sess,
        sess.with_trust_compiler_state::<CensusState, _>(|state| {
            state.order.admissions_boundary()?;
            transcript::record(
                sess,
                json!({
                    "event": "program_admissions_boundary",
                    "program_admission_population": "unmeasured",
                    "environment_mutation_between_checks": "not-a-complete-payload-census",
                }),
            )?;
            Ok(())
        }),
    );
}

/// Trust (LEAN-CENSUS-IMPORT-BATCH-1): does the independently captured kernel
/// roster describe the check this phase actually ran? Every HIR check is
/// header-first. The pre-walk prefix is one module batch with no import
/// recovery. The deferred suffix is TG14's single import batch
/// (`check_import_islands_with_census`): it excludes refused units
/// transactionally, names them by their original unit, keeps every original
/// source and checks the survivors together, and has no module outcome. A
/// refused unit is attributed only to a rejected batch. Whether a rejection
/// kept the session's taint is the reader's check (`lean_island_census.py`).
fn roster_matches_phase(roster: &Value, units: usize, phase: CheckPhase, rejected: bool) -> bool {
    let import_batch = !matches!(phase, CheckPhase::HeaderFirst);
    let recovery = &roster["import_recovery"];
    let recovery_matches = if import_batch {
        let refused: Option<Vec<u64>> = recovery["refused_units"]
            .as_array()
            .and_then(|refused| refused.iter().map(Value::as_u64).collect());
        refused.is_some_and(|refused| {
            refused.windows(2).all(|pair| pair[0] < pair[1])
                && refused.last().is_none_or(|&last| last < units as u64)
                && (refused.is_empty() || rejected)
        }) && recovery["all_original_sources_retained"] == true
            && recovery["survivors_checked_together"] == true
            && recovery.as_object().is_some_and(|fields| fields.len() == 3)
    } else {
        recovery.is_null()
    };
    let wrapper_metadata =
        roster["source_declaration_metadata"] == "unavailable-from-import-wrapper";
    roster["check_mode"] == "header-first-batch"
        && roster["registration_semantics"] == "transactional-module"
        && roster["check_rejected"] == rejected
        && wrapper_metadata == import_batch
        && recovery_matches
}

/// Bind the exact consumed source to an independently captured kernel roster.
/// Does not replace, retry, reorder or grant authority to a language check.
pub(crate) fn checked(
    sess: &Session,
    sources: &[(Span, &str)],
    phase: CheckPhase,
    rejected: bool,
    roster: &Value,
) {
    if sess.opts.unstable_opts.trust_lean_census.is_none() {
        return;
    }
    require(
        sess,
        sess.with_trust_compiler_state::<CensusState, _>(|state| {
            if !roster_matches_phase(roster, sources.len(), phase, rejected) {
                return Err("kernel roster check mode/outcome mismatch".into());
            }
            let mut inputs = Vec::new();
            for (unit, (_, text)) in sources.iter().enumerate() {
                let input =
                    json!({"unit": unit, "bytes": text.len(), "sha256": sha256(text.as_bytes())});
                if roster["inputs"].get(unit) != Some(&input) {
                    return Err(
                        "kernel roster does not bind the exact consumed island bytes".into()
                    );
                }
                inputs.push(input);
            }
            if roster["inputs"].as_array().map(Vec::len) != Some(inputs.len()) {
                return Err("extra or missing kernel roster input".into());
            }
            let positions: Vec<_> =
                sources.iter().map(|(span, _)| (span.lo().0, span.hi().0)).collect();
            let ids = state.order.check(
                &positions,
                phase,
                sess.trust_verification_enabled(),
                rejected,
            )?;
            transcript::record(
                sess,
                json!({
                    "event": "check",
                    "mode": match phase {
                        CheckPhase::HeaderFirst => "pre-walk-header-first",
                        CheckPhase::AfterProgramAdmissions => "post-admission-import-batch",
                        CheckPhase::VerificationDisabled => "verification-disabled-import-batch",
                    },
                    "islands": ids,
                    "rejected": rejected,
                    "consumed_inputs": inputs,
                    "kernel_roster": roster,
                }),
            )?;
            Ok(())
        }),
    );
}

/// Analysis completion only. A later codegen/link failure still invalidates
/// the run; the process exit status is part of every consumer's contract.
pub fn complete(tcx: TyCtxt<'_>) {
    let sess = tcx.sess;
    if sess.opts.unstable_opts.trust_lean_census.is_none()
        || sess.dcx().has_errors_or_delayed_bugs().is_some()
    {
        return;
    }
    let mut sources = Vec::new();
    let working_directory = require(sess, transcript::working_directory(sess));
    let absolute = |path: &std::path::Path| -> Result<String, String> {
        let path =
            if path.is_absolute() { path.to_path_buf() } else { working_directory.join(path) };
        path.to_str().map(str::to_owned).ok_or("non-UTF-8 input label".into())
    };
    for file in sess.source_map().files().iter() {
        if file.src.is_none() {
            continue;
        }
        let FileName::Real(real) = &file.name else { continue };
        let path = require(sess, real.local_path().ok_or("loaded source has no local path".into()));
        let path = require(sess, absolute(path));
        let hash = require(
            sess,
            file.checksum_hash
                .filter(|hash| hash.kind == SourceFileHashAlgorithm::Sha256)
                .ok_or_else(|| format!("loaded source has no SHA-256: {path}")),
        );
        // A binary include may be represented by an empty text surrogate in
        // SourceMap. Never label this a hash of arbitrary raw file contents.
        sources.push(json!({
            "file": path,
            "source_map_checksum_sha256": hash.to_string().strip_prefix("sha256=").unwrap(),
            "raw_auxiliary_input_bytes": "unmeasured",
        }));
    }
    sources.sort_by(|a, b| a["file"].as_str().cmp(&b["file"].as_str()));
    let mut tracked_files = require(
        sess,
        sess.file_depinfo
            .borrow()
            .iter()
            .map(|path| absolute(std::path::Path::new(path.as_str())))
            .collect::<Result<Vec<_>, _>>(),
    );
    tracked_files.sort();
    let mut environment_names: Vec<_> =
        sess.env_depinfo.borrow().iter().map(|(name, _value)| name.to_string()).collect();
    environment_names.sort();
    require(sess, sess.with_trust_compiler_state::<CensusState, _>(|state| {
        let count = state.order.completion_count()?;
        transcript::finish(sess, json!({
            "event": "complete",
            "status": "island-check-events-complete",
            "island_count": count,
            "loaded_sources": sources,
            "source_map_checksum_scope": "compiler source-map checksum; binary inputs may have text surrogates, not raw-byte attestation",
            "other_inputs": {"tracked_files": tracked_files, "environment_variable_names": environment_names, "raw_file_bytes": "unmeasured", "environment_values": "unmeasured", "general_build_and_proc_macro_io": "unmeasured"},
            "runtime_body_universe": "unmeasured",
            "denominator_status": "denominator_unverified",
            "unmeasured": ["pre-root-parser-rejected-populations", "resolver-rust-callee-declaration-payloads", "program-admission-payloads", "preexisting-payload-mutations", "lazy-import-closure", "runtime-erasure-specialization-helpers", "general-proc-macro-and-build-io"],
        }))?;
        Ok(())
    }));
}

#[cfg(test)]
mod tests;
