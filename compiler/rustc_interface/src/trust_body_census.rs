//! Diagnostic, source-independent-of-producer HIR census. This is not a G1
//! reachable-instance census or a proof artifact. A new output file receives
//! begin / HIR snapshot / complete records; an interrupted compilation cannot
//! supply the final record. Consumers must also check the process exit status.

use std::fs::{File, OpenOptions};
use std::io::Write;
use std::path::Path;

use rustc_hir::definitions::DefPathData;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_span::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_span::{FileName, SourceFileHash, SourceFileHashAlgorithm};
use serde_json::{Value, json};

// Trust: v2 adds compiler-independent identity fields to every body row
// (`crate_name`, `def_path_no_crate`, `source`); v1 rows had only the
// crate-disambiguated `def` and `def_path_hash`, which pair across two
// compilers only by printed path.
const SCHEMA: &str = "trust.rust.hir-body-census.v2";

// Trust: only explicit call-observation requests change the wire schema.
fn schema(sess: &Session) -> &'static str {
    if sess.opts.unstable_opts.trust_body_census_calls {
        "trust.rust.hir-body-census.v3"
    } else {
        SCHEMA
    }
}

#[derive(Default)]
struct CensusState {
    output: Option<File>,
    snapshot: Option<(usize, usize, String)>,
}

fn sha256(bytes: &[u8]) -> String {
    SourceFileHash::new_in_memory(SourceFileHashAlgorithm::Sha256, bytes)
        .to_string()
        .strip_prefix("sha256=")
        .expect("SHA-256 hash has its algorithm prefix")
        .to_owned()
}

// Trust: also used for locators in the opt-in raw-span diagnostics.
pub(super) fn absolute_path(path: &Path) -> Result<String, String> {
    let path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().map_err(|error| error.to_string())?.join(path)
    };
    path.to_str().map(str::to_owned).ok_or_else(|| "non-UTF-8 census path".to_owned())
}

fn write_record(output: &mut File, record: &Value) -> Result<String, String> {
    let mut bytes = serde_json::to_vec(record).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    output.write_all(&bytes).map_err(|error| error.to_string())?;
    output.flush().map_err(|error| error.to_string())?;
    Ok(sha256(&bytes))
}

fn require<T>(sess: &Session, result: Result<T, String>) -> T {
    result.unwrap_or_else(|error| sess.dcx().fatal(format!("Rust HIR census: {error}")))
}

/// Create-only, before parsing. Never replace an existing census or source file.
pub(crate) fn prepare(sess: &Session) {
    // Trust: reject a dangling request before parsing or opening an output.
    if sess.opts.unstable_opts.trust_body_census_calls
        && sess.opts.unstable_opts.trust_body_census.is_none()
    {
        sess.dcx().fatal("-Ztrust-body-census-calls requires -Ztrust-body-census");
    }
    let Some(path) = &sess.opts.unstable_opts.trust_body_census else { return };
    if sess.opts.unstable_opts.checksum_hash_algorithm != Some(SourceFileHashAlgorithm::Sha256) {
        sess.dcx().fatal("-Ztrust-body-census requires -Zchecksum-hash-algorithm=sha256");
    }
    let input = require(
        sess,
        sess.io
            .input
            .opt_path()
            .ok_or_else(|| "census requires a file input".to_owned())
            .and_then(absolute_path),
    );
    let mut output = require(
        sess,
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .map_err(|error| format!("cannot create NEW output {}: {error}", path.display())),
    );
    require(
        sess,
        write_record(
            &mut output,
            &json!({
                "schema": schema(sess),
                "event": "begin",
                "input": input,
                "compiler_version": crate::util::rustc_version_str().unwrap_or("unknown"),
                "target": sess.opts.target_triple.to_string(),
                "edition": sess.edition().to_string(),
                "crate_types": sess.opts.crate_types.iter().map(|kind| format!("{kind:?}")).collect::<Vec<_>>(),
                "direct_lowering": sess.trust_ir_lower_enabled(),
                "verification_enabled": sess.trust_verification_enabled(),
                "scope": "local-hir-body-owners-after-typeck",
                "generated_scope": "local-typeck-synthetic-coroutine-bodies",
                "reachable_instances": "unmeasured",
            }),
        ),
    );
    sess.with_trust_compiler_state::<CensusState, _>(|state| {
        state.output = Some(output);
        state.snapshot = None;
    });
}

/// Loaded local sources, using rustc's hash of the ORIGINAL, pre-normalized
/// bytes. Extern-crate source maps are not local inputs to this HIR roster.
fn loaded_sources(sess: &Session) -> Result<Vec<Value>, String> {
    let mut sources = Vec::new();
    for source in sess.source_map().files().iter() {
        if source.src.is_none() {
            continue;
        }
        let FileName::Real(real) = &source.name else { continue };
        let path = real.local_path().ok_or_else(|| "local source has no local path".to_owned())?;
        let hash = source
            .checksum_hash
            .filter(|hash| hash.kind == SourceFileHashAlgorithm::Sha256)
            .ok_or_else(|| format!("missing loaded SHA-256 for {}", path.display()))?;
        sources.push(json!({
            "file": absolute_path(path)?,
            "sha256": hash.to_string().strip_prefix("sha256=").unwrap(),
        }));
    }
    sources.sort_by(|left, right| left["file"].as_str().cmp(&right["file"].as_str()));
    Ok(sources)
}

/// Trust: the owning source of a body, by content. `file` is only a locator;
/// `sha256` is rustc's checksum of the ORIGINAL bytes (the same value
/// `loaded_sources` reports), and `lo`/`hi` are `[line (1-based), char column
/// (0-based)]` of the macro-callsite-resolved `def_span`. Every field is null
/// when the span does not lie in one local, SHA-256-checksummed file: that is
/// disclosed as unmeasured, never filled from another file.
fn source_identity(tcx: TyCtxt<'_>, def: DefId) -> Value {
    let span = tcx.def_span(def).source_callsite();
    let unmeasured = json!({ "file": null, "sha256": null, "lo": null, "hi": null });
    if span.is_dummy() {
        return unmeasured;
    }
    let source_map = tcx.sess.source_map();
    let lo = source_map.lookup_char_pos(span.lo());
    let hi = source_map.lookup_char_pos(span.hi());
    if lo.file.start_pos != hi.file.start_pos {
        return unmeasured;
    }
    let FileName::Real(real) = &lo.file.name else { return unmeasured };
    let Some(file) = real.local_path().and_then(|path| absolute_path(path).ok()) else {
        return unmeasured;
    };
    let Some(hash) =
        lo.file.checksum_hash.filter(|hash| hash.kind == SourceFileHashAlgorithm::Sha256)
    else {
        return unmeasured;
    };
    json!({
        "file": file,
        "sha256": hash.to_string().strip_prefix("sha256=").unwrap(),
        "lo": [lo.line, lo.col.0],
        "hi": [hi.line, hi.col.0],
    })
}

fn body_rows(tcx: TyCtxt<'_>, owners: impl Iterator<Item = LocalDefId>) -> Vec<Value> {
    // Trust: the crate NAME, not its StableCrateId. Measured 2026-09-29: the
    // `local_hash` half of `def_path_hash` is NOT crate-independent (the crate
    // root's local hash is seeded with the StableCrateId, rustc_hir
    // definitions.rs), and it differed for 18/18 bodies of one unchanged
    // source between two compilers. So it is deliberately not emitted.
    let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
    let mut bodies = Vec::new();
    for owner in owners {
        let def = owner.to_def_id();
        // Exactly the spelling used by existing differential events, including
        // the crate disambiguator. Stable identity is retained separately.
        let path = tcx.def_path_debug_str(def);
        let kind = if path.contains("{closure") {
            "closure"
        } else if path.contains("{constant#") {
            "constant"
        } else {
            "named"
        };
        bodies.push(json!({
            "def": path,
            "kind": kind,
            "def_kind": format!("{:?}", tcx.def_kind(def)),
            "def_index": def.index.as_u32(),
            "def_path_hash": format!("{:?}", tcx.def_path_hash(def)),
            // Trust: v2 identity, independent of the StableCrateId.
            "crate_name": crate_name.as_str(),
            "def_path_no_crate": tcx.def_path(def).to_string_no_crate_verbose(),
            "source": source_identity(tcx, def),
        }));
    }
    bodies.sort_by_key(|body| body["def_index"].as_u64());
    bodies
}

pub(crate) fn snapshot(tcx: TyCtxt<'_>) {
    let sess = tcx.sess;
    if sess.opts.unstable_opts.trust_body_census.is_none() {
        return;
    }
    let bodies = body_rows(tcx, tcx.hir_body_owners());
    // Synthetic by-move coroutine bodies have no HIR body. The cached HIR
    // item list cannot enumerate them. Definitions were frozen immediately
    // before this callback, after check_crate forced their creation. Do NOT
    // use iter_local_def_id here: it ensures analysis and would query-cycle.
    let generated = tcx
        .untracked()
        .definitions
        .read()
        .enumerated_keys_and_path_hashes()
        .filter(|(_, key, _)| {
            matches!(key.disambiguated_data.data, DefPathData::SyntheticCoroutineBody)
        })
        .map(|(local_def_index, _, _)| LocalDefId { local_def_index })
        .collect::<Vec<_>>();
    let generated_bodies = body_rows(tcx, generated.into_iter());
    let count = bodies.len();
    let generated_count = generated_bodies.len();
    let mut record = json!({
        "schema": schema(sess),
        "event": "hir_snapshot",
        "body_count": count,
        "bodies": bodies,
        "generated_body_count": generated_count,
        "generated_bodies": generated_bodies,
        "sources": require(sess, loaded_sources(sess)),
    });
    // Trust: preserve the default v2 record shape and its existing consumers.
    if sess.opts.unstable_opts.trust_body_census_calls {
        record["call_observations"] = super::trust_hir_calls::snapshot(tcx);
    }
    let result = sess.with_trust_compiler_state::<CensusState, _>(|state| {
        if state.snapshot.is_some() {
            return Err("duplicate HIR snapshot".to_owned());
        }
        let output =
            state.output.as_mut().ok_or_else(|| "missing census begin record".to_owned())?;
        let digest = write_record(output, &record)?;
        state.snapshot = Some((count, generated_count, digest));
        Ok(())
    });
    require(sess, result);
}

pub(crate) fn complete(tcx: TyCtxt<'_>) {
    let sess = tcx.sess;
    if sess.opts.unstable_opts.trust_body_census.is_none()
        || sess.dcx().has_errors_or_delayed_bugs().is_some()
    {
        return;
    }
    let sources = require(sess, loaded_sources(sess));
    // include_bytes!/include_str! and proc-macro tracked_path may bypass text
    // source loading. In particular a non-UTF8 binary has an EMPTY surrogate in
    // SourceMap; its text hash is not the hash of the bytes consumed by the
    // macro. Disclose these paths as unmeasured, never re-read them later and
    // pretend that was a consumption-time hash. General proc-macro/build I/O
    // is not captured by rustc's tracked-path/environment interfaces either.
    let mut tracked_files = sess
        .file_depinfo
        .borrow()
        .iter()
        .map(|path| absolute_path(Path::new(path.as_str())))
        .collect::<Result<Vec<_>, _>>();
    if let Ok(paths) = &mut tracked_files {
        paths.sort();
    }
    let mut environment_variables =
        sess.env_depinfo.borrow().iter().map(|(name, _value)| name.to_string()).collect::<Vec<_>>();
    environment_variables.sort();
    let other_inputs = json!({
        "tracked_files": require(sess, tracked_files),
        "environment_variables": environment_variables,
        "proc_macro_io": "unmeasured",
        "build_environment": "unmeasured",
        "external_dependency_closure": "unmeasured",
    });
    let result = sess.with_trust_compiler_state::<CensusState, _>(|state| {
        let (count, generated_count, digest) = state
            .snapshot
            .take()
            .ok_or_else(|| "cannot complete without HIR snapshot".to_owned())?;
        let mut output = state
            .output
            .take()
            .ok_or_else(|| "cannot complete without census begin record".to_owned())?;
        write_record(
            &mut output,
            &json!({
                "schema": schema(sess),
                "event": "complete",
                "status": "complete",
                "body_count": count,
                "generated_body_count": generated_count,
                "snapshot_sha256": digest,
                "sources": sources,
                "other_inputs": other_inputs,
            }),
        )?;
        output.sync_all().map_err(|error| error.to_string())
    });
    require(sess, result);
}
