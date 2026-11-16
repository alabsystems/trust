// Trust: diagnostic transport shared by the resolver and post-typeck observer.
//! One invocation-owned, create-only Lean checking transcript. The resolver
//! and HIR observers use different kernel sessions and separate inventories.
//! This transport grants no admission, producer or runtime-body authority.

use std::fs::{File, OpenOptions};
use std::io::Write;
use std::path::PathBuf;

use rustc_span::{SourceFileHash, SourceFileHashAlgorithm, Span};
use serde_json::{Value, json};

use crate::Session;

// Trust (LEAN-CENSUS-IMPORT-BATCH-1): v3 records TG14's deferred suffix as ONE
// header-first import batch and the program-admission boundary in both lanes.
// v2 keeps its one meaning (one sequential island per suffix check, no
// boundary with verification off); a v2 reader refuses every v3 record.
const SCHEMA: &str = "trust.lean.compiler-island-census/v3";

#[derive(Default)]
struct CensusState {
    output: Option<File>,
    working_directory: Option<PathBuf>,
    digests: Vec<String>,
    resolver_sources: Option<Vec<(u32, u32, usize, String)>>,
    resolver_prefix: usize,
    resolver_checked: bool,
    resolver_rejected: bool,
    hir_started: bool,
    finished: bool,
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

fn write(state: &mut CensusState, mut event: Value) -> Result<(), String> {
    if state.finished {
        return Err("event after completion".into());
    }
    event["schema"] = json!(SCHEMA);
    event["sequence"] = json!(state.digests.len());
    event["previous_record_sha256"] = json!(state.digests.last());
    let mut bytes = serde_json::to_vec(&event).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let output = state.output.as_mut().ok_or("missing create-only begin record")?;
    output.write_all(&bytes).map_err(|error| error.to_string())?;
    output.flush().map_err(|error| error.to_string())?;
    state.digests.push(sha256(&bytes));
    Ok(())
}

/// Called before parsing. A failed parse cannot reuse an earlier complete file.
pub fn prepare(sess: &Session, compiler_version: &str) {
    let Some(path) = &sess.opts.unstable_opts.trust_lean_census else { return };
    if sess.opts.unstable_opts.checksum_hash_algorithm != Some(SourceFileHashAlgorithm::Sha256) {
        sess.dcx().fatal("-Ztrust-lean-census requires -Zchecksum-hash-algorithm=sha256");
    }
    let working_directory =
        require(sess, std::env::current_dir().map_err(|error| error.to_string()));
    let input = require(sess, sess.io.input.opt_path().ok_or("file input required".into()));
    let input =
        if input.is_absolute() { input.to_path_buf() } else { working_directory.join(input) };
    let input = require(sess, input.to_str().ok_or("non-UTF-8 input path".into()));
    let output = require(
        sess,
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .map_err(|error| format!("cannot create NEW output {}: {error}", path.display())),
    );
    require(
        sess,
        sess.with_trust_compiler_state::<CensusState, _>(|state| {
            if state.output.is_some() {
                return Err("duplicate preparation".into());
            }
            state.output = Some(output);
            state.working_directory = Some(working_directory);
            write(
                state,
                json!({
                    "event": "begin",
                    "input": input,
                    "compiler_version": compiler_version,
                    "target": sess.opts.target_triple.to_string(),
                    "edition": sess.edition().to_string(),
                    "verification_enabled": sess.trust_verification_enabled(),
                    "direct_lowering": sess.trust_ir_lower_enabled(),
                    "authority": "diagnostic-only",
                    "scope": "actual-root-fragment-and-hir-island-checks",
                    "runtime_body_universe": "unmeasured",
                    "denominator_status": "denominator_unverified",
                }),
            )
        }),
    );
}

/// Inventory the actual sorted root fragment before the mint's kernel check.
/// The prefix is the existing checker partition; the suffix remains unattempted
/// here. These ordinals are NOT HIR identities or an admitted body population.
pub fn resolver_inventory(sess: &Session, sources: &[(Span, &str, bool)], prefix: usize) {
    if sess.opts.unstable_opts.trust_lean_census.is_none() {
        return;
    }
    require(
        sess,
        sess.with_trust_compiler_state::<CensusState, _>(|state| {
            if state.resolver_sources.is_some() || state.hir_started || prefix > sources.len() {
                return Err("duplicate/misplaced resolver inventory or invalid prefix".into());
            }
            let rows: Vec<_> = sources
                .iter()
                .enumerate()
                .map(|(island, (span, text, reported))| {
                    json!({
                        "island": island,
                        "span_lo": span.lo().0,
                        "span_hi": span.hi().0,
                        "parser_text_sha256": sha256(text.as_bytes()),
                        "parser_text_bytes": text.len(),
                        "reported_at_parse": reported,
                    })
                })
                .collect();
            write(
                state,
                json!({
                    "event": "resolver_inventory",
                    "islands": rows,
                    "check_islands": (0..prefix).collect::<Vec<_>>(),
                }),
            )?;
            state.resolver_sources = Some(
                sources
                    .iter()
                    .map(|(span, text, _)| {
                        (span.lo().0, span.hi().0, text.len(), sha256(text.as_bytes()))
                    })
                    .collect(),
            );
            state.resolver_prefix = prefix;
            Ok(())
        }),
    );
}

/// Record the mint's actual existing batch BEFORE reporting its rejection.
/// No planner/mint rows participate, and this fresh session does not continue
/// the later HIR observer's environment or taint state.
pub fn resolver_checked(sess: &Session, sources: &[(Span, &str)], rejected: bool, roster: &Value) {
    if sess.opts.unstable_opts.trust_lean_census.is_none() {
        return;
    }
    require(
        sess,
        sess.with_trust_compiler_state::<CensusState, _>(|state| {
            let expected =
                state.resolver_sources.as_ref().ok_or("resolver check without inventory")?;
            if state.hir_started
                || state.resolver_checked
                || sources.is_empty()
                || sources.len() != state.resolver_prefix
            {
                return Err("missing, duplicate or misplaced resolver check".into());
            }
            if roster["check_mode"] != "header-first-batch" || roster["check_rejected"] != rejected
            {
                return Err("resolver roster check mode/outcome mismatch".into());
            }
            let mut inputs = Vec::new();
            for (unit, (span, text)) in sources.iter().enumerate() {
                let actual = (span.lo().0, span.hi().0, text.len(), sha256(text.as_bytes()));
                if expected.get(unit) != Some(&actual) {
                    return Err("resolver consumed source differs from inventory".into());
                }
                let input = json!({"unit": unit, "bytes": text.len(), "sha256": actual.3});
                if roster["inputs"].get(unit) != Some(&input) {
                    return Err("resolver roster does not bind consumed source".into());
                }
                inputs.push(input);
            }
            if roster["inputs"].as_array().map(Vec::len) != Some(inputs.len()) {
                return Err("extra or missing resolver roster input".into());
            }
            write(
                state,
                json!({
                    "event": "resolver_check",
                    "mode": "root-fragment-header-first",
                    "islands": (0..sources.len()).collect::<Vec<_>>(),
                    "rejected": rejected,
                    "consumed_inputs": inputs,
                    "kernel_roster": roster,
                }),
            )?;
            state.resolver_checked = true;
            state.resolver_rejected = rejected;
            Ok(())
        }),
    );
}

/// Keep HIR phase checks in their existing observer, but seal the shared order.
pub fn begin_hir(sess: &Session) -> Result<(), String> {
    sess.with_trust_compiler_state::<CensusState, _>(|state| {
        if state.resolver_sources.is_none()
            || state.hir_started
            || (state.resolver_prefix != 0 && !state.resolver_checked)
        {
            return Err("HIR observation without the expected resolver observations".into());
        }
        state.hir_started = true;
        Ok(())
    })
}

/// Append one already-validated HIR observation to the shared exact-byte chain.
pub fn record(sess: &Session, event: Value) -> Result<(), String> {
    sess.with_trust_compiler_state::<CensusState, _>(|state| write(state, event))
}

pub fn working_directory(sess: &Session) -> Result<PathBuf, String> {
    sess.with_trust_compiler_state::<CensusState, _>(|state| {
        state.working_directory.clone().ok_or("missing invocation working directory".into())
    })
}

/// Called only after existing HIR completion checks and compiler diagnostics.
/// A later codegen/link failure still invalidates the process, not this prefix.
pub fn finish(sess: &Session, event: Value) -> Result<(), String> {
    sess.with_trust_compiler_state::<CensusState, _>(|state| {
        if !state.hir_started
            || state.resolver_rejected
            || (state.resolver_prefix != 0 && !state.resolver_checked)
        {
            return Err("completion without successful resolver/HIR observations".into());
        }
        write(state, event)?;
        state
            .output
            .as_mut()
            .ok_or("missing output at completion")?
            .sync_all()
            .map_err(|error| error.to_string())?;
        state.finished = true;
        Ok(())
    })
}
