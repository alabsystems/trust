// EngineHead: the front-end-neutral oracle-head abstraction (case → trace |
// sound refusal | harness fault), the three M0 heads: NodeHead / BunHead
// (spawn the embedded trust-js-trace driver; RAW lane spawns the pristine
// file with an exit-status-only projection) and SemHead (in-process
// trust-js-sem with cached include sources), and the M1 D3 fourth head:
// TrustJsHead (in-process trust-js-interp, the faithful tier, mirroring
// SemHead's cache shape). Spawning is fail-closed: any
// timeout, cap overflow, missing sentinel, or driver-internal fault is a
// HarnessError counted in tool_failures, never a silent skip.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::HashMap;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};

use trust_js_trace::{
    extract_trace, Completion, ObservableTrace, ThrownProjection, SCHEMA_VERSION,
    TRACE_SENTINEL,
};


pub const STDOUT_CAP: usize = 512 * 1024 * 1024;
pub const STDERR_CAP: usize = 8 * 1024 * 1024;

/// A mandated run mode (RUN-MODE CONTRACT).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RunMode {
    Bare,
    Strict,
    Raw,
    /// The module goal: the case is evaluated ONCE as an ES module from its real
    /// corpus location (always strict — no bare/strict split). The driver
    /// imports the pristine file so its relative imports resolve.
    Module,
}

impl RunMode {
    pub fn as_str(self) -> &'static str {
        match self {
            RunMode::Bare => "bare",
            RunMode::Strict => "strict",
            RunMode::Raw => "raw",
            RunMode::Module => "module",
        }
    }

    pub fn parse(s: &str) -> Option<RunMode> {
        match s {
            "bare" => Some(RunMode::Bare),
            "strict" => Some(RunMode::Strict),
            "raw" => Some(RunMode::Raw),
            "module" => Some(RunMode::Module),
            _ => None,
        }
    }
}

/// One fully assembled runnable case. Front-end-neutral: a head sees only the
/// pristine body, the ordered include payload paths, the mode, and a timeout.
#[derive(Debug, Clone)]
pub struct AssembledCase {
    /// Corpus-relative path (reporting identity).
    pub rel_path: String,
    /// The pristine on-disk file (the RAW lane spawns exactly this).
    pub source_path: PathBuf,
    /// Pristine file content (drivers receive it verbatim; mode prefixing is
    /// the driver's/head's job).
    pub body: String,
    /// Absolute include paths, in mandated order. Empty for RAW.
    pub includes: Vec<PathBuf>,
    pub mode: RunMode,
    /// `flags: [async]` — the module-goal driver settles real dynamic-import
    /// jobs on the real event loop for these so the async $DONE is observed.
    pub is_async: bool,
    pub timeout: Duration,
}

/// The head verdict for one run.
#[derive(Debug, Clone)]
pub enum HeadResult {
    Trace(ObservableTrace),
    /// A sound refusal (semantics head only): counted, never a divergence.
    NoCoverage(String),
    /// The harness/engine failed to produce a comparable trace. Fail-closed:
    /// counted in tool_failures.
    HarnessError(String),
}

/// A front-end-neutral oracle head.
pub trait EngineHead {
    fn name(&self) -> &'static str;
    fn run(&self, case: &AssembledCase) -> HeadResult;
}

// ---------------------------------------------------------------------------
// Process spawning
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub struct SpawnOutput {
    pub success: bool,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub timed_out: bool,
    pub stdout_capped: bool,
}

fn drain_reader<R: Read>(mut r: R, cap: usize) -> (Vec<u8>, bool) {
    let mut buf = Vec::new();
    let mut chunk = [0u8; 1 << 16];
    let mut capped = false;
    loop {
        match r.read(&mut chunk) {
            Ok(0) => break,
            Ok(n) => {
                if buf.len() < cap {
                    let take = (cap - buf.len()).min(n);
                    buf.extend_from_slice(&chunk[..take]);
                    if take < n {
                        capped = true;
                    }
                } else {
                    capped = true; // keep draining so the child never blocks
                }
            }
            Err(_) => break,
        }
    }
    (buf, capped)
}

/// Spawn `program args...` with the contract env (TZ=UTC LANG=C LC_ALL=C),
/// piped stdio, full stdout capture (512 MiB cap), and a try_wait + 5 ms
/// poll-loop timeout (kill on expiry).
pub fn spawn_engine(program: &Path, args: &[&Path], timeout: Duration) -> Result<SpawnOutput, String> {
    let mut cmd = Command::new(program);
    for a in args {
        cmd.arg(a);
    }
    let mut child = cmd
        .env("TZ", "UTC")
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("spawn {} failed: {e}", program.display()))?;

    let stdout = child.stdout.take().expect("piped stdout");
    let stderr = child.stderr.take().expect("piped stderr");
    let out_thread = std::thread::spawn(move || drain_reader(stdout, STDOUT_CAP));
    let err_thread = std::thread::spawn(move || drain_reader(stderr, STDERR_CAP));

    let deadline = Instant::now() + timeout;
    let mut timed_out = false;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {
                if Instant::now() >= deadline {
                    timed_out = true;
                    let _ = child.kill();
                    let status = child.wait().map_err(|e| format!("wait after kill: {e}"))?;
                    break status;
                }
                std::thread::sleep(Duration::from_millis(5));
            }
            Err(e) => return Err(format!("try_wait: {e}")),
        }
    };
    let (stdout, stdout_capped) = out_thread.join().map_err(|_| "stdout reader panicked")?;
    let (stderr, _) = err_thread.join().map_err(|_| "stderr reader panicked")?;
    Ok(SpawnOutput { success: status.success(), stdout, stderr, timed_out, stdout_capped })
}

/// The RAW lane's exit-status-only projection, synthesized symmetrically on
/// both heads: exit 0 => Normal (no witness); nonzero => Throw with no
/// identity. Calibration ruling (2026-07-21): stderr error-name scraping is
/// engine-asymmetric (Bun prints lowercase "error:" without the constructor
/// name), so the raw lane claims exactly what both engines expose — the exit
/// status — and nothing more.
pub fn raw_projection(out: &SpawnOutput) -> ObservableTrace {
    let completion = if out.success {
        Completion::Normal { v: None }
    } else {
        Completion::Throw {
            v: ThrownProjection::Error { ctor: None, name: None, ctor_name: None },
            phase: None,
        }
    };
    ObservableTrace {
        schema: SCHEMA_VERSION.to_string(),
        caps: None,
        events: vec![],
        completion,
    }
}

/// The LAST sentinel line of captured stdout, verbatim (selftest determinism
/// compares these raw bytes).
pub fn last_sentinel_line(stdout: &[u8]) -> Option<String> {
    let text = String::from_utf8_lossy(stdout);
    text.lines().rev().find(|l| l.trim_start().starts_with(TRACE_SENTINEL)).map(|l| l.to_string())
}

// ---------------------------------------------------------------------------
// Driver-spawning heads (Node, Bun)
// ---------------------------------------------------------------------------

/// Case manifest JSON consumed by the embedded trace driver.
#[derive(serde::Serialize)]
struct DriverManifest<'a> {
    includes: Vec<String>,
    source: String,
    mode: &'a str,
    kind: &'a str,
    /// `flags: [async]` — the module-goal driver settles real dynamic-import
    /// jobs on the real event loop for these (see trace_driver.mjs
    /// settleModuleAsync). Serialized as the manifest `async` field.
    #[serde(rename = "async")]
    is_async: bool,
}

/// Shared implementation for the two engine-process heads. Owns a reusable
/// per-worker slot directory (body.js + manifest.json overwritten per case)
/// to avoid per-case temp churn.
#[derive(Debug, Clone)]
pub struct ProcessHead {
    name: &'static str,
    engine: PathBuf,
    driver: PathBuf,
    slot_dir: PathBuf,
    /// Engine CLI arguments injected BEFORE the driver script (e.g. Node's
    /// `--experimental-transform-types`, needed so Node transpiles — not merely
    /// strips — the imported `.ts` for the non-erasable transform corpus).
    /// Empty for the erasable/js262 lanes.
    prefix_args: Vec<PathBuf>,
}

impl ProcessHead {
    pub fn new(
        name: &'static str,
        engine: PathBuf,
        driver: PathBuf,
        slot_dir: PathBuf,
    ) -> std::io::Result<Self> {
        Self::new_with_prefix(name, engine, driver, slot_dir, Vec::new())
    }

    /// Like [`ProcessHead::new`] but injects `prefix_args` before the driver on
    /// every engine spawn.
    pub fn new_with_prefix(
        name: &'static str,
        engine: PathBuf,
        driver: PathBuf,
        slot_dir: PathBuf,
        prefix_args: Vec<PathBuf>,
    ) -> std::io::Result<Self> {
        std::fs::create_dir_all(&slot_dir)?;
        Ok(Self { name, engine, driver, slot_dir, prefix_args })
    }

    /// Run the driver over an assembled non-raw case, returning raw spawn
    /// output (selftest needs the sentinel bytes; `run` parses them).
    pub fn run_driver_raw(&self, case: &AssembledCase) -> Result<SpawnOutput, String> {
        debug_assert!(case.mode != RunMode::Raw);
        let manifest_path = self.slot_dir.join("manifest.json");
        // Module goal: the driver imports the REAL corpus test file (so its
        // relative/self/_FIXTURE imports resolve) — there is no body.js slot,
        // the pristine on-disk path IS the module source. Script goal keeps the
        // per-worker body.js slot (mode-prefixing is the driver's job).
        let (source, kind) = if case.mode == RunMode::Module {
            (case.source_path.display().to_string(), "module")
        } else {
            let body_path = self.slot_dir.join("body.js");
            std::fs::write(&body_path, &case.body)
                .map_err(|e| format!("write {}: {e}", body_path.display()))?;
            (body_path.display().to_string(), "script")
        };
        let manifest = DriverManifest {
            includes: case.includes.iter().map(|p| p.display().to_string()).collect(),
            source,
            mode: case.mode.as_str(),
            kind,
            is_async: case.is_async,
        };
        let manifest_json =
            serde_json::to_string(&manifest).map_err(|e| format!("manifest json: {e}"))?;
        std::fs::write(&manifest_path, manifest_json)
            .map_err(|e| format!("write {}: {e}", manifest_path.display()))?;
        let mut args: Vec<&Path> = self.prefix_args.iter().map(|p| p.as_path()).collect();
        args.push(self.driver.as_path());
        args.push(manifest_path.as_path());
        spawn_engine(&self.engine, &args, case.timeout)
    }

    fn run_raw_lane(&self, case: &AssembledCase) -> HeadResult {
        let mut args: Vec<&Path> = self.prefix_args.iter().map(|p| p.as_path()).collect();
        args.push(case.source_path.as_path());
        match spawn_engine(&self.engine, &args, case.timeout) {
            Ok(out) if out.timed_out => HeadResult::HarnessError("timeout".to_string()),
            Ok(out) => HeadResult::Trace(raw_projection(&out)),
            Err(e) => HeadResult::HarnessError(e),
        }
    }
}

impl EngineHead for ProcessHead {
    fn name(&self) -> &'static str {
        self.name
    }

    fn run(&self, case: &AssembledCase) -> HeadResult {
        if case.mode == RunMode::Raw {
            return self.run_raw_lane(case);
        }
        let out = match self.run_driver_raw(case) {
            Ok(out) => out,
            Err(e) => return HeadResult::HarnessError(e),
        };
        if out.timed_out {
            return HeadResult::HarnessError("timeout".to_string());
        }
        if out.stdout_capped {
            return HeadResult::HarnessError("stdout exceeded 512 MiB cap".to_string());
        }
        match extract_trace(&out.stdout) {
            Ok(trace) => match &trace.completion {
                Completion::HarnessIncludeError { v } => HeadResult::HarnessError(format!(
                    "harness include failed to evaluate: {}",
                    serde_json::to_string(v).unwrap_or_default()
                )),
                Completion::DriverError { v } => HeadResult::HarnessError(format!(
                    "driver-internal error: {}",
                    serde_json::to_string(v).unwrap_or_default()
                )),
                _ => HeadResult::Trace(trace),
            },
            Err(e) => {
                let stderr = String::from_utf8_lossy(&out.stderr);
                let mut start = stderr.len().saturating_sub(300);
                while !stderr.is_char_boundary(start) {
                    start += 1;
                }
                HeadResult::HarnessError(format!(
                    "trace extraction failed: {e} (stderr tail: {:?})",
                    &stderr[start..]
                ))
            }
        }
    }
}

/// The Node oracle head.
pub struct NodeHead(pub ProcessHead);

/// The Bun oracle head.
pub struct BunHead(pub ProcessHead);

impl NodeHead {
    pub fn new(engine: PathBuf, driver: PathBuf, slot_dir: PathBuf) -> std::io::Result<Self> {
        Ok(Self(ProcessHead::new("node", engine, driver, slot_dir)?))
    }

    /// A Node head that passes `flags` (e.g. `--experimental-transform-types`)
    /// before the driver — the oracle for the non-erasable transform corpus,
    /// where Node must transpile the imported `.ts` rather than only strip it.
    pub fn new_with_flags(
        engine: PathBuf,
        driver: PathBuf,
        slot_dir: PathBuf,
        flags: Vec<String>,
    ) -> std::io::Result<Self> {
        let prefix = flags.into_iter().map(PathBuf::from).collect();
        Ok(Self(ProcessHead::new_with_prefix("node", engine, driver, slot_dir, prefix)?))
    }
}

impl BunHead {
    pub fn new(engine: PathBuf, driver: PathBuf, slot_dir: PathBuf) -> std::io::Result<Self> {
        Ok(Self(ProcessHead::new("bun", engine, driver, slot_dir)?))
    }
}

impl EngineHead for NodeHead {
    fn name(&self) -> &'static str {
        self.0.name()
    }
    fn run(&self, case: &AssembledCase) -> HeadResult {
        self.0.run(case)
    }
}

impl EngineHead for BunHead {
    fn name(&self) -> &'static str {
        self.0.name()
    }
    fn run(&self, case: &AssembledCase) -> HeadResult {
        self.0.run(case)
    }
}

/// Write the embedded trace driver once; returns its path.
pub fn write_driver(dir: &Path) -> std::io::Result<PathBuf> {
    std::fs::create_dir_all(dir)?;
    let path = dir.join("trace_driver.mjs");
    std::fs::write(&path, trust_js_trace::TRACE_DRIVER_SOURCE)?;
    Ok(path)
}

// ---------------------------------------------------------------------------
// SemHead — trust-js-sem, in-process
// ---------------------------------------------------------------------------

/// The independent-semantics head. Include SOURCES are read once and cached
/// (shared across workers).
pub struct SemHead {
    include_cache: Arc<HashMap<PathBuf, String>>,
}

impl SemHead {
    pub fn new(include_cache: Arc<HashMap<PathBuf, String>>) -> Self {
        Self { include_cache }
    }

    /// Read and cache the union of include sources for a case set.
    pub fn build_cache<'a>(
        paths: impl Iterator<Item = &'a PathBuf>,
    ) -> Arc<HashMap<PathBuf, String>> {
        let mut cache = HashMap::new();
        for p in paths {
            if !cache.contains_key(p) {
                if let Ok(src) = std::fs::read_to_string(p) {
                    cache.insert(p.clone(), src);
                }
                // A read failure stays out of the cache; the affected run
                // becomes a HarnessError below (fail-closed, audited).
            }
        }
        Arc::new(cache)
    }
}

impl EngineHead for SemHead {
    fn name(&self) -> &'static str {
        "sem"
    }

    fn run(&self, case: &AssembledCase) -> HeadResult {
        if case.mode == RunMode::Module {
            // The in-house semantics head does not execute module goal yet: a
            // SOUND refusal, never a guessed module trace (zero-wrong-traces).
            return HeadResult::NoCoverage("module execution (out of slice)".to_string());
        }
        if case.mode == RunMode::Raw {
            return HeadResult::NoCoverage(
                "raw-flag case: the exit-status-only projection is not modeled by the sem head"
                    .to_string(),
            );
        }
        let mut includes: Vec<&str> = Vec::with_capacity(case.includes.len());
        for p in &case.includes {
            match self.include_cache.get(p) {
                Some(src) => includes.push(src.as_str()),
                None => {
                    return HeadResult::HarnessError(format!(
                        "sem include source unavailable for {}: {}",
                        case.rel_path,
                        p.display()
                    ));
                }
            }
        }
        // The sem head receives the same mode-prefixed body the driver builds
        // for manifest mode == "strict".
        let body = if case.mode == RunMode::Strict {
            format!("\"use strict\";\n{}", case.body)
        } else {
            case.body.clone()
        };
        match trust_js_sem::evaluate_case_opts(&includes, &body, false) {
            trust_js_sem::SemOutcome::Trace(t) => HeadResult::Trace(t),
            trust_js_sem::SemOutcome::NoCoverage { reason } => HeadResult::NoCoverage(reason),
        }
    }
}

// ---------------------------------------------------------------------------
// TrustJsHead — trust-js-interp (the faithful tier), in-process
// ---------------------------------------------------------------------------

/// The fourth head: the faithful-tier interpreter (trust-js-interp),
/// in-process, mirroring SemHead's include-source cache shape. Each case runs
/// on the dedicated wide-stack thread machinery `evaluate_case` already
/// provides internally (totality-protected: panics surface as sound
/// refusals), so it is called directly. The completion witness is OFF — the
/// interp default — matching the calibrated corpus lanes.
pub struct TrustJsHead {
    include_cache: Arc<HashMap<PathBuf, String>>,
}

impl TrustJsHead {
    pub fn new(include_cache: Arc<HashMap<PathBuf, String>>) -> Self {
        Self { include_cache }
    }
}

impl EngineHead for TrustJsHead {
    fn name(&self) -> &'static str {
        "trustjs"
    }

    fn run(&self, case: &AssembledCase) -> HeadResult {
        if case.mode == RunMode::Raw {
            return HeadResult::NoCoverage("raw lane not applicable".to_string());
        }
        let mut includes: Vec<&str> = Vec::with_capacity(case.includes.len());
        for p in &case.includes {
            match self.include_cache.get(p) {
                Some(src) => includes.push(src.as_str()),
                None => {
                    return HeadResult::HarnessError(format!(
                        "trustjs include source unavailable for {}: {}",
                        case.rel_path,
                        p.display()
                    ));
                }
            }
        }
        // Module goal: the faithful tier links a SOUND, conservative subset of
        // sibling-importing graphs (increment 2b-part-3). The head owns disk
        // access + the relative-path policy via a resolver closure; the interp
        // owns the graph algorithm + the sound-subset guards. A parse/early
        // error still covers the negative:parse module tests (SyntaxError,
        // matching Node); import-free modules take the exact single-module path.
        if case.mode == RunMode::Module {
            let resolver = module_sibling_resolver();
            let main_key = canonical_key(&case.source_path);
            return match trust_js_interp::evaluate_module_graph(
                &includes, &main_key, &case.body, resolver,
            ) {
                trust_js_interp::InterpOutcome::Trace(t) => HeadResult::Trace(t),
                trust_js_interp::InterpOutcome::NoCoverage { reason } => {
                    HeadResult::NoCoverage(reason)
                }
            };
        }
        // evaluate_case prepends `"use strict";\n` itself when asked, exactly
        // as the driver's strict mode does — the pristine body goes through.
        let strict = case.mode == RunMode::Strict;
        match trust_js_interp::evaluate_case(&includes, &case.body, strict) {
            trust_js_interp::InterpOutcome::Trace(t) => HeadResult::Trace(t),
            trust_js_interp::InterpOutcome::NoCoverage { reason } => {
                HeadResult::NoCoverage(reason)
            }
        }
    }
}

/// The canonical on-disk key for a module file: the resolved absolute path
/// (symlinks + `.`/`..` collapsed) so self-import / cycle identity is robust.
/// Best-effort — an un-canonicalizable path falls back to its lexical form.
fn canonical_key(path: &Path) -> String {
    std::fs::canonicalize(path)
        .unwrap_or_else(|_| path.to_path_buf())
        .to_string_lossy()
        .into_owned()
}

/// The head's sibling-module resolver for the module-graph linker: relative
/// specifiers ONLY (`./x.js`), resolved against the importing module's
/// directory, read from disk, keyed by canonical path. Refuses (sound
/// `NoCoverage` upstream) any bare specifier, any `..` parent traversal, or an
/// unreadable/missing sibling — never a guessed graph. The interp enforces the
/// remaining subset (acyclicity, bounds, self-import, named-only shapes).
fn module_sibling_resolver() -> trust_js_interp::ModuleResolver {
    Box::new(|importer_key: &str, spec: &str| -> Result<(String, String), String> {
        let Some(rel) = spec.strip_prefix("./") else {
            return Err(format!("non-relative import specifier `{spec}`"));
        };
        if spec.contains("..") {
            return Err(format!("parent-relative import specifier `{spec}`"));
        }
        if rel.is_empty() || rel.starts_with('/') {
            return Err(format!("degenerate import specifier `{spec}`"));
        }
        let importer_dir = Path::new(importer_key)
            .parent()
            .ok_or_else(|| "importing module has no directory".to_string())?;
        let target = importer_dir.join(rel);
        let source = std::fs::read_to_string(&target)
            .map_err(|e| format!("unreadable sibling `{}`: {e}", target.display()))?;
        let key = std::fs::canonicalize(&target)
            .map(|p| p.to_string_lossy().into_owned())
            .unwrap_or_else(|_| target.to_string_lossy().into_owned());
        Ok((key, source))
    })
}

// ---------------------------------------------------------------------------
// TrustTsHead — trust-ts-strip → trust-js-interp (the TrustTS front-end), in-process
// ---------------------------------------------------------------------------

/// The TrustTS head: the erasable-TypeScript front-end judged end-to-end. It
/// runs `trust_ts_strip::strip` (fail-closed TS→JS eraser) over the case body,
/// then feeds the stripped JavaScript to `trust_js_interp::evaluate_module` —
/// the MODULE goal, because the Node/Bun oracle runs the `.ts` natively by
/// `import()`-ing it (type-strip + module evaluation). An erasable, import-free
/// program's stripped JS evaluates identically under the module goal (the
/// import-free lowering handles it; anything it cannot is a sound refusal).
///
/// Zero-wrong-traces: a strip refusal is a sound `NoCoverage` ("ts: <reason>");
/// the interp's own refusals pass through unchanged; a covered trace is claimed
/// only when the interp faithfully reproduces it — never a guessed trace.
/// Mirrors `TrustJsHead`'s include-source cache shape.
pub struct TrustTsHead {
    include_cache: Arc<HashMap<PathBuf, String>>,
    /// When set, lower non-erasable enum/namespace via
    /// `trust_ts_strip::transform` (the transform tier); otherwise pure
    /// `trust_ts_strip::strip` (erasure only). Either way the result is judged
    /// under the module goal against the engine oracles.
    transform: bool,
}

impl TrustTsHead {
    pub fn new(include_cache: Arc<HashMap<PathBuf, String>>) -> Self {
        Self { include_cache, transform: false }
    }

    /// The transform-tier head: erases types AND lowers enums/namespaces.
    pub fn new_transform(include_cache: Arc<HashMap<PathBuf, String>>) -> Self {
        Self { include_cache, transform: true }
    }
}

impl EngineHead for TrustTsHead {
    fn name(&self) -> &'static str {
        "trustts"
    }

    fn run(&self, case: &AssembledCase) -> HeadResult {
        if case.mode == RunMode::Raw {
            return HeadResult::NoCoverage("raw lane not applicable".to_string());
        }
        let mut includes: Vec<&str> = Vec::with_capacity(case.includes.len());
        for p in &case.includes {
            match self.include_cache.get(p) {
                Some(src) => includes.push(src.as_str()),
                None => {
                    return HeadResult::HarnessError(format!(
                        "trustts include source unavailable for {}: {}",
                        case.rel_path,
                        p.display()
                    ));
                }
            }
        }
        // Fail-closed TS→JS lowering. A refusal is sound (never a wrong trace).
        // Erasure-only (`strip`) or the transform tier (`transform`, which also
        // lowers enum/namespace) per this head's configuration.
        let outcome = if self.transform {
            trust_ts_strip::transform(&case.body)
        } else {
            trust_ts_strip::strip(&case.body)
        };
        let js = match outcome {
            trust_ts_strip::StripOutcome::Js(js) => js,
            trust_ts_strip::StripOutcome::Refused(reason) => {
                return HeadResult::NoCoverage(format!("ts: {reason}"));
            }
        };
        // The oracle imports the `.ts` as an ES module, so the stripped JS is
        // judged under the module goal exactly like TrustJsHead's module path.
        match trust_js_interp::evaluate_module(&includes, &js) {
            trust_js_interp::InterpOutcome::Trace(t) => HeadResult::Trace(t),
            trust_js_interp::InterpOutcome::NoCoverage { reason } => {
                HeadResult::NoCoverage(reason)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_projection_shapes() {
        let ok = SpawnOutput {
            success: true,
            stdout: vec![],
            stderr: vec![],
            timed_out: false,
            stdout_capped: false,
        };
        let t = raw_projection(&ok);
        assert_eq!(t.schema, SCHEMA_VERSION);
        assert!(t.caps.is_none());
        assert!(t.events.is_empty());
        assert!(matches!(t.completion, Completion::Normal { v: None }));

        let boom = SpawnOutput {
            success: false,
            stdout: vec![],
            stderr: b"file.js:1\nSyntaxError: Unexpected token".to_vec(), // name is NOT scraped
            timed_out: false,
            stdout_capped: false,
        };
        match raw_projection(&boom).completion {
            Completion::Throw { v: ThrownProjection::Error { ctor, name, ctor_name }, phase } => {
                assert_eq!(ctor, None);
                assert_eq!(name, None); // exit-status-only: stderr scraping is engine-asymmetric
                assert_eq!(ctor_name, None);
                assert_eq!(phase, None);
            }
            other => panic!("unexpected completion {other:?}"),
        }
    }

    #[test]
    fn sentinel_line_extraction() {
        let stdout = b"noise\n__TRUST_JS_TRACE_V1__{\"a\":1}\nmore\n  __TRUST_JS_TRACE_V1__{\"b\":2}\n";
        assert_eq!(
            last_sentinel_line(stdout).as_deref(),
            Some("  __TRUST_JS_TRACE_V1__{\"b\":2}")
        );
        assert_eq!(last_sentinel_line(b"nothing here"), None);
    }

    #[test]
    fn sem_head_refuses_raw() {
        let head = SemHead::new(Arc::new(HashMap::new()));
        let case = AssembledCase {
            rel_path: "test/x.js".into(),
            source_path: PathBuf::from("/nonexistent"),
            body: "1;".into(),
            includes: vec![],
            mode: RunMode::Raw,
            is_async: false,
            timeout: Duration::from_secs(1),
        };
        assert!(matches!(head.run(&case), HeadResult::NoCoverage(_)));
    }

    #[test]
    fn in_house_heads_module_goal_sound() {
        let mk = |body: &str| AssembledCase {
            rel_path: "test/language/module-code/m.js".into(),
            source_path: PathBuf::from("/nonexistent"),
            body: body.into(),
            includes: vec![],
            mode: RunMode::Module,
            is_async: false,
            timeout: Duration::from_secs(1),
        };
        // sem still soundly refuses all module goal.
        match SemHead::new(Arc::new(HashMap::new())).run(&mk("export const x = 1;")) {
            HeadResult::NoCoverage(r) => assert_eq!(r, "module execution (out of slice)"),
            other => panic!("sem: expected NoCoverage, got {other:?}"),
        }
        // trustjs: an IMPORT-FREE module with plain-declaration exports is
        // lowered to a strict script and COVERS (normal completion, no events) —
        // exactly the trace `import()`-ing it yields on a real engine.
        match TrustJsHead::new(Arc::new(HashMap::new())).run(&mk("export const x = 1;")) {
            HeadResult::Trace(t) => {
                assert!(t.events.is_empty(), "expected no events, got {:?}", t.events);
                assert!(
                    matches!(t.completion, Completion::Normal { .. }),
                    "expected normal completion, got {:?}",
                    t.completion
                );
            }
            other => panic!("trustjs import-free module: expected Trace, got {other:?}"),
        }
        // trustjs: a module-only construct (module top-level `this`) is a sound
        // refusal — a strict script cannot reproduce its `undefined` this.
        match TrustJsHead::new(Arc::new(HashMap::new())).run(&mk("this;")) {
            HeadResult::NoCoverage(_) => {}
            other => panic!("trustjs top-level this: expected NoCoverage, got {other:?}"),
        }
        // trustjs: a real `import` still refuses (module loader out of slice).
        match TrustJsHead::new(Arc::new(HashMap::new())).run(&mk("import { x } from './o.js';")) {
            HeadResult::NoCoverage(_) => {}
            other => panic!("trustjs import: expected NoCoverage, got {other:?}"),
        }
        // trustjs: a module PARSE / early error is covered with the SyntaxError
        // throw an engine raises when import()-ing it (matching Node).
        match TrustJsHead::new(Arc::new(HashMap::new())).run(&mk("export const x = 1; export const x = 2;")) {
            HeadResult::Trace(t) => match t.completion {
                Completion::Throw { v: ThrownProjection::Error { ref name, .. }, .. } => {
                    assert_eq!(name.as_deref(), Some("SyntaxError"))
                }
                other => panic!("trustjs dup-export: expected SyntaxError throw, got {other:?}"),
            },
            other => panic!("trustjs dup-export: expected Trace, got {other:?}"),
        }
    }

    #[test]
    fn run_mode_module_string_round_trip() {
        assert_eq!(RunMode::Module.as_str(), "module");
        assert_eq!(RunMode::parse("module"), Some(RunMode::Module));
    }

    fn trustjs_case(body: &str, mode: RunMode) -> AssembledCase {
        AssembledCase {
            rel_path: "test/x.js".into(),
            source_path: PathBuf::from("/nonexistent"),
            body: body.into(),
            includes: vec![],
            mode,
            is_async: false,
            timeout: Duration::from_secs(1),
        }
    }

    #[test]
    fn trustjs_head_refuses_raw_with_contract_reason() {
        let head = TrustJsHead::new(Arc::new(HashMap::new()));
        match head.run(&trustjs_case("1;", RunMode::Raw)) {
            HeadResult::NoCoverage(reason) => assert_eq!(reason, "raw lane not applicable"),
            other => panic!("expected NoCoverage, got {other:?}"),
        }
    }

    #[test]
    fn trustjs_head_traces_and_refuses_in_process() {
        let head = TrustJsHead::new(Arc::new(HashMap::new()));
        // A covered body yields a trace with the witness OFF (interp default).
        match head.run(&trustjs_case("1 + 2;", RunMode::Bare)) {
            HeadResult::Trace(t) => {
                assert!(matches!(t.completion, Completion::Normal { v: None }));
            }
            other => panic!("expected Trace, got {other:?}"),
        }
        // Strict mode is passed through as the interp's strict prefix: a
        // strict-only early error becomes an exact SyntaxError trace.
        match head.run(&trustjs_case("var eval = 1;", RunMode::Strict)) {
            HeadResult::Trace(t) => match t.completion {
                Completion::Throw {
                    v: ThrownProjection::Error { name: Some(n), .. },
                    ..
                } => assert_eq!(n, "SyntaxError"),
                other => panic!("expected SyntaxError throw, got {other:?}"),
            },
            other => panic!("expected Trace, got {other:?}"),
        }
        // Async generators (§27.6) are covered: creating one yields a trace
        // (its body runs on `.next()`).
        match head.run(&trustjs_case(
            "async function* g() { yield 1; } g();",
            RunMode::Bare,
        )) {
            HeadResult::Trace(t) => {
                assert!(matches!(t.completion, Completion::Normal { .. }));
            }
            other => panic!("expected Trace for an async generator, got {other:?}"),
        }
        // The subtle async-generator surfaces stay sound refusals, never guessed
        // traces: `.return()` (AwaitReturn interleaving) and `yield*` delegation.
        assert!(matches!(
            head.run(&trustjs_case(
                "async function* g() { yield 1; } g().return(9);",
                RunMode::Bare
            )),
            HeadResult::NoCoverage(_)
        ));
        // A missing cached include is a fail-closed harness error (mirrors
        // SemHead).
        let mut case = trustjs_case("1;", RunMode::Bare);
        case.includes = vec![PathBuf::from("/nonexistent/assert.js")];
        assert!(matches!(head.run(&case), HeadResult::HarnessError(_)));
    }

    #[test]
    fn trustts_head_strips_and_evaluates() {
        let head = TrustTsHead::new(Arc::new(HashMap::new()));
        // An erasable, import-free TS program strips to plain JS and traces
        // under the module goal (a normal completion, no events).
        let ts = "function add(a: number, b: number): number { return a + b; }\nadd(2, 3);\n";
        match head.run(&trustjs_case(ts, RunMode::Module)) {
            HeadResult::Trace(t) => {
                assert!(matches!(t.completion, Completion::Normal { .. }));
            }
            other => panic!("expected Trace for erasable TS, got {other:?}"),
        }
    }

    #[test]
    fn trustts_head_refuses_non_erasable_with_ts_prefix() {
        let head = TrustTsHead::new(Arc::new(HashMap::new()));
        // A non-erasable construct (enum) is a fail-closed strip refusal,
        // surfaced as a sound NoCoverage tagged "ts: ...".
        match head.run(&trustjs_case("enum E { A, B }\n", RunMode::Module)) {
            HeadResult::NoCoverage(reason) => {
                assert!(reason.starts_with("ts: "), "reason was {reason:?}");
            }
            other => panic!("expected NoCoverage for enum, got {other:?}"),
        }
    }

    #[test]
    fn trustts_head_refuses_raw() {
        let head = TrustTsHead::new(Arc::new(HashMap::new()));
        match head.run(&trustjs_case("const x: number = 1;", RunMode::Raw)) {
            HeadResult::NoCoverage(reason) => assert_eq!(reason, "raw lane not applicable"),
            other => panic!("expected NoCoverage, got {other:?}"),
        }
    }
}
