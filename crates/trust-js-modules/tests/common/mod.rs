// Shared test harness: a concrete `Host` (TestHost) over a virtual, content-
// addressed module map keyed by name, plus a compact `ModuleSource` describing
// one module's records + observable body markers. This is what the M2 interp
// plugs in, in miniature — the parser (`parse`), the resolver (`resolve` over the
// virtual map), the binding store (`initialize_environment`), the evaluator
// (`execute_module`), and — for top-level await — the reactor seam
// (`start_async_module` + the FIFO async-job queue the test drains, standing in
// for the reactor's microtask queue).
//
// The host logs a console.log-equivalent marker when a body runs, so the ordered
// `log` is exactly the observable evaluation trace the ordering-oracle compares
// against Node. Everything host-internal (the evaluated-set for cross-module TDZ,
// the source map) is membership-only; nothing observable rides hash order.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

#![allow(dead_code)]

use indexmap::IndexMap;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;
use trust_js_modules::{
    Host, ImportBinding, ImportEntry, IndirectExport, LocalExport, ModuleGraph, ParseError,
    ParsedModule, ResolveError, StarExport,
};

/// The state of a top-level capability (the promise `Evaluate()` returns).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TlaState {
    Pending,
    Resolved,
    Rejected(String),
}

/// A shared top-level-capability handle (the host's opaque `TopLevelCapability`).
pub type Cap = Rc<RefCell<TlaState>>;

/// One module's static records + observable behaviour. Built once and handed to
/// both the record model (`to_parsed`) and Node (the ordering test generates JS
/// from the same definition), so there is a single source of truth per module.
#[derive(Debug, Clone, Default)]
pub struct ModuleSource {
    /// `[[RequestedModules]]` — specifiers in source order (deduped by the parser).
    pub requested: Vec<String>,
    pub imports: Vec<ImportEntry>,
    pub local_exports: Vec<LocalExport>,
    pub indirect_exports: Vec<IndirectExport>,
    pub star_exports: Vec<StarExport>,
    pub has_tla: bool,
    /// Markers the body logs before any top-level await (or the whole body, when
    /// synchronous).
    pub markers: Vec<String>,
    /// Markers the body logs after its top-level await resumes (async only).
    pub post_markers: Vec<String>,
    /// Names of modules whose *live* (TDZ-sensitive) bindings this body reads at
    /// evaluation time; reading one before its providing body ran throws.
    pub access: Vec<String>,
    /// If set, the (synchronous) body throws this error value.
    pub throws: Option<String>,
    /// If set, the top-level await REJECTS with this value instead of fulfilling.
    pub async_rejects: Option<String>,
}

impl ModuleSource {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn to_parsed(&self) -> ParsedModule {
        ParsedModule {
            requested_modules: self.requested.clone(),
            import_entries: self.imports.clone(),
            local_exports: self.local_exports.clone(),
            indirect_exports: self.indirect_exports.clone(),
            star_exports: self.star_exports.clone(),
            has_top_level_await: self.has_tla,
        }
    }
}

/// A pending top-level-await settlement — the reactor job that will resume a
/// module's continuation and settle its implicit promise.
struct AsyncJob {
    key: String,
    post_markers: Vec<String>,
    rejects: Option<String>,
}

/// The concrete host.
pub struct TestHost {
    /// The virtual content-addressed map: module name → source.
    pub sources: IndexMap<String, ModuleSource>,
    /// The ordered console.log-equivalent markers — the observable trace.
    pub log: Vec<String>,
    /// The order `initialize_environment` was called (the link visit order).
    pub link_order: Vec<String>,
    /// The order bodies were started (`execute_module` / `start_async_module`).
    pub run_order: Vec<String>,
    /// Bodies whose (pre-await) portion has run — for cross-module TDZ.
    evaluated: Vec<String>,
    /// The FIFO reactor-job queue for pending top-level awaits.
    pending_async: VecDeque<AsyncJob>,
    /// Every top-level capability minted, for inspection.
    pub caps: Vec<Cap>,
}

impl TestHost {
    pub fn new() -> Self {
        Self {
            sources: IndexMap::new(),
            log: Vec::new(),
            link_order: Vec::new(),
            run_order: Vec::new(),
            evaluated: Vec::new(),
            pending_async: VecDeque::new(),
            caps: Vec::new(),
        }
    }

    /// Register a module source under `name`.
    pub fn insert(&mut self, name: &str, source: ModuleSource) {
        self.sources.insert(name.to_string(), source);
    }

    /// Whether any pending async settlements remain.
    pub fn has_pending_async(&self) -> bool {
        !self.pending_async.is_empty()
    }

    fn tdz_check(&self, key: &str) -> Result<(), String> {
        if let Some(src) = self.sources.get(key) {
            for a in &src.access {
                if !self.evaluated.iter().any(|e| e == a) {
                    return Err(format!("ReferenceError: cannot access {a} before initialization"));
                }
            }
        }
        Ok(())
    }
}

impl Default for TestHost {
    fn default() -> Self {
        Self::new()
    }
}

/// Normalise a specifier (`"./b.mjs"`, `"b.mjs"`, `"b"`) to a module name.
fn normalize(specifier: &str) -> String {
    let s = specifier.strip_prefix("./").unwrap_or(specifier);
    let s = s.strip_suffix(".mjs").or_else(|| s.strip_suffix(".js")).unwrap_or(s);
    s.to_string()
}

impl Host for TestHost {
    type Key = String;
    type Error = String;
    type TopLevelCapability = Cap;

    fn resolve(&mut self, _referrer: &String, specifier: &str) -> Result<String, ResolveError> {
        let key = normalize(specifier);
        if self.sources.contains_key(&key) {
            Ok(key)
        } else {
            Err(ResolveError::new(specifier, "no such module in the virtual map"))
        }
    }

    fn parse(&mut self, key: &String) -> Result<ParsedModule, ParseError> {
        match self.sources.get(key) {
            Some(src) => Ok(src.to_parsed()),
            None => Err(ParseError::new(key, "no source registered")),
        }
    }

    fn initialize_environment(&mut self, key: &String, _bindings: &[ImportBinding<String>]) {
        self.link_order.push(key.clone());
    }

    fn new_top_level_capability(&mut self) -> Cap {
        let cap = Rc::new(RefCell::new(TlaState::Pending));
        self.caps.push(cap.clone());
        cap
    }

    fn settle_top_level(&mut self, cap: &Cap, result: Result<(), String>) {
        *cap.borrow_mut() = match result {
            Ok(()) => TlaState::Resolved,
            Err(e) => TlaState::Rejected(e),
        };
    }

    fn execute_module(&mut self, key: &String) -> Result<(), String> {
        self.run_order.push(key.clone());
        self.tdz_check(key)?;
        let src = self.sources.get(key).expect("known module").clone();
        for m in &src.markers {
            self.log.push(m.clone());
        }
        self.evaluated.push(key.clone());
        match src.throws {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    fn start_async_module(&mut self, key: &String) {
        self.run_order.push(key.clone());
        let src = self.sources.get(key).expect("known module").clone();
        // The pre-await portion runs synchronously now.
        if let Err(e) = self.tdz_check(key) {
            // A pre-await throw rejects immediately — modelled as a reject job.
            self.pending_async.push_back(AsyncJob {
                key: key.clone(),
                post_markers: Vec::new(),
                rejects: Some(e),
            });
            return;
        }
        for m in &src.markers {
            self.log.push(m.clone());
        }
        self.evaluated.push(key.clone());
        self.pending_async.push_back(AsyncJob {
            key: key.clone(),
            post_markers: src.post_markers.clone(),
            rejects: src.async_rejects.clone(),
        });
    }
}

/// Drive the mock reactor: pop pending top-level-await settlements FIFO (the
/// microtask order), log each continuation's post-await markers, then hand the
/// fulfillment/rejection back to the graph — which may start newly-available
/// async ancestors, enqueueing more jobs.
pub fn drive_async(graph: &mut ModuleGraph<TestHost>, host: &mut TestHost) {
    while let Some(job) = host.pending_async.pop_front() {
        let id = graph.module_id(&job.key).expect("started module is loaded");
        match job.rejects {
            // A rejected top-level await skips the post-await continuation.
            Some(e) => graph.async_module_execution_rejected(host, id, e),
            None => {
                for m in &job.post_markers {
                    host.log.push(m.clone());
                }
                graph.async_module_execution_fulfilled(host, id);
            }
        }
    }
}

/// Load + link + evaluate `entry`, then drain any pending top-level awaits.
/// Returns the entry's top-level capability. Panics on a load/link failure (use
/// the phase methods directly to assert those).
pub fn run(host: &mut TestHost, entry: &str) -> (ModuleGraph<TestHost>, Cap) {
    let mut graph = ModuleGraph::new();
    let id = graph.load(host, &entry.to_string()).expect("load");
    graph.link(host, id).expect("link");
    let cap = graph.evaluate(host, id);
    drive_async(&mut graph, host);
    (graph, cap)
}

// ---------------------------------------------------------------------------
// ModuleSource builders — concise construction for the unit tests.
// ---------------------------------------------------------------------------

/// A module that just logs its own name (synchronous), depending on `deps`
/// (side-effect imports, in source order).
pub fn logger(name: &str, deps: &[&str]) -> ModuleSource {
    ModuleSource {
        requested: deps.iter().map(|d| d.to_string()).collect(),
        markers: vec![name.to_string()],
        ..ModuleSource::new()
    }
}

/// A module that logs its name, awaits, then logs `"<name>$"` (top-level await),
/// depending on `deps`.
pub fn async_logger(name: &str, deps: &[&str]) -> ModuleSource {
    ModuleSource {
        requested: deps.iter().map(|d| d.to_string()).collect(),
        has_tla: true,
        markers: vec![name.to_string()],
        post_markers: vec![format!("{name}$")],
        ..ModuleSource::new()
    }
}

/// A named import entry.
pub fn import_named(from: &str, name: &str, local: &str) -> ImportEntry {
    ImportEntry {
        module_request: from.to_string(),
        import_name: trust_js_modules::ImportName::Named(name.to_string()),
        local_name: local.to_string(),
    }
}

/// A namespace import entry (`import * as local from "from"`).
pub fn import_ns(from: &str, local: &str) -> ImportEntry {
    ImportEntry {
        module_request: from.to_string(),
        import_name: trust_js_modules::ImportName::Namespace,
        local_name: local.to_string(),
    }
}

/// A local export (`export const name = ...` / `export { local as name }`).
pub fn export_local(name: &str, local: &str) -> LocalExport {
    LocalExport { export_name: name.to_string(), local_name: local.to_string() }
}

/// A named re-export (`export { name as as_name } from "from"`).
pub fn reexport_named(from: &str, name: &str, as_name: &str) -> IndirectExport {
    IndirectExport {
        export_name: as_name.to_string(),
        module_request: from.to_string(),
        import_name: trust_js_modules::ReExportName::Named(name.to_string()),
    }
}

/// A star re-export (`export * from "from"`).
pub fn reexport_star(from: &str) -> StarExport {
    StarExport { module_request: from.to_string() }
}

/// A namespace re-export (`export * as as_name from "from"`).
pub fn reexport_ns(from: &str, as_name: &str) -> IndirectExport {
    IndirectExport {
        export_name: as_name.to_string(),
        module_request: from.to_string(),
        import_name: trust_js_modules::ReExportName::All,
    }
}
