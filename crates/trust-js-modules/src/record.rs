// The Cyclic Module Record and its `[[Status]]` state machine.
//
// A dense record per loaded module, indexed by a `ModuleId` newtype (a dense Vec
// slot — never a hash key), so nothing observable depends on hash iteration
// order. The fields mirror §16.2.1.5's Cyclic Module Record fields one-for-one:
// the loading map, the three export-entry lists, the DFS bookkeeping
// (`[[DFSIndex]]`/`[[DFSAncestorIndex]]`), and the top-level-await state
// (`[[PendingAsyncDependencies]]`, `[[AsyncEvaluation]]`, `[[AsyncParentModules]]`,
// `[[CycleRoot]]`, `[[EvaluationError]]`, `[[TopLevelCapability]]`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::host::{Host, ImportEntry, IndirectExport, LocalExport, StarExport};
use indexmap::IndexMap;

/// A module identity within one graph: a dense index into the graph's record
/// table. Stable for the graph's lifetime; handed to and from the consumer
/// opaquely. NOT the host key (which is content-addressed) — the boundary between
/// the two is the graph's `index_of` table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleId(pub(crate) usize);

impl ModuleId {
    /// The raw dense index (for a consumer that keeps its own parallel table).
    pub fn index(self) -> usize {
        self.0
    }
}

/// A Cyclic Module Record's `[[Status]]` (§16.2.1.5): the linear lifecycle
/// `new → unlinked → linking → linked → evaluating → {evaluating-async} → evaluated`.
/// The graph asserts the spec's status invariants at every transition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    /// Freshly created, loading not yet complete.
    New,
    /// Loaded (record built) but not yet linked.
    Unlinked,
    /// Inside InnerModuleLinking's DFS (on the link stack).
    Linking,
    /// Linked: environment created, bindings resolved, ready to evaluate.
    Linked,
    /// Inside InnerModuleEvaluation's DFS (on the eval stack).
    Evaluating,
    /// Body started but blocked on a top-level await (its own or a dependency's).
    EvaluatingAsync,
    /// Evaluation finished (successfully or with a retained `[[EvaluationError]]`).
    Evaluated,
}

/// One Cyclic Module Record. Generic over the host so it can carry the host key
/// and the opaque top-level capability.
pub(crate) struct CyclicModuleRecord<H: Host> {
    /// `[[HostDefined]]`-ish: the content-addressed key this record was loaded as.
    pub key: H::Key,
    /// `[[Status]]`.
    pub status: Status,

    // ---- static analysis (from ParseModule) ----
    /// `[[RequestedModules]]` — source order.
    pub requested: Vec<String>,
    /// `[[ImportEntries]]`.
    pub imports: Vec<ImportEntry>,
    /// `[[LocalExportEntries]]`.
    pub local_exports: Vec<LocalExport>,
    /// `[[IndirectExportEntries]]`.
    pub indirect_exports: Vec<IndirectExport>,
    /// `[[StarExportEntries]]`.
    pub star_exports: Vec<StarExport>,
    /// `[[HasTLA]]`.
    pub has_tla: bool,

    // ---- loading map ----
    /// `[[LoadedModules]]`: specifier → resolved module. Insertion-ordered so
    /// GetImportedModule and any iteration are deterministic.
    pub loaded: IndexMap<String, ModuleId>,

    // ---- link/eval DFS bookkeeping ----
    /// `[[DFSIndex]]`.
    pub dfs_index: usize,
    /// `[[DFSAncestorIndex]]`.
    pub dfs_ancestor_index: usize,

    // ---- evaluation state ----
    /// `[[EvaluationError]]`: retained abrupt completion value once set.
    pub eval_error: Option<H::Error>,
    /// `[[PendingAsyncDependencies]]`.
    pub pending_async_deps: usize,
    /// `[[AsyncEvaluation]]` (as a Boolean).
    pub async_evaluation: bool,
    /// The ordering rank captured when `[[AsyncEvaluation]]` is set true — the
    /// spec's "the order in which modules have AsyncEvaluation set is
    /// significant" (the ES2025 `[[AsyncEvaluationOrder]]`). Sorts sortedExecList.
    pub async_eval_order: Option<u64>,
    /// `[[AsyncParentModules]]`: modules awaiting this one, in registration order.
    pub async_parents: Vec<ModuleId>,
    /// `[[CycleRoot]]`.
    pub cycle_root: Option<ModuleId>,
    /// `[[TopLevelCapability]]`: the promise `Evaluate()` returned for this module
    /// (only ever set on a cycle root that was an `Evaluate()` entry point).
    pub top_level_capability: Option<H::TopLevelCapability>,

    /// `[[Namespace]]`: the cached module-namespace descriptor (sorted names +
    /// indirections), computed lazily by GetModuleNamespace.
    pub namespace: Option<crate::host::NamespaceDescriptor<H::Key>>,
}

impl<H: Host> CyclicModuleRecord<H> {
    /// Build an `Unlinked` record from a parse result. (Loading has resolved the
    /// key; `loaded` is filled in as requested modules are loaded.)
    pub fn new(key: H::Key, parsed: crate::host::ParsedModule) -> Self {
        Self {
            key,
            status: Status::Unlinked,
            requested: parsed.requested_modules,
            imports: parsed.import_entries,
            local_exports: parsed.local_exports,
            indirect_exports: parsed.indirect_exports,
            star_exports: parsed.star_exports,
            has_tla: parsed.has_top_level_await,
            loaded: IndexMap::new(),
            dfs_index: 0,
            dfs_ancestor_index: 0,
            eval_error: None,
            pending_async_deps: 0,
            async_evaluation: false,
            async_eval_order: None,
            async_parents: Vec::new(),
            cycle_root: None,
            top_level_capability: None,
            namespace: None,
        }
    }

    /// GetImportedModule(module, specifier): look the resolved module up in
    /// `[[LoadedModules]]`. Always present after a successful load.
    pub fn imported(&self, specifier: &str) -> Option<ModuleId> {
        self.loaded.get(specifier).copied()
    }
}
