// trust-js-modules: the TrustJS ECMAScript module-graph engine (M2 D2).
//
// The linker / graph engine that ECMA-262 §16.2.1 describes, modelled over an
// opaque `Host` seam (see host.rs). It owns:
//
//   * the LOADING phase (`load`): resolve + parse each requested specifier over
//     the host's virtual, content-addressed map, de-duplicating by key so a
//     cyclic graph loads each module exactly once — the graph operation
//     LoadRequestedModules needs (here synchronous; a network host wraps each
//     resolve/parse in a reactor job);
//   * the LINK phase (`link`): InnerModuleLinking's Tarjan-style DFS with the
//     index / DFS-ancestor stack, ResolveExport (with star-export ambiguity and
//     cycle handling), and the InitializeEnvironment ordering — the graph runs
//     ResolveExport and raises the ambiguous / unresolved-export SyntaxErrors;
//     the host creates the environment and instantiates local declarations;
//   * the EVALUATE phase (`evaluate`): InnerModuleEvaluation's `[[Status]]` state
//     machine, `[[DFSIndex]]`/`[[DFSAncestorIndex]]`, and the top-level-await
//     machinery — `[[PendingAsyncDependencies]]`, GatherAvailableAncestors, and
//     AsyncModuleExecutionFulfilled / Rejected (the two public callbacks the host
//     drives from its reactor when a top-level await settles);
//   * GetModuleNamespace (`get_module_namespace`): the sorted export-name list and
//     the per-name binding indirection — the interp builds the exotic object.
//
// Determinism is the invariant. Records live in a dense `Vec<CyclicModuleRecord>`
// keyed by `ModuleId`; the key→id table and every module's loaded-specifier map
// are insertion-ordered `IndexMap`s; the DFS visits requested modules in source
// order over a `Vec` stack; namespace names are explicitly code-unit sorted; and
// the async execution list is sorted by a monotonic `[[AsyncEvaluation]]` rank.
// No hash-map iteration appears in any observable path, so `link` and `evaluate`
// visit modules and run bodies in a byte-identical order across runs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod error;
mod host;
mod record;

pub use error::{GraphError, ParseError, ResolveError};
pub use host::{
    BindingName, Host, ImportBinding, ImportEntry, ImportName, IndirectExport, LocalExport,
    NamespaceBinding, NamespaceDescriptor, ParsedModule, ReExportName, ResolveExportResult,
    StarExport,
};
pub use record::{ModuleId, Status};

use indexmap::IndexMap;
use record::CyclicModuleRecord;

/// The result of `dynamic_import`: the imported module plus the promise its
/// evaluation settles. The host, from the reactor job that ran the dynamic
/// import, chains `evaluation` so that when it fulfils it resolves the `import()`
/// promise with `get_module_namespace(module)` (and forwards a rejection).
pub struct DynamicImport<C> {
    /// The imported module — call `get_module_namespace` on it once evaluated.
    pub module: ModuleId,
    /// The `Evaluate()` promise for the imported module's graph.
    pub evaluation: C,
}

/// The internal (id-keyed) form of a ResolveExport outcome.
enum InnerResolve {
    Resolved { module: ModuleId, binding: BindingName },
    Ambiguous,
    NotFound,
}

/// An ECMAScript module graph: a set of Cyclic Module Records over one host,
/// with the §16.2.1 load / link / evaluate algorithms.
pub struct ModuleGraph<H: Host> {
    /// Dense record table, indexed by `ModuleId`.
    modules: Vec<CyclicModuleRecord<H>>,
    /// Key → id, insertion-ordered (dedup + deterministic).
    index_of: IndexMap<H::Key, ModuleId>,
    /// Monotonic rank assigned when a module's `[[AsyncEvaluation]]` is set true;
    /// orders the async execution list (the spec's `[[AsyncEvaluationOrder]]`).
    async_order_counter: u64,
}

impl<H: Host> Default for ModuleGraph<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: Host> ModuleGraph<H> {
    /// A fresh, empty graph.
    pub fn new() -> Self {
        Self { modules: Vec::new(), index_of: IndexMap::new(), async_order_counter: 0 }
    }

    // ------------------------------------------------------------------
    // record accessors
    // ------------------------------------------------------------------

    fn rec(&self, id: ModuleId) -> &CyclicModuleRecord<H> {
        &self.modules[id.0]
    }

    fn rec_mut(&mut self, id: ModuleId) -> &mut CyclicModuleRecord<H> {
        &mut self.modules[id.0]
    }

    /// GetImportedModule(module, specifier): the module a specifier resolved to
    /// during loading. Present for every requested specifier after `load`.
    fn imported(&self, id: ModuleId, specifier: &str) -> ModuleId {
        self.rec(id).imported(specifier).expect("requested module was loaded")
    }

    /// The id a key loaded as, if any.
    pub fn module_id(&self, key: &H::Key) -> Option<ModuleId> {
        self.index_of.get(key).copied()
    }

    /// The content-addressed key a module loaded as.
    pub fn module_key(&self, id: ModuleId) -> &H::Key {
        &self.rec(id).key
    }

    /// A module's `[[Status]]`.
    pub fn status(&self, id: ModuleId) -> Status {
        self.rec(id).status
    }

    /// A module's `[[DFSIndex]]` (for introspection / debugging).
    pub fn dfs_index(&self, id: ModuleId) -> usize {
        self.rec(id).dfs_index
    }

    /// A module's `[[DFSAncestorIndex]]` (for introspection / debugging).
    pub fn dfs_ancestor_index(&self, id: ModuleId) -> usize {
        self.rec(id).dfs_ancestor_index
    }

    /// A module's retained `[[EvaluationError]]`, if it threw.
    pub fn evaluation_error(&self, id: ModuleId) -> Option<&H::Error> {
        self.rec(id).eval_error.as_ref()
    }

    /// A module's `[[CycleRoot]]` (set once evaluation reaches it).
    pub fn cycle_root(&self, id: ModuleId) -> Option<ModuleId> {
        self.rec(id).cycle_root
    }

    // ------------------------------------------------------------------
    // loading phase — resolve + parse, deduplicated by key
    // ------------------------------------------------------------------

    /// Load the module at `key` and, transitively, everything it requests —
    /// the graph operation the spec's LoadRequestedModules / InnerModuleLoading
    /// drive. Resolve and parse run over the host's virtual map; each key is
    /// loaded exactly once, so a cyclic graph terminates. Synchronous here; an
    /// async host wraps each `resolve`/`parse` in a reactor job and calls this
    /// per newly-discovered module.
    pub fn load(&mut self, host: &mut H, key: &H::Key) -> Result<ModuleId, GraphError<H::Error>> {
        if let Some(id) = self.module_id(key) {
            return Ok(id);
        }
        // Parse first, then register — so a parse failure leaves no half-record.
        let parsed = host.parse(key).map_err(GraphError::Parse)?;
        let id = ModuleId(self.modules.len());
        // Register BEFORE recursing so a cyclic requested-module finds this id.
        self.index_of.insert(key.clone(), id);
        self.modules.push(CyclicModuleRecord::new(key.clone(), parsed));

        // Resolve + load each requested specifier, then record the mapping. Done
        // in two steps so the recursive `load` (which mutates `self.modules`) does
        // not alias the record we are filling.
        let requested = self.rec(id).requested.clone();
        let mut resolved: Vec<(String, ModuleId)> = Vec::with_capacity(requested.len());
        for specifier in &requested {
            let dep_key = host.resolve(key, specifier).map_err(GraphError::Resolve)?;
            let dep_id = self.load(host, &dep_key)?;
            resolved.push((specifier.clone(), dep_id));
        }
        for (specifier, dep_id) in resolved {
            self.rec_mut(id).loaded.insert(specifier, dep_id);
        }
        Ok(id)
    }

    /// Alias for `load` under the spec's name, for API discoverability: load a
    /// module and all its requested dependencies.
    pub fn load_requested_modules(
        &mut self,
        host: &mut H,
        key: &H::Key,
    ) -> Result<ModuleId, GraphError<H::Error>> {
        self.load(host, key)
    }

    // ------------------------------------------------------------------
    // ResolveExport (§16.2.1.6.3) + GetExportedNames (§16.2.1.6.2)
    // ------------------------------------------------------------------

    /// ResolveExport(exportName): the unique binding for `name` as exported by
    /// `id`, or `Ambiguous` / `NotFound`. The interp uses this for `import`
    /// resolution and namespace construction.
    pub fn resolve_export(&self, id: ModuleId, name: &str) -> ResolveExportResult<H::Key> {
        let mut resolve_set = Vec::new();
        match self.resolve_export_inner(id, name, &mut resolve_set) {
            InnerResolve::Resolved { module, binding } => ResolveExportResult::Resolved {
                module: self.rec(module).key.clone(),
                binding,
            },
            InnerResolve::Ambiguous => ResolveExportResult::Ambiguous,
            InnerResolve::NotFound => ResolveExportResult::NotFound,
        }
    }

    fn resolve_export_inner(
        &self,
        id: ModuleId,
        name: &str,
        resolve_set: &mut Vec<(ModuleId, String)>,
    ) -> InnerResolve {
        // Step 1: a circular import request → null.
        if resolve_set.iter().any(|(m, n)| *m == id && n == name) {
            return InnerResolve::NotFound;
        }
        resolve_set.push((id, name.to_string()));

        // Step 3: local exports.
        for e in &self.rec(id).local_exports {
            if e.export_name == name {
                return InnerResolve::Resolved {
                    module: id,
                    binding: BindingName::Local(e.local_name.clone()),
                };
            }
        }
        // Step 4: indirect (re-)exports.
        for e in &self.rec(id).indirect_exports {
            if e.export_name == name {
                let dep = self.imported(id, &e.module_request);
                match &e.import_name {
                    ReExportName::All => {
                        return InnerResolve::Resolved { module: dep, binding: BindingName::Namespace };
                    }
                    ReExportName::Named(import_name) => {
                        let import_name = import_name.clone();
                        return self.resolve_export_inner(dep, &import_name, resolve_set);
                    }
                }
            }
        }
        // Step 5: `default` is never provided by `export *`.
        if name == "default" {
            return InnerResolve::NotFound;
        }
        // Steps 6–8: star exports, watching for an ambiguous collision.
        let mut star_resolution: Option<(ModuleId, BindingName)> = None;
        let star_requests: Vec<String> =
            self.rec(id).star_exports.iter().map(|e| e.module_request.clone()).collect();
        for request in &star_requests {
            let dep = self.imported(id, request);
            match self.resolve_export_inner(dep, name, resolve_set) {
                InnerResolve::Ambiguous => return InnerResolve::Ambiguous,
                InnerResolve::Resolved { module, binding } => match &star_resolution {
                    None => star_resolution = Some((module, binding)),
                    Some((m0, b0)) => {
                        if *m0 != module || *b0 != binding {
                            return InnerResolve::Ambiguous;
                        }
                    }
                },
                InnerResolve::NotFound => {}
            }
        }
        match star_resolution {
            Some((module, binding)) => InnerResolve::Resolved { module, binding },
            None => InnerResolve::NotFound,
        }
    }

    /// GetExportedNames(exportStarSet): every name `id` exports, in source order,
    /// following `export *` (skipping `default` and duplicates), with cycle
    /// handling via the star set.
    fn exported_names(&self, id: ModuleId, star_set: &mut Vec<ModuleId>) -> Vec<String> {
        if star_set.contains(&id) {
            return Vec::new();
        }
        star_set.push(id);
        let mut names: Vec<String> = Vec::new();
        for e in &self.rec(id).local_exports {
            names.push(e.export_name.clone());
        }
        for e in &self.rec(id).indirect_exports {
            names.push(e.export_name.clone());
        }
        let star_requests: Vec<String> =
            self.rec(id).star_exports.iter().map(|e| e.module_request.clone()).collect();
        for request in &star_requests {
            let dep = self.imported(id, request);
            for n in self.exported_names(dep, star_set) {
                if n != "default" && !names.contains(&n) {
                    names.push(n);
                }
            }
        }
        names
    }

    // ------------------------------------------------------------------
    // GetModuleNamespace (§16.2.1.10)
    // ------------------------------------------------------------------

    /// GetModuleNamespace(module): the module-namespace descriptor — the sorted
    /// (code-unit order) unambiguous export names plus each name's binding
    /// indirection. Cached. The interp builds the actual exotic object from it.
    pub fn get_module_namespace(&mut self, id: ModuleId) -> &NamespaceDescriptor<H::Key> {
        if self.rec(id).namespace.is_none() {
            let descriptor = self.compute_namespace(id);
            self.rec_mut(id).namespace = Some(descriptor);
        }
        self.rec(id).namespace.as_ref().expect("just computed")
    }

    fn compute_namespace(&self, id: ModuleId) -> NamespaceDescriptor<H::Key> {
        let mut star_set = Vec::new();
        let exported = self.exported_names(id, &mut star_set);
        let mut bindings: Vec<NamespaceBinding<H::Key>> = Vec::new();
        for name in &exported {
            let mut resolve_set = Vec::new();
            if let InnerResolve::Resolved { module, binding } =
                self.resolve_export_inner(id, name, &mut resolve_set)
            {
                bindings.push(NamespaceBinding {
                    name: name.clone(),
                    target_module: self.rec(module).key.clone(),
                    binding,
                });
            }
            // NotFound / Ambiguous names are excluded from the namespace object.
        }
        // The namespace exotic object's own property keys are sorted by code-unit
        // order (SortCompare over the String names).
        bindings.sort_by(|a, b| a.name.cmp(&b.name));
        let names = bindings.iter().map(|b| b.name.clone()).collect();
        NamespaceDescriptor { module: self.rec(id).key.clone(), names, bindings }
    }

    // ------------------------------------------------------------------
    // LINK phase (§16.2.1.5.1)
    // ------------------------------------------------------------------

    /// Link(): instantiate the graph rooted at `root` — the three-phase link's
    /// second phase. Runs InnerModuleLinking's DFS; on a SyntaxError (ambiguous /
    /// unresolved export) unwinds every module still `linking` back to `unlinked`
    /// and returns the error, leaving the graph re-linkable.
    pub fn link(&mut self, host: &mut H, root: ModuleId) -> Result<(), GraphError<H::Error>> {
        debug_assert!(matches!(
            self.rec(root).status,
            Status::Unlinked | Status::Linked | Status::EvaluatingAsync | Status::Evaluated
        ));
        let mut stack: Vec<ModuleId> = Vec::new();
        match self.inner_module_linking(host, root, &mut stack, 0) {
            Ok(_) => {
                debug_assert!(matches!(
                    self.rec(root).status,
                    Status::Linked | Status::EvaluatingAsync | Status::Evaluated
                ));
                debug_assert!(stack.is_empty());
                Ok(())
            }
            Err(e) => {
                // Unwind: every module still on the stack goes back to unlinked.
                for &m in &stack {
                    debug_assert_eq!(self.rec(m).status, Status::Linking);
                    self.rec_mut(m).status = Status::Unlinked;
                }
                debug_assert_eq!(self.rec(root).status, Status::Unlinked);
                Err(e)
            }
        }
    }

    fn inner_module_linking(
        &mut self,
        host: &mut H,
        id: ModuleId,
        stack: &mut Vec<ModuleId>,
        mut index: usize,
    ) -> Result<usize, GraphError<H::Error>> {
        match self.rec(id).status {
            Status::Linking | Status::Linked | Status::EvaluatingAsync | Status::Evaluated => {
                return Ok(index);
            }
            Status::Unlinked => {}
            other => debug_assert!(false, "InnerModuleLinking on status {other:?}"),
        }
        {
            let r = self.rec_mut(id);
            r.status = Status::Linking;
            r.dfs_index = index;
            r.dfs_ancestor_index = index;
        }
        index += 1;
        stack.push(id);

        let requested = self.rec(id).requested.clone();
        for specifier in &requested {
            let dep = self.imported(id, specifier);
            index = self.inner_module_linking(host, dep, stack, index)?;
            // dep is a Cyclic Module Record; if still linking (on the stack), it
            // is an ancestor in this SCC — pull our ancestor index down to it.
            if self.rec(dep).status == Status::Linking {
                debug_assert!(stack.contains(&dep));
                let da = self.rec(dep).dfs_ancestor_index;
                let r = self.rec_mut(id);
                r.dfs_ancestor_index = r.dfs_ancestor_index.min(da);
            }
        }

        // InitializeEnvironment: run the export-resolvability checks (SyntaxErrors
        // are ours) and hand the host the resolved import wiring.
        self.initialize_environment(host, id)?;

        debug_assert!(self.rec(id).dfs_ancestor_index <= self.rec(id).dfs_index);
        if self.rec(id).dfs_ancestor_index == self.rec(id).dfs_index {
            loop {
                let m = stack.pop().expect("scc member on stack");
                self.rec_mut(m).status = Status::Linked;
                if m == id {
                    break;
                }
            }
        }
        Ok(index)
    }

    /// InitializeEnvironment (§16.2.1.6.4) — the graph's half: check every
    /// indirect export resolves unambiguously, resolve every import to its
    /// binding (raising the ambiguous / unresolved SyntaxErrors), and hand the
    /// host the wiring to build the environment.
    fn initialize_environment(
        &mut self,
        host: &mut H,
        id: ModuleId,
    ) -> Result<(), GraphError<H::Error>> {
        let this_key_display = format!("{:?}", self.rec(id).key);

        // Step 1: every indirect export must resolve unambiguously.
        let indirect: Vec<IndirectExport> = self.rec(id).indirect_exports.clone();
        for e in &indirect {
            match self.resolve_export(id, &e.export_name) {
                ResolveExportResult::Resolved { .. } => {}
                ResolveExportResult::Ambiguous => {
                    return Err(GraphError::AmbiguousExport {
                        module: this_key_display,
                        name: e.export_name.clone(),
                    });
                }
                ResolveExportResult::NotFound => {
                    return Err(GraphError::UnresolvedImport {
                        module: this_key_display,
                        name: e.export_name.clone(),
                    });
                }
            }
        }

        // Step 6: resolve every import to a binding instruction.
        let imports: Vec<ImportEntry> = self.rec(id).imports.clone();
        let mut bindings: Vec<ImportBinding<H::Key>> = Vec::with_capacity(imports.len());
        for ie in &imports {
            let dep = self.imported(id, &ie.module_request);
            match &ie.import_name {
                ImportName::Namespace => {
                    let namespace = self.get_module_namespace(dep).clone();
                    bindings.push(ImportBinding::Namespace {
                        local_name: ie.local_name.clone(),
                        namespace,
                    });
                }
                ImportName::Named(import_name) => {
                    match self.resolve_export_inner(dep, import_name, &mut Vec::new()) {
                        InnerResolve::NotFound => {
                            return Err(GraphError::UnresolvedImport {
                                module: format!("{:?}", self.rec(dep).key),
                                name: import_name.clone(),
                            });
                        }
                        InnerResolve::Ambiguous => {
                            return Err(GraphError::AmbiguousExport {
                                module: format!("{:?}", self.rec(dep).key),
                                name: import_name.clone(),
                            });
                        }
                        InnerResolve::Resolved { module, binding } => match binding {
                            BindingName::Namespace => {
                                let namespace = self.get_module_namespace(module).clone();
                                bindings.push(ImportBinding::Namespace {
                                    local_name: ie.local_name.clone(),
                                    namespace,
                                });
                            }
                            BindingName::Local(target_binding) => {
                                bindings.push(ImportBinding::Indirect {
                                    local_name: ie.local_name.clone(),
                                    target_module: self.rec(module).key.clone(),
                                    target_binding,
                                });
                            }
                        },
                    }
                }
            }
        }

        let key = self.rec(id).key.clone();
        host.initialize_environment(&key, &bindings);
        Ok(())
    }

    // ------------------------------------------------------------------
    // EVALUATE phase (§16.2.1.5.2)
    // ------------------------------------------------------------------

    /// Evaluate(): run the graph rooted at `root` — the three-phase link's third
    /// phase. Returns the promise (top-level capability) the evaluation settles:
    /// resolved synchronously for a graph with no top-level await, or later,
    /// through `async_module_execution_fulfilled` / `_rejected`, for one with it.
    pub fn evaluate(&mut self, host: &mut H, root: ModuleId) -> H::TopLevelCapability {
        debug_assert!(matches!(
            self.rec(root).status,
            Status::Linked | Status::EvaluatingAsync | Status::Evaluated
        ));
        // Steps 1–2: a module already (async-)evaluated hands back its cycle root.
        let mut module = root;
        if matches!(self.rec(module).status, Status::EvaluatingAsync | Status::Evaluated) {
            module = self.rec(module).cycle_root.expect("evaluated module has a cycle root");
        }
        // Step 3: an in-flight / finished top-level evaluation returns its promise.
        if let Some(cap) = &self.rec(module).top_level_capability {
            return cap.clone();
        }
        // Steps 4–6: fresh top-level capability.
        let capability = host.new_top_level_capability();
        self.rec_mut(module).top_level_capability = Some(capability.clone());

        // Step 7: drive the DFS.
        let mut stack: Vec<ModuleId> = Vec::new();
        match self.inner_module_evaluation(host, module, &mut stack, 0) {
            Err(err) => {
                // Step 8: mark every module still on the stack evaluated-with-error.
                for &m in &stack {
                    debug_assert_eq!(self.rec(m).status, Status::Evaluating);
                    let r = self.rec_mut(m);
                    r.status = Status::Evaluated;
                    r.eval_error = Some(err.clone());
                }
                host.settle_top_level(&capability, Err(err));
            }
            Ok(_) => {
                // Step 9: success. A non-async graph resolves now; an async graph
                // stays pending and settles via the async callbacks.
                debug_assert!(matches!(
                    self.rec(module).status,
                    Status::EvaluatingAsync | Status::Evaluated
                ));
                if !self.rec(module).async_evaluation {
                    debug_assert_eq!(self.rec(module).status, Status::Evaluated);
                    host.settle_top_level(&capability, Ok(()));
                }
                debug_assert!(stack.is_empty());
            }
        }
        capability
    }

    fn inner_module_evaluation(
        &mut self,
        host: &mut H,
        id: ModuleId,
        stack: &mut Vec<ModuleId>,
        mut index: usize,
    ) -> Result<usize, H::Error> {
        // Step 2: already (async-)evaluated — propagate any retained error.
        match self.rec(id).status {
            Status::EvaluatingAsync | Status::Evaluated => {
                return match &self.rec(id).eval_error {
                    None => Ok(index),
                    Some(e) => Err(e.clone()),
                };
            }
            // Step 3: currently evaluating (a cycle back-edge) — nothing to do.
            Status::Evaluating => return Ok(index),
            Status::Linked => {}
            other => debug_assert!(false, "InnerModuleEvaluation on status {other:?}"),
        }

        {
            let r = self.rec_mut(id);
            r.status = Status::Evaluating;
            r.dfs_index = index;
            r.dfs_ancestor_index = index;
            r.pending_async_deps = 0;
        }
        index += 1;
        stack.push(id);

        let requested = self.rec(id).requested.clone();
        for specifier in &requested {
            let mut required = self.imported(id, specifier);
            index = self.inner_module_evaluation(host, required, stack, index)?;
            // Step 11.c: required is a Cyclic Module Record.
            if self.rec(required).status == Status::Evaluating {
                debug_assert!(stack.contains(&required));
                let ra = self.rec(required).dfs_ancestor_index;
                let r = self.rec_mut(id);
                r.dfs_ancestor_index = r.dfs_ancestor_index.min(ra);
            } else {
                // evaluating-async or evaluated: follow to the cycle root.
                debug_assert!(matches!(
                    self.rec(required).status,
                    Status::EvaluatingAsync | Status::Evaluated
                ));
                required = self.rec(required).cycle_root.expect("required has a cycle root");
                if let Some(err) = &self.rec(required).eval_error {
                    return Err(err.clone());
                }
            }
            // Step 11.c.v: an async dependency defers us.
            if self.rec(required).async_evaluation {
                self.rec_mut(required).async_parents.push(id);
                self.rec_mut(id).pending_async_deps += 1;
            }
        }

        // Step 12 / 13: async vs synchronous body.
        let pending = self.rec(id).pending_async_deps;
        let has_tla = self.rec(id).has_tla;
        if pending > 0 || has_tla {
            debug_assert!(!self.rec(id).async_evaluation);
            let order = self.async_order_counter;
            self.async_order_counter += 1;
            let r = self.rec_mut(id);
            r.async_evaluation = true;
            r.async_eval_order = Some(order);
            if pending == 0 {
                self.execute_async_module(host, id);
            }
        } else {
            let key = self.rec(id).key.clone();
            host.execute_module(&key)?;
        }

        // Step 16: close the SCC once we return to its root.
        debug_assert!(self.rec(id).dfs_ancestor_index <= self.rec(id).dfs_index);
        if self.rec(id).dfs_ancestor_index == self.rec(id).dfs_index {
            loop {
                let m = stack.pop().expect("scc member on stack");
                self.rec_mut(m).status = if self.rec(m).async_evaluation {
                    Status::EvaluatingAsync
                } else {
                    Status::Evaluated
                };
                self.rec_mut(m).cycle_root = Some(id);
                if m == id {
                    break;
                }
            }
        }
        Ok(index)
    }

    /// ExecuteAsyncModule (§16.2.1.5.2.2): start a top-level-await body. The host
    /// runs its pre-await portion now and arranges, via the reactor, to call
    /// `async_module_execution_fulfilled` / `_rejected` when the await settles.
    fn execute_async_module(&mut self, host: &mut H, id: ModuleId) {
        debug_assert!(matches!(
            self.rec(id).status,
            Status::Evaluating | Status::EvaluatingAsync
        ));
        debug_assert!(self.rec(id).has_tla);
        let key = self.rec(id).key.clone();
        host.start_async_module(&key);
    }

    // ------------------------------------------------------------------
    // top-level-await settlement callbacks (host → graph, from the reactor)
    // ------------------------------------------------------------------

    /// AsyncModuleExecutionFulfilled (§16.2.1.5.2.4): the host calls this when
    /// `module`'s top-level await fulfils. Settles its top-level promise, then
    /// runs every dependant whose last async dependency this was (in
    /// `[[AsyncEvaluation]]` order).
    pub fn async_module_execution_fulfilled(&mut self, host: &mut H, module: ModuleId) {
        if self.rec(module).status == Status::Evaluated {
            debug_assert!(self.rec(module).eval_error.is_some());
            return;
        }
        debug_assert_eq!(self.rec(module).status, Status::EvaluatingAsync);
        debug_assert!(self.rec(module).async_evaluation);
        debug_assert!(self.rec(module).eval_error.is_none());

        {
            let r = self.rec_mut(module);
            r.async_evaluation = false;
            r.status = Status::Evaluated;
        }
        if self.rec(module).top_level_capability.is_some() {
            debug_assert_eq!(self.rec(module).cycle_root, Some(module));
            let cap = self.rec(module).top_level_capability.clone().unwrap();
            host.settle_top_level(&cap, Ok(()));
        }

        let mut exec_list: Vec<ModuleId> = Vec::new();
        self.gather_available_ancestors(module, &mut exec_list);
        // Sort by [[AsyncEvaluation]] rank (ascending) — the significant order.
        exec_list.sort_by_key(|m| self.rec(*m).async_eval_order);

        for m in exec_list {
            if self.rec(m).status == Status::Evaluated {
                debug_assert!(self.rec(m).eval_error.is_some());
            } else if self.rec(m).has_tla {
                self.execute_async_module(host, m);
            } else {
                let key = self.rec(m).key.clone();
                match host.execute_module(&key) {
                    Err(e) => self.async_module_execution_rejected(host, m, e),
                    Ok(()) => {
                        self.rec_mut(m).status = Status::Evaluated;
                        if self.rec(m).top_level_capability.is_some() {
                            debug_assert_eq!(self.rec(m).cycle_root, Some(m));
                            let cap = self.rec(m).top_level_capability.clone().unwrap();
                            host.settle_top_level(&cap, Ok(()));
                        }
                    }
                }
            }
        }
    }

    /// GatherAvailableAncestors (§16.2.1.5.2.3): decrement each async parent's
    /// pending count; those that hit zero (and their sync-cascaded ancestors)
    /// join `exec_list`.
    fn gather_available_ancestors(&mut self, module: ModuleId, exec_list: &mut Vec<ModuleId>) {
        let parents = self.rec(module).async_parents.clone();
        for m in parents {
            let root_ok = {
                let root = self.rec(m).cycle_root.expect("async parent has a cycle root");
                self.rec(root).eval_error.is_none()
            };
            if !exec_list.contains(&m) && root_ok {
                debug_assert_eq!(self.rec(m).status, Status::EvaluatingAsync);
                debug_assert!(self.rec(m).eval_error.is_none());
                debug_assert!(self.rec(m).async_evaluation);
                debug_assert!(self.rec(m).pending_async_deps > 0);
                self.rec_mut(m).pending_async_deps -= 1;
                if self.rec(m).pending_async_deps == 0 {
                    exec_list.push(m);
                    if !self.rec(m).has_tla {
                        self.gather_available_ancestors(m, exec_list);
                    }
                }
            }
        }
    }

    /// AsyncModuleExecutionRejected (§16.2.1.5.2.5): the host calls this when
    /// `module`'s top-level await rejects (or its body threw). Retains the error,
    /// propagates it to every async parent, and rejects its top-level promise.
    pub fn async_module_execution_rejected(
        &mut self,
        host: &mut H,
        module: ModuleId,
        error: H::Error,
    ) {
        if self.rec(module).status == Status::Evaluated {
            debug_assert!(self.rec(module).eval_error.is_some());
            return;
        }
        debug_assert_eq!(self.rec(module).status, Status::EvaluatingAsync);
        debug_assert!(self.rec(module).async_evaluation);
        debug_assert!(self.rec(module).eval_error.is_none());

        {
            let r = self.rec_mut(module);
            r.eval_error = Some(error.clone());
            r.status = Status::Evaluated;
        }
        let parents = self.rec(module).async_parents.clone();
        for m in parents {
            self.async_module_execution_rejected(host, m, error.clone());
        }
        if self.rec(module).top_level_capability.is_some() {
            debug_assert_eq!(self.rec(module).cycle_root, Some(module));
            let cap = self.rec(module).top_level_capability.clone().unwrap();
            host.settle_top_level(&cap, Err(error));
        }
    }

    // ------------------------------------------------------------------
    // dynamic import()  (host-driven, onto the reactor's job queue)
    // ------------------------------------------------------------------

    /// The graph half of a dynamic `import(specifier)` (§13.3.10.2 /
    /// ContinueDynamicImport): resolve + load + link + evaluate the target and
    /// return its module id and evaluation promise. The host calls this from the
    /// reactor job the `import()` scheduled; when `evaluation` fulfils it resolves
    /// the `import()` promise with `get_module_namespace(module)` (forwarding a
    /// rejection). Loading + linking are synchronous over the virtual map; the
    /// asynchrony is the host's (the job queue + `evaluation`'s settlement).
    pub fn dynamic_import(
        &mut self,
        host: &mut H,
        referrer: &H::Key,
        specifier: &str,
    ) -> Result<DynamicImport<H::TopLevelCapability>, GraphError<H::Error>> {
        let key = host.resolve(referrer, specifier).map_err(GraphError::Resolve)?;
        let id = self.load(host, &key)?;
        if self.rec(id).status == Status::Unlinked {
            self.link(host, id)?;
        }
        let evaluation = self.evaluate(host, id);
        Ok(DynamicImport { module: id, evaluation })
    }
}
