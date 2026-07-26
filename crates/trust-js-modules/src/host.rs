// The `Host` trait: the seam between the engine-only module graph and a real JS
// front end, plus the static record types the seam trades in.
//
// The graph owns the module RECORD and the link/evaluate ALGORITHM. Everything
// that requires a JS *implementation* is a typed method on `Host`, which the M2
// interpreter provides:
//
//   * `resolve` / `parse` — the loading phase over the virtual, content-addressed
//     module map (HostResolveImportedModule) and the parser (ParseModule → the
//     requested specifiers + import/export entries). The graph models the record;
//     the host supplies the parse.
//   * `initialize_environment` — the interp's binding store: given the graph's
//     fully-resolved import wiring (namespace + live indirect bindings), create
//     the module environment and instantiate the body's local declarations. The
//     ambiguous/unresolved-export SyntaxErrors are the GRAPH's (it runs
//     ResolveExport); the host's part is infallible per §16.2.1.6.4.
//   * `execute_module` / `start_async_module` — run a module body. A synchronous
//     body returns its completion; a top-level-await body is *started* and later
//     settles by calling back `ModuleGraph::async_module_execution_fulfilled` /
//     `_rejected` — the async seam, threaded through the interp's reactor without
//     this crate ever depending on it.
//   * `new_top_level_capability` / `settle_top_level` — the promise `Evaluate()`
//     returns (§16.2.1.5.2 step 5): opaque here, a real reactor promise there.
//
// The graph NEVER interprets JS and NEVER re-enters the host during a host call:
// every instruction handed across the seam is self-contained (module keys, owned
// name strings, inlined namespace descriptors), so there is no `&mut` aliasing
// and no reentrancy on the link path. The async settlement callbacks flow the
// other way (host → graph) as ordinary public method calls from reactor jobs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::error::{ParseError, ResolveError};
use std::fmt::Debug;
use std::hash::Hash;

/// An `ImportEntry` (§16.2.1.4): one imported binding. `module_request` is a
/// specifier appearing in `[[RequestedModules]]`; `local_name` is the name bound
/// in this module's environment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportEntry {
    /// `[[ModuleRequest]]` — the requested specifier the binding comes from.
    pub module_request: String,
    /// `[[ImportName]]` — the source export name, or the namespace-object sentinel.
    pub import_name: ImportName,
    /// `[[LocalName]]` — the name bound locally.
    pub local_name: String,
}

/// An import's source name: a specific export, or the whole module namespace
/// (`import * as ns from "m"`). The spec's `String | namespace-object`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportName {
    /// A named import — `[[ImportName]]` is this export name. A default import is
    /// `Named("default")`.
    Named(String),
    /// A namespace import — `import * as ns from "m"`.
    Namespace,
}

/// A `[[LocalExportEntries]]` entry: an export of a binding declared in THIS
/// module (`export var v`, `export function f`, `export { x }`, `export default`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalExport {
    /// `[[ExportName]]` — the name this module exports it under.
    pub export_name: String,
    /// `[[LocalName]]` — the local binding it names.
    pub local_name: String,
}

/// An `[[IndirectExportEntries]]` entry: a re-export of a specific name
/// (`export { y } from "m"`, `export { y as z } from "m"`, `export * as ns from "m"`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndirectExport {
    /// `[[ExportName]]` — the name this module re-exports it under.
    pub export_name: String,
    /// `[[ModuleRequest]]` — the specifier it comes from.
    pub module_request: String,
    /// `[[ImportName]]` — the source name, or `all` for `export * as ns from`.
    pub import_name: ReExportName,
}

/// A `[[StarExportEntries]]` entry: `export * from "m"` — re-export every name
/// (except `default`) of `module_request`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StarExport {
    /// `[[ModuleRequest]]` — the specifier whose names are re-exported.
    pub module_request: String,
}

/// A re-export's source name: a specific export, or `all` (the whole namespace,
/// as `export * as ns from "m"` binds under one name). The spec's `String | all`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReExportName {
    /// `export { name as ... } from "m"`.
    Named(String),
    /// `export * as ns from "m"` — the source module's namespace object.
    All,
}

/// The static analysis of one module source — what `ParseModule` (§16.2.1.6.1)
/// produces, which is exactly what a Cyclic Module Record is built from. The
/// graph models this record; the HOST's `parse` supplies it (from the interp's
/// real parser). Every list is in SOURCE ORDER — the graph never reorders them,
/// so evaluation order is a function of the source alone.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ParsedModule {
    /// `[[RequestedModules]]` — every specifier the module imports/re-exports,
    /// in source order (a well-formed parser supplies each specifier once).
    pub requested_modules: Vec<String>,
    /// `[[ImportEntries]]`.
    pub import_entries: Vec<ImportEntry>,
    /// `[[LocalExportEntries]]`.
    pub local_exports: Vec<LocalExport>,
    /// `[[IndirectExportEntries]]`.
    pub indirect_exports: Vec<IndirectExport>,
    /// `[[StarExportEntries]]`.
    pub star_exports: Vec<StarExport>,
    /// `[[HasTLA]]` — whether the body contains a top-level `await`.
    pub has_top_level_await: bool,
}

/// A resolved binding name (`ResolveExport`'s `ResolvedBinding.[[BindingName]]`):
/// an ordinary local binding in the resolving module, or that module's own
/// namespace object (a resolution reached through `export * as ns from`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BindingName {
    /// A local binding of the resolving module.
    Local(String),
    /// The resolving module's namespace exotic object.
    Namespace,
}

/// The outcome of `ResolveExport` (§16.2.1.6.3): a concrete binding, an ambiguous
/// star collision (→ SyntaxError at link), or not found (`null`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolveExportResult<K> {
    /// A unique binding: the value lives at `binding` in module `module`.
    Resolved {
        /// The module whose environment holds the binding.
        module: K,
        /// The binding within `module`.
        binding: BindingName,
    },
    /// Two distinct bindings for the name across star re-exports.
    Ambiguous,
    /// No export provides the name.
    NotFound,
}

/// A per-name indirection inside a module-namespace exotic object: property
/// `name` reads `binding` from `target_module`'s environment (or, when `binding`
/// is `Namespace`, `target_module`'s own namespace).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamespaceBinding<K> {
    /// The exported name as it appears on the namespace object.
    pub name: String,
    /// The module whose environment (or namespace) backs the property.
    pub target_module: K,
    /// The backing binding within `target_module`.
    pub binding: BindingName,
}

/// The graph's model of a module-namespace exotic object (§10.4.6): the SORTED
/// (code-unit order) list of unambiguous export names plus each name's binding
/// indirection. The interp builds the actual exotic object from this — the graph
/// owns the NAME LIST and the indirection, not the object.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamespaceDescriptor<K> {
    /// The module this namespace belongs to.
    pub module: K,
    /// The unambiguous exported names, sorted by code-unit order.
    pub names: Vec<String>,
    /// Per-name binding indirection, parallel to `names`.
    pub bindings: Vec<NamespaceBinding<K>>,
}

/// One import-binding instruction the graph hands the host in
/// `initialize_environment` — the fully-resolved wiring for a single
/// `[[ImportEntries]]` entry, self-contained so the host needs nothing back from
/// the graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportBinding<K> {
    /// Bind `local_name` (immutable) to a module-namespace exotic object — from a
    /// namespace import, or a named import whose resolution is a namespace
    /// binding. The descriptor carries everything to build the object.
    Namespace {
        /// The local name to bind.
        local_name: String,
        /// The namespace to bind it to.
        namespace: NamespaceDescriptor<K>,
    },
    /// A live indirect binding (`CreateImportBinding`): `local_name` aliases
    /// `target_binding` in `target_module`'s environment.
    Indirect {
        /// The local name to bind.
        local_name: String,
        /// The module whose environment holds the aliased binding.
        target_module: K,
        /// The aliased binding within `target_module`.
        target_binding: String,
    },
}

/// The consumer plug-in: the interp's parser, resolver, binding store, evaluator,
/// and reactor, behind one trait. `Key` is the opaque, content-addressed module
/// identity; `Error` is the opaque host error value (a thrown JS exception);
/// `TopLevelCapability` is the opaque promise `Evaluate()` returns.
pub trait Host {
    /// The content-addressed module identity (e.g. a resolved URL or a source
    /// hash). Compared and de-duplicated by the graph; never interpreted.
    type Key: Clone + Eq + Hash + Debug;
    /// The host's opaque error value — a thrown JS exception (`SyntaxError`,
    /// a TDZ `ReferenceError`, a body throw). Carried, never inspected.
    type Error: Clone + Debug;
    /// The opaque promise `Evaluate()` returns (§16.2.1.5.2): a real reactor
    /// promise in the interp, settled via `settle_top_level`. `Clone` because a
    /// re-entrant `Evaluate()` on an already-evaluating module returns the SAME
    /// promise (step 3) — a reactor capability is a cheap id/`Rc` handle.
    type TopLevelCapability: Clone;

    /// HostResolveImportedModule: resolve `specifier` relative to `referrer` to a
    /// module key over the virtual, content-addressed map. No ambient disk — the
    /// corpus supplies the graph, so resolution is reproducible.
    fn resolve(&mut self, referrer: &Self::Key, specifier: &str)
        -> Result<Self::Key, ResolveError>;

    /// ParseModule: parse the source addressed by `key` into its record data.
    /// The graph models the record; this supplies the parse.
    fn parse(&mut self, key: &Self::Key) -> Result<ParsedModule, ParseError>;

    /// InitializeEnvironment's host half (§16.2.1.6.4 steps 4–7): create the
    /// module environment, wire the graph-resolved import `bindings`, and
    /// instantiate the body's local (var/function/lexical) declarations. Infallible
    /// per the spec — the ambiguous/unresolved-export SyntaxErrors are the graph's.
    fn initialize_environment(&mut self, key: &Self::Key, bindings: &[ImportBinding<Self::Key>]);

    /// NewPromiseCapability(%Promise%) for `Evaluate()` (step 5): mint the promise
    /// the top-level evaluation settles.
    fn new_top_level_capability(&mut self) -> Self::TopLevelCapability;

    /// Settle a top-level capability: `Ok` resolves it with `undefined`
    /// (Evaluate step 9.c.ii / AsyncModuleExecutionFulfilled step 7.b), `Err`
    /// rejects it with the error (Evaluate step 8.c / AsyncModuleExecutionRejected
    /// step 8.b).
    fn settle_top_level(
        &mut self,
        cap: &Self::TopLevelCapability,
        result: Result<(), Self::Error>,
    );

    /// ExecuteModule for a SYNCHRONOUS module body (no top-level await): run it to
    /// completion, returning `Ok` on a normal completion or `Err(thrown)` on an
    /// abrupt one. All of the module's dependencies have already been evaluated
    /// (post-order), so this is a leaf call — no reentrancy into the graph.
    fn execute_module(&mut self, key: &Self::Key) -> Result<(), Self::Error>;

    /// ExecuteAsyncModule for a top-level-await body (§16.2.1.5.2.2): START the
    /// body (its pre-await portion runs synchronously here) and arrange, via the
    /// reactor, to call `ModuleGraph::async_module_execution_fulfilled` /
    /// `_rejected` for `key` when the top-level await settles. The graph has
    /// already confirmed the module's async dependencies are all done.
    fn start_async_module(&mut self, key: &Self::Key);
}
