// Typed module-graph refusals.
//
// The graph fails closed: an unresolvable specifier, a parse rejection, an
// ambiguous star-export, an unresolved import, or a body throw all surface as a
// typed variant rather than a panic, a silent skip, or an approximation. The
// link-time variants (`AmbiguousExport`, `UnresolvedImport`) are exactly the
// SyntaxError conditions ECMA-262 §16.2.1.6.4 (InitializeEnvironment) and
// §16.2.1.6.3 (ResolveExport) raise; `Resolve`/`Parse` wrap the host's own
// loading-phase refusals; `Evaluation` carries an opaque host error value from a
// module body that threw.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// The host's refusal to resolve a specifier against the virtual, content-
/// addressed module map (HostResolveImportedModule / HostLoadImportedModule).
/// `specifier` is the unresolved request; `reason` is the host's message.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("cannot resolve module specifier {specifier:?}: {reason}")]
pub struct ResolveError {
    /// The specifier that could not be resolved.
    pub specifier: String,
    /// The host's human-readable reason.
    pub reason: String,
}

impl ResolveError {
    /// Build a resolve refusal for `specifier` with `reason`.
    pub fn new(specifier: impl Into<String>, reason: impl Into<String>) -> Self {
        Self { specifier: specifier.into(), reason: reason.into() }
    }
}

/// The host parser's refusal to turn a module source into a record
/// (a SyntaxError at parse). `reason` is the host's message.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("cannot parse module {key:?}: {reason}")]
pub struct ParseError {
    /// A display form of the module key that failed to parse.
    pub key: String,
    /// The host's human-readable reason.
    pub reason: String,
}

impl ParseError {
    /// Build a parse refusal for the module displayed as `key` with `reason`.
    pub fn new(key: impl Into<String>, reason: impl Into<String>) -> Self {
        Self { key: key.into(), reason: reason.into() }
    }
}

/// A typed module-graph refusal, generic over the host's opaque error value `E`
/// (the value a JS module body throws — a `SyntaxError`, `ReferenceError` from a
/// TDZ access, etc.). Fail-closed: every failure the graph can surface is one of
/// these; the graph never panics on a well-formed record set and never fabricates
/// a success.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum GraphError<E> {
    /// The loading phase could not resolve a requested specifier.
    #[error(transparent)]
    Resolve(#[from] ResolveError),

    /// The loading phase could not parse a resolved module source.
    #[error(transparent)]
    Parse(#[from] ParseError),

    /// ResolveExport for a star-exported name found two different source
    /// bindings — the ambiguous-export SyntaxError (§16.2.1.6.3 step 8 /
    /// InitializeEnvironment step 6.c.ii). `module` and `name` display the
    /// offending re-export site.
    #[error("ambiguous star export {name:?} in module {module:?} (resolves to two different bindings)")]
    AmbiguousExport {
        /// Display form of the importing/re-exporting module's key.
        module: String,
        /// The export name whose resolution was ambiguous.
        name: String,
    },

    /// ResolveExport for an imported (or re-exported) name found no binding — the
    /// unresolved-import SyntaxError (InitializeEnvironment steps 1.b / 6.c.ii).
    #[error("module {module:?} has no exported member {name:?} (imported/re-exported but never provided)")]
    UnresolvedImport {
        /// Display form of the module whose export was requested.
        module: String,
        /// The requested export name.
        name: String,
    },

    /// A module body threw during evaluation; the opaque host error value is
    /// carried through (the `[[EvaluationError]]` of §16.2.1.5.2). This is also
    /// how a cross-module TDZ access (using a live binding before the providing
    /// module's body initialised it) surfaces: the host body returns a throw and
    /// the graph propagates it here.
    #[error("module evaluation threw")]
    Evaluation(E),
}
