//! Original, typed THIR facts for a level-S source consistency check.
//!
//! These facts precede template construction. Neither the template nor its
//! constructed IR is a source census. The concrete adapter must reconstruct
//! their Rust types and callees under the requested actual Instance. A matching
//! effect census is not a Rust refinement theorem or an admission token.

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use trust_ir::template::HostKey;

use crate::template_metadata::OwnerBindings;

pub mod capture;
pub mod concrete;
pub mod binding;
pub(crate) mod wire;

pub const SOURCE_SCHEMA: u32 = 1;
pub(crate) const MAX_SOURCE_NODES: usize = 65536;
pub(crate) const MAX_SOURCE_DEPTH: usize = 128;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceRefusal(pub String);
impl std::fmt::Display for SourceRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for SourceRefusal {}
pub type Result<T> = std::result::Result<T, SourceRefusal>;
fn refuse(s: impl Into<String>) -> SourceRefusal {
    SourceRefusal(format!("THIR source facts: {}", s.into()))
}

/// Original source-memory roots. Private local assignments are recorded as
/// nodes, but never confused with an escaping write. An uncertain pointer is
/// Indirect; this is not a claim that it aliases any particular argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceRoot {
    Argument(u32),
    Indirect,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceEffect {
    Call {
        /// Actual original THIR arena index, not a fabricated Rustc Span.
        expression: u32,
        key: HostKey,
        argument_types: Vec<u32>,
        result_type: u32,
    },
    Store {
        expression: u32,
        root: SourceRoot,
        value_type: u32,
        /// A plain, unmodified entry argument, otherwise no refinement.
        exact_argument: Option<u32>,
    },
}

/// The accepted source vocabulary is closed in the capturer. The node record
/// retains coverage separately from the effect list, including private writes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SourceNodeKind {
    Wrapper,
    Dereference,
    NeverCoercion,
    Block,
    Literal,
    Variable(u32),
    Return,
    Array,
    Tuple,
    Repeat,
    Cast,
    Not,
    Bitwise,
    Compare,
    LocalAssignment(u32),
    Call,
    EscapingStore,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceNode {
    pub expression: u32,
    pub ty: u32,
    pub kind: SourceNodeKind,
    /// Actual structural THIR visitor edges. This is not an execution trace.
    pub children: Vec<u32>,
}

/// Captured from the actual owner by `capture::local`, or read as a claim from
/// an expected-owner, content-bound S2 input. Decoded facts retain the P-TIR
/// producer-honesty premise; no data constructor is a source theorem.
/// Read-only data: its existence grants no body, source-proof or codegen grade.
#[derive(Clone, Debug, PartialEq)]
pub struct CapturedSource {
    bindings: OwnerBindings,
    target: trust_ir::TargetInfo,
    overflow_checks: bool,
    root: u32,
    arena_expressions: u32,
    argument_types: Vec<u32>,
    argument_variables: Vec<Option<u32>>,
    modified_variables: Vec<u32>,
    return_type: u32,
    /// Original-owner checked schema-1 Type keys. This includes every visited
    /// expression/pattern and signature type, before any type is erased.
    types: Vec<HostKey>,
    nodes: Vec<SourceNode>,
    effects: Vec<SourceEffect>,
}
impl CapturedSource {
    pub fn bindings(&self) -> &OwnerBindings { &self.bindings }
    pub fn target(&self) -> &trust_ir::TargetInfo { &self.target }
    pub fn overflow_checks(&self) -> bool { self.overflow_checks }
    pub fn original_root(&self) -> u32 { self.root }
    pub fn original_arena_expressions(&self) -> u32 { self.arena_expressions }
    pub fn visited_expressions(&self) -> usize { self.nodes.len() }
    pub fn type_keys(&self) -> &[HostKey] { &self.types }
    pub fn argument_types(&self) -> &[u32] { &self.argument_types }
    pub fn return_type(&self) -> u32 { self.return_type }
    pub fn effects(&self) -> &[SourceEffect] { &self.effects }
}

#[derive(Default)]
struct SourceRegistry {
    captures: BTreeMap<u32, Result<CapturedSource>>,
    duplicate: BTreeSet<u32>,
}

/// Called only by the canonical THIR template capture seam, before erasure.
/// It reads no MIR body and neither constructs nor censuses a template module.
pub(crate) fn record(tcx: TyCtxt<'_>, owner: LocalDefId) {
    if !tcx.sess.opts.unstable_opts.trust_ir_lower_templates
        || !crate::rmeta_entry::entries_enabled(tcx)
    {
        return;
    }
    let capture = capture::local(tcx, owner);
    let index = owner.local_def_index.as_u32();
    tcx.sess.with_trust_compiler_state::<SourceRegistry, _>(|r| {
        if r.captures.insert(index, capture).is_some() { r.duplicate.insert(index); }
    });
}

pub(crate) fn recorded(tcx: TyCtxt<'_>, owner: LocalDefId) -> Result<CapturedSource> {
    tcx.sess.with_trust_compiler_state::<SourceRegistry, _>(|r| {
        let index = owner.local_def_index.as_u32();
        if r.duplicate.contains(&index) { return Err(refuse("duplicate source capture")); }
        r.captures.get(&index).cloned().unwrap_or_else(|| Err(refuse("no source capture")))
    })
}

#[cfg(test)]
mod tests;
