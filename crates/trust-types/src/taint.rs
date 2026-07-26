// trust-types/taint.rs: Taint tracking and data flow analysis
//
// Experimental policy-driven information-flow diagnostics over the legacy
// verification IR. The lattice and propagation machinery are useful for debug
// scans, but `analyze_taint` is not a sound proof or compiler-verdict engine;
// see its API documentation for the current CFG and name-resolution limits.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::{Operand, Place, Rvalue, SourceSpan, Statement, Terminator, VerifiableBody};

// ---------------------------------------------------------------------------
// Core taint label and source/sink types
// ---------------------------------------------------------------------------

/// Categories of taint origins. Each label identifies a class of untrusted data.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TaintLabel {
    /// Data from user input (stdin, form fields, command-line args).
    UserInput,
    /// Data received from the network (sockets, HTTP responses).
    NetworkData,
    /// Sensitive data (passwords, API keys, tokens).
    Secret,
    /// Data read from files.
    FileData,
    /// Data from environment variables.
    EnvVar,
    /// Data originating from an unsafe block.
    UnsafeBlock,
    /// Data from an extern (FFI) call.
    ExternCall,
    /// Custom application-defined taint label.
    Custom(String),
}

/// Where tainted data originates, substring-matched against call paths.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TaintSource {
    pub label: TaintLabel,
    pub pattern: String,
}

/// Where tainted data must not reach without sanitization, substring-matched
/// against call paths.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TaintSink {
    pub label: SinkKind,
    pub pattern: String,
}

/// Categories of security-sensitive sinks.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SinkKind {
    /// SQL query execution (injection risk).
    SqlQuery,
    /// Log output (information leakage).
    LogOutput,
    /// Network send (data exfiltration).
    NetworkSend,
    /// HTML rendering (XSS risk).
    HtmlRender,
    /// File write (path traversal, data corruption).
    FileWrite,
    /// Shell command execution (command injection).
    ShellCommand,
    /// Raw pointer dereference (memory corruption).
    RawPointer,
    /// Assertion (tainted data in assertions may leak info or cause DoS).
    Assertion,
    /// Custom application-defined sink.
    Custom(String),
}

/// A sanitizer pattern removes a specific taint label from a call result.
///
/// Patterns are substring-matched by the experimental analyzer, so this must
/// not be treated as an exact or trusted declassification boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Sanitizer {
    pub removes: TaintLabel,
    pub pattern: String,
}

// ---------------------------------------------------------------------------
// Taint policy
// ---------------------------------------------------------------------------

/// A complete taint policy: sources, sinks, and sanitizers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TaintPolicy {
    pub sources: Vec<TaintSource>,
    pub sinks: Vec<TaintSink>,
    pub sanitizers: Vec<Sanitizer>,
}

impl Default for TaintPolicy {
    fn default() -> Self {
        default_web_policy()
    }
}

impl TaintPolicy {
    pub fn default_web_policy() -> Self {
        default_web_policy()
    }
}

// ---------------------------------------------------------------------------
// Data flow graph types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataFlowNode {
    pub local: usize,
    pub block: usize,
    pub taint: BTreeSet<TaintLabel>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataFlowEdge {
    pub from_local: usize,
    pub to_local: usize,
    pub block: usize,
    pub kind: FlowKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FlowKind {
    Assignment,
    CallArgument,
    CallReturn,
    FieldAccess,
    Ref,
}

// ---------------------------------------------------------------------------
// Violation and result types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintFlowViolation {
    pub source_label: TaintLabel,
    pub sink_kind: SinkKind,
    pub sink_func: String,
    pub path: Vec<FlowStep>,
    pub source_span: SourceSpan,
    pub sink_span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FlowStep {
    pub local: usize,
    pub block: usize,
    pub description: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintAnalysisResult {
    pub violations: Vec<TaintFlowViolation>,
    pub tainted_locals: BTreeMap<usize, BTreeSet<TaintLabel>>,
    pub flow_edges: Vec<DataFlowEdge>,
}

// ---------------------------------------------------------------------------
// Taint lattice
// ---------------------------------------------------------------------------

/// A taint set modeled as a lattice over `BTreeSet<TaintLabel>`.
///
/// The lattice is ordered by set inclusion:
/// - Bottom = empty set (no taint)
/// - Top = set of all possible labels (maximally tainted)
/// - Join = set union (least upper bound)
/// - Meet = set intersection (greatest lower bound)
///
/// This implements the standard powerset lattice used in information-flow
/// analysis (Denning, 1976).
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct TaintLattice {
    labels: BTreeSet<TaintLabel>,
}

impl TaintLattice {
    /// Bottom element: no taint.
    pub fn bottom() -> Self {
        Self { labels: BTreeSet::new() }
    }

    /// Top element: all standard taint labels.
    pub fn top() -> Self {
        Self {
            labels: BTreeSet::from([
                TaintLabel::UserInput,
                TaintLabel::NetworkData,
                TaintLabel::Secret,
                TaintLabel::FileData,
                TaintLabel::EnvVar,
                TaintLabel::UnsafeBlock,
                TaintLabel::ExternCall,
            ]),
        }
    }

    /// Create a lattice element from a single label.
    pub fn singleton(label: TaintLabel) -> Self {
        let mut labels = BTreeSet::new();
        labels.insert(label);
        Self { labels }
    }

    /// Create a lattice element from a set of labels.
    pub fn from_set(labels: BTreeSet<TaintLabel>) -> Self {
        Self { labels }
    }

    /// Join (least upper bound) = set union.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        Self { labels: self.labels.union(&other.labels).cloned().collect() }
    }

    /// Meet (greatest lower bound) = set intersection.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        Self { labels: self.labels.intersection(&other.labels).cloned().collect() }
    }

    /// Returns true if this is the bottom element (no taint).
    pub fn is_bottom(&self) -> bool {
        self.labels.is_empty()
    }

    /// Returns true if this element contains a specific label.
    pub fn contains(&self, label: &TaintLabel) -> bool {
        self.labels.contains(label)
    }

    /// Add a label to this lattice element.
    pub fn add(&mut self, label: TaintLabel) {
        self.labels.insert(label);
    }

    /// Remove a label from this lattice element (sanitization).
    pub fn remove(&mut self, label: &TaintLabel) {
        self.labels.remove(label);
    }

    /// Returns true if `self` is a subset of `other` (self <= other in the lattice).
    pub fn is_subset_of(&self, other: &Self) -> bool {
        self.labels.is_subset(&other.labels)
    }

    /// Number of taint labels in this element.
    pub fn len(&self) -> usize {
        self.labels.len()
    }

    /// Returns true if empty (same as `is_bottom`).
    pub fn is_empty(&self) -> bool {
        self.labels.is_empty()
    }

    /// Reference to the underlying label set.
    pub fn labels(&self) -> &BTreeSet<TaintLabel> {
        &self.labels
    }

    /// Consume self and return the label set.
    pub fn into_labels(self) -> BTreeSet<TaintLabel> {
        self.labels
    }
}

// ---------------------------------------------------------------------------
// Taint propagation rules
// ---------------------------------------------------------------------------

/// How taint propagates through different MIR operations.
///
/// Each rule defines whether and how taint transfers from source operands
/// to destination places. The propagator is stateless; it applies rules
/// to individual operations.
#[derive(Debug, Clone)]
pub struct TaintPropagator {
    /// If true, binary operations propagate taint from both operands to the result.
    pub propagate_binary_ops: bool,
    /// If true, field accesses propagate taint from the aggregate to the field.
    pub propagate_field_access: bool,
    /// If true, references propagate taint bidirectionally (ref and deref).
    pub propagate_refs: bool,
    /// If true, casts preserve taint from the source.
    pub propagate_casts: bool,
    /// If true, aggregates inherit taint from all constituent operands.
    pub propagate_aggregates: bool,
}

impl Default for TaintPropagator {
    fn default() -> Self {
        Self {
            propagate_binary_ops: true,
            propagate_field_access: true,
            propagate_refs: true,
            propagate_casts: true,
            propagate_aggregates: true,
        }
    }
}

impl TaintPropagator {
    /// Propagate taint through an rvalue, returning the resulting taint set.
    ///
    /// `local_taint` maps each local index to its current taint lattice element.
    pub fn propagate_rvalue(
        &self,
        rvalue: &Rvalue,
        local_taint: &BTreeMap<usize, TaintLattice>,
    ) -> TaintLattice {
        match rvalue {
            Rvalue::Use(operand) => self.propagate_operand(operand, local_taint),
            Rvalue::Cast(operand, _) => {
                if self.propagate_casts {
                    self.propagate_operand(operand, local_taint)
                } else {
                    TaintLattice::bottom()
                }
            }
            Rvalue::UnaryOp(_, operand) => self.propagate_operand(operand, local_taint),
            Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                if self.propagate_binary_ops {
                    let l = self.propagate_operand(lhs, local_taint);
                    let r = self.propagate_operand(rhs, local_taint);
                    l.join(&r)
                } else {
                    TaintLattice::bottom()
                }
            }
            Rvalue::Ref { place, .. } => {
                if self.propagate_refs {
                    self.taint_for_place(place, local_taint)
                } else {
                    TaintLattice::bottom()
                }
            }
            Rvalue::Aggregate(_, operands) => {
                if self.propagate_aggregates {
                    operands.iter().fold(TaintLattice::bottom(), |acc, op| {
                        acc.join(&self.propagate_operand(op, local_taint))
                    })
                } else {
                    TaintLattice::bottom()
                }
            }
            Rvalue::Discriminant(place) | Rvalue::Len(place) | Rvalue::CopyForDeref(place) => {
                if self.propagate_field_access {
                    self.taint_for_place(place, local_taint)
                } else {
                    TaintLattice::bottom()
                }
            }
            Rvalue::AddressOf(_, place) => {
                if self.propagate_refs {
                    self.taint_for_place(place, local_taint)
                } else {
                    TaintLattice::bottom()
                }
            }
            Rvalue::Repeat(operand, _) => self.propagate_operand(operand, local_taint),
            // Trust: W2 inc-0 — the resulting pointer's taint depends on BOTH the
            // base pointer and the offset count (a real data dependency), so join
            // both, exactly like a `BinaryOp` value flow.
            Rvalue::PtrOffset { ptr, count } => {
                let p = self.propagate_operand(ptr, local_taint);
                let c = self.propagate_operand(count, local_taint);
                p.join(&c)
            }
            Rvalue::Unsupported { operands, .. } => {
                operands.iter().fold(TaintLattice::bottom(), |acc, operand| {
                    acc.join(&self.propagate_operand(operand, local_taint))
                })
            }
        }
    }

    /// Propagate taint through an operand.
    pub fn propagate_operand(
        &self,
        operand: &Operand,
        local_taint: &BTreeMap<usize, TaintLattice>,
    ) -> TaintLattice {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.taint_for_place(place, local_taint),
            Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => {
                TaintLattice::bottom()
            }
        }
    }

    /// Get the taint lattice element for a place.
    fn taint_for_place(
        &self,
        place: &Place,
        local_taint: &BTreeMap<usize, TaintLattice>,
    ) -> TaintLattice {
        local_taint.get(&place.local).cloned().unwrap_or_default()
    }
}

// ---------------------------------------------------------------------------
// TaintSeverity and TaintState: public per-variable taint tracking
// ---------------------------------------------------------------------------

/// Severity classification for a taint violation.
///
/// Used to prioritize which violations to address first and to filter
/// reports by severity threshold.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TaintSeverity {
    /// Informational: tainted data flows to a non-critical sink (e.g., debug log).
    Info,
    /// Warning: tainted data flows to a moderately sensitive sink.
    Warning,
    /// Error: tainted data flows to a security-critical sink (e.g., SQL, shell).
    Error,
    /// Critical: secret data flows to an external sink (exfiltration risk).
    Critical,
}

impl std::fmt::Display for TaintSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TaintSeverity::Info => write!(f, "info"),
            TaintSeverity::Warning => write!(f, "warning"),
            TaintSeverity::Error => write!(f, "error"),
            TaintSeverity::Critical => write!(f, "critical"),
        }
    }
}

impl TaintSeverity {
    /// Classify the severity of a taint flow from a given source label to a sink kind.
    pub fn classify(source: &TaintLabel, sink: &SinkKind) -> Self {
        match (source, sink) {
            // Secret data to any external sink is critical.
            (TaintLabel::Secret, SinkKind::LogOutput)
            | (TaintLabel::Secret, SinkKind::NetworkSend)
            | (TaintLabel::Secret, SinkKind::FileWrite) => TaintSeverity::Critical,
            // User/network input to injection-prone sinks is error.
            (TaintLabel::UserInput | TaintLabel::NetworkData, SinkKind::SqlQuery)
            | (TaintLabel::UserInput | TaintLabel::NetworkData, SinkKind::ShellCommand)
            | (TaintLabel::UserInput | TaintLabel::NetworkData, SinkKind::HtmlRender)
            | (TaintLabel::UserInput | TaintLabel::NetworkData, SinkKind::RawPointer) => {
                TaintSeverity::Error
            }
            // User/network input to log/network = warning (potential info leak).
            (TaintLabel::UserInput | TaintLabel::NetworkData, SinkKind::LogOutput)
            | (TaintLabel::UserInput | TaintLabel::NetworkData, SinkKind::NetworkSend) => {
                TaintSeverity::Warning
            }
            // Anything else is informational.
            _ => TaintSeverity::Info,
        }
    }
}

/// Per-variable taint state: tracks what labels are attached to a local
/// and where each label originated.
///
/// This is the public API for querying taint information about a specific
/// variable after analysis completes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TaintState {
    /// The local variable index.
    pub local: usize,
    /// Human-readable variable name, if known.
    pub name: Option<String>,
    /// Current taint labels attached to this variable.
    pub labels: BTreeSet<TaintLabel>,
    /// For each label, the source span where the taint originated.
    pub origins: BTreeMap<TaintLabel, SourceSpan>,
}

impl TaintState {
    /// Create a clean (untainted) state for a variable.
    pub fn clean(local: usize, name: Option<String>) -> Self {
        Self { local, name, labels: BTreeSet::new(), origins: BTreeMap::new() }
    }

    /// Returns true if this variable has no taint.
    pub fn is_clean(&self) -> bool {
        self.labels.is_empty()
    }

    /// Returns true if this variable carries a specific taint label.
    pub fn has_label(&self, label: &TaintLabel) -> bool {
        self.labels.contains(label)
    }

    /// Add a taint label with its origin span.
    pub fn add_taint(&mut self, label: TaintLabel, origin: SourceSpan) {
        self.labels.insert(label.clone());
        self.origins.entry(label).or_insert(origin);
    }

    /// Remove a taint label (sanitization).
    pub fn sanitize(&mut self, label: &TaintLabel) {
        self.labels.remove(label);
        self.origins.remove(label);
    }

    /// The worst-case severity if this variable reaches any of the given sink kinds.
    pub fn worst_severity(&self, sink_kinds: &[SinkKind]) -> Option<TaintSeverity> {
        let mut worst: Option<TaintSeverity> = None;
        for label in &self.labels {
            for sink in sink_kinds {
                let sev = TaintSeverity::classify(label, sink);
                worst = Some(match worst {
                    None => sev,
                    Some(w) if sev > w => sev,
                    Some(w) => w,
                });
            }
        }
        worst
    }

    /// Build TaintState entries from a completed TaintAnalysisResult.
    pub fn from_analysis(result: &TaintAnalysisResult, body: &VerifiableBody) -> Vec<Self> {
        body.locals
            .iter()
            .map(|decl| {
                let labels = result.tainted_locals.get(&decl.index).cloned().unwrap_or_default();
                let origins =
                    labels.iter().map(|label| (label.clone(), SourceSpan::default())).collect();
                TaintState { local: decl.index, name: decl.name.clone(), labels, origins }
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Internal analysis state
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct TaintTrace {
    source_span: SourceSpan,
    path: Vec<FlowStep>,
}

#[derive(Debug, Default)]
struct AnalysisState {
    tainted_locals: BTreeMap<usize, BTreeSet<TaintLabel>>,
    traces: BTreeMap<usize, BTreeMap<TaintLabel, TaintTrace>>,
    flow_edges: Vec<DataFlowEdge>,
    violations: Vec<TaintFlowViolation>,
}

impl AnalysisState {
    fn labels_for_local(&self, local: usize) -> BTreeSet<TaintLabel> {
        self.tainted_locals.get(&local).cloned().unwrap_or_default()
    }

    fn trace_for_label(&self, local: usize, label: &TaintLabel) -> Option<TaintTrace> {
        self.traces.get(&local).and_then(|labels| labels.get(label)).cloned()
    }

    fn write_place_taint(
        &mut self,
        place: &Place,
        labels: BTreeSet<TaintLabel>,
        traces: BTreeMap<TaintLabel, TaintTrace>,
    ) {
        if place.projections.is_empty() {
            if labels.is_empty() {
                self.tainted_locals.remove(&place.local);
                self.traces.remove(&place.local);
            } else {
                self.tainted_locals.insert(place.local, labels);
                self.traces.insert(place.local, traces);
            }
            return;
        }

        if labels.is_empty() {
            return;
        }

        self.tainted_locals.entry(place.local).or_default().extend(labels);
        self.traces.entry(place.local).or_default().extend(traces);
    }

    fn into_result(self) -> TaintAnalysisResult {
        TaintAnalysisResult {
            violations: self.violations,
            tainted_locals: self.tainted_locals,
            flow_edges: self.flow_edges,
        }
    }
}

// ---------------------------------------------------------------------------
// Main analysis entry point
// ---------------------------------------------------------------------------

/// Run the experimental, best-effort taint diagnostic.
///
/// This function processes `body.blocks` once in storage order with a single
/// mutable state. It does not join predecessor states or iterate loops to a
/// fixpoint, and source/sink/sanitizer policies use callee-name substring
/// matching. Consequently it can both miss flows and match the wrong callable;
/// in particular, a similarly named sanitizer can incorrectly clear taint.
///
/// Do not use an empty violation set as a proof of noninterference or as a
/// compiler acceptance verdict. A production analysis must operate on the
/// TrustIR CFG, join incoming states, reach a loop fixpoint, and use exact
/// resolved callee identities.
pub fn analyze_taint(body: &VerifiableBody, policy: &TaintPolicy) -> TaintAnalysisResult {
    let mut state = AnalysisState::default();

    for block in &body.blocks {
        let block_id = block.id.0;

        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                analyze_assign(&mut state, block_id, place, rvalue);
            }
        }

        if let Terminator::Call { func, args, dest, span, .. } = &block.terminator {
            analyze_call(&mut state, policy, block_id, func, args, dest, span);
        }
    }

    state.into_result()
}

pub fn default_web_policy() -> TaintPolicy {
    TaintPolicy {
        sources: vec![
            TaintSource { label: TaintLabel::UserInput, pattern: "read_line".into() },
            TaintSource { label: TaintLabel::NetworkData, pattern: "recv".into() },
            TaintSource { label: TaintLabel::UserInput, pattern: "env::var".into() },
            TaintSource { label: TaintLabel::UserInput, pattern: "stdin".into() },
            TaintSource { label: TaintLabel::FileData, pattern: "fs::read".into() },
            TaintSource { label: TaintLabel::EnvVar, pattern: "env::var".into() },
            TaintSource { label: TaintLabel::ExternCall, pattern: "extern_fn".into() },
        ],
        sinks: vec![
            TaintSink { label: SinkKind::SqlQuery, pattern: "execute_sql".into() },
            TaintSink { label: SinkKind::HtmlRender, pattern: "write_html".into() },
            TaintSink { label: SinkKind::LogOutput, pattern: "log".into() },
            TaintSink { label: SinkKind::NetworkSend, pattern: "send".into() },
            TaintSink { label: SinkKind::ShellCommand, pattern: "exec_cmd".into() },
            TaintSink { label: SinkKind::FileWrite, pattern: "fs::write".into() },
        ],
        sanitizers: vec![
            Sanitizer { removes: TaintLabel::UserInput, pattern: "escape_html".into() },
            Sanitizer { removes: TaintLabel::UserInput, pattern: "prepared_statement".into() },
            Sanitizer { removes: TaintLabel::UserInput, pattern: "validate".into() },
            Sanitizer { removes: TaintLabel::NetworkData, pattern: "validate".into() },
        ],
    }
}

// ---------------------------------------------------------------------------
// Internal analysis helpers
// ---------------------------------------------------------------------------

fn analyze_assign(state: &mut AnalysisState, block_id: usize, place: &Place, rvalue: &Rvalue) {
    let mut labels = BTreeSet::new();
    let mut traces = BTreeMap::new();

    for (source_local, kind) in rvalue_sources(rvalue) {
        state.flow_edges.push(DataFlowEdge {
            from_local: source_local,
            to_local: place.local,
            block: block_id,
            kind,
        });
        record_local_flow(
            state,
            source_local,
            place.local,
            block_id,
            assign_description(kind, source_local, place.local),
            &mut labels,
            &mut traces,
        );
    }

    state.write_place_taint(place, labels, traces);
}

fn analyze_call(
    state: &mut AnalysisState,
    policy: &TaintPolicy,
    block_id: usize,
    func: &str,
    args: &[Operand],
    dest: &Place,
    span: &SourceSpan,
) {
    for source_local in operand_locals(args) {
        state.flow_edges.push(DataFlowEdge {
            from_local: source_local,
            to_local: dest.local,
            block: block_id,
            kind: FlowKind::CallArgument,
        });
    }

    for sink in policy.sinks.iter().filter(|sink| func.contains(&sink.pattern)) {
        record_sink_violations(state, block_id, func, args, span, sink);
    }

    let mut result_labels = BTreeSet::new();
    let mut result_traces = BTreeMap::new();

    for source_local in operand_locals(args) {
        state.flow_edges.push(DataFlowEdge {
            from_local: source_local,
            to_local: dest.local,
            block: block_id,
            kind: FlowKind::CallReturn,
        });
        record_local_flow(
            state,
            source_local,
            dest.local,
            block_id,
            format!("local _{} receives call result from `{}`", dest.local, func),
            &mut result_labels,
            &mut result_traces,
        );
    }

    for source in policy.sources.iter().filter(|source| func.contains(&source.pattern)) {
        result_labels.insert(source.label.clone());
        result_traces.entry(source.label.clone()).or_insert_with(|| TaintTrace {
            source_span: span.clone(),
            path: vec![FlowStep {
                local: dest.local,
                block: block_id,
                description: format!(
                    "local _{} becomes {} from source `{}`",
                    dest.local,
                    taint_label_name(&source.label),
                    source.pattern
                ),
            }],
        });
    }

    for sanitizer in policy.sanitizers.iter().filter(|sanitizer| func.contains(&sanitizer.pattern))
    {
        result_labels.remove(&sanitizer.removes);
        result_traces.remove(&sanitizer.removes);
    }

    state.write_place_taint(dest, result_labels, result_traces);
}

fn record_local_flow(
    state: &AnalysisState,
    source_local: usize,
    dest_local: usize,
    block_id: usize,
    description: String,
    labels: &mut BTreeSet<TaintLabel>,
    traces: &mut BTreeMap<TaintLabel, TaintTrace>,
) {
    for label in state.labels_for_local(source_local) {
        labels.insert(label.clone());
        traces.entry(label.clone()).or_insert_with(|| {
            let mut trace = state
                .trace_for_label(source_local, &label)
                .unwrap_or(TaintTrace { source_span: SourceSpan::default(), path: vec![] });
            trace.path.push(FlowStep {
                local: dest_local,
                block: block_id,
                description: description.clone(),
            });
            trace
        });
    }
}

fn record_sink_violations(
    state: &mut AnalysisState,
    block_id: usize,
    func: &str,
    args: &[Operand],
    span: &SourceSpan,
    sink: &TaintSink,
) {
    for operand in args {
        let Some(place) = operand_place(operand) else {
            continue;
        };

        for label in state.labels_for_local(place.local) {
            let trace = state
                .trace_for_label(place.local, &label)
                .unwrap_or(TaintTrace { source_span: SourceSpan::default(), path: vec![] });
            let mut path = trace.path.clone();
            path.push(FlowStep {
                local: place.local,
                block: block_id,
                description: format!(
                    "local _{} reaches {} sink `{}`",
                    place.local,
                    sink_kind_name(&sink.label),
                    func
                ),
            });
            state.violations.push(TaintFlowViolation {
                source_label: label,
                sink_kind: sink.label.clone(),
                sink_func: func.to_string(),
                path,
                source_span: trace.source_span,
                sink_span: span.clone(),
            });
        }
    }
}

fn rvalue_sources(rvalue: &Rvalue) -> Vec<(usize, FlowKind)> {
    match rvalue {
        Rvalue::Use(operand) | Rvalue::Cast(operand, _) | Rvalue::UnaryOp(_, operand) => {
            operand_local(operand)
                .map(|local| (local, operand_flow_kind(operand, FlowKind::Assignment)))
                .into_iter()
                .collect()
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => [lhs, rhs]
            .into_iter()
            .filter_map(|operand| {
                operand_local(operand)
                    .map(|local| (local, operand_flow_kind(operand, FlowKind::Assignment)))
            })
            .collect(),
        Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) => {
            vec![(place.local, FlowKind::Ref)]
        }
        Rvalue::Aggregate(_, operands) => operands
            .iter()
            .filter_map(|operand| {
                operand_local(operand)
                    .map(|local| (local, operand_flow_kind(operand, FlowKind::Assignment)))
            })
            .collect(),
        Rvalue::Repeat(operand, _) => operand_local(operand)
            .map(|local| (local, operand_flow_kind(operand, FlowKind::Assignment)))
            .into_iter()
            .collect(),
        Rvalue::Discriminant(place) | Rvalue::Len(place) | Rvalue::CopyForDeref(place) => {
            vec![(place.local, place_flow_kind(place, FlowKind::Assignment))]
        }
        // Trust: W2 inc-0 — pointer arithmetic sources flow from BOTH operands.
        Rvalue::PtrOffset { ptr, count } => [ptr, count]
            .into_iter()
            .filter_map(|operand| {
                operand_local(operand)
                    .map(|local| (local, operand_flow_kind(operand, FlowKind::Assignment)))
            })
            .collect(),
        Rvalue::Unsupported { operands, .. } => operands
            .iter()
            .filter_map(|operand| {
                operand_local(operand)
                    .map(|local| (local, operand_flow_kind(operand, FlowKind::Assignment)))
            })
            .collect(),
    }
}

fn operand_locals(args: &[Operand]) -> Vec<usize> {
    args.iter().filter_map(operand_local).collect()
}

fn operand_local(operand: &Operand) -> Option<usize> {
    operand_place(operand).map(|place| place.local)
}

fn operand_place(operand: &Operand) -> Option<&Place> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => None,
    }
}

fn operand_flow_kind(operand: &Operand, default: FlowKind) -> FlowKind {
    operand_place(operand).map(|place| place_flow_kind(place, default)).unwrap_or(default)
}

fn place_flow_kind(place: &Place, default: FlowKind) -> FlowKind {
    if place.projections.is_empty() { default } else { FlowKind::FieldAccess }
}

fn assign_description(kind: FlowKind, source_local: usize, dest_local: usize) -> String {
    match kind {
        FlowKind::Assignment => {
            format!("local _{} is assigned from local _{}", dest_local, source_local)
        }
        FlowKind::FieldAccess => {
            format!("local _{} is derived from projected local _{}", dest_local, source_local)
        }
        FlowKind::Ref => {
            format!("local _{} references local _{}", dest_local, source_local)
        }
        FlowKind::CallArgument | FlowKind::CallReturn => {
            format!("local _{} is updated from local _{}", dest_local, source_local)
        }
    }
}

fn taint_label_name(label: &TaintLabel) -> String {
    match label {
        TaintLabel::UserInput => "user input".into(),
        TaintLabel::NetworkData => "network data".into(),
        TaintLabel::Secret => "secret".into(),
        TaintLabel::FileData => "file data".into(),
        TaintLabel::EnvVar => "environment variable".into(),
        TaintLabel::UnsafeBlock => "unsafe block".into(),
        TaintLabel::ExternCall => "extern call".into(),
        TaintLabel::Custom(name) => name.clone(),
    }
}

fn sink_kind_name(kind: &SinkKind) -> String {
    match kind {
        SinkKind::SqlQuery => "SQL".into(),
        SinkKind::LogOutput => "log".into(),
        SinkKind::NetworkSend => "network".into(),
        SinkKind::HtmlRender => "HTML".into(),
        SinkKind::FileWrite => "file write".into(),
        SinkKind::ShellCommand => "shell command".into(),
        SinkKind::RawPointer => "raw pointer".into(),
        SinkKind::Assertion => "assertion".into(),
        SinkKind::Custom(name) => name.clone(),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    fn span(line: u32) -> SourceSpan {
        SourceSpan {
            file: "taint.rs".into(),
            line_start: line,
            col_start: 1,
            line_end: line,
            col_end: 10,
        }
    }

    fn local(index: usize, name: &str, ty: Ty) -> LocalDecl {
        LocalDecl { index, ty, name: Some(name.into()) }
    }

    fn taint_body(blocks: Vec<BasicBlock>, locals: Vec<LocalDecl>) -> VerifiableBody {
        VerifiableBody { locals, blocks, arg_count: 0, return_ty: Ty::Unit }
    }

    // -------------------------------------------------------------------
    // Experimental untrusted-to-verdict policy coverage. This validates the
    // current heuristic engine behavior; it is not a production wiring or
    // soundness test.
    // -------------------------------------------------------------------

    /// A synthetic untrusted-to-verdict policy with a source, sink, and
    /// sanitizer substring.
    fn untrusted_verdict_policy() -> TaintPolicy {
        TaintPolicy {
            sources: vec![TaintSource {
                label: TaintLabel::Custom("untrusted".into()),
                pattern: "parse_cert".into(),
            }],
            sinks: vec![TaintSink {
                label: SinkKind::Custom("verdict".into()),
                pattern: "accept".into(),
            }],
            sanitizers: vec![Sanitizer {
                removes: TaintLabel::Custom("untrusted".into()),
                pattern: "rederive_from_subject".into(),
            }],
        }
    }

    fn ivcall(func: &str, args: Vec<Operand>, dest: usize, at: u32, next: usize) -> Terminator {
        Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: false, is_foreign: false,
            func: func.into(),
            args,
            dest: Place::local(dest),
            target: Some(BlockId(next)),
            span: span(at),
            atomic: None,
        }
    }
    /// `L1 = parse_cert()` — seed the untrusted source into local 1.
    fn ivall_seed() -> Terminator {
        ivcall("parse_cert", vec![], 1, 10, 1)
    }
    /// `accept(local[from])` — the verdict sink consuming local `from`.
    fn ivcall_accept(from: usize) -> Terminator {
        ivcall("accept", vec![Operand::Copy(Place::local(from))], 0, 20, 2)
    }

    #[test]
    fn untrusted_field_reaching_verdict_is_a_violation() {
        // L1 = parse_cert(input);  accept(L1)  — the forgery shape: a parsed
        // certificate field flows straight into the accept decision.
        let body = taint_body(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: ivall_seed(),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: ivcall_accept(1),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![local(0, "ret", Ty::Unit), local(1, "field", Ty::usize()), local(2, "v", Ty::Unit)],
        );
        let result = analyze_taint(&body, &untrusted_verdict_policy());
        let leaks: Vec<_> = result
            .violations
            .iter()
            .filter(|v| {
                matches!(&v.sink_kind, SinkKind::Custom(k) if k == "verdict")
                    && matches!(&v.source_label, TaintLabel::Custom(l) if l == "untrusted")
            })
            .collect();
        assert_eq!(leaks.len(), 1, "untrusted->verdict must be flagged; got {:?}", result.violations);
    }

    #[test]
    fn rederived_value_reaching_verdict_is_clean() {
        // L1 = parse_cert(input);
        // L2 = rederive_from_subject(input);   // declassifier, fresh local
        // accept(L2)                            // feed the RE-DERIVED value
        let body = taint_body(
            vec![
                BasicBlock { id: BlockId(0), stmts: vec![], terminator: ivall_seed() },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: ivcall("rederive_from_subject", vec![Operand::Copy(Place::local(0))], 2, 15, 2),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: ivcall_accept(2) },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![
                local(0, "input", Ty::usize()),
                local(1, "field", Ty::usize()),
                local(2, "rederived", Ty::usize()),
                local(3, "v", Ty::Unit),
            ],
        );
        let result = analyze_taint(&body, &untrusted_verdict_policy());
        let leaks = result.violations.iter().filter(|v| {
            matches!(&v.sink_kind, SinkKind::Custom(k) if k == "verdict")
        });
        assert_eq!(leaks.count(), 0, "a re-derived value must NOT be flagged; got {:?}", result.violations);
    }

    // -------------------------------------------------------------------
    // Existing tests (preserved)
    // -------------------------------------------------------------------

    #[test]
    fn test_tainted_data_reaches_sql_sink() {
        let body = taint_body(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::io::read_line".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "db::execute_sql".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: span(20),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![local(0, "ret", Ty::Unit), local(1, "input", Ty::usize())],
        );

        let result = analyze_taint(&body, &default_web_policy());

        assert_eq!(result.violations.len(), 1);
        assert!(matches!(result.violations[0].source_label, TaintLabel::UserInput));
        assert!(matches!(result.violations[0].sink_kind, SinkKind::SqlQuery));
        assert_eq!(result.violations[0].source_span.line_start, 10);
        assert_eq!(result.violations[0].sink_span.line_start, 20);
        assert!(result.violations[0].path.len() >= 2);
    }

    #[test]
    fn test_sanitized_data_is_clean() {
        let body = taint_body(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::io::read_line".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "web::escape_html".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(2)),
                        span: span(15),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "db::execute_sql".into(),
                        args: vec![Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(3)),
                        span: span(20),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![
                local(0, "ret", Ty::Unit),
                local(1, "raw", Ty::usize()),
                local(2, "clean", Ty::usize()),
            ],
        );

        let result = analyze_taint(&body, &default_web_policy());

        assert!(result.violations.is_empty());
        assert!(!result.tainted_locals.contains_key(&2));
    }

    #[test]
    fn test_secret_leakage_to_log() {
        let mut policy = default_web_policy();
        policy
            .sources
            .push(TaintSource { label: TaintLabel::Secret, pattern: "get_secret".into() });

        let body = taint_body(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "secrets::get_secret".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "audit::log".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: span(20),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![local(0, "ret", Ty::Unit), local(1, "secret", Ty::usize())],
        );

        let result = analyze_taint(&body, &policy);

        assert_eq!(result.violations.len(), 1);
        assert!(matches!(result.violations[0].source_label, TaintLabel::Secret));
        assert!(matches!(result.violations[0].sink_kind, SinkKind::LogOutput));
    }

    #[test]
    fn test_clean_constant_flow() {
        let body = taint_body(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
                        span: span(10),
                    }],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "db::execute_sql".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: span(20),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![local(0, "ret", Ty::Unit), local(1, "value", Ty::i32())],
        );

        let result = analyze_taint(&body, &default_web_policy());

        assert!(result.violations.is_empty());
        assert!(result.tainted_locals.is_empty());
    }

    #[test]
    fn test_taint_propagation_through_assignment() {
        let body = taint_body(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::io::read_line".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span(15),
                    }],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "db::execute_sql".into(),
                        args: vec![Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: span(20),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![
                local(0, "ret", Ty::Unit),
                local(1, "input", Ty::usize()),
                local(2, "query", Ty::usize()),
            ],
        );

        let result = analyze_taint(&body, &default_web_policy());

        assert_eq!(result.violations.len(), 1);
        assert!(result.flow_edges.iter().any(|edge| {
            edge.from_local == 1
                && edge.to_local == 2
                && edge.block == 1
                && edge.kind == FlowKind::Assignment
        }));
        assert!(matches!(
            result.tainted_locals.get(&2),
            Some(labels) if labels.contains(&TaintLabel::UserInput)
        ));
    }

    #[test]
    fn test_multiple_violations_detected() {
        let mut policy = default_web_policy();
        policy
            .sources
            .push(TaintSource { label: TaintLabel::Secret, pattern: "get_secret".into() });

        let body = taint_body(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::io::read_line".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "secrets::get_secret".into(),
                        args: vec![],
                        dest: Place::local(2),
                        target: Some(BlockId(2)),
                        span: span(15),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "db::execute_sql".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(3)),
                        span: span(20),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "audit::log".into(),
                        args: vec![Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(4)),
                        span: span(25),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![
                local(0, "ret", Ty::Unit),
                local(1, "user_input", Ty::usize()),
                local(2, "secret", Ty::usize()),
            ],
        );

        let result = analyze_taint(&body, &policy);

        assert_eq!(result.violations.len(), 2);
        assert!(
            result
                .violations
                .iter()
                .any(|violation| matches!(violation.sink_kind, SinkKind::SqlQuery))
        );
        assert!(
            result
                .violations
                .iter()
                .any(|violation| matches!(violation.sink_kind, SinkKind::LogOutput))
        );
    }

    #[test]
    fn test_serialization_roundtrip() {
        let body = taint_body(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::io::read_line".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "db::execute_sql".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: span(20),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![local(0, "ret", Ty::Unit), local(1, "input", Ty::usize())],
        );

        let result = analyze_taint(&body, &default_web_policy());
        let json = serde_json::to_string(&result).expect("serialize result");
        let roundtrip: TaintAnalysisResult =
            serde_json::from_str(&json).expect("deserialize result");

        assert_eq!(roundtrip.violations.len(), result.violations.len());
        assert_eq!(roundtrip.flow_edges.len(), result.flow_edges.len());
        assert!(matches!(
            roundtrip.tainted_locals.get(&1),
            Some(labels) if labels.contains(&TaintLabel::UserInput)
        ));
    }

    #[test]
    fn test_default_web_policy_has_patterns() {
        let policy = default_web_policy();

        assert!(policy.sources.iter().any(|source| source.pattern == "read_line"));
        assert!(policy.sources.iter().any(|source| source.pattern == "recv"));
        assert!(policy.sources.iter().any(|source| source.pattern == "env::var"));
        assert!(policy.sources.iter().any(|source| source.pattern == "stdin"));
        assert!(policy.sinks.iter().any(|sink| sink.pattern == "execute_sql"));
        assert!(policy.sinks.iter().any(|sink| sink.pattern == "write_html"));
        assert!(policy.sinks.iter().any(|sink| sink.pattern == "log"));
        assert!(policy.sinks.iter().any(|sink| sink.pattern == "send"));
        assert!(policy.sanitizers.iter().any(|sanitizer| sanitizer.pattern == "escape_html"));
        assert!(
            policy.sanitizers.iter().any(|sanitizer| sanitizer.pattern == "prepared_statement")
        );
        assert!(policy.sanitizers.iter().any(|sanitizer| sanitizer.pattern == "validate"));
    }

    // -------------------------------------------------------------------
    // New tests: TaintLattice
    // -------------------------------------------------------------------

    #[test]
    fn test_lattice_bottom_is_empty() {
        let bot = TaintLattice::bottom();
        assert!(bot.is_bottom());
        assert!(bot.is_empty());
        assert_eq!(bot.len(), 0);
    }

    #[test]
    fn test_lattice_top_has_all_standard_labels() {
        let top = TaintLattice::top();
        assert!(!top.is_bottom());
        assert!(top.contains(&TaintLabel::UserInput));
        assert!(top.contains(&TaintLabel::NetworkData));
        assert!(top.contains(&TaintLabel::Secret));
        assert!(top.contains(&TaintLabel::FileData));
        assert!(top.contains(&TaintLabel::EnvVar));
        assert!(top.contains(&TaintLabel::UnsafeBlock));
        assert!(top.contains(&TaintLabel::ExternCall));
        assert_eq!(top.len(), 7);
    }

    #[test]
    fn test_lattice_singleton() {
        let s = TaintLattice::singleton(TaintLabel::Secret);
        assert_eq!(s.len(), 1);
        assert!(s.contains(&TaintLabel::Secret));
        assert!(!s.contains(&TaintLabel::UserInput));
    }

    #[test]
    fn test_lattice_join_is_union() {
        let a = TaintLattice::singleton(TaintLabel::UserInput);
        let b = TaintLattice::singleton(TaintLabel::Secret);
        let joined = a.join(&b);
        assert_eq!(joined.len(), 2);
        assert!(joined.contains(&TaintLabel::UserInput));
        assert!(joined.contains(&TaintLabel::Secret));
    }

    #[test]
    fn test_lattice_meet_is_intersection() {
        let a = TaintLattice::from_set(BTreeSet::from([TaintLabel::UserInput, TaintLabel::Secret]));
        let b = TaintLattice::from_set(BTreeSet::from([TaintLabel::Secret, TaintLabel::FileData]));
        let met = a.meet(&b);
        assert_eq!(met.len(), 1);
        assert!(met.contains(&TaintLabel::Secret));
    }

    #[test]
    fn test_lattice_join_with_bottom_is_identity() {
        let a = TaintLattice::singleton(TaintLabel::NetworkData);
        let bot = TaintLattice::bottom();
        assert_eq!(a.join(&bot), a);
        assert_eq!(bot.join(&a), a);
    }

    #[test]
    fn test_lattice_meet_with_bottom_is_bottom() {
        let a = TaintLattice::singleton(TaintLabel::NetworkData);
        let bot = TaintLattice::bottom();
        let met = a.meet(&bot);
        assert!(met.is_bottom());
    }

    #[test]
    fn test_lattice_join_with_top_is_top() {
        let a = TaintLattice::singleton(TaintLabel::UserInput);
        let top = TaintLattice::top();
        let joined = a.join(&top);
        // The join with top should contain everything top has.
        assert!(top.is_subset_of(&joined));
    }

    #[test]
    fn test_lattice_meet_with_top_is_self() {
        let a = TaintLattice::singleton(TaintLabel::UserInput);
        let top = TaintLattice::top();
        let met = a.meet(&top);
        assert_eq!(met, a);
    }

    #[test]
    fn test_lattice_join_idempotent() {
        let a = TaintLattice::from_set(BTreeSet::from([TaintLabel::UserInput, TaintLabel::Secret]));
        assert_eq!(a.join(&a), a);
    }

    #[test]
    fn test_lattice_meet_idempotent() {
        let a = TaintLattice::from_set(BTreeSet::from([TaintLabel::UserInput, TaintLabel::Secret]));
        assert_eq!(a.meet(&a), a);
    }

    #[test]
    fn test_lattice_join_commutative() {
        let a = TaintLattice::singleton(TaintLabel::UserInput);
        let b = TaintLattice::singleton(TaintLabel::Secret);
        assert_eq!(a.join(&b), b.join(&a));
    }

    #[test]
    fn test_lattice_meet_commutative() {
        let a = TaintLattice::from_set(BTreeSet::from([TaintLabel::UserInput, TaintLabel::Secret]));
        let b = TaintLattice::from_set(BTreeSet::from([TaintLabel::Secret, TaintLabel::FileData]));
        assert_eq!(a.meet(&b), b.meet(&a));
    }

    #[test]
    fn test_lattice_join_associative() {
        let a = TaintLattice::singleton(TaintLabel::UserInput);
        let b = TaintLattice::singleton(TaintLabel::Secret);
        let c = TaintLattice::singleton(TaintLabel::FileData);
        assert_eq!(a.join(&b).join(&c), a.join(&b.join(&c)));
    }

    #[test]
    fn test_lattice_subset_ordering() {
        let a = TaintLattice::singleton(TaintLabel::UserInput);
        let b = TaintLattice::from_set(BTreeSet::from([TaintLabel::UserInput, TaintLabel::Secret]));
        assert!(a.is_subset_of(&b));
        assert!(!b.is_subset_of(&a));
    }

    #[test]
    fn test_lattice_add_and_remove() {
        let mut lat = TaintLattice::bottom();
        lat.add(TaintLabel::UserInput);
        lat.add(TaintLabel::Secret);
        assert_eq!(lat.len(), 2);
        lat.remove(&TaintLabel::UserInput);
        assert_eq!(lat.len(), 1);
        assert!(lat.contains(&TaintLabel::Secret));
        assert!(!lat.contains(&TaintLabel::UserInput));
    }

    #[test]
    fn test_lattice_serialization_roundtrip() {
        let lat = TaintLattice::from_set(BTreeSet::from([
            TaintLabel::UserInput,
            TaintLabel::Secret,
            TaintLabel::FileData,
        ]));
        let json = serde_json::to_string(&lat).expect("serialize");
        let round: TaintLattice = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(lat, round);
    }

    #[test]
    fn test_lattice_into_labels() {
        let lat = TaintLattice::from_set(BTreeSet::from([
            TaintLabel::UserInput,
            TaintLabel::NetworkData,
        ]));
        let labels = lat.into_labels();
        assert_eq!(labels.len(), 2);
        assert!(labels.contains(&TaintLabel::UserInput));
        assert!(labels.contains(&TaintLabel::NetworkData));
    }

    // -------------------------------------------------------------------
    // New tests: TaintPropagator
    // -------------------------------------------------------------------

    #[test]
    fn test_propagator_constant_has_no_taint() {
        let prop = TaintPropagator::default();
        let taint_map = BTreeMap::new();

        let result = prop.propagate_operand(&Operand::Constant(ConstValue::Int(42)), &taint_map);
        assert!(result.is_bottom());
    }

    #[test]
    fn test_propagator_copy_propagates_taint() {
        let prop = TaintPropagator::default();
        let mut taint_map = BTreeMap::new();
        taint_map.insert(1, TaintLattice::singleton(TaintLabel::UserInput));

        let result = prop.propagate_operand(&Operand::Copy(Place::local(1)), &taint_map);
        assert!(result.contains(&TaintLabel::UserInput));
    }

    #[test]
    fn test_propagator_binary_op_joins_both_operands() {
        let prop = TaintPropagator::default();
        let mut taint_map = BTreeMap::new();
        taint_map.insert(1, TaintLattice::singleton(TaintLabel::UserInput));
        taint_map.insert(2, TaintLattice::singleton(TaintLabel::Secret));

        let rvalue = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        );

        let result = prop.propagate_rvalue(&rvalue, &taint_map);
        assert!(result.contains(&TaintLabel::UserInput));
        assert!(result.contains(&TaintLabel::Secret));
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_propagator_cast_preserves_taint() {
        let prop = TaintPropagator::default();
        let mut taint_map = BTreeMap::new();
        taint_map.insert(1, TaintLattice::singleton(TaintLabel::NetworkData));

        let rvalue = Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i32());
        let result = prop.propagate_rvalue(&rvalue, &taint_map);
        assert!(result.contains(&TaintLabel::NetworkData));
    }

    #[test]
    fn test_propagator_cast_disabled_drops_taint() {
        let prop = TaintPropagator { propagate_casts: false, ..TaintPropagator::default() };
        let mut taint_map = BTreeMap::new();
        taint_map.insert(1, TaintLattice::singleton(TaintLabel::NetworkData));

        let rvalue = Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i32());
        let result = prop.propagate_rvalue(&rvalue, &taint_map);
        assert!(result.is_bottom());
    }

    #[test]
    fn test_propagator_ref_propagates_taint() {
        let prop = TaintPropagator::default();
        let mut taint_map = BTreeMap::new();
        taint_map.insert(1, TaintLattice::singleton(TaintLabel::FileData));

        let rvalue = Rvalue::Ref { mutable: false, place: Place::local(1) };
        let result = prop.propagate_rvalue(&rvalue, &taint_map);
        assert!(result.contains(&TaintLabel::FileData));
    }

    #[test]
    fn test_propagator_aggregate_joins_all_operands() {
        let prop = TaintPropagator::default();
        let mut taint_map = BTreeMap::new();
        taint_map.insert(1, TaintLattice::singleton(TaintLabel::UserInput));
        taint_map.insert(2, TaintLattice::singleton(TaintLabel::Secret));

        let rvalue = Rvalue::Aggregate(
            AggregateKind::Tuple,
            vec![
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Int(0)),
            ],
        );

        let result = prop.propagate_rvalue(&rvalue, &taint_map);
        assert!(result.contains(&TaintLabel::UserInput));
        assert!(result.contains(&TaintLabel::Secret));
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_propagator_untainted_local_returns_bottom() {
        let prop = TaintPropagator::default();
        let taint_map = BTreeMap::new(); // no locals are tainted

        let result = prop.propagate_operand(&Operand::Copy(Place::local(5)), &taint_map);
        assert!(result.is_bottom());
    }

    #[test]
    fn test_propagator_binary_op_disabled() {
        let prop = TaintPropagator { propagate_binary_ops: false, ..TaintPropagator::default() };
        let mut taint_map = BTreeMap::new();
        taint_map.insert(1, TaintLattice::singleton(TaintLabel::UserInput));

        let rvalue = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Int(1)),
        );

        let result = prop.propagate_rvalue(&rvalue, &taint_map);
        assert!(result.is_bottom());
    }

    // -------------------------------------------------------------------
    // New tests: new TaintLabel variants and SinkKind variants
    // -------------------------------------------------------------------

    #[test]
    fn test_new_taint_label_names() {
        assert_eq!(taint_label_name(&TaintLabel::EnvVar), "environment variable");
        assert_eq!(taint_label_name(&TaintLabel::UnsafeBlock), "unsafe block");
        assert_eq!(taint_label_name(&TaintLabel::ExternCall), "extern call");
    }

    #[test]
    fn test_new_sink_kind_names() {
        assert_eq!(sink_kind_name(&SinkKind::ShellCommand), "shell command");
        assert_eq!(sink_kind_name(&SinkKind::RawPointer), "raw pointer");
        assert_eq!(sink_kind_name(&SinkKind::Assertion), "assertion");
    }

    #[test]
    fn test_taint_label_serialization_roundtrip_all_variants() {
        let labels = [
            TaintLabel::UserInput,
            TaintLabel::NetworkData,
            TaintLabel::Secret,
            TaintLabel::FileData,
            TaintLabel::EnvVar,
            TaintLabel::UnsafeBlock,
            TaintLabel::ExternCall,
            TaintLabel::Custom("test".into()),
        ];
        for label in &labels {
            let json = serde_json::to_string(label).expect("serialize");
            let round: TaintLabel = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(*label, round);
        }
    }

    #[test]
    fn test_sink_kind_serialization_roundtrip_all_variants() {
        let kinds = [
            SinkKind::SqlQuery,
            SinkKind::LogOutput,
            SinkKind::NetworkSend,
            SinkKind::HtmlRender,
            SinkKind::FileWrite,
            SinkKind::ShellCommand,
            SinkKind::RawPointer,
            SinkKind::Assertion,
            SinkKind::Custom("test".into()),
        ];
        for kind in &kinds {
            let json = serde_json::to_string(kind).expect("serialize");
            let round: SinkKind = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(*kind, round);
        }
    }

    #[test]
    fn test_shell_command_sink_detection() {
        let body = taint_body(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::io::read_line".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::process::exec_cmd".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: span(20),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![local(0, "ret", Ty::Unit), local(1, "cmd", Ty::usize())],
        );

        let result = analyze_taint(&body, &default_web_policy());

        assert_eq!(result.violations.len(), 1);
        assert!(matches!(result.violations[0].sink_kind, SinkKind::ShellCommand));
    }

    #[test]
    fn test_enhanced_policy_has_new_patterns() {
        let policy = default_web_policy();

        // New source patterns
        assert!(policy.sources.iter().any(|s| s.label == TaintLabel::FileData));
        assert!(policy.sources.iter().any(|s| s.label == TaintLabel::EnvVar));
        assert!(policy.sources.iter().any(|s| s.label == TaintLabel::ExternCall));

        // New sink patterns
        assert!(policy.sinks.iter().any(|s| s.label == SinkKind::ShellCommand));
        assert!(policy.sinks.iter().any(|s| s.label == SinkKind::FileWrite));
    }

    #[test]
    fn test_taint_label_ord_is_deterministic() {
        // Verify ordering is deterministic for BTreeSet usage.
        let mut labels = vec![
            TaintLabel::Secret,
            TaintLabel::UserInput,
            TaintLabel::FileData,
            TaintLabel::NetworkData,
        ];
        let sorted1 = {
            labels.sort();
            labels.clone()
        };
        labels.reverse();
        labels.sort();
        assert_eq!(sorted1, labels);
    }

    // -------------------------------------------------------------------
    // New tests: TaintSeverity
    // -------------------------------------------------------------------

    #[test]
    fn test_taint_severity_display() {
        assert_eq!(TaintSeverity::Info.to_string(), "info");
        assert_eq!(TaintSeverity::Warning.to_string(), "warning");
        assert_eq!(TaintSeverity::Error.to_string(), "error");
        assert_eq!(TaintSeverity::Critical.to_string(), "critical");
    }

    #[test]
    fn test_taint_severity_ordering() {
        assert!(TaintSeverity::Info < TaintSeverity::Warning);
        assert!(TaintSeverity::Warning < TaintSeverity::Error);
        assert!(TaintSeverity::Error < TaintSeverity::Critical);
    }

    #[test]
    fn test_taint_severity_classify_critical() {
        // Secret to log = critical.
        assert_eq!(
            TaintSeverity::classify(&TaintLabel::Secret, &SinkKind::LogOutput),
            TaintSeverity::Critical
        );
        // Secret to network send = critical.
        assert_eq!(
            TaintSeverity::classify(&TaintLabel::Secret, &SinkKind::NetworkSend),
            TaintSeverity::Critical
        );
    }

    #[test]
    fn test_taint_severity_classify_error() {
        // User input to SQL = error.
        assert_eq!(
            TaintSeverity::classify(&TaintLabel::UserInput, &SinkKind::SqlQuery),
            TaintSeverity::Error
        );
        // Network data to shell command = error.
        assert_eq!(
            TaintSeverity::classify(&TaintLabel::NetworkData, &SinkKind::ShellCommand),
            TaintSeverity::Error
        );
    }

    #[test]
    fn test_taint_severity_classify_warning() {
        // User input to log = warning.
        assert_eq!(
            TaintSeverity::classify(&TaintLabel::UserInput, &SinkKind::LogOutput),
            TaintSeverity::Warning
        );
    }

    #[test]
    fn test_taint_severity_classify_info() {
        // FileData to assertion = info.
        assert_eq!(
            TaintSeverity::classify(&TaintLabel::FileData, &SinkKind::Assertion),
            TaintSeverity::Info
        );
    }

    #[test]
    fn test_taint_severity_serialization_roundtrip() {
        let severities = [
            TaintSeverity::Info,
            TaintSeverity::Warning,
            TaintSeverity::Error,
            TaintSeverity::Critical,
        ];
        for sev in &severities {
            let json = serde_json::to_string(sev).expect("serialize");
            let round: TaintSeverity = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(*sev, round);
        }
    }

    // -------------------------------------------------------------------
    // New tests: TaintState
    // -------------------------------------------------------------------

    #[test]
    fn test_taint_state_clean_is_clean() {
        let state = TaintState::clean(0, Some("x".into()));
        assert!(state.is_clean());
        assert!(!state.has_label(&TaintLabel::UserInput));
        assert_eq!(state.local, 0);
        assert_eq!(state.name, Some("x".into()));
    }

    #[test]
    fn test_taint_state_add_and_query() {
        let mut state = TaintState::clean(1, None);
        state.add_taint(TaintLabel::UserInput, span(10));
        state.add_taint(TaintLabel::Secret, span(20));

        assert!(!state.is_clean());
        assert!(state.has_label(&TaintLabel::UserInput));
        assert!(state.has_label(&TaintLabel::Secret));
        assert!(!state.has_label(&TaintLabel::FileData));
        assert_eq!(state.labels.len(), 2);
    }

    #[test]
    fn test_taint_state_sanitize() {
        let mut state = TaintState::clean(1, None);
        state.add_taint(TaintLabel::UserInput, span(10));
        state.add_taint(TaintLabel::Secret, span(20));

        state.sanitize(&TaintLabel::UserInput);
        assert!(!state.has_label(&TaintLabel::UserInput));
        assert!(state.has_label(&TaintLabel::Secret));
        assert_eq!(state.labels.len(), 1);
        // Origin should also be removed.
        assert!(!state.origins.contains_key(&TaintLabel::UserInput));
    }

    #[test]
    fn test_taint_state_worst_severity() {
        let mut state = TaintState::clean(1, None);
        state.add_taint(TaintLabel::Secret, span(10));

        let sev = state.worst_severity(&[SinkKind::LogOutput, SinkKind::SqlQuery]);
        assert_eq!(sev, Some(TaintSeverity::Critical));
    }

    #[test]
    fn test_taint_state_worst_severity_clean() {
        let state = TaintState::clean(0, None);
        assert_eq!(state.worst_severity(&[SinkKind::SqlQuery]), None);
    }

    #[test]
    fn test_taint_state_from_analysis() {
        let body = taint_body(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::io::read_line".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: span(10),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            vec![local(0, "ret", Ty::Unit), local(1, "input", Ty::usize())],
        );

        let result = analyze_taint(&body, &default_web_policy());
        let states = TaintState::from_analysis(&result, &body);

        assert_eq!(states.len(), 2);
        // local 0 should be clean.
        assert!(states[0].is_clean());
        // local 1 should have UserInput taint.
        assert!(states[1].has_label(&TaintLabel::UserInput));
    }

    #[test]
    fn test_taint_state_serialization_roundtrip() {
        let mut state = TaintState::clean(3, Some("data".into()));
        state.add_taint(TaintLabel::NetworkData, span(42));

        let json = serde_json::to_string(&state).expect("serialize");
        let round: TaintState = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(state, round);
    }
}
