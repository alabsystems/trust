//! Merkle digests of formula-DAG nodes, the bound-variable alpha digest, and
//! the number of context nodes a row reaches (work item T3, commit C03).
//!
//! Design of record: `docs/design/2026-10-08-t3-memory-proportional-reconstruction.md`
//! (§3 D-VC-5, §2 I4 and I5, §8). The per-function VC context (C06) composes these
//! pieces, and the identities that move onto the digest bring their `docs/TCB.md` rows
//! with them. C06 adds [`MerkleCache::digest_shell`], the digest of a transient root (a
//! spine's), and the context (`crate::vc_context`) composes them. T3 L4 C09w moves the
//! wire identities onto the digest, under TCB "Merkle formula identity": the compiler's
//! exact-VC claim v3 binds every formula of a VC (its own and its obligation record's) by
//! the digest ([`FormulaDigester`]), the VC content digest v2 and the obligation
//! fingerprint v4 bind the VC's formula by it ([`formula_digest`]). No verdict and no key
//! of a vector reads one; the certify memo (C10c) and lineage v4 (C12d) are still to come.
//!
//! # The Merkle digest
//!
//! One SHA-256 digest per [`FormulaDag`] node, under the domain
//! [`FORMULA_MERKLE_DOMAIN`], memoized per node by [`MerkleCache`]:
//!
//! ```text
//! M(n) = SHA-256( DOMAIN ‖ 0x00 ‖ lp(payload(n)) ‖ u64le(arity(n)) ‖ M(child_1) ‖ … ‖ M(child_k) )
//! ```
//!
//! where `payload(n)` is `serde_json` of the node's [`Shell`] payload (its
//! operator and every payload field, with placeholder children; the same derived
//! serialization [`crate::formula_hash::canonical_query_hash`] rests on, so every
//! current and future variant is covered by construction) and `lp` is a
//! little-endian `u64` length prefix. The child digests are fixed-width, so the
//! preimage parses back uniquely, and the digest denotes exactly the TREE the node
//! stands for: it never reads a node id, a DAG brand, an insertion order or how
//! much the DAG shares (I5). Two nodes of one DAG are the same node exactly when
//! their trees are equal; a digest only SELECTS candidates (D-VC-5), it never
//! decides identity inside a context. A [`crate::Symbol`] serializes as its
//! string, so interning order cannot reach a digest either.
//!
//! # The bound-variable alpha digest
//!
//! [`MerkleCache::bound_alpha_digest`] is the Merkle digest of the formula with
//! every BOUND variable replaced by its de Bruijn index, the candidate key of
//! `vc_dedup` (design §8): two formulas get the same bound-alpha digest exactly
//! when they are equal up to a consistent renaming of the variables each
//! quantifier binds. Free variables keep their names. A binder hashes its
//! quantifier and the SORTS it binds (not the names), and a bound occurrence
//! hashes its index, its leaf kind (`Var` or `SymVar`) and its sort:
//!
//! ```text
//! binder:   SHA-256( DOMAIN ‖ 0x01 ‖ quantifier ‖ u64le(k) ‖ lp(sort_1) ‖ … ‖ lp(sort_k) ‖ A(body) )
//! bound x:  SHA-256( DOMAIN ‖ 0x02 ‖ u64le(index of x) ‖ leaf kind ‖ lp(sort) )
//! ```
//!
//! and every other node is hashed as `M` is, over its children's `A`. So a
//! quantifier-free formula's bound-alpha digest IS its Merkle digest, and a
//! formula with a quantifier never shares one with a Merkle digest. Fail-closed
//! choices: binding ORDER is positional (`∀x y. P` and `∀y x. P` differ, a missed
//! merge); a `Var` and a `SymVar` occurrence of one bound name differ; a binder
//! that lists one name twice has no bound-alpha digest at all
//! ([`MerkleError::DuplicateBinding`]), because which binding its occurrences
//! denote is a reading this module does not choose; and a node that binds
//! variables but is neither `Forall` nor `Exists` is refused
//! ([`MerkleError::UnknownBinder`]) rather than hashed as if it bound nothing.
//!
//! Work: every node reachable from the root is serialized once for `M`. Under a
//! binder the walk is memoized per (node, binding environment), so a subterm is
//! hashed once in each binder body it occurs in — the bound the sharing SMT-LIB
//! printer states for itself (`trust_ir_contract::formula_dag`). The memo
//! strategy is not part of the digest: refining it moves no digest.
//!
//! # The per-row node count
//!
//! [`row_node_count`] is the number of distinct context nodes a row's roots
//! reach. I4 says it equals BUDGET-1's size(q), [`crate::determinism::query_size`]
//! of the row's materialized trees, so the shared context changes no row's
//! effort(q); the tests check that on rows interned into one shared context.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

use sha2::{Digest, Sha256};
use trust_ir_contract::formula_dag::{DagError, FormulaDag, NodeId, Shell};

use crate::digest::{lowercase_hex, write_lowercase_hex};
use crate::fx::{FxHashMap, FxHashSet};
use crate::{Formula, Sort};

/// Domain separator of every digest this module computes. Bump the version
/// when the encoding or the meaning of a field changes, so a digest of one
/// encoding never compares equal to one of another.
pub const FORMULA_MERKLE_DOMAIN: &[u8] = b"trust-formula-merkle/v1\0";

const TAG_NODE: u8 = 0;
const TAG_BINDER: u8 = 1;
const TAG_BOUND: u8 = 2;

const QUANTIFIER_FORALL: u8 = 0;
const QUANTIFIER_EXISTS: u8 = 1;

const LEAF_VAR: u8 = 0;
const LEAF_SYMVAR: u8 = 1;

/// A SHA-256 digest of one formula tree ([`MerkleCache`]).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FormulaDigest([u8; 32]);

impl FormulaDigest {
    /// The 32 digest bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Lowercase hex of the digest.
    #[must_use]
    pub fn to_hex(&self) -> String {
        lowercase_hex(&self.0)
    }
}

impl fmt::Display for FormulaDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_lowercase_hex(f, &self.0)
    }
}

impl fmt::Debug for FormulaDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("FormulaDigest(")?;
        write_lowercase_hex(f, &self.0)?;
        f.write_str(")")
    }
}

/// Why a digest was refused. There is then no digest, and a caller keys
/// nothing on the formula (it never falls back to another spelling).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MerkleError {
    /// The id is not a node of the DAG it was passed with.
    UnknownNode {
        /// The offending id.
        node: NodeId,
        /// The number of nodes the DAG holds.
        len: usize,
    },
    /// The id is a node of a DAG other than the one this cache serves (the
    /// DAG of the first node it was asked about). A cache's memo is indexed by
    /// node, so it serves one DAG; a clone of that DAG is another DAG.
    OtherDag {
        /// The offending id.
        node: NodeId,
    },
    /// A node's payload did not serialize.
    Unserializable {
        /// The node.
        node: NodeId,
        /// The serializer's message.
        message: String,
    },
    /// A binder lists `name` twice: which binding its occurrences denote is not
    /// a reading this module chooses, so the formula has no bound-alpha digest.
    DuplicateBinding {
        /// The binder.
        node: NodeId,
        /// The repeated name.
        name: String,
    },
    /// A node binds variables but is neither `Forall` nor `Exists`.
    UnknownBinder {
        /// The node.
        node: NodeId,
    },
    /// A transient root's shell was given a number of child digests other than its arity
    /// ([`MerkleCache::digest_shell`]).
    ShellArity {
        /// The shell's arity.
        expected: usize,
        /// The digests given.
        found: usize,
    },
    /// A transient root's shell payload did not serialize.
    UnserializableShell {
        /// The serializer's message.
        message: String,
    },
}

impl fmt::Display for MerkleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MerkleError::UnknownNode { node, len } => {
                write!(f, "{node} is not a node of this DAG (it holds {len} nodes)")
            }
            MerkleError::OtherDag { node } => {
                write!(f, "{node} belongs to a DAG other than the one this Merkle cache serves")
            }
            MerkleError::Unserializable { node, message } => {
                write!(f, "the payload of {node} does not serialize: {message}")
            }
            MerkleError::DuplicateBinding { node, name } => write!(
                f,
                "binder {node} binds `{name}` twice, so it has no bound-variable alpha digest"
            ),
            MerkleError::UnknownBinder { node } => {
                write!(f, "{node} binds variables but is neither Forall nor Exists")
            }
            MerkleError::ShellArity { expected, found } => {
                write!(f, "a shell of arity {expected} was given {found} child digests")
            }
            MerkleError::UnserializableShell { message } => {
                write!(f, "a transient shell's payload does not serialize: {message}")
            }
        }
    }
}

impl std::error::Error for MerkleError {}

/// Work counters of a [`MerkleCache`]: deterministic, report-only.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct MerkleStats {
    /// Nodes whose Merkle digest is memoized.
    pub merkle_nodes: u64,
    /// Node payloads serialized (each node at most once).
    pub payloads_serialized: u64,
    /// Memoized (node, binding environment) bound-alpha digests.
    pub alpha_entries: u64,
    /// Distinct binding environments entered.
    pub environments: u64,
}

/// The names one binder adds to its parent environment, in binding order.
struct Environment {
    parent: usize,
    names: Vec<crate::Symbol>,
}

/// The memoized Merkle and bound-alpha digests of the nodes of ONE
/// [`FormulaDag`] (module docs).
///
/// The DAG is passed to each call rather than borrowed, so the context that
/// owns the DAG and this cache can keep interning between calls: nodes are
/// append-only and a node's digest never changes. The first node a cache is
/// asked about binds it to that node's DAG, and an id of any other DAG (a
/// clone included) is refused with [`MerkleError::OtherDag`].
pub struct MerkleCache {
    /// A node of the DAG this cache serves; `None` until the first call.
    anchor: Option<NodeId>,
    /// `M(n)` by node index.
    merkle: Vec<Option<FormulaDigest>>,
    /// Whether the node or anything below it binds variables, by node index
    /// (filled with `merkle`).
    binder_below: Vec<bool>,
    /// `A(n, env)` by (node index, environment index).
    alpha: FxHashMap<(usize, usize), FormulaDigest>,
    /// Index 0 is the empty environment.
    envs: Vec<Environment>,
    /// (parent environment, binder node index) -> environment index.
    env_index: FxHashMap<(usize, usize), usize>,
    stats: MerkleStats,
}

impl Default for MerkleCache {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for MerkleCache {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MerkleCache")
            .field("anchor", &self.anchor)
            .field("stats", &self.stats)
            .finish_non_exhaustive()
    }
}

/// What a node is, for the bound-alpha walk.
enum Kind<'a> {
    /// A variable leaf: its name, leaf kind and sort.
    Variable(&'a str, u8, &'a Sort),
    /// A quantifier: its kind and bindings.
    Binder(u8, &'a [(crate::Symbol, Sort)]),
    /// Any other node.
    Other,
}

fn kind_of(shell: &Shell) -> Result<Kind<'_>, ()> {
    match shell.payload() {
        Formula::Var(name, sort) => Ok(Kind::Variable(name.as_str(), LEAF_VAR, sort)),
        Formula::SymVar(sym, sort) => Ok(Kind::Variable(sym.as_str(), LEAF_SYMVAR, sort)),
        Formula::Forall(bindings, _) => Ok(Kind::Binder(QUANTIFIER_FORALL, bindings)),
        Formula::Exists(bindings, _) => Ok(Kind::Binder(QUANTIFIER_EXISTS, bindings)),
        other if other.binds_variables() => Err(()),
        _ => Ok(Kind::Other),
    }
}

fn length_prefixed(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

#[inline]
fn static_sort_json_bytes(sort: &Sort) -> Option<&'static [u8]> {
    match sort {
        Sort::Bool => Some(b"\"Bool\""),
        Sort::Int => Some(b"\"Int\""),
        Sort::Real => Some(b"\"Real\""),
        Sort::RoundingMode => Some(b"\"RoundingMode\""),
        Sort::BitVec(1) => Some(b"{\"BitVec\":1}"),
        Sort::BitVec(8) => Some(b"{\"BitVec\":8}"),
        Sort::BitVec(16) => Some(b"{\"BitVec\":16}"),
        Sort::BitVec(32) => Some(b"{\"BitVec\":32}"),
        Sort::BitVec(64) => Some(b"{\"BitVec\":64}"),
        Sort::BitVec(128) => Some(b"{\"BitVec\":128}"),
        Sort::Float { eb: 8, sb: 24 } => Some(b"{\"Float\":{\"eb\":8,\"sb\":24}}"),
        Sort::Float { eb: 11, sb: 53 } => Some(b"{\"Float\":{\"eb\":11,\"sb\":53}}"),
        _ => None,
    }
}

#[inline]
fn static_shell_payload_json_bytes(payload: &Formula) -> Option<&'static [u8]> {
    match payload {
        Formula::Bool(true) => Some(b"{\"Bool\":true}"),
        Formula::Bool(false) => Some(b"{\"Bool\":false}"),
        Formula::Not(a) if matches!(**a, Formula::Bool(true)) => {
            Some(b"{\"Not\":{\"Bool\":true}}")
        }
        Formula::Neg(a) if matches!(**a, Formula::Bool(true)) => {
            Some(b"{\"Neg\":{\"Bool\":true}}")
        }
        Formula::And(terms) if terms.is_empty() => Some(b"{\"And\":[]}"),
        Formula::Or(terms) if terms.is_empty() => Some(b"{\"Or\":[]}"),
        Formula::Implies(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Implies\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Eq(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Eq\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Lt(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Lt\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Le(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Le\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Gt(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Gt\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Ge(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Ge\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Add(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Add\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Sub(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Sub\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Mul(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Mul\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Div(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Div\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Rem(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Rem\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Ite(a, b, c)
            if matches!(
                (&**a, &**b, &**c),
                (Formula::Bool(true), Formula::Bool(true), Formula::Bool(true))
            ) =>
        {
            Some(b"{\"Ite\":[{\"Bool\":true},{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Select(a, b)
            if matches!((&**a, &**b), (Formula::Bool(true), Formula::Bool(true))) =>
        {
            Some(b"{\"Select\":[{\"Bool\":true},{\"Bool\":true}]}")
        }
        Formula::Store(a, b, c)
            if matches!(
                (&**a, &**b, &**c),
                (Formula::Bool(true), Formula::Bool(true), Formula::Bool(true))
            ) =>
        {
            Some(b"{\"Store\":[{\"Bool\":true},{\"Bool\":true},{\"Bool\":true}]}")
        }
        _ => None,
    }
}

fn finish(hasher: Sha256) -> FormulaDigest {
    FormulaDigest(hasher.finalize().into())
}

impl MerkleCache {
    /// An empty cache, bound to no DAG yet.
    #[must_use]
    pub fn new() -> Self {
        MerkleCache {
            anchor: None,
            merkle: Vec::new(),
            binder_below: Vec::new(),
            alpha: FxHashMap::default(),
            envs: vec![Environment { parent: 0, names: Vec::new() }],
            env_index: FxHashMap::default(),
            stats: MerkleStats::default(),
        }
    }

    /// The work counters so far.
    #[must_use]
    pub fn stats(&self) -> MerkleStats {
        MerkleStats {
            environments: u64::try_from(self.envs.len().saturating_sub(1)).unwrap_or(u64::MAX),
            alpha_entries: u64::try_from(self.alpha.len()).unwrap_or(u64::MAX),
            ..self.stats
        }
    }

    /// Check that `id` is a node of `dag` and that `dag` is this cache's DAG,
    /// binding the cache on its first call; grow the per-node tables.
    fn admit(&mut self, dag: &FormulaDag, id: NodeId) -> Result<(), MerkleError> {
        if !dag.contains(id) {
            return Err(MerkleError::UnknownNode { node: id, len: dag.len() });
        }
        match self.anchor {
            Some(anchor) if !dag.contains(anchor) => {
                return Err(MerkleError::OtherDag { node: id });
            }
            Some(_) => {}
            None => self.anchor = Some(id),
        }
        if self.merkle.len() < dag.len() {
            self.merkle.resize(dag.len(), None);
            self.binder_below.resize(dag.len(), false);
        }
        Ok(())
    }

    fn memo(&self, index: usize) -> Option<FormulaDigest> {
        self.merkle.get(index).copied().flatten()
    }

    /// The Merkle digest of node `root` of `dag` (module docs): a function of
    /// the tree `root` stands for and of nothing else.
    ///
    /// Iterative and memoized: each node reachable from `root` is serialized
    /// and hashed once over the cache's life.
    ///
    /// # Errors
    ///
    /// [`MerkleError::UnknownNode`], [`MerkleError::OtherDag`], or
    /// [`MerkleError::Unserializable`] when a payload does not serialize.
    pub fn digest(&mut self, dag: &FormulaDag, root: NodeId) -> Result<FormulaDigest, MerkleError> {
        self.admit(dag, root)?;
        let mut stack: Vec<(NodeId, bool)> = Vec::with_capacity(16);
        stack.push((root, false));
        let mut payload = Vec::with_capacity(64);
        while let Some((id, expanded)) = stack.pop() {
            if self.memo(id.index()).is_some() {
                continue;
            }
            if !expanded {
                stack.push((id, true));
                stack.extend(
                    dag.kids(id)
                        .filter(|kid| self.memo(kid.index()).is_none())
                        .map(|kid| (kid, false)),
                );
                continue;
            }
            let shell = dag.shell(id);
            let payload_bytes = if let Some(static_bytes) =
                static_shell_payload_json_bytes(shell.payload())
            {
                static_bytes
            } else {
                payload.clear();
                serde_json::to_writer(&mut payload, shell.payload()).map_err(|error| {
                    MerkleError::Unserializable { node: id, message: error.to_string() }
                })?;
                payload.as_slice()
            };
            self.stats.payloads_serialized += 1;
            let mut hasher = Sha256::new();
            hasher.update(FORMULA_MERKLE_DOMAIN);
            hasher.update([TAG_NODE]);
            length_prefixed(&mut hasher, payload_bytes);
            hasher.update((shell.arity() as u64).to_le_bytes());
            let mut binder_below = shell.binds_variables();
            for kid in dag.kids(id) {
                let Some(digest) = self.memo(kid.index()) else {
                    // A child is hashed before its parent by construction; a
                    // missing one is a refusal, never a guess.
                    return Err(MerkleError::UnknownNode { node: kid, len: dag.len() });
                };
                hasher.update(digest.0);
                binder_below |= self.binder_below.get(kid.index()).copied().unwrap_or(true);
            }
            if let (Some(slot), Some(flag)) =
                (self.merkle.get_mut(id.index()), self.binder_below.get_mut(id.index()))
            {
                *slot = Some(finish(hasher));
                *flag = binder_below;
                self.stats.merkle_nodes += 1;
            }
        }
        self.memo(root.index()).ok_or(MerkleError::UnknownNode { node: root, len: dag.len() })
    }

    /// The Merkle digest `M` of a TRANSIENT node: `shell` over children whose digests are
    /// `kids`, in order, computed from the same preimage as [`MerkleCache::digest`] (module
    /// docs) without interning anything (T3 L4, C06). A spine's root, which is never
    /// interned (D-VC-3), is digested this way, so its digest equals `formula_digest` of
    /// the tree it stands for (I5).
    ///
    /// # Errors
    ///
    /// [`MerkleError::ShellArity`] when `kids` is not the shell's arity, and
    /// [`MerkleError::UnserializableShell`] when its payload does not serialize.
    pub fn digest_shell(
        shell: &Shell,
        kids: &[FormulaDigest],
    ) -> Result<FormulaDigest, MerkleError> {
        if kids.len() != shell.arity() {
            return Err(MerkleError::ShellArity { expected: shell.arity(), found: kids.len() });
        }
        let mut payload = Vec::new();
        let payload_bytes =
            if let Some(static_bytes) = static_shell_payload_json_bytes(shell.payload()) {
                static_bytes
            } else {
                payload.reserve(64);
                serde_json::to_writer(&mut payload, shell.payload()).map_err(|error| {
                    MerkleError::UnserializableShell { message: error.to_string() }
                })?;
                payload.as_slice()
            };
        let mut hasher = Sha256::new();
        hasher.update(FORMULA_MERKLE_DOMAIN);
        hasher.update([TAG_NODE]);
        length_prefixed(&mut hasher, payload_bytes);
        hasher.update((shell.arity() as u64).to_le_bytes());
        for kid in kids {
            hasher.update(kid.0);
        }
        Ok(finish(hasher))
    }

    /// The index of `name` in environment `env`: the number of bindings
    /// between its innermost binding and the occurrence, or `None` when no
    /// enclosing binder binds it.
    fn lookup(&self, mut env: usize, name: &str) -> Option<u64> {
        let mut passed: u64 = 0;
        while env != 0 {
            let frame = self.envs.get(env)?;
            if let Some(at) = frame.names.iter().rposition(|bound| bound.as_str() == name) {
                let after = frame.names.len() - 1 - at;
                return Some(passed + after as u64);
            }
            passed += frame.names.len() as u64;
            env = frame.parent;
        }
        None
    }

    /// The environment binder `node` opens inside `parent`.
    fn enter(
        &mut self,
        parent: usize,
        node: NodeId,
        bindings: &[(crate::Symbol, Sort)],
    ) -> Result<usize, MerkleError> {
        let binder = node.index();
        if let Some(&env) = self.env_index.get(&(parent, binder)) {
            return Ok(env);
        }
        if bindings.len() <= 8 {
            for (idx, (sym, _)) in bindings.iter().enumerate() {
                if bindings[..idx].iter().any(|(prev, _)| prev.as_str() == sym.as_str()) {
                    return Err(MerkleError::DuplicateBinding {
                        node,
                        name: sym.as_str().to_string(),
                    });
                }
            }
        } else {
            let mut seen: FxHashSet<&str> = FxHashSet::default();
            for (sym, _) in bindings {
                if !seen.insert(sym.as_str()) {
                    return Err(MerkleError::DuplicateBinding {
                        node,
                        name: sym.as_str().to_string(),
                    });
                }
            }
        }
        let env = self.envs.len();
        self.envs.push(Environment {
            parent,
            names: bindings.iter().map(|(sym, _)| sym.clone()).collect(),
        });
        self.env_index.insert((parent, binder), env);
        Ok(env)
    }

    /// The bound-variable alpha digest of node `root` of `dag` (module docs).
    ///
    /// # Errors
    ///
    /// As [`MerkleCache::digest`], and [`MerkleError::DuplicateBinding`] or
    /// [`MerkleError::UnknownBinder`] for a binder this digest does not read.
    pub fn bound_alpha_digest(
        &mut self,
        dag: &FormulaDag,
        root: NodeId,
    ) -> Result<FormulaDigest, MerkleError> {
        let merkle_root = self.digest(dag, root)?;
        if !self.binder_below.get(root.index()).copied().unwrap_or(true) {
            return Ok(merkle_root);
        }
        let key = |id: NodeId, env: usize| (id.index(), env);
        // (node, environment, children pushed)
        let mut stack: Vec<(NodeId, usize, bool)> = Vec::with_capacity(16);
        stack.push((root, 0, false));
        let mut payload = Vec::with_capacity(64);
        let mut kids: Vec<FormulaDigest> = Vec::new();
        while let Some((id, env, expanded)) = stack.pop() {
            let slot = key(id, env);
            if self.alpha.contains_key(&slot) {
                continue;
            }
            let merkle = self
                .memo(id.index())
                .ok_or(MerkleError::UnknownNode { node: id, len: dag.len() })?;
            // A subtree with no binder, outside every binder, is its Merkle digest.
            if env == 0 && !self.binder_below.get(id.index()).copied().unwrap_or(true) {
                self.alpha.insert(slot, merkle);
                continue;
            }
            let shell = dag.shell(id);
            let kind = kind_of(shell).map_err(|()| MerkleError::UnknownBinder { node: id })?;
            match kind {
                Kind::Variable(name, leaf, sort) => {
                    let digest = match self.lookup(env, name) {
                        None => merkle,
                        Some(index) => {
                            let sort_bytes = if let Some(static_bytes) =
                                static_sort_json_bytes(sort)
                            {
                                static_bytes
                            } else {
                                payload.clear();
                                serde_json::to_writer(&mut payload, sort).map_err(|error| {
                                    MerkleError::Unserializable {
                                        node: id,
                                        message: error.to_string(),
                                    }
                                })?;
                                payload.as_slice()
                            };
                            let mut hasher = Sha256::new();
                            hasher.update(FORMULA_MERKLE_DOMAIN);
                            hasher.update([TAG_BOUND]);
                            hasher.update(index.to_le_bytes());
                            hasher.update([leaf]);
                            length_prefixed(&mut hasher, sort_bytes);
                            finish(hasher)
                        }
                    };
                    self.alpha.insert(slot, digest);
                }
                Kind::Binder(quantifier, bindings) => {
                    let inner = self.enter(env, id, bindings)?;
                    let Some(body) = dag.kids(id).next() else {
                        return Err(MerkleError::UnknownBinder { node: id });
                    };
                    let body_slot = key(body, inner);
                    if !expanded {
                        stack.push((id, env, true));
                        if !self.alpha.contains_key(&body_slot) {
                            stack.push((body, inner, false));
                        }
                        continue;
                    }
                    let Some(body_digest) = self.alpha.get(&body_slot).copied() else {
                        return Err(MerkleError::UnknownNode { node: body, len: dag.len() });
                    };
                    let mut hasher = Sha256::new();
                    hasher.update(FORMULA_MERKLE_DOMAIN);
                    hasher.update([TAG_BINDER, quantifier]);
                    hasher.update((bindings.len() as u64).to_le_bytes());
                    for (_, sort) in bindings {
                        let sort_bytes = if let Some(static_bytes) = static_sort_json_bytes(sort) {
                            static_bytes
                        } else {
                            payload.clear();
                            serde_json::to_writer(&mut payload, sort).map_err(|error| {
                                MerkleError::Unserializable { node: id, message: error.to_string() }
                            })?;
                            payload.as_slice()
                        };
                        length_prefixed(&mut hasher, sort_bytes);
                    }
                    hasher.update(body_digest.0);
                    self.alpha.insert(slot, finish(hasher));
                }
                Kind::Other => {
                    if !expanded {
                        stack.push((id, env, true));
                        for kid in dag.kids(id) {
                            if !self.alpha.contains_key(&key(kid, env)) {
                                stack.push((kid, env, false));
                            }
                        }
                        continue;
                    }
                    kids.clear();
                    let mut all_merkle = true;
                    for kid in dag.kids(id) {
                        let Some(digest) = self.alpha.get(&key(kid, env)).copied() else {
                            return Err(MerkleError::UnknownNode { node: kid, len: dag.len() });
                        };
                        all_merkle &= self.memo(kid.index()) == Some(digest);
                        kids.push(digest);
                    }
                    let digest = if all_merkle {
                        merkle
                    } else {
                        let payload_bytes = if let Some(static_bytes) =
                            static_shell_payload_json_bytes(shell.payload())
                        {
                            static_bytes
                        } else {
                            payload.clear();
                            serde_json::to_writer(&mut payload, shell.payload()).map_err(
                                |error| MerkleError::Unserializable {
                                    node: id,
                                    message: error.to_string(),
                                },
                            )?;
                            payload.as_slice()
                        };
                        self.stats.payloads_serialized += 1;
                        let mut hasher = Sha256::new();
                        hasher.update(FORMULA_MERKLE_DOMAIN);
                        hasher.update([TAG_NODE]);
                        length_prefixed(&mut hasher, payload_bytes);
                        hasher.update((shell.arity() as u64).to_le_bytes());
                        for digest in &kids {
                            hasher.update(digest.0);
                        }
                        finish(hasher)
                    };
                    self.alpha.insert(slot, digest);
                }
            }
        }
        self.alpha
            .get(&key(root, 0))
            .copied()
            .ok_or(MerkleError::UnknownNode { node: root, len: dag.len() })
    }
}

/// [`MerkleCache::digest`] of `formula`, interned into a fresh DAG.
///
/// # Errors
///
/// As [`MerkleCache::digest`].
pub fn formula_digest(formula: &Formula) -> Result<FormulaDigest, MerkleError> {
    let mut dag = FormulaDag::new();
    let root = dag.intern(formula);
    MerkleCache::new().digest(&dag, root)
}

/// Merkle digests of several formulas over one DAG and one cache (T3 L4, C09w), so a
/// subtree they share is hashed once: the exact-VC claim digests a VC's formula and every
/// formula of its obligation record, which repeat the formula's subtrees. Each digest is
/// [`formula_digest`] of its formula (I5: a function of the tree, never of what else was
/// interned first).
pub struct FormulaDigester {
    dag: FormulaDag,
    cache: MerkleCache,
}

impl Default for FormulaDigester {
    fn default() -> Self {
        Self::new()
    }
}

impl FormulaDigester {
    /// An empty DAG and cache.
    #[must_use]
    pub fn new() -> Self {
        Self { dag: FormulaDag::new(), cache: MerkleCache::new() }
    }

    /// [`formula_digest`] of `formula`.
    ///
    /// # Errors
    ///
    /// As [`MerkleCache::digest`].
    pub fn digest(&mut self, formula: &Formula) -> Result<FormulaDigest, MerkleError> {
        let root = self.dag.intern(formula);
        self.cache.digest(&self.dag, root)
    }
}

/// [`MerkleCache::bound_alpha_digest`] of `formula`, interned into a fresh DAG.
///
/// # Errors
///
/// As [`MerkleCache::bound_alpha_digest`].
pub fn formula_bound_alpha_digest(formula: &Formula) -> Result<FormulaDigest, MerkleError> {
    let mut dag = FormulaDag::new();
    let root = dag.intern(formula);
    MerkleCache::new().bound_alpha_digest(&dag, root)
}

/// The number of distinct nodes of the context `dag` that `roots` reach: a
/// row's size read off the shared context. I4: for a row whose roots are its
/// assertions interned into the context, this equals
/// [`crate::determinism::query_size`] of the row's materialized trees, however
/// many other rows the context holds. Duplicate roots count once.
///
/// Iterative; its work and memory are the reached nodes, not the context.
///
/// # Errors
///
/// [`DagError::UnknownNode`] for a root that is not a node of `dag`.
pub fn row_node_count(dag: &FormulaDag, roots: &[NodeId]) -> Result<u64, DagError> {
    if roots.is_empty() {
        return Ok(0);
    }
    let mut seen: FxHashSet<usize> =
        FxHashSet::with_capacity_and_hasher(roots.len(), Default::default());
    let mut stack: Vec<NodeId> = Vec::with_capacity(roots.len());
    for &root in roots {
        if !dag.contains(root) {
            return Err(DagError::UnknownNode { node: root, len: dag.len() });
        }
        if seen.insert(root.index()) {
            stack.push(root);
        }
    }
    while let Some(id) = stack.pop() {
        for kid in dag.kids(id) {
            if seen.insert(kid.index()) {
                stack.push(kid);
            }
        }
    }
    Ok(u64::try_from(seen.len()).unwrap_or(u64::MAX))
}

#[cfg(test)]
#[path = "formula_merkle_tests.rs"]
mod tests;
