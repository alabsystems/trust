// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The KEYED ENVIRONMENT of a Clean island session (Trust TG6): the only
//! owner of the session's kernel [`Environment`], its elaborator
//! [`FileContext`] and the temporal modules it has served, and therefore the
//! only way a session's environment is built.
//!
//! # Why it is structural
//!
//! The three fields are private to this module. Nothing reaches them mutably
//! except through [`KeyedEnv::parts_mut`] and its narrower forms, and each of
//! those either runs inside a KEYED OPERATION — one elaboration whose every
//! input this module folds into the key before it runs — or POISONS the
//! session: once anything changed the environment outside an operation, no
//! fact is read or written for the rest of the session, and it checks
//! afresh. There is no third door, so "everything an elaboration reads is in
//! its key" does not rest on a caller remembering to say so.
//!
//! # The key of one operation
//!
//! `H(prefix, kernel theory, chain, session params, operation)`, where
//!
//! * `prefix` is [`FactContext::key_prefix`]: the fact format, the compiler
//!   identity (trustc commit, Clean version and delta format, the SHA-256 of
//!   the checker's image), the Clean prelude's content digest, the
//!   Clean-relevant environment variables and the target pointer width;
//! * `chain` folds every earlier operation of the session in order — its key,
//!   its dependencies, and the digests of the delta and outcome it produced —
//!   so a fact's key names the environment it was produced in, upstream
//!   islands, declared Rust callees and served modules included;
//! * the operation is the island bytes (all of a header-first batch's islands,
//!   since a batch elaborates every header before any body and an island may
//!   name a later one) or the callee declarations.
//!
//! Program admissions (E6 imports, seeded models, TG11 datatype faces) are
//! not in the chain: they change with every Rust body edit, and an island
//! that does not use a body must not miss because it changed. Instead a fact
//! records its DEPENDENCIES: every name its declarations reach in the kernel
//! (types and values, through further names, stopping at the prelude and at
//! its own declarations), plus every name in an admitted namespace its text
//! spells (`trust_import_`, `trust_checked_`, `trust_type_`, `TrustOdt.`),
//! present or not. Each is digested (`dependency_digest`) over the kernel
//! records held under it ([`Environment::kernel_record_digest`]), what the
//! elaborator reads under it ([`Environment::elaboration_record_digest`]:
//! a structure's field table, parameter names, aliases, attributes), its
//! verification stamp, its marks and its origin. A lookup recomputes each
//! digest in the current environment, so a changed imported body is a miss —
//! and its island is elaborated and checked again — while an edit to a body
//! the island never reaches is not. "Reach" is the kernel's: a projection
//! reaches its structure, and a definition its callees' bodies, so a tag
//! table edited under unchanged constructor names and match branches still
//! changes what a theorem about the tags reaches, and two same-typed fields
//! swapped in a Rust struct change the structure's field table.
//!
//! Metadata readers also record every exact `.bounded` and `.stateBudget`
//! name they consult, present or absent, and those names' transitive closures.
//! A bounded acceptance therefore misses if its permission disappears or changes.
//!
//! That walk sees what an operation REGISTERED. An operation whose text
//! checks a judgment it does not register — an `example`, a `#`-command
//! (`#guard`, `#eval`, `#check`, …) or an `elab` (`checks_without_registering`)
//! — reads the environment in a way no registered declaration records: the
//! kernel checks it against the environment and throws it away. It depends on
//! the whole environment it ran in, outside the prelude (`environment_digest`),
//! so a name added, removed or changed anywhere misses it.
//!
//! A REJECTED elaboration is never stored: Clean's clock-budgeted tactics can
//! refuse under load what they accept otherwise, and a stored rejection would
//! fail every later build that hit it (`TG6-FACTS-1` (9)). Outside a
//! transactional check it is chained and logged like an acceptance, so the
//! operations after it key the same way; inside one it poisons the working
//! copy, which the caller restores.
//!
//! An admission window may change only per-name records, the ones those
//! digests cover: one that changes session state (options, rule lists,
//! instance positions; `EnvFactDelta::changed_session_table`) stops the
//! session's use of facts.
//!
//! # A hit
//!
//! The stored delta is applied (no elaboration, no check; the producer's
//! stamps replayed, `COMPILE-TIME-FACTS-1`), every entry it changes first
//! checked against its before value. The elaborator's own state (the file
//! context) is NOT carried, so the session becomes elaborator-STALE: before it
//! elaborates anything else it rebuilds by replaying its operation log with
//! real elaboration, each operation under the session settings it first ran
//! with, and compares what it rebuilt with what the hits built: every
//! replayed outcome with the outcome its hit returned, and the rebuilt
//! environment with the one the hits built. A difference quarantines every
//! fact the session applied AND fails the operation that triggered the
//! rebuild: the session has just seen a hit it returned disagree with real
//! elaboration, so nothing it reported from facts may stand.
//!
//! One hit in 32, chosen by the key's first byte, is AUDITED: elaborated for
//! real, and its delta, outcome and dependencies compared with the stored
//! fact. A mismatch quarantines the fact and sweeps the index of every entry
//! that names it (`TG6-FACTS-1` (24)).

use std::cell::OnceCell;
use std::collections::{BTreeSet, HashSet};
use std::sync::{Arc, OnceLock};

use clean_elab::FileContext;
use clean_kernel::env::{EnvFactDelta, TrustedEnvExt as _};
use clean_kernel::{Environment, Name};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::clean_fact::{self, Digest32, FactContext, StoreRead, digest_parts, encode, hex, stat};

/// One step that changed a session's elaboration state, as the session logs
/// it for a rebuild and as each fact carries it for its own re-check.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum LoggedOp {
    /// Rust callees declared before the islands (W5).
    Callees(Vec<super::RustCallee>),
    /// A module marked satisfied from source.
    MarkSatisfied(String),
    /// A header-first batch of islands.
    CheckAll(Vec<String>),
    /// One island, checked sequentially.
    Check(String),
    /// A window of program admissions, as the environment delta it made.
    Admissions(Vec<u8>),
    /// The declaration phase of a batch whose reports a later owner selects
    /// (`prepare_all`, TG4's producer).
    Prepare(Vec<String>),
    /// The reporting phase of the batch the last `Prepare` declared, under
    /// the session's report policy.
    Report(Vec<String>),
}

impl LoggedOp {
    fn texts(&self) -> Vec<&str> {
        match self {
            Self::CheckAll(sources) | Self::Prepare(sources) | Self::Report(sources) => {
                sources.iter().map(String::as_str).collect()
            }
            Self::Check(source) => vec![source.as_str()],
            _ => Vec::new(),
        }
    }

    pub(crate) fn kind(&self) -> &'static str {
        match self {
            Self::Callees(_) => "callees",
            Self::MarkSatisfied(_) => "mark-satisfied",
            Self::CheckAll(_) => "check-all",
            Self::Check(_) => "check",
            Self::Admissions(_) => "admissions",
            Self::Prepare(_) => "prepare",
            Self::Report(_) => "report",
        }
    }
}

/// One entry of a session's log: the operation, and the session settings it
/// ran with when it reads them (a fact or an elaboration; `None` for callee
/// declarations, a marked module and an admission window, which read none). A
/// rebuild and a fact's re-check replay each operation under its own
/// settings, so a setting changed later in the session (TG4 turns model
/// checks on before it reports) cannot make a replay differ.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct LogEntry {
    pub(crate) op: LoggedOp,
    pub(crate) params: Option<SessionParams>,
}

impl LogEntry {
    fn unparameterized(op: LoggedOp) -> Self {
        Self { op, params: None }
    }
}

/// A fact this session applied: its key and store object, the log index of
/// its operation, and the SHA-256 of the outcome it returned, for a rebuild
/// to compare.
#[derive(Clone)]
struct Applied {
    key: Digest32,
    object: Digest32,
    index: usize,
    outcome: Digest32,
}

/// The session settings an elaboration reads.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SessionParams {
    pub(crate) model_checks: bool,
    pub(crate) binding_reads: bool,
    pub(crate) model_state_budget: u64,
    pub(crate) model_work_limit: u64,
    pub(crate) model_heartbeats_per_work: u64,
}

/// A stored fact.
#[derive(Serialize, Deserialize)]
pub(crate) struct StoredFact {
    format: String,
    key: Digest32,
    pub(crate) params: SessionParams,
    /// Every operation before this one, so the fact re-checks on its own.
    pub(crate) prior: Vec<LogEntry>,
    pub(crate) op: LoggedOp,
    /// What the fact's declarations reach outside the prelude and themselves.
    deps: Vec<(Name, Option<Digest32>)>,
    /// Only Prepare with a model/binding baseline reads the full name set.
    /// Values are intentionally excluded: unrelated body edits still hit.
    model_baseline_names: Option<Digest32>,
    delta: Vec<u8>,
    pub(crate) outcome: Vec<u8>,
    served_after: Vec<String>,
}

impl StoredFact {
    pub(crate) fn decode(bytes: &[u8]) -> Result<Self, String> {
        let fact: Self =
            clean_fact::decode(bytes).map_err(|error| format!("undecodable fact: {error}"))?;
        if fact.format != clean_fact::FACT_FORMAT {
            return Err("a fact of another format".to_string());
        }
        Ok(fact)
    }
}

/// What [`KeyedEnv::lookup`] decided.
pub(crate) enum Lookup {
    /// The fact was applied; here is its stored outcome.
    Hit(Vec<u8>),
    /// Elaborate: there is no usable fact (or facts are off for this
    /// session). `audit` is a hit chosen for re-elaboration.
    Miss(Box<Pending>),
}

/// A miss in progress, from [`KeyedEnv::lookup`] to [`KeyedEnv::finish`].
pub(crate) struct Pending {
    key: Option<Digest32>,
    op: LoggedOp,
    params: SessionParams,
    before: Option<Environment>,
    audit: Option<(Digest32, StoredFact)>,
}

/// The constants of Clean's built-in prelude, read once per process from the
/// first prelude a session builds. A dependency walk stops at them: the
/// prelude is in every key ([`FactContext::key_prefix`]).
fn prelude_names() -> &'static HashSet<Name> {
    static NAMES: OnceLock<HashSet<Name>> = OnceLock::new();
    NAMES.get_or_init(|| environment_names(&Environment::with_prelude()).into_iter().collect())
}

/// Every name the environment holds a kernel record under, sorted.
fn environment_names(env: &Environment) -> BTreeSet<Name> {
    env.constants()
        .map(|info| info.name.clone())
        .chain(env.inductives().map(|info| info.name.clone()))
        .chain(env.constructors().map(|info| info.name.clone()))
        .chain(env.recursors().map(|info| info.name.clone()))
        .chain(env.quotients().map(|info| info.name.clone()))
        .collect()
}

/// The dependency a rejected fact has instead of a list of names: the whole
/// environment it was elaborated in, outside the prelude. It contains a space,
/// so it is no Clean declaration's name.
const ENVIRONMENT: &str = "trust fact environment";

fn environment_dependency() -> Name {
    Name::from_string(ENVIRONMENT)
}

/// Every name outside the prelude with its dependency digest, in name order:
/// a name added, removed or changed changes it.
fn environment_digest(env: &Environment) -> Digest32 {
    let prelude = prelude_names();
    let mut hasher = Sha256::new();
    hasher.update(b"trust.clean-kernel-fact.environment.v1");
    for name in environment_names(env).into_iter().filter(|name| !prelude.contains(name)) {
        let digest = name_digest(env, &name);
        let name = name.to_string();
        hasher.update((name.len() as u64).to_le_bytes());
        hasher.update(name.as_bytes());
        hasher.update(digest.unwrap_or([0; 32]));
        hasher.update([u8::from(digest.is_some())]);
    }
    hasher.finalize().into()
}

/// The structural constant-name set a prepared continuation records. Its
/// pre-operation input excludes bodies, stamps and origins; owned imports and
/// declarations are already bound by the operation and its compiler identity.
fn constant_names_digest(env: &Environment) -> Option<Digest32> {
    let mut names: Vec<Name> = env.constants().map(|info| info.name.clone()).collect();
    names.sort();
    encode(&names).map(|bytes| digest_parts(&[b"trust.fact.constant-names.v1", &bytes]))
}

/// The prefixes of the names program admissions write: E6 imports
/// ([`super::KERNEL_IMPORT_PREFIX`]), seeded kernel models
/// ([`super::SEEDED_MODEL_PREFIX`]) and TG11's readable datatype spellings.
const ADMITTED_PREFIXES: &[&str] =
    &[super::KERNEL_IMPORT_PREFIX, super::SEEDED_MODEL_PREFIX, "trust_type_"];

/// The namespace of TG11's nominal datatype faces (`trust_odt::TypeKey`).
const ADMITTED_NAMESPACE: &str = "TrustOdt";

/// Every name in an admitted namespace a text spells, read with Clean's lexer
/// (comments and string literals do not count): each identifier with a
/// component in [`ADMITTED_PREFIXES`] or under [`ADMITTED_NAMESPACE`], whole,
/// and each `trust_import_…` component alone (the TG3 deferral predicate,
/// [`super::island_kernel_import_identifiers`]). A spelled name is a
/// dependency whether or not it exists, so an admission that adds one the
/// island resolved past misses.
fn spelled_admitted_names(text: &str) -> BTreeSet<String> {
    let mut names: BTreeSet<String> = super::island_kernel_import_identifiers(text)
        .into_iter()
        .map(|(_, _, name)| name)
        .collect();
    for name in dotted_identifiers(text) {
        let admitted = name.split('.').next() == Some(ADMITTED_NAMESPACE)
            || name
                .split('.')
                .any(|part| ADMITTED_PREFIXES.iter().any(|prefix| part.starts_with(prefix)));
        if admitted {
            names.insert(name);
        }
    }
    names
}

/// The dotted identifiers a text spells (`a.b.c`), joined from Clean's lexer
/// tokens: identifiers and `.`s with nothing between them.
fn dotted_identifiers(text: &str) -> Vec<String> {
    use clean_parser::lexer::{Lexer, TokenKind};
    let mut names = Vec::new();
    // The identifier being joined, and where it (or its trailing `.`) ends.
    let mut current: Option<(String, usize)> = None;
    let mut dotted = false;
    for token in Lexer::tokenize(text) {
        let adjacent = current.as_ref().is_some_and(|(_, end)| *end == token.span.start);
        match token.kind {
            TokenKind::Ident(part) if adjacent && dotted => {
                if let Some((name, end)) = &mut current {
                    name.push('.');
                    name.push_str(&part);
                    *end = token.span.end;
                }
                dotted = false;
            }
            TokenKind::Dot if adjacent && !dotted => {
                if let Some((_, end)) = &mut current {
                    *end = token.span.end;
                }
                dotted = true;
            }
            kind => {
                names.extend(current.take().map(|(name, _)| name));
                dotted = false;
                if let TokenKind::Ident(part) = kind {
                    current = Some((part, token.span.end));
                }
            }
        }
    }
    names.extend(current.map(|(name, _)| name));
    names
}

/// Whether a text checks a judgment it does not register: an `example`, a
/// `#`-command or an `elab` (read with Clean's lexer). The kernel checks such
/// a judgment against the environment and keeps nothing, so no registered
/// declaration records what it read.
fn checks_without_registering(text: &str) -> bool {
    use clean_parser::lexer::{Lexer, TokenKind};
    Lexer::tokenize(text)
        .into_iter()
        .any(|token| matches!(token.kind, TokenKind::Example | TokenKind::Hash | TokenKind::Elab))
}

/// What a fact's elaboration could have read about one name it reaches: the
/// kernel records under it, what the elaborator reads under it, its
/// verification stamp, its `unsafe` and `partial` marks, its origin and
/// whether it is a staged header (the certification audit reads the last
/// five; the kernel check the first). `None` when the environment holds none
/// of them.
fn dependency_digest(env: &Environment, name: &Name) -> Option<Digest32> {
    if *name == environment_dependency() {
        return Some(environment_digest(env));
    }
    name_digest(env, name)
}

fn name_digest(env: &Environment, name: &Name) -> Option<Digest32> {
    let record = env.kernel_record_digest(name);
    let elaboration = env.elaboration_record_digest(name);
    let stamp = env.declaration_verification(name);
    let origin = env.get_constant_origin(name);
    let marks = [env.is_unsafe(name), env.is_partial(name), env.is_staged_header(name)];
    if record.is_none()
        && elaboration.is_none()
        && stamp.is_none()
        && origin.is_none()
        && marks == [false; 3]
    {
        return None;
    }
    Some(digest_parts(&[
        b"trust.clean-kernel-fact.dependency.v2",
        &record.unwrap_or([0; 32]),
        &[u8::from(record.is_some())],
        &elaboration.unwrap_or([0; 32]),
        &[u8::from(elaboration.is_some())],
        &encode(&stamp).unwrap_or_default(),
        &encode(&origin).unwrap_or_default(),
        &marks.map(u8::from),
    ]))
}

/// What a fact depends on (see the module docs). An accepted elaboration
/// depends on what its declarations reach and on the admitted names its text
/// spells. A judgment checked and not registered (an `example`, a `#guard`)
/// has no declarations to walk, and what it checked can be any name its
/// elaboration resolved, read or missed (a tag table, an alias, a name not
/// admitted yet); it depends on the whole environment the operation ran in,
/// `before`, outside the prelude, so such a fact never outlives a change that
/// could change its verdict. A rejection is never stored, but it is chained
/// with the same whole-environment dependency.
fn fact_dependencies(
    before: &Environment,
    after: &Environment,
    delta: &EnvFactDelta,
    texts: &[&str],
    rejected: bool,
    anonymous: bool,
    metadata_reads: &[Name],
) -> Vec<(Name, Option<Digest32>)> {
    if rejected || anonymous || texts.iter().any(|text| checks_without_registering(text)) {
        return vec![(environment_dependency(), Some(environment_digest(before)))];
    }
    dependencies(after, delta, texts, metadata_reads)
}

fn dependencies(
    env: &Environment,
    delta: &EnvFactDelta,
    texts: &[&str],
    metadata_reads: &[Name],
) -> Vec<(Name, Option<Digest32>)> {
    let prelude = prelude_names();
    let own: HashSet<&Name> = delta.changed_constant_names().into_iter().collect();
    let mut queue: Vec<Name> = own.iter().flat_map(|name| env.kernel_references(name)).collect();
    for text in texts {
        queue.extend(spelled_admitted_names(text).iter().map(|token| Name::from_string(token)));
    }
    // TG9: metadata changes acceptance without occurring in a declaration's
    // type/value. Include exact names (also absent ones) and their full closure.
    queue.extend(metadata_reads.iter().cloned());
    let mut seen: HashSet<Name> = HashSet::new();
    let mut deps = Vec::new();
    while let Some(name) = queue.pop() {
        if own.contains(&name) || prelude.contains(&name) || !seen.insert(name.clone()) {
            continue;
        }
        queue.extend(env.kernel_references(&name));
        deps.push((name.clone(), dependency_digest(env, &name)));
    }
    deps.sort_by(|a, b| a.0.cmp(&b.0));
    deps
}

fn deps_digest(deps: &[(Name, Option<Digest32>)], baseline: Option<&Digest32>) -> Digest32 {
    let mut hasher = Sha256::new();
    for (name, digest) in deps {
        let name = name.to_string();
        hasher.update((name.len() as u64).to_le_bytes());
        hasher.update(name.as_bytes());
        hasher.update(digest.unwrap_or([0; 32]));
        hasher.update([u8::from(digest.is_some())]);
    }
    hasher.update([u8::from(baseline.is_some())]);
    if let Some(digest) = baseline {
        hasher.update(digest);
    }
    hasher.finalize().into()
}

/// See the module docs. A clone is a fork: the same environment, file
/// context, chain, log and facts, from which two sessions go on separately
/// (the resolver's declaration preview).
#[derive(Clone)]
pub(crate) struct KeyedEnv {
    env: OnceCell<Environment>,
    file_ctx: FileContext,
    served: Vec<&'static str>,
    facts: Option<Arc<FactContext>>,
    chain: Digest32,
    log: Vec<LogEntry>,
    /// The facts this session applied, for a rebuild to compare and, when it
    /// disagrees, to quarantine.
    applied: Vec<Applied>,
    /// A hit applied a delta: the file context is behind the environment.
    stale: bool,
    /// Something changed the environment outside an operation: no fact is
    /// read or written from here on.
    poisoned: bool,
    /// The log cannot rebuild the elaborator (an admission window could not
    /// be recorded); an elaboration that needs a rebuild fails closed.
    unrebuildable: Option<String>,
    in_op: bool,
    /// TG14: the caller runs ordinary check_all transactionally and restores
    /// its checkpoint on a rejection, so a rejection poisons this working copy.
    /// It controls that poison, never the operation's meaning, key or storage.
    transactional: bool,
    /// An open admission window: the environment before its first admission.
    admission_base: Option<Environment>,
    admitting: bool,
    /// Keyed operations this session elaborated (misses and audits).
    pub(crate) elaborations: usize,
    /// Times this session rebuilt a stale elaborator.
    pub(crate) rebuilds: usize,
}

fn fresh_file_ctx() -> FileContext {
    let mut file_ctx = FileContext::new();
    file_ctx.disable_external_import_search();
    file_ctx
}

impl KeyedEnv {
    pub(crate) fn new() -> Self {
        Self {
            env: OnceCell::new(),
            file_ctx: fresh_file_ctx(),
            served: Vec::new(),
            facts: None,
            chain: digest_parts(&[b"trust.clean-kernel-fact.chain.v1"]),
            log: Vec::new(),
            applied: Vec::new(),
            stale: false,
            poisoned: false,
            unrebuildable: None,
            in_op: false,
            transactional: false,
            admission_base: None,
            admitting: false,
            elaborations: 0,
            rebuilds: 0,
        }
    }

    /// Read facts through `facts` from here on. Only an untouched session
    /// may: a session whose environment already changed has history no key
    /// names.
    ///
    /// Every change to the environment is either a logged operation or
    /// poisons the session, so an empty log on an unpoisoned session means
    /// the environment is still the prelude.
    pub(crate) fn enable_facts(&mut self, facts: Arc<FactContext>) {
        if self.log.is_empty() && !self.poisoned && self.admission_base.is_none() {
            self.facts = Some(facts);
        }
    }

    /// Whether this session reads and writes facts.
    pub(crate) fn active(&self) -> Option<&Arc<FactContext>> {
        if self.poisoned { None } else { self.facts.as_ref() }
    }

    pub(crate) fn env(&self) -> &Environment {
        self.env.get_or_init(Environment::with_prelude)
    }

    pub(crate) fn is_materialized(&self) -> bool {
        self.env.get().is_some()
    }

    pub(crate) fn served(&self) -> &[&'static str] {
        &self.served
    }

    pub(crate) fn is_stale(&self) -> bool {
        self.stale
    }

    fn env_slot(&mut self) -> &mut Environment {
        self.env.get_or_init(Environment::with_prelude);
        self.env.get_mut().expect("initialized on the line above")
    }

    /// Mutable access to the environment, the file context and the served
    /// modules. Inside an operation (or a rebuild) this is the operation's
    /// own; outside one it POISONS the session.
    pub(crate) fn parts_mut(
        &mut self,
    ) -> (&mut Environment, &mut FileContext, &mut Vec<&'static str>) {
        assert!(
            !self.stale,
            "internal: a stale Clean elaborator was handed out; every entry point rebuilds first"
        );
        if !self.in_op {
            self.poison("an unkeyed change to the session");
        }
        self.env.get_or_init(Environment::with_prelude);
        let env = self.env.get_mut().expect("initialized on the line above");
        (env, &mut self.file_ctx, &mut self.served)
    }

    /// Mutable access to the environment alone; see [`Self::parts_mut`]. An
    /// open admission window is keyed (by the dependencies of later facts),
    /// so it does not poison.
    pub(crate) fn env_mut(&mut self) -> &mut Environment {
        if !self.in_op && !self.admitting {
            self.poison("an unkeyed change to the environment");
        }
        self.env_slot()
    }

    /// The environment, for a unit test that drives the kernel directly (an
    /// unkeyed change: it poisons, like any other).
    #[cfg(test)]
    pub(crate) fn env_mut_for_tests(&mut self) -> &mut Environment {
        self.env_mut()
    }

    /// The elaborator's file context, for a unit test to read.
    #[cfg(test)]
    pub(crate) fn file_ctx_for_tests(&self) -> &FileContext {
        &self.file_ctx
    }

    fn poison(&mut self, why: &str) {
        if !self.poisoned && self.facts.is_some() {
            stat("UNKEYED", why);
        }
        self.poisoned = true;
        self.admission_base = None;
    }

    // -----------------------------------------------------------------------
    // Program admissions
    // -----------------------------------------------------------------------

    /// Run `admit` with the environment open for program admissions. The
    /// first admission after an operation opens a window; the next operation
    /// closes it and logs its delta.
    ///
    /// Before facts are enabled there is no window to open: the admission is
    /// an unkeyed change, so a later [`Self::enable_facts`] refuses (its
    /// premise, a prelude environment, would no longer hold).
    pub(crate) fn admit<R>(&mut self, admit: impl FnOnce(&mut Environment) -> R) -> R {
        if self.active().is_none() {
            self.poison("an admission outside a fact-keyed session");
        } else if self.admission_base.is_none() {
            let base = self.env().clone();
            self.admission_base = Some(base);
        }
        self.admitting = true;
        let result = admit(self.env_slot());
        self.admitting = false;
        result
    }

    fn close_admissions(&mut self) {
        let Some(base) = self.admission_base.take() else { return };
        // Reference entry construction screens the WHOLE base's metadata,
        // while a successful fact's body dependencies cover only its closure.
        // An unrelated structurally admitted/non-Lean record must not let a
        // cached acceptance survive where fresh checking would refuse.
        // This performs no body reproof; supported unrelated bodies keep hits.
        if clean_kernel::ReferenceKernel::new(self.env().clone()).is_err() {
            self.poison("an admission made the reference base ineligible");
        }

        let recorded =
            self.env().local_fact_delta_since(&base).map_err(|error| error.to_string()).and_then(
                |delta| match delta.changed_session_table() {
                    // A fact's dependencies cover per-name records only.
                    Some(table) => Err(format!(
                        "it changed `{table}`, session state no fact dependency covers"
                    )),
                    None => delta.encode().map_err(|error| error.to_string()),
                },
            );
        match recorded {
            Ok(bytes) => self.log.push(LogEntry::unparameterized(LoggedOp::Admissions(bytes))),
            Err(why) => {
                if self.stale {
                    self.unrebuildable = Some(format!("an admission window: {why}"));
                }
                self.poison("an admission window the log cannot record");
            }
        }
    }

    // -----------------------------------------------------------------------
    // Logged operations that are not facts (cheap, applied for real)
    // -----------------------------------------------------------------------

    /// Fold `op` into the chain and the log, then run it for real.
    pub(crate) fn logged<R>(
        &mut self,
        op: LoggedOp,
        run: impl FnOnce(&mut Environment, &mut FileContext) -> R,
    ) -> R {
        self.close_admissions();
        if let Some(bytes) = encode(&op) {
            self.chain = digest_parts(&[b"logged", &self.chain, &bytes]);
        } else {
            self.poison("an unencodable operation");
        }
        self.log.push(LogEntry::unparameterized(op));
        self.in_op = true;
        self.env.get_or_init(Environment::with_prelude);
        let env = self.env.get_mut().expect("initialized on the line above");
        let result = run(env, &mut self.file_ctx);
        self.in_op = false;
        result
    }

    // -----------------------------------------------------------------------
    // Facts
    // -----------------------------------------------------------------------

    fn key(&self, facts: &FactContext, op: &LoggedOp, params: &SessionParams) -> Option<Digest32> {
        let theory = format!("{:?}", self.env().kernel_theory());
        Some(digest_parts(&[
            // v2 (2026-11-07): v1 facts were written while rejections were
            // stored (`TG6-FACTS-1` (9)); no v1 key is looked up again, so no
            // rejection stored then, under load or not, is ever hit.
            b"trust.clean-kernel-fact.key.v2",
            &facts.key_prefix(),
            theory.as_bytes(),
            &self.chain,
            &encode(params)?,
            &encode(op)?,
        ]))
    }

    /// Look `op` up. A hit is applied here; a miss (or an audited hit) is
    /// returned to be elaborated between [`Self::begin`] and [`Self::finish`].
    pub(crate) fn lookup(&mut self, op: LoggedOp, params: &SessionParams) -> Lookup {
        self.close_admissions();
        let unkeyed = |op| {
            Lookup::Miss(Box::new(Pending {
                key: None,
                op,
                params: params.clone(),
                before: None,
                audit: None,
            }))
        };
        let Some(facts) = self.active().cloned() else {
            return unkeyed(op);
        };
        let Some(key) = self.key(&facts, &op, params) else {
            self.poison("an unencodable key");
            return unkeyed(op);
        };
        let miss = |audit: Option<(Digest32, StoredFact)>| {
            Lookup::Miss(Box::new(Pending {
                key: Some(key),
                op: op.clone(),
                params: params.clone(),
                before: None,
                audit,
            }))
        };
        let (object, bytes) = match facts.store().get(&key) {
            StoreRead::Present { object, bytes } => (object, bytes),
            StoreRead::Absent => {
                stat("MISS", format_args!("{} key={}", op.kind(), hex(&key)));
                return miss(None);
            }
            StoreRead::Quarantined(why) => {
                stat("MISS", format_args!("{} key={} quarantined={why}", op.kind(), hex(&key)));
                return miss(None);
            }
        };
        let fact = match StoredFact::decode(&bytes) {
            Ok(fact) if fact.key == key && fact.op == op && fact.params == *params => fact,
            Ok(_) | Err(_) => {
                facts.store().quarantine_fact(&key, &object, "the fact does not name its key");
                return miss(None);
            }
        };
        if fact.model_baseline_names.is_some()
            && constant_names_digest(self.env()) != fact.model_baseline_names
        {
            stat("MISS", format_args!("{} key={} changed=constant-names", op.kind(), hex(&key)));
            return miss(None);
        }
        if let Some((name, _)) =
            fact.deps.iter().find(|(name, digest)| dependency_digest(self.env(), name) != *digest)
        {
            stat("MISS", format_args!("{} key={} changed={name}", op.kind(), hex(&key)));
            return miss(None);
        }
        if facts.audits(&key) {
            stat("AUDIT", format_args!("{} key={}", op.kind(), hex(&key)));
            return miss(Some((object, fact)));
        }
        match self.apply(&fact) {
            Ok(()) => {
                stat("HIT", format_args!("{} key={}", op.kind(), hex(&key)));
                self.applied.push(Applied {
                    key,
                    object,
                    index: self.log.len() - 1,
                    outcome: Sha256::digest(&fact.outcome).into(),
                });
                Lookup::Hit(fact.outcome)
            }
            Err(why) => {
                stat("MISS", format_args!("{} key={} refused={why}", op.kind(), hex(&key)));
                miss(None)
            }
        }
    }

    fn apply(&mut self, fact: &StoredFact) -> Result<(), String> {
        let served: Vec<&'static str> = fact
            .served_after
            .iter()
            .map(|module| {
                trust_temporal_prelude::MODULES
                    .iter()
                    .find(|(name, _, _)| *name == module.as_str())
                    .map(|(name, _, _)| *name)
                    .ok_or_else(|| format!("served module `{module}` is unknown"))
            })
            .collect::<Result<_, _>>()?;
        let delta = EnvFactDelta::decode(&fact.delta).map_err(|error| error.to_string())?;
        self.env_slot().apply_local_fact_delta(&delta).map_err(|error| error.to_string())?;
        self.served = served;
        self.chain = digest_parts(&[
            b"fact",
            &self.chain,
            &fact.key,
            &deps_digest(&fact.deps, fact.model_baseline_names.as_ref()),
            &Sha256::digest(&fact.delta),
            &Sha256::digest(&fact.outcome),
        ]);
        self.log.push(LogEntry { op: fact.op.clone(), params: Some(fact.params.clone()) });
        self.stale = true;
        Ok(())
    }

    /// Start elaborating a miss. The caller has rebuilt a stale session.
    pub(crate) fn begin(&mut self, pending: &mut Pending) {
        assert!(!self.stale, "internal: elaborating on a stale Clean elaborator");
        if pending.key.is_some() && self.active().is_some() {
            pending.before = Some(self.env().clone());
        }
        self.elaborations += 1;
        if self.facts.is_some() {
            let why = if pending.audit.is_some() {
                "audit"
            } else if pending.key.is_some() {
                "miss"
            } else {
                "unkeyed"
            };
            stat("ELABORATE", format_args!("{} {why}", pending.op.kind()));
        }
        self.in_op = true;
    }

    /// Mark the caller as running ordinary check_all transactionally. A
    /// rejection then poisons this working copy; the caller must restore its
    /// checkpoint before using independent facts. Accepted checks keep their
    /// ordinary dependency keys, replay log and stored facts.
    pub(crate) fn set_transactional(&mut self, transactional: bool) {
        self.transactional = transactional;
    }

    /// Finish a miss: log it, and store its fact when it was accepted and its
    /// delta is replayable. `outcome` is the stored form of what the caller
    /// returns.
    ///
    /// A REJECTED elaboration is never stored (`TG6-FACTS-1` (9), amended
    /// 2026-11-07). Storing one rested on elaboration being a function of the
    /// key, and it is not: Clean's `grind` gives its automation engine a wall
    /// clock budget and `smt` a timeout, so a rejection made under load would
    /// fail every later build that hit it. An acceptance is kernel-checked and
    /// no clock can make one false. Outside a transactional check a rejection
    /// is still chained and logged like an acceptance, so the operations after
    /// it in this session key the same way. It is only re-elaborated in the
    /// next build, and every rejection fails its build, so the cost falls on
    /// failing builds alone.
    pub(crate) fn finish(
        &mut self,
        pending: Pending,
        outcome: Option<Vec<u8>>,
        rejected: bool,
        anonymous: bool,
        metadata_reads: &[Name],
        model_baseline_read: bool,
    ) {
        self.in_op = false;
        if rejected && self.transactional {
            // The caller restores its full checkpoint. Until then, partial
            // declarations cannot authorize any further fact operation.
            if let (Some(key), Some((object, _))) = (pending.key, &pending.audit) {
                self.audit_failed(&key, object, "a transactional import recheck was rejected");
            }
            stat("DISCARD", "rejected transactional import island; no fact stored");
            self.poison("a rejected transactional import island");
            return;
        }
        let Pending { key, op, params, before, audit } = pending;
        let texts: Vec<String> = op.texts().into_iter().map(str::to_string).collect();
        let prior = std::mem::take(&mut self.log);
        self.log = prior.clone();
        self.log.push(LogEntry { op: op.clone(), params: Some(params.clone()) });
        let (Some(key), Some(before), Some(facts), Some(outcome)) =
            (key, before, self.active().cloned(), outcome)
        else {
            if let (Some((object, _)), Some(key)) = (audit, key) {
                self.audit_failed(&key, &object, "the re-elaboration has no stored form");
            }
            self.poison("an elaboration that stores no fact");
            return;
        };
        let texts: Vec<&str> = texts.iter().map(String::as_str).collect();
        let delta = match self.env().local_fact_delta_since(&before) {
            Ok(delta) => delta,
            Err(why) => {
                stat("UNSTORABLE", format_args!("{} key={} why={why}", op.kind(), hex(&key)));
                self.poison("an elaboration whose delta is not replayable");
                return;
            }
        };
        let deps = fact_dependencies(
            &before,
            self.env(),
            &delta,
            &texts,
            rejected,
            anonymous,
            metadata_reads,
        );
        let model_baseline_names = if model_baseline_read {
            let Some(digest) = constant_names_digest(&before) else {
                self.poison("an unencodable model-name baseline");
                return;
            };
            Some(digest)
        } else {
            None
        };
        drop(before);
        let Ok(delta_bytes) = delta.encode() else {
            self.poison("an unencodable delta");
            return;
        };
        let fact = StoredFact {
            format: clean_fact::FACT_FORMAT.to_string(),
            key,
            params,
            prior,
            op,
            deps,
            model_baseline_names,
            delta: delta_bytes,
            outcome,
            served_after: self.served.iter().map(|module| (*module).to_string()).collect(),
        };
        if let Some((object, stored)) = &audit {
            if stored.delta == fact.delta
                && stored.outcome == fact.outcome
                && stored.deps == fact.deps
                && stored.model_baseline_names == fact.model_baseline_names
            {
                stat("AUDIT-MATCH", format_args!("key={}", hex(&key)));
            } else {
                self.audit_failed(&key, object, "a re-elaboration differs from the stored fact");
            }
        }
        self.chain = digest_parts(&[
            b"fact",
            &self.chain,
            &key,
            &deps_digest(&fact.deps, fact.model_baseline_names.as_ref()),
            &Sha256::digest(&fact.delta),
            &Sha256::digest(&fact.outcome),
        ]);
        if rejected {
            stat("DISCARD", format_args!("{} key={} rejected", fact.op.kind(), hex(&key)));
            return;
        }
        let Some(bytes) = encode(&fact) else {
            self.poison("an unencodable fact");
            return;
        };
        match facts.store().put(&key, &bytes) {
            Ok(_) => {
                facts.note_written();
                stat(
                    "STORE",
                    format_args!("{} key={} bytes={}", fact.op.kind(), hex(&key), bytes.len()),
                );
            }
            Err(error) => stat("UNSTORABLE", format_args!("key={} write={error}", hex(&key))),
        }
    }

    fn audit_failed(&mut self, key: &Digest32, object: &Digest32, why: &str) {
        stat("AUDIT-MISMATCH", format_args!("key={} why={why}", hex(key)));
        if let Some(facts) = self.facts.clone() {
            facts.store().quarantine_fact(key, object, why);
        }
    }

    // -----------------------------------------------------------------------
    // Rebuilding a stale elaborator
    // -----------------------------------------------------------------------

    /// Start a rebuild: hand the caller the log to replay with real
    /// elaboration, and reset the elaborator to a fresh prelude. Returns the
    /// environment the hits built, for [`Self::finish_rebuild`] to compare.
    /// An open admission window is closed first, so the log replays it.
    pub(crate) fn start_rebuild(&mut self) -> Result<(Vec<LogEntry>, Environment), String> {
        self.close_admissions();
        if let Some(why) = &self.unrebuildable {
            return Err(why.clone());
        }
        let log = std::mem::take(&mut self.log);
        let built = self.env.take().unwrap_or_else(Environment::with_prelude);
        self.file_ctx = fresh_file_ctx();
        self.served.clear();
        self.stale = false;
        self.in_op = true;
        self.rebuilds += 1;
        stat("REBUILD", format_args!("ops={}", log.len()));
        Ok((log, built))
    }

    /// Replay one admission window during a rebuild.
    pub(crate) fn replay_admissions(&mut self, bytes: &[u8]) -> Result<(), String> {
        let delta = EnvFactDelta::decode(bytes).map_err(|error| error.to_string())?;
        self.env_slot().apply_local_fact_delta(&delta).map_err(|error| error.to_string())
    }

    /// Whether a rebuild's replay of log entry `index` returned something
    /// other than the outcome the hit that produced the entry returned. An
    /// entry no hit produced has nothing to compare.
    pub(crate) fn replay_differs(&self, index: usize, outcome: Option<&[u8]>) -> bool {
        self.applied.iter().find(|applied| applied.index == index).is_some_and(|applied| {
            outcome.map(|bytes| Digest32::from(Sha256::digest(bytes))) != Some(applied.outcome)
        })
    }

    /// Finish a rebuild: restore the log and compare the rebuilt environment
    /// with the one the hits built. `diverged` is the first replayed outcome
    /// the caller found to differ from its hit's. A difference means a fact
    /// this session applied was wrong: every one of them is quarantined, the
    /// rebuilt environment stands, and `Err` says what differed, for the
    /// caller to fail the operation that triggered the rebuild.
    pub(crate) fn finish_rebuild(
        &mut self,
        log: Vec<LogEntry>,
        built: &Environment,
        diverged: Option<String>,
    ) -> Result<(), String> {
        self.in_op = false;
        self.log = log;
        let Some(difference) = diverged.or_else(|| self.env().local_fact_difference(built)) else {
            return Ok(());
        };
        for applied in std::mem::take(&mut self.applied) {
            self.audit_failed(
                &applied.key,
                &applied.object,
                &format!("a rebuild differs in {difference}"),
            );
        }
        Err(format!(
            "a fact this session applied disagrees with real elaboration ({difference}); every \
             fact it applied is quarantined"
        ))
    }
}

// ---------------------------------------------------------------------------
// Re-checking stored facts (`targo trust store verify --facts`)
// ---------------------------------------------------------------------------

/// One fact's re-check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FactRecheck {
    /// Elaborated again from its own log, it produced the same delta, outcome
    /// and dependencies.
    Reproduced,
    /// It did not; the fact is quarantined.
    Differs(String),
}

/// What [`super::verify_fact_store`] found.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FactStoreReport {
    /// Facts whose re-check reproduced them.
    pub reproduced: usize,
    /// Facts quarantined because the re-check did not.
    pub quarantined: Vec<(String, String)>,
    /// What the integrity rescan found first.
    pub rescan: clean_fact::RescanReport,
}

impl super::CleanIslandSession {
    /// Re-check one stored fact from scratch: a fresh session with the fact's
    /// settings replays every operation before it with real elaboration, then
    /// performs its own, and compares delta, outcome and dependencies.
    pub(crate) fn recheck_fact(fact: &StoredFact) -> FactRecheck {
        let mut session = Self::new();
        session.keyed.in_op = true;
        let mut prepared = None;
        for entry in &fact.prior {
            if let Some(params) = &entry.params {
                session.set_params(params);
            }
            if let Err(why) = session.replay(&entry.op, &mut prepared) {
                return FactRecheck::Differs(format!("its log does not replay: {why}"));
            }
        }
        session.set_params(&fact.params);
        let before = session.env().clone();
        let (outcome, rejected, anonymous) = match &fact.op {
            // No rejection is stored now, but a store can hold one written
            // before that (under a v1 key) or forged. It is re-checked like an
            // acceptance: by its outcome, compared below.
            LoggedOp::CheckAll(sources) => {
                let sources: Vec<&str> = sources.iter().map(String::as_str).collect();
                let batch = session.check_all_uncached(&sources);
                (super::encode_batch(&batch), batch.is_rejected(), batch.has_anonymous_judgments())
            }
            LoggedOp::Check(source) => {
                let outcome = session.check_uncached(source);
                (
                    super::encode_outcome(&outcome),
                    outcome.is_rejected(),
                    outcome.anonymous_judgments != 0,
                )
            }
            LoggedOp::Prepare(sources) => {
                let sources: Vec<&str> = sources.iter().map(String::as_str).collect();
                let declarations = session.prepare_declarations(&sources, true);
                (
                    declarations.encode(),
                    declarations.is_rejected(),
                    declarations.has_anonymous_judgments(),
                )
            }
            LoggedOp::Report(sources) => {
                let Some(declarations) = prepared.take() else {
                    return FactRecheck::Differs("a report with no preparation before it".into());
                };
                let sources: Vec<&str> = sources.iter().map(String::as_str).collect();
                let batch = session.finish_declarations(&sources, declarations);
                (super::encode_batch(&batch), batch.is_rejected(), batch.has_anonymous_judgments())
            }
            other => return FactRecheck::Differs(format!("a `{}` is not a fact", other.kind())),
        };
        let texts = fact.op.texts();
        let delta = match session.env().local_fact_delta_since(&before) {
            Ok(delta) => delta,
            Err(why) => return FactRecheck::Differs(format!("its delta: {why}")),
        };
        if delta.encode().ok().as_deref() != Some(fact.delta.as_slice()) {
            return FactRecheck::Differs("its environment delta differs".to_string());
        }
        if outcome.as_deref() != Some(fact.outcome.as_slice()) {
            return FactRecheck::Differs("its outcome differs".to_string());
        }
        let baseline = if session.model_baseline_read {
            let Some(digest) = constant_names_digest(&before) else {
                return FactRecheck::Differs("its model-name baseline does not encode".into());
            };
            Some(digest)
        } else {
            None
        };
        if baseline != fact.model_baseline_names {
            return FactRecheck::Differs("its model-name baseline differs".into());
        }
        if fact_dependencies(
            &before,
            session.env(),
            &delta,
            &texts,
            rejected,
            anonymous,
            &session.model_metadata_reads,
        ) != fact.deps
        {
            return FactRecheck::Differs("its dependencies differ".to_string());
        }
        FactRecheck::Reproduced
    }
}

/// Rescan the store's integrity, then re-check every fact this compiler
/// identity can read; quarantine each one that does not reproduce.
pub(crate) fn verify_store(store: &clean_fact::FactStore) -> FactStoreReport {
    let mut report = FactStoreReport { rescan: store.rescan(), ..FactStoreReport::default() };
    for key in store.keys() {
        let StoreRead::Present { object, bytes } = store.get(&key) else { continue };
        let verdict = match StoredFact::decode(&bytes) {
            Ok(fact) if fact.key == key => super::CleanIslandSession::recheck_fact(&fact),
            Ok(_) => FactRecheck::Differs("the fact does not name its key".to_string()),
            Err(why) => FactRecheck::Differs(why),
        };
        match verdict {
            FactRecheck::Reproduced => report.reproduced += 1,
            FactRecheck::Differs(why) => {
                store.quarantine_fact(&key, &object, &why);
                report.quarantined.push((hex(&key), why));
            }
        }
    }
    report
}

#[cfg(test)]
#[path = "keyed_env_tests.rs"]
mod tests;
