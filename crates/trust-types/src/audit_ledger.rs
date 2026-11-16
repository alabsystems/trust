//! The L4 audit ledger: the size refusals T3 L4 deletes or moves, the stops the
//! determinism ledger notes, and the certification runs a stop reached, each with the body
//! it belongs to, for `TRUST_ELIDE_AUDIT` (work item T3, landing L4, commit C06a).
//!
//! Plan: `docs/design/2026-10-11-t3-l4-commit-plan.md` (C06a; L4-AUDIT-1, L4-SCOPE-1,
//! L4-CAP-1; the queue's L4-AUDIT-7, L4-AUDIT-8 and L4-SCOPE-2). The rows it feeds are
//! documented beside the compiler's writer
//! (`compiler/rustc_mir_transform/src/trust_verify/elide_audit.rs`) and read by
//! `targo trust gate compare-audit --l4`.
//!
//! # Measurement only
//!
//! No verdict, key, transport byte, `.stderr` or crate accounting reads anything here. The
//! one production spelling [`build_independent`] reads, the SC-8 row disclosure, is
//! defined beside the spawn census's vocabulary ([`crate::SC8_ROW_DISCLOSURE_OPEN`]) and
//! only read here. With `TRUST_ELIDE_AUDIT` unset or empty nothing is computed: every
//! recording entry point returns after one read of a `LazyLock`. The ledger is separate
//! from the determinism ledger ([`crate::determinism::take_noted_stops`]) and never drains
//! it; a noted stop is copied here as well, never moved.
//!
//! # Attribution (L4-SCOPE-1, L4-SCOPE-2)
//!
//! An entry belongs to the INNERMOST [`Scope`] open on the thread that records it. On a
//! thread that opened no scope (a solver's rayon worker, a watchdog) it belongs to the
//! innermost open scope when every open scope was opened on one thread, and is
//! crate-level otherwise; with no scope open it is crate-level. Solver work runs on rayon
//! and helper threads as well as on the thread that verifies the body, the same reason the
//! determinism ledger is process-wide, and a Trust proof session runs ONE front-end thread
//! whatever `-Zthreads` asks (`rustc_session::trust_frontend_threads_by_flags`, T4.3), so
//! every body scope of a verifying unit is opened on that thread. Innermost, because a
//! body's pass can run nested in another's (publication forcing `optimized_mir` of another
//! body): the outer pass waits while the nested one runs, so what is recorded then is the
//! nested body's. The compiler opens one scope per body in `run_pass`, one for the R1
//! pre-pass (`crate:r1`) and one for crate finalization (`crate:finalize`); a body scope is
//! drained into the body's rows when the body's pass ends, and the crate-level entries with
//! the crate accounting. Residual, named: a helper thread that outlives the call that
//! started it (a solver its caller stopped waiting for) records into whichever scope is
//! innermost when it finishes. Attribution is per function, because a refusal site cannot
//! know an obligation key.
//!
//! # Cap sites
//!
//! A CAP site is the census's `<file>:<CONSTANT>`
//! (`docs/audits/2026-10-08-t3-size-threshold-census.tsv`) or a named refusal that keys on
//! one; the native `targo-trust/src/audit_comparison/caps.rs` catalog maps each to the
//! L4 commit that deletes or moves it. A site records a hit with [`cap_hit`], or inline in
//! the condition that refuses with [`cap_hit_if`], which returns the condition unchanged.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{LazyLock, Mutex, MutexGuard, PoisonError};
use std::thread::ThreadId;

use crate::determinism::{StopCause, StopItem};

/// The audit directory `TRUST_ELIDE_AUDIT` names, or `None` when it is unset or empty.
static AUDIT_DIRECTORY: LazyLock<Option<PathBuf>> = LazyLock::new(|| {
    std::env::var_os("TRUST_ELIDE_AUDIT").filter(|value| !value.is_empty()).map(PathBuf::from)
});

/// The process's ledger.
static LEDGER: Ledger = Ledger::new();

/// Whether `TRUST_ELIDE_AUDIT` names a directory: one `LazyLock` read.
#[must_use]
pub fn enabled() -> bool {
    AUDIT_DIRECTORY.is_some()
}

/// The audit directory, when the audit is enabled.
#[must_use]
pub fn directory() -> Option<&'static Path> {
    AUDIT_DIRECTORY.as_deref()
}

/// One measurement the ledger holds.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum AuditEntry {
    /// One hit of a size refusal an L4 commit deletes or moves (`CAP <site>`).
    Cap {
        /// The census's `<file>:<CONSTANT>`, or a named refusal.
        site: &'static str,
    },
    /// A stop the determinism ledger noted (`STOP <lane> <cause>`): every stop
    /// [`crate::determinism::note_stop`] records and every named one
    /// [`crate::determinism::note_item`] records.
    Stop {
        /// The lane that saw it.
        lane: String,
        /// What ended the work.
        cause: StopCause,
        /// The named stop, when the lane recognised one.
        item: Option<StopItem>,
    },
    /// A certification run a stop reached (`CERTIFY-STOP <index> <cause>`): a run whose
    /// own work a clock or budget stopped, or a row a deadline kept from the kernel.
    CertifyStop {
        /// The row's index in the results the caller certified, when it has one.
        index: Option<usize>,
        /// The least reproducible stop the run saw.
        cause: StopCause,
    },
}

impl AuditEntry {
    /// The row kind this entry is written as.
    #[must_use]
    pub fn kind(&self) -> &'static str {
        match self {
            AuditEntry::Cap { .. } => "CAP",
            AuditEntry::Stop { .. } => "STOP",
            AuditEntry::CertifyStop { .. } => "CERTIFY-STOP",
        }
    }

    /// The row's columns after its function columns.
    #[must_use]
    pub fn columns(&self) -> Vec<String> {
        match self {
            AuditEntry::Cap { site } => vec![(*site).to_string()],
            AuditEntry::Stop { lane, cause, item } => {
                let lane = match item {
                    Some(item) => format!("{lane}[{item}]"),
                    None => lane.clone(),
                };
                vec![lane, cause.as_str().to_string()]
            }
            AuditEntry::CertifyStop { index, cause } => vec![
                index.map_or_else(|| "-".to_string(), |index| index.to_string()),
                cause.as_str().to_string(),
            ],
        }
    }
}

/// One open scope: its id, the thread that opened it, and its entries.
#[derive(Debug)]
struct ActiveScope {
    id: u64,
    thread: ThreadId,
    entries: Vec<AuditEntry>,
}

#[derive(Debug)]
struct LedgerState {
    next_scope: u64,
    /// The open scopes, in the order they were entered.
    active: Vec<ActiveScope>,
    /// Entries no open scope owns (module docs).
    crate_level: Vec<AuditEntry>,
}

impl LedgerState {
    /// The open scope an entry recorded on `thread` belongs to (module docs), by position.
    fn owner(&self, thread: ThreadId) -> Option<usize> {
        if let Some(own) = self.active.iter().rposition(|scope| scope.thread == thread) {
            return Some(own);
        }
        let holder = self.active.first()?.thread;
        if self.active.iter().all(|scope| scope.thread == holder) {
            self.active.len().checked_sub(1)
        } else {
            None
        }
    }
}

/// Scopes and the entries recorded under them (module docs). The process has one, behind
/// the free functions of this module; a test builds its own.
#[derive(Debug)]
pub struct Ledger {
    state: Mutex<LedgerState>,
}

impl Default for Ledger {
    fn default() -> Self {
        Self::new()
    }
}

impl Ledger {
    /// An empty ledger.
    #[must_use]
    pub const fn new() -> Self {
        Ledger {
            state: Mutex::new(LedgerState {
                next_scope: 0,
                active: Vec::new(),
                crate_level: Vec::new(),
            }),
        }
    }

    fn state(&self) -> MutexGuard<'_, LedgerState> {
        // A poisoned ledger still holds what was recorded before the panic.
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Record `entry`: to the scope that owns it (module docs), or crate-level.
    pub fn record(&self, entry: AuditEntry) {
        let thread = std::thread::current().id();
        let mut guard = self.state();
        let state = &mut *guard;
        match state.owner(thread).and_then(|at| state.active.get_mut(at)) {
            Some(scope) => scope.entries.push(entry),
            None => state.crate_level.push(entry),
        }
    }

    /// Open a scope named `label` on the calling thread.
    pub fn enter(&self, label: &str) -> Scope<'_> {
        let thread = std::thread::current().id();
        let mut state = self.state();
        let id = state.next_scope;
        state.next_scope = state.next_scope.wrapping_add(1);
        state.active.push(ActiveScope { id, thread, entries: Vec::new() });
        Scope { ledger: self, id, label: label.to_string(), open: true }
    }

    /// Every crate-level entry so far, clearing them.
    pub fn take_crate_level(&self) -> Vec<AuditEntry> {
        std::mem::take(&mut self.state().crate_level)
    }

    /// Close scope `id` and return its entries.
    fn close(&self, id: u64) -> Vec<AuditEntry> {
        let mut state = self.state();
        match state.active.iter().position(|scope| scope.id == id) {
            Some(at) => state.active.remove(at).entries,
            None => Vec::new(),
        }
    }
}

/// An open attribution scope (module docs). [`Scope::finish`] closes it and returns its
/// entries, once: it takes the scope by value. A scope dropped without `finish` (an early
/// return, a panic) hands its entries to the crate level, so none is lost.
#[derive(Debug)]
pub struct Scope<'a> {
    ledger: &'a Ledger,
    id: u64,
    label: String,
    open: bool,
}

impl Scope<'static> {
    /// Open a scope in the process's ledger, or `None` when the audit is disabled.
    #[must_use]
    pub fn enter(label: &str) -> Option<Scope<'static>> {
        enabled().then(|| LEDGER.enter(label))
    }
}

impl Scope<'_> {
    /// The label the scope was opened with.
    #[must_use]
    pub fn label(&self) -> &str {
        &self.label
    }

    /// Close the scope and return the entries attributed to it.
    #[must_use]
    pub fn finish(mut self) -> Vec<AuditEntry> {
        self.open = false;
        self.ledger.close(self.id)
    }
}

impl Drop for Scope<'_> {
    fn drop(&mut self) {
        if self.open {
            let entries = self.ledger.close(self.id);
            self.ledger.state().crate_level.extend(entries);
        }
    }
}

/// Record one hit of the size refusal `site` (module docs). A no-op when the audit is
/// disabled.
pub fn cap_hit(site: &'static str) {
    if enabled() {
        LEDGER.record(AuditEntry::Cap { site });
    }
}

/// [`cap_hit`] when `refused`; returns `refused`, so a site wraps the condition it already
/// refuses on without changing it.
#[must_use]
pub fn cap_hit_if(refused: bool, site: &'static str) -> bool {
    if refused {
        cap_hit(site);
    }
    refused
}

/// Record a stop the determinism ledger noted. A no-op when the audit is disabled.
pub fn stop(lane: &str, cause: StopCause, item: Option<StopItem>) {
    if enabled() {
        LEDGER.record(AuditEntry::Stop { lane: lane.to_string(), cause, item });
    }
}

/// Record a certification run a stop reached. A no-op when the audit is disabled.
pub fn certify_stop(index: Option<usize>, cause: StopCause) {
    if enabled() {
        LEDGER.record(AuditEntry::CertifyStop { index, cause });
    }
}

/// Every crate-level entry of the process's ledger so far, clearing them; empty when the
/// audit is disabled.
#[must_use]
pub fn take_crate_level() -> Vec<AuditEntry> {
    if enabled() { LEDGER.take_crate_level() } else { Vec::new() }
}

/// The prefix of a crate identity stamp in a rendered path (`__trust_crate@<id>::…`,
/// [`crate::stamp_unauthenticated_crate_path`], the id the crate's `StableCrateId`).
const CRATE_STAMP: &str = crate::TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX;

/// The opener of a generic-argument fingerprint (`::<__trust_args@<hex>>`,
/// [`crate::args_fingerprint`]): a stable hash of the arguments, which hashes the
/// `StableCrateId`s of the crates they name.
const ARGS_FINGERPRINT: &str = crate::args_fingerprint::TRUST_ARGS_FINGERPRINT_PREFIX;

/// What opens the crate of rustc's `DefId` debug rendering (`DefId(2:4495 ~
/// core[82a8]::ops::…)`): `~ `, the crate's name, `[`, and the top 16 bits of its
/// `StableCrateId` as four hex digits (`TyCtxt::def_path_debug_str`).
const DEF_PATH_DEBUG_CRATE: &str = "~ ";

/// What an SC-8 row disclosure becomes: its count of causes, and nothing else
/// ([`build_independent`]).
const SC8_CAUSES_COUNTED: &str = " [SC-8 causes=";

/// One function's texts (its rows' canonical VC payloads for `ROWDIGEST`, or its published
/// rows' descriptions for a `VERDICT` row's audit key) as the elision audit compares them
/// between the compilers of two commits (L4-AUDIT-7, L4-AUDIT-8), in the order given.
/// Nothing but the audit reads it.
///
/// A crate's `StableCrateId` hashes the compiler's version, so the compilers of two
/// commits spell one row of one source differently wherever a row renders one: a crate
/// identity stamp (`__trust_crate@<id>`), a generic-argument fingerprint
/// (`__trust_args@<hex>`), and the crate of a rustc `DefId` debug rendering
/// (`~ core[82a8]`). Each id is renamed (`#0`, `#1`, …, one sequence per kind of id) by
/// its first appearance across the WHOLE function: the texts are visited in the order of
/// their own spelling with the ids renamed text by text (which is the same under any
/// build), ties in their given order, and each text is renamed as visited. Two functions'
/// texts are then equal, text for text, exactly when they are equal up to one one-to-one
/// renaming of those ids for the whole function: one crate named by two rows is still one
/// crate, and two crates are still two. What no renaming can show is which id a text
/// names when nothing else in the function names it (an argument fingerprint is the
/// arguments' only identity in the text): such a swap is invisible here, and the
/// in-process row and identity oracles (C07, C09), which compare within one build,
/// are what see it.
///
/// The SC-8 row disclosure ([`crate::SC8_ROW_DISCLOSURE_OPEN`]) names its first causes in
/// the order of a hash of such ids, so no renaming makes two builds' disclosures agree; it
/// becomes its count of causes (` [SC-8 causes=<n>]`), which does not follow the ids. The
/// causes themselves are disclosure only (SC-8 (c) adds no analysis and no premise).
///
/// rustc's `Debug` rendering of a `dyn` type's predicates (`dyn [Binder { value: …, .. }, …]`,
/// which CALL-REACH-1's message prints) lists the projections and the auto traits each in the
/// order of their `DefPathHash`, and a crate's root `DefPathHash` is its `StableCrateId`: two
/// builds can list `Sync` and `Send` the other way round. Each such list is put in an order no
/// build changes before the ids are renamed ([`dyn_predicate_lists_ordered`]).
#[must_use]
pub fn build_independent(texts: &[&str]) -> Vec<String> {
    let counted: Vec<String> = texts
        .iter()
        .map(|text| dyn_predicate_lists_ordered(&sc8_row_disclosures_counted(text)))
        .collect();
    let alone: Vec<String> = counted.iter().map(|text| Renaming::default().apply(text)).collect();
    let mut order: Vec<usize> = (0..counted.len()).collect();
    order.sort_by(|&a, &b| alone.get(a).cmp(&alone.get(b)).then(a.cmp(&b)));
    let mut renaming = Renaming::default();
    let mut out = vec![String::new(); counted.len()];
    for index in order {
        if let (Some(slot), Some(text)) = (out.get_mut(index), counted.get(index)) {
            *slot = renaming.apply(text);
        }
    }
    out
}

/// The ids renamed so far, one sequence per kind of id ([`build_independent`]).
#[derive(Debug, Default)]
struct Renaming {
    stamps: FirstAppearance,
    args: FirstAppearance,
    crates: FirstAppearance,
}

impl Renaming {
    fn apply(&mut self, text: &str) -> String {
        let text = hex_ids_renamed(text, CRATE_STAMP, &mut self.stamps);
        let text = hex_ids_renamed(&text, ARGS_FINGERPRINT, &mut self.args);
        def_path_disambiguators_renamed(&text, &mut self.crates)
    }
}

/// Distinct ids in the order they first appeared.
#[derive(Debug, Default)]
struct FirstAppearance {
    ids: crate::fx::FxHashMap<String, usize>,
}

impl FirstAppearance {
    /// The ordinal of `id`, `id` added when new.
    fn ordinal(&mut self, id: &str) -> usize {
        let next = self.ids.len();
        *self.ids.entry(id.to_string()).or_insert(next)
    }
}

/// `text` with the run of hex digits after every `marker` renamed in `seen` (`#<n>`). A
/// `marker` with no hex digit after it is left as it is.
fn hex_ids_renamed(text: &str, marker: &str, seen: &mut FirstAppearance) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find(marker) {
        let (before, marked) = rest.split_at(at + marker.len());
        out.push_str(before);
        let (id, after) = marked.split_at(marked.bytes().take_while(u8::is_ascii_hexdigit).count());
        if !id.is_empty() {
            out.push('#');
            out.push_str(&seen.ordinal(id).to_string());
        }
        rest = after;
    }
    out.push_str(rest);
    out
}

/// `text` with the crate disambiguator of every rustc `DefId` debug rendering renamed in
/// `seen`: after [`DEF_PATH_DEBUG_CRATE`], a crate name, `[`, four hex digits and `]`, the
/// digits become `#<n>`. A `~ ` followed by anything else is left as it is.
fn def_path_disambiguators_renamed(text: &str, seen: &mut FirstAppearance) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find(DEF_PATH_DEBUG_CRATE) {
        let (before, marked) = rest.split_at(at + DEF_PATH_DEBUG_CRATE.len());
        out.push_str(before);
        let bytes = marked.as_bytes();
        let name = bytes.iter().take_while(|b| b.is_ascii_alphanumeric() || **b == b'_').count();
        let starts_a_name = bytes.first().is_some_and(|b| b.is_ascii_alphabetic() || *b == b'_');
        let disambiguator = bytes.get(name..name + 6).filter(|group| {
            group.first() == Some(&b'[')
                && group.get(1..5).is_some_and(|hex| hex.iter().all(u8::is_ascii_hexdigit))
                && group.get(5) == Some(&b']')
        });
        rest = match (starts_a_name, disambiguator, marked.get(name + 1..name + 5)) {
            (true, Some(_), Some(id)) => {
                out.push_str(&marked[..=name]);
                out.push('#');
                out.push_str(&seen.ordinal(id).to_string());
                &marked[name + 5..]
            }
            _ => marked,
        };
    }
    out.push_str(rest);
    out
}

/// `text` with every SC-8 row disclosure ([`crate::SC8_ROW_DISCLOSURE_OPEN`] through
/// [`crate::SC8_ROW_DISCLOSURE_CLOSE`]) replaced by its count of causes. An opener with
/// no close after it is left as it is.
fn sc8_row_disclosures_counted(text: &str) -> String {
    let (open, close) = (crate::SC8_ROW_DISCLOSURE_OPEN, crate::SC8_ROW_DISCLOSURE_CLOSE);
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find(open) {
        let inner = &rest[at + open.len()..];
        let Some(end) = inner.find(close) else {
            break;
        };
        out.push_str(&rest[..at]);
        out.push_str(SC8_CAUSES_COUNTED);
        out.push_str(&sc8_cause_count(&inner[..end]).to_string());
        out.push(']');
        rest = &inner[end + close.len()..];
    }
    out.push_str(rest);
    out
}

/// How many causes the inside of one SC-8 row disclosure counts
/// ([`crate::sc8_row_disclosure`]): the named ones and the `+<n> more`. A cause may itself
/// hold the separator (`[u8; 4]`), so the named ones count at most
/// [`crate::SC8_ROW_NAMED_CAUSES`]; the count is then a function of the causes, whichever
/// of them a build names first.
fn sc8_cause_count(causes: &str) -> usize {
    let separator = crate::SC8_ROW_DISCLOSURE_SEPARATOR;
    let more = causes.rsplit_once(separator).and_then(|(_, last)| {
        let digits = last.strip_prefix('+')?.strip_suffix(" more")?;
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        digits.parse::<usize>().ok()
    });
    match more {
        Some(more) => crate::SC8_ROW_NAMED_CAUSES.saturating_add(more),
        None => causes.split(separator).count().min(crate::SC8_ROW_NAMED_CAUSES),
    }
}

/// What opens rustc's `Debug` rendering of a `dyn` type's existential predicates
/// (`dyn [Binder { value: Trait(..), .. }, Binder { value: AutoTrait(DefId(..)), .. }] + '..`).
const DYN_PREDICATES_OPEN: &str = "dyn [";

/// What opens each entry of that list (`ty::Binder`'s `Debug`).
const DYN_PREDICATE_ENTRY: &str = "Binder { value: ";

/// `text` with the entries of every `dyn` predicate list ([`DYN_PREDICATES_OPEN`]) in an order
/// no build changes ([`build_independent`]). rustc lists the principal trait first, then the
/// projections, then the auto traits, the last two each in the order of their `DefPathHash`
/// (`ExistentialPredicate::stable_cmp`), which a crate's `StableCrateId` seeds. Each class keeps
/// its place; within the projections and within the auto traits the entries are put in the order
/// of their spelling with every `DefId` index and crate disambiguator left out (the paths, which
/// no build changes), ties in rustc's order. Lists inside an entry are ordered first. A list
/// whose brackets do not close, or one with an entry that is not a `Binder` of a `Trait`,
/// `Projection` or `AutoTrait`, is left as it is: reordering only ever permutes a list's
/// entries, so it can make two builds' texts agree but never hides a different set.
fn dyn_predicate_lists_ordered(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find(DYN_PREDICATES_OPEN) {
        let (before, list_and_after) = rest.split_at(at + DYN_PREDICATES_OPEN.len());
        out.push_str(before);
        rest = match closing_bracket(list_and_after) {
            Some(end) => {
                let (list, after) = list_and_after.split_at(end);
                let inner = dyn_predicate_lists_ordered(list);
                match dyn_entries_ordered(&inner) {
                    Some(ordered) => out.push_str(&ordered),
                    None => out.push_str(&inner),
                }
                after
            }
            None => list_and_after,
        };
    }
    out.push_str(rest);
    out
}

/// The byte index of the `]` that closes the list `text` opens with (brackets, braces and
/// parentheses counted), or `None` when another closer comes first or none comes.
fn closing_bracket(text: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (index, byte) in text.bytes().enumerate() {
        match byte {
            b'(' | b'[' | b'{' => depth = depth.saturating_add(1),
            b')' | b']' | b'}' if depth == 0 => return (byte == b']').then_some(index),
            b')' | b']' | b'}' => depth -= 1,
            _ => {}
        }
    }
    None
}

/// The entries of one `dyn` predicate list ([`dyn_predicate_lists_ordered`]) in their
/// build-independent order, joined as rustc joins them; `None` when an entry is not one of the
/// three classes.
fn dyn_entries_ordered(list: &str) -> Option<String> {
    let mut keyed = Vec::new();
    for (position, entry) in top_level_entries(list)?.into_iter().enumerate() {
        let value = entry.strip_prefix(DYN_PREDICATE_ENTRY)?;
        // rustc compares two principals as equal, so a principal keeps its place.
        let (class, key) = if value.starts_with("Trait(") {
            (0u8, String::new())
        } else if value.starts_with("Projection(") {
            (1, def_ids_left_out(entry))
        } else if value.starts_with("AutoTrait(") {
            (2, def_ids_left_out(entry))
        } else {
            return None;
        };
        keyed.push((class, key, position, entry));
    }
    keyed.sort();
    Some(keyed.into_iter().map(|(_, _, _, entry)| entry).collect::<Vec<_>>().join(", "))
}

/// `list` split at each `, ` outside every bracket, brace and parenthesis.
fn top_level_entries(list: &str) -> Option<Vec<&str>> {
    let bytes = list.as_bytes();
    let mut entries = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;
    for (index, &byte) in bytes.iter().enumerate() {
        match byte {
            b'(' | b'[' | b'{' => depth = depth.saturating_add(1),
            b')' | b']' | b'}' => depth = depth.saturating_sub(1),
            b',' if depth == 0 && bytes.get(index + 1) == Some(&b' ') => {
                entries.push(list.get(start..index)?);
                start = index + 2;
            }
            _ => {}
        }
    }
    entries.push(list.get(start..)?);
    Some(entries)
}

/// `entry` with the index of every `DefId` rendering (`DefId(2:4225 ~ `) and the crate
/// disambiguator after it (`core[16eb]`) left out: the sort key of
/// [`dyn_entries_ordered`].
fn def_ids_left_out(entry: &str) -> String {
    const OPEN: &str = "DefId(";
    let mut out = String::with_capacity(entry.len());
    let mut rest = entry;
    while let Some(at) = rest.find(OPEN) {
        let (before, marked) = rest.split_at(at + OPEN.len());
        out.push_str(before);
        let index = marked.bytes().take_while(|b| b.is_ascii_digit() || *b == b':').count();
        rest = marked.get(index..).unwrap_or(marked);
    }
    out.push_str(rest);
    def_path_disambiguators_renamed(&out, &mut FirstAppearance::default())
}

/// One audit column: a tab, newline or carriage return inside it (a path, a kind tag)
/// would shift every later column of the row, so each becomes a space.
#[must_use]
pub fn escape_column(column: &str) -> String {
    column.chars().map(|c| if matches!(c, '\t' | '\n' | '\r') { ' ' } else { c }).collect()
}

/// One audit row, newline included: `kind`, the function columns, then `columns`, each
/// escaped ([`escape_column`]) and tab-separated.
#[must_use]
pub fn row_line(kind: &str, function: &[&str], columns: &[String]) -> String {
    let mut row = escape_column(kind);
    for column in function.iter().copied().chain(columns.iter().map(String::as_str)) {
        row.push('\t');
        row.push_str(&escape_column(column));
    }
    row.push('\n');
    row
}

/// Append `rows` (whole lines, from [`row_line`]) to `<audit dir>/<file_name>`, one
/// write per row so rows from threads writing at once never interleave inside a line.
/// A failed write loses rows, never a verdict. A no-op when the audit is disabled.
pub fn append_rows(file_name: &str, rows: &[String]) {
    let Some(directory) = directory() else {
        return;
    };
    if rows.is_empty() {
        return;
    }
    if let Ok(mut file) =
        std::fs::OpenOptions::new().create(true).append(true).open(directory.join(file_name))
    {
        for row in rows {
            let _ = file.write_all(row.as_bytes());
        }
    }
}

#[cfg(test)]
#[path = "audit_ledger_tests.rs"]
mod tests;
