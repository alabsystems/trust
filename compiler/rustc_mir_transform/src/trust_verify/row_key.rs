//! Trust (T3 L4, C09; plan `docs/design/2026-10-11-t3-l4-commit-plan.md` C09, design
//! `docs/design/2026-10-08-t3-memory-proportional-reconstruction.md` §8, D-VC-5,
//! ROW-IDENTITY-1): [`RowKey`], the exact key of a row at every exact-identity site, and the
//! identity oracle that runs beside it until C11.
//!
//! A [`RowKey`] holds the row's canonical string (`canonical_exact_vc_payload`, the key the
//! parent compares) and, while the oracle runs, the row's
//! [`RowIdentity`](trust_types::vc_context::RowIdentity) in its body's oracle context.
//!
//! THE RULE (L4-ORACLE-1). The canonical string decides, exactly as on the parent.
//! [`RowKey::same`] compares the two identities in the same call and counts the comparison.
//! `PartialEq` for a key IS [`RowKey::same`], so every type that carries a key
//! (`ExactVcKey`, `ExactResultRowIdentity`, and through it every binding, authority, receipt
//! and record that seals a row) compares it through `same`, by `==`, `!=` or a derived
//! equality, and no comparison site changed. `Hash` hashes the canonical string only, so a
//! hashed table (the dedupe, the origin table, the bridge's counts, the definition-entry
//! counts) finds a key exactly where it found the string. A lookup compares only keys whose
//! strings hash alike, so each of those tables also counts the other direction, two keys
//! whose strings differ and whose identities are one, with [`count_partition`] over the keys
//! it holds.
//!
//! TWO CLASSES (L4-C09-7). A comparison is JUDGED when both keys are identified in one oracle
//! context that is still alive: it is counted in the `identity` class, as a mismatch when the
//! identities disagree with the decision, in either direction. Every other comparison is
//! UNJUDGED, counted in the `identity-scope` class: a key with no identity (made where no
//! context was installed), keys of two contexts, or keys of one context that is gone. The
//! oracle cannot call such keys one row, so it would disagree exactly when the strings are
//! equal, and that is the class's mismatch. An unjudged mismatch is not an identity
//! disagreement: it is a binding that C11, where the identity decides, must give one context
//! before it lets the identity decide there. `PARITY <fn> identity` therefore means what the
//! oracle disagreed with, and `PARITY <fn> identity-scope` what it could not judge.
//!
//! WHERE A STRING LEAVES A KEY. The canonical string is private to this module. It is read
//! out only by [`RowKey::canonical`], for the elision audit's row keys, and
//! `canonical_exact_vc_payload` is called only here and by the audit's own rows: the source
//! census in this module's tests pins both, so a new comparison of bare strings fails it.
//!
//! THE ORACLE'S CONTEXT. A key's identity is interned in a VC context of the oracle's own
//! ([`RowKeyContext`]), one per body collection, not in the body's context: the body's context
//! is owned by the lane writing into it during collection and frozen after it, and the sites
//! see a row only as `(index, vc)`. The context is installed on the thread while it is in use
//! ([`Installed`]): by `collect_verification_artifacts_cached` around one body's collection
//! (`Installed::open`), which leaves it in the frozen context's memo slot
//! (`MemoSlot::RowKeys`, `Installed::adopt`); and again, from that slot, by the verify pass
//! that consumes the artifacts and by the E9 amendment of a pending citation
//! (`Installed::resume`). So a key minted when a capability is sealed and the key of the row it
//! is checked against later are identified in one context. It lives as long as the body's
//! context: a key holds it weakly, so a key kept past the body (the crate's grounded
//! panic-freedom record) retains nothing, and a later comparison of it is unjudged.
//!
//! WHERE A COUNT GOES (L4-C09-6). A comparison is counted into the innermost context installed
//! on the thread, whose pass writes the row of the comparison it is making; with none
//! installed, into a live context of the two keys; with none alive, straight into the
//! compile's [`Ledger`]. Every count is also kept in the ledger, and every row written is
//! marked there, so what no body's row writes (a collection whose own pass never resumes its
//! context, a count into a context after its last row) is written at the crate accounting as
//! `PARITY crate identity` and `PARITY crate identity-scope` ([`take_crate_level`]). The crate
//! accounting runs once every pass and amendment has run, so every count made before it is
//! written exactly once, and one made after it is not written. Two keys neither of
//! which was identified, compared on a thread with no context installed, are not counted:
//! the oracle does not run there (with the audit off, nothing is ever installed).
//!
//! THE OPEN GAP, FOR C11. A key kept past its body is compared, where the crate's sites hold
//! keys past every body (`ClockStops`, the grounded panic-freedom record), with no live
//! context: such a comparison is never judged. It is counted unjudged when either key was
//! identified, and not at all when neither was. U's and TC's `identity` rows at
//! `mismatches=0` therefore say nothing about those sites, and C11 measures them before the
//! identity decides there.
//!
//! THE COST. Nothing is installed, identified or counted unless the elision audit is on
//! (`TRUST_ELIDE_AUDIT`): the count is all the oracle changes, and only the audit's `PARITY`
//! rows read it, as for the row oracle's publication check (`RowResults::check_in`). With the
//! audit on, each key interns its row's span, formula and record into the oracle's context
//! (hash-consed, so a row identified again adds nothing) and its formula's Merkle digest is
//! memoized per node; the context holds at most what the body's rows hold, and is released
//! with them. Each count also takes the ledger's lock once.
//!
//! THE ROW. A body's counts are written as one `PARITY <fn> identity` and one
//! `PARITY <fn> identity-scope` row when the verify pass that consumed its artifacts ends,
//! always, even at `rows=0`; a body whose publication waited for its E9 amendment writes a
//! second pair, for what was counted since. The crate's pair is written at the crate
//! accounting, always.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::cell::RefCell;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use trust_types::VerificationCondition;
use trust_types::formula_merkle::FormulaDigest;
use trust_types::vc_context::{MemoSlot, ParityCount, RowIdentity, VcContext};

use super::elide_audit;

/// The class a comparison is counted in (module docs, TWO CLASSES).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Class {
    /// Both keys identified in one live context: `PARITY <fn> identity`.
    Judged,
    /// Any other comparison: `PARITY <fn> identity-scope`.
    Unjudged,
}

const NO_COUNT: ParityCount = ParityCount { rows: 0, mismatches: 0 };

fn add_count(total: &mut ParityCount, more: ParityCount) {
    total.rows = total.rows.saturating_add(more.rows);
    total.mismatches = total.mismatches.saturating_add(more.mismatches);
}

fn count_since(now: ParityCount, then: ParityCount) -> ParityCount {
    ParityCount {
        rows: now.rows.saturating_sub(then.rows),
        mismatches: now.mismatches.saturating_sub(then.mismatches),
    }
}

/// The identity oracle's counts, one per class (module docs, TWO CLASSES).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Tally {
    /// What the oracle judged: `PARITY <fn> identity`.
    pub(super) judged: ParityCount,
    /// What it could not judge: `PARITY <fn> identity-scope`.
    pub(super) unjudged: ParityCount,
}

impl Tally {
    pub(super) const ZERO: Self = Self { judged: NO_COUNT, unjudged: NO_COUNT };

    fn one(class: Class, mismatch: bool) -> Self {
        let mut tally = Self::ZERO;
        tally.add(class, mismatch);
        tally
    }

    fn add(&mut self, class: Class, mismatch: bool) {
        let count = match class {
            Class::Judged => &mut self.judged,
            Class::Unjudged => &mut self.unjudged,
        };
        add_count(count, ParityCount { rows: 1, mismatches: u64::from(mismatch) });
    }

    fn plus(&mut self, other: &Self) {
        add_count(&mut self.judged, other.judged);
        add_count(&mut self.unjudged, other.unjudged);
    }

    /// What `self` counted past `earlier`.
    fn since(&self, earlier: &Self) -> Self {
        Self {
            judged: count_since(self.judged, earlier.judged),
            unjudged: count_since(self.unjudged, earlier.unjudged),
        }
    }
}

/// What was counted, and what of it a `PARITY` row has written.
#[derive(Clone, Copy)]
struct Book {
    counted: Tally,
    written: Tally,
}

impl Book {
    const EMPTY: Self = Self { counted: Tally::ZERO, written: Tally::ZERO };

    /// What was counted since the last call, now marked written.
    fn take_unwritten(&mut self) -> Tally {
        let since = self.counted.since(&self.written);
        self.written = self.counted;
        since
    }
}

/// Every count of a compile, and what the body rows wrote of it (module docs, WHERE A COUNT
/// GOES): the crate's rows write the rest.
pub(super) struct Ledger(Mutex<Book>);

impl Ledger {
    pub(super) const fn new() -> Self {
        Self(Mutex::new(Book::EMPTY))
    }

    fn book(&self) -> MutexGuard<'_, Book> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn count(&self, tally: &Tally) {
        self.book().counted.plus(tally);
    }

    fn wrote(&self, tally: &Tally) {
        self.book().written.plus(tally);
    }

    /// What was counted and no row has written, now marked written.
    pub(super) fn take_unwritten(&self) -> Tally {
        self.book().take_unwritten()
    }
}

/// The compile's ledger: every oracle context the compiler opens counts into it.
static CRATE: Ledger = Ledger::new();

/// What the identity oracle counted in this compile and no body's `PARITY` row wrote, now
/// marked written: the crate's `identity` and `identity-scope` rows
/// (`elide_audit::drain_crate_level`; module docs, WHERE A COUNT GOES).
pub(super) fn take_crate_level() -> Tally {
    CRATE.take_unwritten()
}

/// The identity oracle's VC context for one body's keys (module docs).
pub(super) struct RowKeyContext {
    rows: Mutex<VcContext>,
    /// What this context counted, and what of it its `PARITY` rows wrote: [`Installed`]'s
    /// drop writes what was counted since.
    book: Mutex<Book>,
    /// Where each count is kept as well, so one no row writes reaches the crate's.
    ledger: &'static Ledger,
}

impl RowKeyContext {
    fn new(ledger: &'static Ledger) -> Self {
        Self { rows: Mutex::new(VcContext::new()), book: Mutex::new(Book::EMPTY), ledger }
    }

    fn lock(&self) -> MutexGuard<'_, VcContext> {
        self.rows.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn book(&self) -> MutexGuard<'_, Book> {
        self.book.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Count `tally` here, and in the ledger.
    fn count(&self, tally: &Tally) {
        self.book().counted.plus(tally);
        self.ledger.count(tally);
    }

    /// The judged count here so far (`PARITY <fn> identity`).
    #[cfg(test)]
    pub(super) fn parity(&self) -> ParityCount {
        self.book().counted.judged
    }

    /// Both classes' counts here so far.
    #[cfg(test)]
    pub(super) fn tally(&self) -> Tally {
        self.book().counted
    }

    /// What was counted here since the last call, which is now written, and so marked in the
    /// ledger.
    fn unwritten(&self) -> Tally {
        let since = self.book().take_unwritten();
        self.ledger.wrote(&since);
        since
    }
}

/// What a body's frozen context keeps in its `MemoSlot::RowKeys` slot.
#[derive(Default)]
struct Home(Option<Arc<RowKeyContext>>);

thread_local! {
    /// The oracle contexts installed on this thread, innermost last (module docs). One body's
    /// collection can run inside another's verify pass (a query it forces), so they nest.
    static INSTALLED: RefCell<Vec<Arc<RowKeyContext>>> = const { RefCell::new(Vec::new()) };
}

fn innermost() -> Option<Arc<RowKeyContext>> {
    INSTALLED.with(|installed| installed.borrow().last().cloned())
}

/// Whether a key made now would be identified: an oracle context is installed.
pub(super) fn oracle_runs() -> bool {
    INSTALLED.with(|installed| !installed.borrow().is_empty())
}

/// Count `tally` where the pass making the comparison writes it (module docs, WHERE A COUNT
/// GOES): into the innermost installed context, else into `home` (a live context of the
/// keys), else straight into `ledger`, for the crate's rows.
fn record(tally: &Tally, home: Option<Arc<RowKeyContext>>, ledger: &'static Ledger) {
    match innermost().or(home) {
        Some(context) => context.count(tally),
        None => ledger.count(tally),
    }
}

/// An oracle context installed on this thread while this lives (module docs). Inert, and
/// installing nothing, when the elision audit is off.
pub(super) struct Installed<'tcx> {
    context: Option<Arc<RowKeyContext>>,
    /// The function whose `PARITY <fn> identity` rows the drop writes, if it writes them.
    report: Option<(TyCtxt<'tcx>, DefId)>,
}

impl<'tcx> Installed<'tcx> {
    /// A fresh oracle context, for one body's collection; its counts are written by the pass
    /// that resumes it, never by this guard, or, if none does, by the crate's rows.
    pub(super) fn open() -> Self {
        let context = elide_audit::enabled().then(|| Arc::new(RowKeyContext::new(&CRATE)));
        Self::install(context, None)
    }

    /// The oracle context `rows` keeps (the one its collection adopted), for the verify pass
    /// or the E9 amendment that consumes the artifacts `rows` is frozen into. When this drops
    /// it writes `def_id`'s `PARITY <fn> identity` and `identity-scope` rows of what was
    /// counted since the last rows, always when the context exists, even at `rows=0`.
    /// Nothing when `rows` keeps none.
    pub(super) fn resume(tcx: TyCtxt<'tcx>, def_id: DefId, rows: &VcContext) -> Self {
        Self::install(stored(rows), Some((tcx, def_id)))
    }

    fn install(context: Option<Arc<RowKeyContext>>, report: Option<(TyCtxt<'tcx>, DefId)>) -> Self {
        if let Some(context) = &context {
            INSTALLED.with(|installed| installed.borrow_mut().push(Arc::clone(context)));
        }
        Self { context, report }
    }

    /// Leave this guard's context in `rows`'s memo slot, so it lives as long as `rows` and
    /// [`Self::resume`] finds it: called on the context the collected artifacts were frozen
    /// with. A context `rows` kept before is replaced.
    pub(super) fn adopt(&self, rows: &VcContext) {
        let Some(context) = &self.context else { return };
        // A slot of another type cannot be: only this module writes `RowKeys`.
        let _ = rows
            .memo()
            .with(MemoSlot::RowKeys, |home: &mut Home| home.0 = Some(Arc::clone(context)));
    }

    /// A fresh oracle context installed whatever the audit says, counting into `ledger`, and
    /// the context, for the tests to read its counts.
    #[cfg(test)]
    pub(super) fn for_test_with(ledger: &'static Ledger) -> (Self, Arc<RowKeyContext>) {
        let context = Arc::new(RowKeyContext::new(ledger));
        (Self::install(Some(Arc::clone(&context)), None), context)
    }

    /// [`Self::for_test_with`] a ledger of the test's own.
    #[cfg(test)]
    pub(super) fn for_test() -> (Self, Arc<RowKeyContext>) {
        Self::for_test_with(Box::leak(Box::new(Ledger::new())))
    }

    /// What this guard's drop writes as rows, without a `TyCtxt`: what its context counted
    /// since its last rows, now written. The guard is then uninstalled with nothing left to
    /// write.
    #[cfg(test)]
    pub(super) fn finish_for_test(mut self) -> Tally {
        let context = self.context.take().expect("an installed context");
        uninstall(&context);
        context.unwritten()
    }
}

/// Take `context` off this thread's stack of installed contexts.
fn uninstall(context: &Arc<RowKeyContext>) {
    INSTALLED.with(|installed| {
        let mut installed = installed.borrow_mut();
        if let Some(at) = installed.iter().rposition(|held| Arc::ptr_eq(held, context)) {
            installed.remove(at);
        }
    });
}

impl Drop for Installed<'_> {
    fn drop(&mut self) {
        let Some(context) = self.context.take() else { return };
        uninstall(&context);
        // Unwinding: no row, as an audit scope writes none (`elide_audit`'s docs). What was
        // counted stays unwritten, for the crate's rows.
        if std::thread::panicking() {
            return;
        }
        if let Some((tcx, def_id)) = self.report {
            elide_audit::record_identity_parity(tcx, def_id, context.unwritten());
        }
    }
}

/// The oracle context `rows` keeps, if any. Reads only: a context with no slot gets none.
fn stored(rows: &VcContext) -> Option<Arc<RowKeyContext>> {
    if !rows.memo().contains(MemoSlot::RowKeys) {
        return None;
    }
    rows.memo().with(MemoSlot::RowKeys, |home: &mut Home| home.0.clone()).flatten()
}

/// The exact key of a row (module docs): its canonical string, which decides, and, while the
/// oracle runs, its identity in the body's oracle context, which is compared and counted.
#[derive(Clone)]
pub(super) struct RowKey {
    canonical: String,
    identity: Option<Identified>,
}

/// A key's identity and the oracle context it is an identity of.
#[derive(Clone)]
struct Identified {
    context: Weak<RowKeyContext>,
    /// The context's ledger, for a comparison made once the context is gone.
    ledger: &'static Ledger,
    identity: RowIdentity,
}

impl Identified {
    fn of(context: &Arc<RowKeyContext>, vc: &VerificationCondition) -> Option<Self> {
        let identity = context.lock().identity_of(vc);
        match identity {
            Ok(identity) => {
                Some(Self { context: Arc::downgrade(context), ledger: context.ledger, identity })
            }
            // A row the oracle could not identify (a full table) where the parent has a key:
            // a disagreement, counted now, since no later comparison can judge it.
            Err(_) => {
                context.count(&Tally::one(Class::Judged, true));
                None
            }
        }
    }

    fn is_of(&self, context: &Arc<RowKeyContext>) -> bool {
        std::ptr::eq(self.context.as_ptr(), Arc::as_ptr(context))
    }
}

impl RowKey {
    /// The key of `vc`: `None` exactly when it has no canonical string (its serialization
    /// failed), as on the parent. Identified in the innermost installed oracle context.
    pub(super) fn of(vc: &VerificationCondition) -> Option<Self> {
        let canonical = super::canonical_exact_vc_payload(vc)?;
        let identity = innermost().and_then(|context| Identified::of(&context, vc));
        Some(Self { canonical, identity })
    }

    /// The canonical string, for the elision audit's row keys only (module docs; the census
    /// pins every caller).
    pub(super) fn canonical(&self) -> &str {
        &self.canonical
    }

    /// A live context this key's identity is of.
    fn live_context(&self) -> Option<Arc<RowKeyContext>> {
        self.identity.as_ref().and_then(|identified| identified.context.upgrade())
    }

    /// Whether `self` and `other` are one row: the canonical strings decide (L4-ORACLE-1).
    /// The identities are compared in the same call, and the comparison is counted, judged
    /// or unjudged (module docs, TWO CLASSES), where its pass writes it (WHERE A COUNT GOES).
    pub(super) fn same(&self, other: &Self) -> bool {
        let decided = self.canonical == other.canonical;
        let identified = self.identity.as_ref().or(other.identity.as_ref());
        // Neither key identified, and nothing installed: the oracle does not run here.
        let Some(ledger) =
            identified.map(|key| key.ledger).or_else(|| oracle_runs().then_some(&CRATE))
        else {
            return decided;
        };
        let home = self.live_context().or_else(|| other.live_context());
        let judged = match (&self.identity, &other.identity) {
            (Some(a), Some(b)) if Weak::ptr_eq(&a.context, &b.context) => {
                home.as_ref().map(|context| {
                    let rows = context.lock();
                    rows.holds_identity(&a.identity)
                        && rows.holds_identity(&b.identity)
                        && rows.same_identity(&a.identity, &b.identity)
                })
            }
            _ => None,
        };
        let tally = match judged {
            // Judged: a mismatch when the identities disagree with the decision.
            Some(agreed) => Tally::one(Class::Judged, agreed != decided),
            // Unjudged: never one row to the oracle, which so disagrees exactly when the
            // strings are equal.
            None => Tally::one(Class::Unjudged, decided),
        };
        record(&tally, home, ledger);
        decided
    }

    /// The canonical string, to plant a stale key.
    #[cfg(test)]
    pub(super) fn canonical_mut_for_test(&mut self) -> &mut String {
        &mut self.canonical
    }

    /// This key with `other`'s identity and its own canonical string: the seeded
    /// disagreement, and the negative control's identity that drops what tells the two rows
    /// apart.
    #[cfg(test)]
    pub(super) fn with_identity_of_for_test(mut self, other: &RowKey) -> Self {
        self.identity = other.identity.clone();
        self
    }

    /// A key with this canonical string and no identity.
    #[cfg(test)]
    pub(super) fn unidentified_for_test(canonical: &str) -> Self {
        Self { canonical: canonical.to_string(), identity: None }
    }

    /// Whether the oracle identified this key.
    #[cfg(test)]
    pub(super) fn is_identified(&self) -> bool {
        self.identity.is_some()
    }
}

impl PartialEq for RowKey {
    /// [`RowKey::same`]: the canonical string decides, and the identities are counted.
    fn eq(&self, other: &Self) -> bool {
        self.same(other)
    }
}

impl Eq for RowKey {}

impl Hash for RowKey {
    /// The canonical string only, so equal keys hash alike and a table finds a key where it
    /// found its string.
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.canonical.hash(state);
    }
}

impl fmt::Debug for RowKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RowKey")
            .field("canonical", &self.canonical)
            .field("identified", &self.identity.is_some())
            .finish()
    }
}

/// The identity oracle over `keys` as a partition (module docs), one count per key. The
/// partition's context is the first identified key's, while it lives. A key identified in it
/// is judged: a mismatch when the first key of that context with its canonical string is not
/// the first of that context with its identity. Any other key is unjudged: a mismatch when
/// another key of `keys` holds its canonical string, a binding the oracle cannot judge. A
/// hashed table calls this over the keys it was built from, in order, because a lookup
/// compares only keys whose strings hash alike. Reads and counts only; counted where the
/// pass writes it (module docs, WHERE A COUNT GOES), and not at all when no key is identified
/// and nothing is installed.
pub(super) fn count_partition<'a>(keys: impl IntoIterator<Item = &'a RowKey>) {
    let keys: Vec<&RowKey> = keys.into_iter().collect();
    let first = keys.iter().find_map(|key| key.identity.as_ref());
    let Some(ledger) = first.map(|first| first.ledger).or_else(|| oracle_runs().then_some(&CRATE))
    else {
        return;
    };
    let home = first.and_then(|first| first.context.upgrade());
    let mut holding: FxHashMap<&str, usize> = FxHashMap::default();
    for key in &keys {
        *holding.entry(key.canonical.as_str()).or_default() += 1;
    }
    let mut tally = Tally::ZERO;
    {
        let guard = home.as_ref().map(|context| context.lock());
        let mut first_with_canonical: FxHashMap<&str, usize> = FxHashMap::default();
        let mut by_digest: FxHashMap<FormulaDigest, Vec<usize>> = FxHashMap::default();
        for (at, key) in keys.iter().enumerate() {
            let judged = match (key.identity.as_ref(), home.as_ref(), guard.as_ref()) {
                (Some(identified), Some(context), Some(rows))
                    if identified.is_of(context) && rows.holds_identity(&identified.identity) =>
                {
                    Some((identified, rows))
                }
                _ => None,
            };
            let Some((identified, rows)) = judged else {
                let shared = holding.get(key.canonical.as_str()).is_some_and(|&held| held > 1);
                tally.add(Class::Unjudged, shared);
                continue;
            };
            let first_canonical = *first_with_canonical.entry(key.canonical.as_str()).or_insert(at);
            let class = by_digest.entry(identified.identity.digest).or_default();
            let found = class.iter().copied().find(|&earlier| {
                keys[earlier]
                    .identity
                    .as_ref()
                    .is_some_and(|other| rows.same_identity(&other.identity, &identified.identity))
            });
            if found.is_none() {
                class.push(at);
            }
            tally.add(Class::Judged, first_canonical != found.unwrap_or(at));
        }
    }
    record(&tally, home, ledger);
}

#[cfg(test)]
mod tests;
