//! TINV step 10.2: the USE SET, what a use site may assume from one Houdini run
//! (`docs/design/2026-10-04-type-invariant-tinv.md` §2 P6, §6 step 10).
//!
//! A [`TinvUseSet`] holds, per published type, the surviving conjuncts of its certificate
//! and the field list the rows were generated for; the run's inventory (the callees after
//! whose normal return `I` may be assumed); the bodies the final round walked (the only
//! bodies in which the entry assumption is justified); and the map from each assumption
//! TAG ([`trust_types::type_invariant_assume_tag`]) to the `(type, conjunct)` it names.
//!
//! ITS ONLY CONSTRUCTOR is [`TinvUseSet::from_outcome`], over a [`TinvOutcome`] and the
//! caller's publication predicate: a consumer cannot add a type, a conjunct, a callee or
//! a body that the run did not check, it can only leave a type out. Construction refuses
//! (`Err`) rather than build a partial set:
//! * two `(type, conjunct)` pairs whose tags collide (the tag is a 64-bit digest, so a
//!   collision is not expected; if it happens a tag could not name one conjunct);
//! * a published certificate whose conjunct list or field list is empty, or whose
//!   `def_path` differs from its key;
//! * a published certificate with no checked body (the outcome is inconsistent).
//!
//! An empty set (nothing published) is a valid set; it gives no fact.
//!
//! NO AUTHORITY. The set grants nothing by itself. Facts drawn from it are TAGGED, the
//! kernel refuses every tagged VC (`VerificationCondition::kernel_authority_refusal`,
//! TINV-23), and the compiler's mint must find the tags it reads in a row's formula equal
//! to the tags the use site installed (step 10.4).

use std::collections::{BTreeMap, BTreeSet, HashSet};

use trust_types::{CalleeIdentity, type_invariant_assume_tag};

use super::TinvType;
use super::houdini::TinvOutcome;

/// Why no use set was built from an outcome. Every variant refuses the WHOLE set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TinvUseSetRefusal {
    /// Two `(type, conjunct)` pairs spell the same tag.
    TagCollision { tag: String, first: (String, u32), second: (String, u32) },
    /// A published certificate that cannot be used as published (empty conjunct or field
    /// list, or a key that is not its `def_path`).
    MalformedCertificate(String),
    /// Certificates were published but the outcome names no checked body.
    NoCheckedBodies,
}

/// What a use site may assume from one Houdini run (module doc). Read-only.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinvUseSet {
    types: BTreeMap<String, TinvType>,
    inventory: HashSet<CalleeIdentity>,
    checked_bodies: BTreeSet<String>,
    /// Tag name -> `(type def_path, conjunct id)`.
    tags: BTreeMap<String, (String, u32)>,
    /// `type def_path` -> (`conjunct id` -> tag name) for O(log n) [`Self::tag_for`].
    tags_by_conjunct: BTreeMap<String, BTreeMap<u32, String>>,
}

impl TinvUseSet {
    /// The use set of `outcome`, restricted to the certificates whose type `def_path`
    /// satisfies `published`. The inventory and the checked bodies are the outcome's, whole:
    /// they describe the induction every certificate of the run rests on, whichever of them
    /// is published.
    ///
    /// # Errors
    /// The refusals of the module doc; nothing is built then.
    pub fn from_outcome<E>(
        outcome: &TinvOutcome<E>,
        published: impl Fn(&str) -> bool,
    ) -> Result<Self, TinvUseSetRefusal> {
        Self::build(outcome, published, type_invariant_assume_tag)
    }

    /// [`Self::from_outcome`] with the tag spelling as a parameter, so a test can force a
    /// collision.
    fn build<E>(
        outcome: &TinvOutcome<E>,
        published: impl Fn(&str) -> bool,
        tag_of: impl Fn(&str, u32) -> String,
    ) -> Result<Self, TinvUseSetRefusal> {
        let mut types: BTreeMap<String, TinvType> = BTreeMap::new();
        let mut tags: BTreeMap<String, (String, u32)> = BTreeMap::new();
        let mut tags_by_conjunct: BTreeMap<String, BTreeMap<u32, String>> = BTreeMap::new();
        for (key, cert) in &outcome.certificates {
            if !published(key) {
                continue;
            }
            if cert.def_path() != key || cert.conjuncts().is_empty() || cert.fields().is_empty() {
                return Err(TinvUseSetRefusal::MalformedCertificate(key.clone()));
            }
            let mut per_type_tags: BTreeMap<u32, String> = BTreeMap::new();
            for c in cert.conjuncts() {
                let tag = tag_of(key, c.id);
                let named = (key.clone(), c.id);
                if let Some(first) = tags.get(&tag) {
                    return Err(TinvUseSetRefusal::TagCollision {
                        tag,
                        first: first.clone(),
                        second: named,
                    });
                }
                per_type_tags.insert(c.id, tag.clone());
                tags.insert(tag, named);
            }
            tags_by_conjunct.insert(key.clone(), per_type_tags);
            types.insert(
                key.clone(),
                TinvType {
                    def_path: key.clone(),
                    fields: cert.fields().to_vec(),
                    conjuncts: cert.conjuncts().to_vec(),
                },
            );
        }
        if !types.is_empty() && outcome.checked_bodies.is_empty() {
            return Err(TinvUseSetRefusal::NoCheckedBodies);
        }
        Ok(Self {
            types,
            inventory: outcome.inventory.clone(),
            checked_bodies: outcome.checked_bodies.clone(),
            tags,
            tags_by_conjunct,
        })
    }

    /// Whether the set publishes no type (it then gives no fact).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }

    /// The published types, by `def_path`, each with its surviving conjuncts.
    #[must_use]
    pub fn types(&self) -> &BTreeMap<String, TinvType> {
        &self.types
    }

    /// The callees after whose normal return `I` may be assumed.
    #[must_use]
    pub fn inventory(&self) -> &HashSet<CalleeIdentity> {
        &self.inventory
    }

    /// The bodies the final round walked: the only bodies a use site gives facts in.
    #[must_use]
    pub fn checked_bodies(&self) -> &BTreeSet<String> {
        &self.checked_bodies
    }

    /// The tag naming conjunct `conjunct` of `def_path`, if that conjunct is published.
    #[must_use]
    pub fn tag_for(&self, def_path: &str, conjunct: u32) -> Option<&str> {
        self.tags_by_conjunct
            .get(def_path)
            .and_then(|by_id| by_id.get(&conjunct))
            .map(String::as_str)
    }

    /// The `(type def_path, conjunct id)` a tag names, if it names a published conjunct.
    #[must_use]
    pub fn decode_tag(&self, tag: &str) -> Option<(&str, u32)> {
        self.tags.get(tag).map(|(ty, id)| (ty.as_str(), *id))
    }

    /// Every tag and the `(type, conjunct)` it names, in tag order.
    #[must_use]
    pub fn tags(&self) -> &BTreeMap<String, (String, u32)> {
        &self.tags
    }
}

/// TINV step 10.3: one generated row a use-site fact was conjoined into — the
/// GENERATION-SCOPED disclosure channel (the second channel; the first is the tag inside
/// the row's formula). The compiler's mint requires the two to agree (step 10.4).
///
/// Rows are recorded only inside [`with_tinv_assumed_rows_scope`], for the one body the
/// scope names, so the record describes exactly the generation whose rows the caller
/// consumes: a replay, a probe or a clone generated outside the scope gets no fact at all
/// (and records nothing), and cannot pollute it.
///
/// THE COMPARISON RULE. The row key is `(def_path, kind, location)` (`def_path` is the
/// generating body's; a VC's `function` is its short name). A key need not be unique, and
/// one generation may run the safety walk more than once. A consumer therefore compares
/// each row's FORMULA tag set with the UNION of the tag sets of every record with the
/// row's key: equal is required for a composed grade, and a key shared by a row with facts
/// and one without makes the untagged one disagree (fail closed: a precision cost only).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TinvAssumedRow {
    pub def_path: String,
    pub kind: trust_types::VcKind,
    pub location: trust_types::SourceSpan,
    /// The tags of the facts actually conjoined into the row (after every filter).
    pub tags: BTreeSet<String>,
}

/// One open recording scope (see [`with_tinv_assumed_rows_scope`]).
struct RecordScope {
    def_path: String,
    /// The UNEXPANDED body has a tail call (D5): no use-site fact in it. Decided here,
    /// on the body the caller hands in, because generation expands tail calls before the
    /// safety walk sees the body.
    tail_call: bool,
    rows: Vec<TinvAssumedRow>,
    /// The use set the scope's facts were drawn from (the first one seen).
    use_set: Option<std::sync::Arc<TinvUseSet>>,
    /// Facts were drawn from two different sets inside one scope.
    conflicting_sets: bool,
}

/// What one generation's recording scope saw (step 10.3/10.4): the rows a use-site fact
/// was conjoined into, and the IDENTITY of the use set those facts came from, so a
/// consumer decodes the tags against exactly that set. `conflicting_sets` (facts from two
/// different sets in one generation) must refuse every tagged row of the generation.
#[derive(Debug, Clone, Default)]
pub struct TinvGenerationRecord {
    pub rows: Vec<TinvAssumedRow>,
    pub use_set: Option<std::sync::Arc<TinvUseSet>>,
    pub conflicting_sets: bool,
}

impl TinvGenerationRecord {
    /// Whether a use-site fact was conjoined into ANY row of the generation.
    #[must_use]
    pub fn carries_premise(&self) -> bool {
        self.rows.iter().any(|row| !row.tags.is_empty())
    }
}

thread_local! {
    static RECORD_SCOPES: std::cell::RefCell<Vec<RecordScope>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Run ONE generation of `func` under a recording scope and return its result together
/// with its [`TinvGenerationRecord`]: every row a use-site fact was conjoined into during
/// it and the set those facts came from (step 10.3). Use-site facts
/// are given ONLY inside such a scope, only for the body it names (the innermost scope
/// decides), and never when that body has a tail call; so every conjoined fact is recorded,
/// and a generation outside any scope assumes nothing. The scope is closed on unwind too.
pub fn with_tinv_assumed_rows_scope<R>(
    func: &trust_types::VerifiableFunction,
    f: impl FnOnce() -> R,
) -> (R, TinvGenerationRecord) {
    struct Guard(usize);
    impl Drop for Guard {
        fn drop(&mut self) {
            let _ = RECORD_SCOPES.try_with(|s| s.borrow_mut().truncate(self.0));
        }
    }
    let depth = RECORD_SCOPES.with(|s| {
        let mut s = s.borrow_mut();
        s.push(RecordScope {
            def_path: func.def_path.clone(),
            tail_call: func
                .body
                .blocks
                .iter()
                .any(|b| matches!(b.terminator, trust_types::Terminator::TailCall { .. })),
            rows: Vec::new(),
            use_set: None,
            conflicting_sets: false,
        });
        s.len() - 1
    });
    let guard = Guard(depth);
    let out = f();
    let record = RECORD_SCOPES.with(|s| {
        s.borrow_mut().get_mut(depth).map(|scope| TinvGenerationRecord {
            rows: std::mem::take(&mut scope.rows),
            use_set: scope.use_set.take(),
            conflicting_sets: scope.conflicting_sets,
        })
    });
    drop(guard);
    (out, record.unwrap_or_default())
}

/// Note, in the innermost scope, the set the facts about to be conjoined come from.
pub(crate) fn note_scope_use_set(set: &std::sync::Arc<TinvUseSet>) {
    RECORD_SCOPES.with(|s| {
        if let Some(scope) = s.borrow_mut().last_mut() {
            match &scope.use_set {
                None => scope.use_set = Some(std::sync::Arc::clone(set)),
                Some(seen) if std::sync::Arc::ptr_eq(seen, set) => {}
                Some(_) => scope.conflicting_sets = true,
            }
        }
    });
}

/// Whether the innermost recording scope admits use-site facts for `def_path`.
pub(crate) fn record_scope_admits(def_path: &str) -> bool {
    RECORD_SCOPES.with(|s| {
        s.borrow().last().is_some_and(|scope| scope.def_path == def_path && !scope.tail_call)
    })
}

/// Record `row` in the innermost scope, which must admit its body (it is the scope that
/// admitted the facts). Returns `false`, recording nothing, otherwise.
pub(crate) fn record_assumed_row(row: TinvAssumedRow) -> bool {
    RECORD_SCOPES.with(|s| {
        let mut s = s.borrow_mut();
        match s.last_mut() {
            Some(scope) if scope.def_path == row.def_path && !scope.tail_call => {
                scope.rows.push(row);
                true
            }
            _ => false,
        }
    })
}

#[cfg(test)]
#[path = "use_set_tests.rs"]
mod tests;
