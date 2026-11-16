//! Exact path-fact membership with an adaptive borrowed index. The index is lookup-only:
//! the existing fact list determines output order and retains its duplicates.

use std::borrow::Cow;
use std::collections::HashSet;
use std::hash::{BuildHasher, Hash};

use trust_types::Formula;
use trust_types::fx::FxBuildHasher;

pub(super) fn intersect<'a>(
    existing: &'a [Formula],
    incoming: &[Formula],
) -> Option<Cow<'a, [Formula]>> {
    intersect_with_hasher(
        existing,
        incoming,
        FxBuildHasher::default(),
        trust_types::verify_budget::budget_exhausted,
    )
}

/// Hashing narrows membership candidates; `Eq` still decides every match, including
/// hash collisions. Both traits are derived together for `Formula`. Borrowing the
/// incoming facts avoids cloning them just to build this temporary index.
/// If every existing fact survives, borrow that list: the caller discards an
/// unchanged intersection after its convergence check. Copy only after a miss.
fn intersect_with_hasher<'a, T: Clone + Eq + Hash, S: BuildHasher>(
    existing: &'a [T],
    incoming: &[T],
    hasher: S,
    mut exhausted: impl FnMut() -> bool,
) -> Option<Cow<'a, [T]>> {
    let mut merged: Option<Vec<T>> = None;
    let mut members: HashSet<&T, S> = HashSet::with_hasher(hasher);
    let mut indexed = false;
    let mut comparisons = 0usize;
    // Preserve cheap early matches: eagerly hashing a large incoming tail for one
    // existing fact can cost more than the original short-circuit search. Build
    // the index only after linear searches have spent work proportional to BOTH
    // input lists. A final search can exceed this threshold by at most incoming.len().
    let linear_limit = existing.len().saturating_add(incoming.len()).saturating_mul(2);
    for (index, fact) in existing.iter().enumerate() {
        // The same one poll per existing fact, before its membership lookup.
        // An empty existing list or an initial refusal hashes nothing.
        if exhausted() {
            return None;
        }
        if !indexed && comparisons >= linear_limit {
            members.reserve(incoming.len());
            members.extend(incoming);
            indexed = true;
        }
        let present = if indexed {
            members.contains(fact)
        } else {
            incoming.iter().any(|candidate| {
                comparisons = comparisons.saturating_add(1);
                candidate == fact
            })
        };
        if present {
            if let Some(merged) = &mut merged {
                merged.push(fact.clone());
            }
        } else if merged.is_none() {
            // Before the first miss, every prefix fact survived, in order and
            // with its duplicates. Materialize that prefix exactly once.
            let mut retained = Vec::with_capacity(existing.len() - 1);
            retained.extend_from_slice(&existing[..index]);
            merged = Some(retained);
        }
    }
    Some(match merged {
        Some(facts) => Cow::Owned(facts),
        None => Cow::Borrowed(existing),
    })
}

#[cfg(test)]
#[path = "path_fact_membership_tests.rs"]
mod tests;
