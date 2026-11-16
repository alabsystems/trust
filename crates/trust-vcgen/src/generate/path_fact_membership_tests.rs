use std::cell::Cell;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::rc::Rc;

use trust_types::Sort;

use super::*;

// The retired vector rule is the independent semantic oracle: membership only,
// retaining the existing list's order and multiplicity.
fn reference<T: Clone + PartialEq>(existing: &[T], incoming: &[T]) -> Vec<T> {
    existing.iter().filter(|fact| incoming.contains(fact)).cloned().collect()
}

fn sequences(alphabet: &[Formula], max_len: usize) -> Vec<Vec<Formula>> {
    let mut all = vec![Vec::new()];
    let mut rung = vec![Vec::new()];
    for _ in 0..max_len {
        let mut next = Vec::new();
        for prefix in &rung {
            for fact in alphabet {
                let mut row = prefix.clone();
                row.push(fact.clone());
                next.push(row);
            }
        }
        all.extend(next.iter().cloned());
        rung = next;
    }
    all
}

#[test]
fn ordered_formula_intersections_match_the_vector_oracle_exhaustively() {
    let alphabet = [
        Formula::Int(0),
        Formula::UInt(0),
        Formula::Var("x".into(), Sort::Int),
        Formula::Var("y".into(), Sort::Int),
        Formula::Eq(Box::new(Formula::Int(0)), Box::new(Formula::Int(1))),
    ];
    let rows = sequences(&alphabet, 3);
    assert_eq!(rows.len(), 156);
    for existing in &rows {
        for incoming in &rows {
            let actual =
                intersect_with_hasher(existing, incoming, FxBuildHasher::default(), || false);
            assert_eq!(actual.map(Cow::into_owned), Some(reference(existing, incoming)));
        }
    }
}

#[derive(Default)]
struct CollidingHasher;

impl Hasher for CollidingHasher {
    fn write(&mut self, _: &[u8]) {}

    fn finish(&self) -> u64 {
        0
    }
}

#[derive(Clone, Default)]
struct CountedCollidingBuildHasher(Rc<Cell<usize>>);

impl BuildHasher for CountedCollidingBuildHasher {
    type Hasher = CollidingHasher;

    fn build_hasher(&self) -> Self::Hasher {
        self.0.set(self.0.get() + 1);
        CollidingHasher
    }
}

#[test]
fn collisions_never_merge_distinct_facts_or_deduplicate_existing_facts() {
    let x = Formula::Var("x".into(), Sort::Int);
    let y = Formula::Var("y".into(), Sort::Int);
    let alphabet = [
        Formula::Int(0),
        Formula::UInt(0),
        Formula::Eq(Box::new(x.clone()), Box::new(Formula::Int(1))),
        Formula::Eq(Box::new(y), Box::new(Formula::Int(1))),
        Formula::Eq(Box::new(x), Box::new(Formula::Int(2))),
    ];
    let rows = sequences(&alphabet, 3);
    for existing in &rows {
        for incoming in &rows {
            let actual = intersect_with_hasher(
                existing,
                incoming,
                BuildHasherDefault::<CollidingHasher>::default(),
                || false,
            );
            assert_eq!(actual.map(Cow::into_owned), Some(reference(existing, incoming)));
        }
    }
    // Cross the adaptive index threshold with misses before the matching facts:
    // the exhaustive small lists above intentionally retain their linear shortcut.
    let fact = |i: usize| {
        Formula::Eq(
            Box::new(Formula::Var(format!("fact{i}"), Sort::Int)),
            Box::new(Formula::Int(i as i128)),
        )
    };
    let mut existing: Vec<_> = (0..32).map(fact).collect();
    existing.extend([fact(20), fact(20), Formula::UInt(20)]);
    let mut incoming: Vec<_> = (16..48).map(fact).collect();
    incoming.extend([fact(20), Formula::UInt(7)]);
    let hasher = CountedCollidingBuildHasher::default();
    let actual = intersect_with_hasher(&existing, &incoming, hasher.clone(), || false);
    assert!(hasher.0.get() > 0, "the forced-collision fixture never built the index");
    assert_eq!(actual.map(Cow::into_owned), Some(reference(&existing, &incoming)));
}

#[test]
fn each_fact_keeps_its_original_budget_poll_and_refusal_position() {
    // Cover both the linear prefix and the indexed branch, with refusal at every
    // position including immediately before/after the adaptive switch.
    let fixtures = [
        (vec![3u64, 1, 3, 9, 2], vec![1u64, 2, 3]),
        ((0..32).collect::<Vec<_>>(), (16..48).collect::<Vec<_>>()),
    ];
    for (existing, incoming) in fixtures {
        for allowed in 0..=existing.len() + 1 {
            let mut polls = 0;
            let actual =
                intersect_with_hasher(&existing, &incoming, FxBuildHasher::default(), || {
                    polls += 1;
                    polls > allowed
                });
            let expected =
                if allowed < existing.len() { None } else { Some(reference(&existing, &incoming)) };
            assert_eq!(actual.map(Cow::into_owned), expected, "allow {allowed} polls");
            assert_eq!(polls, existing.len().min(allowed + 1));
        }
    }
}

#[test]
fn production_entry_keeps_the_ambient_step_refusal() {
    use trust_types::verify_budget::{VerifyBudgetGuard, exhausted_readonly};

    let existing = [Formula::Int(1), Formula::Int(2)];
    let incoming = [Formula::Int(2)];
    {
        let _guard = VerifyBudgetGuard::install(None, 1);
        assert_eq!(intersect(&existing, &incoming), None);
        assert!(exhausted_readonly());
    }
    {
        let _guard = VerifyBudgetGuard::install(None, 2);
        assert_eq!(
            intersect(&existing, &incoming).map(Cow::into_owned),
            Some(vec![Formula::Int(2)])
        );
        assert!(exhausted_readonly());
    }
}

#[derive(Default)]
struct Work {
    equalities: Cell<usize>,
    hashes: Cell<usize>,
    clones: Cell<usize>,
}

impl Work {
    fn reset(&self) {
        self.equalities.set(0);
        self.hashes.set(0);
        self.clones.set(0);
    }
}

struct Counted {
    value: u64,
    work: Rc<Work>,
}

impl Clone for Counted {
    fn clone(&self) -> Self {
        self.work.clones.set(self.work.clones.get() + 1);
        Self { value: self.value, work: Rc::clone(&self.work) }
    }
}

impl PartialEq for Counted {
    fn eq(&self, other: &Self) -> bool {
        self.work.equalities.set(self.work.equalities.get() + 1);
        self.value == other.value
    }
}

impl Eq for Counted {}

impl Hash for Counted {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.work.hashes.set(self.work.hashes.get() + 1);
        self.value.hash(state);
    }
}

fn counted(values: impl IntoIterator<Item = u64>, work: &Rc<Work>) -> Vec<Counted> {
    values.into_iter().map(|value| Counted { value, work: Rc::clone(work) }).collect()
}

#[test]
fn unchanged_intersections_reuse_existing_storage_without_cloning() {
    let mut observations = Vec::new();
    for n in [1u64, 64, 512] {
        let work = Rc::new(Work::default());
        let existing = counted((0..n).chain([0, 0]), &work);
        let incoming = counted((0..n).rev(), &work);
        let mut polls = 0;
        let actual = intersect_with_hasher(&existing, &incoming, FxBuildHasher::default(), || {
            polls += 1;
            false
        })
        .unwrap();
        assert_eq!(
            actual.iter().map(|fact| fact.value).collect::<Vec<_>>(),
            (0..n).chain([0, 0]).collect::<Vec<_>>()
        );
        assert_eq!(polls, existing.len());
        let clones = work.clones.get();
        let borrowed = actual.as_ptr() == existing.as_ptr();
        eprintln!("unchanged-path-facts n={n} clones={clones} borrowed={borrowed}");
        observations.push((clones, borrowed));
    }
    assert_eq!(observations, vec![(0, true); 3]);
}

#[test]
fn shrinking_intersections_copy_only_the_retained_prefix_and_tail() {
    for missing in [1, 2, 3] {
        let work = Rc::new(Work::default());
        let existing = counted([1, 1, 2, 2, 3, 3], &work);
        let incoming = counted([3, 2, 1].into_iter().filter(|value| *value != missing), &work);
        let mut polls = 0;
        let actual = intersect_with_hasher(&existing, &incoming, FxBuildHasher::default(), || {
            polls += 1;
            false
        })
        .unwrap();
        let values: Vec<_> = actual.iter().map(|fact| fact.value).collect();
        assert_eq!(
            values,
            [1, 1, 2, 2, 3, 3].into_iter().filter(|value| *value != missing).collect::<Vec<_>>()
        );
        assert!(matches!(actual, Cow::Owned(_)));
        assert_eq!(work.clones.get(), actual.len());
        assert_eq!(polls, existing.len());
    }
}

#[test]
fn empty_inputs_and_initial_refusal_do_no_membership_work() {
    let work = Rc::new(Work::default());
    let existing = counted([1], &work);
    let incoming = counted(0..128, &work);
    let mut polls = 0;
    let actual = intersect_with_hasher(&[], &incoming, FxBuildHasher::default(), || {
        polls += 1;
        true
    });
    assert!(actual.is_some_and(|facts| facts.is_empty()));
    assert_eq!(polls, 0);
    let actual = intersect_with_hasher(&existing, &incoming, FxBuildHasher::default(), || {
        polls += 1;
        true
    });
    assert!(actual.is_none());
    assert_eq!(polls, 1);
    assert_eq!(work.equalities.get(), 0);
    assert_eq!(work.hashes.get(), 0);
    assert_eq!(work.clones.get(), 0);
}

#[test]
fn the_temporary_index_borrows_incoming_and_clones_only_retained_facts() {
    let work = Rc::new(Work::default());
    let existing = counted((0..32).chain([20, 20, 127]), &work);
    let incoming = counted(16..48, &work);
    let actual =
        intersect_with_hasher(&existing, &incoming, FxBuildHasher::default(), || false).unwrap();
    let values: Vec<_> = actual.iter().map(|fact| fact.value).collect();
    assert_eq!(values, (16..32).chain([20, 20]).collect::<Vec<_>>());
    assert!(work.hashes.get() > 0, "the borrowing fixture never built the index");
    assert_eq!(work.clones.get(), actual.len());
}

#[test]
fn large_incoming_tails_keep_the_original_early_match_shortcut() {
    let work = Rc::new(Work::default());
    let incoming = counted(0..1024, &work);
    for count in [1usize, 512] {
        let existing = counted(std::iter::repeat_n(0, count), &work);
        work.reset();
        let mut polls = 0;
        let actual = intersect_with_hasher(&existing, &incoming, FxBuildHasher::default(), || {
            polls += 1;
            false
        })
        .unwrap();
        assert_eq!(actual.len(), count);
        assert_eq!(work.equalities.get(), count);
        assert_eq!(work.hashes.get(), 0, "an irrelevant incoming tail was hashed");
        assert_eq!(work.clones.get(), 0);
        assert_eq!(polls, count);
    }
}

#[test]
fn wide_fact_membership_work_grows_linearly_instead_of_quadratically() {
    let work = Rc::new(Work::default());
    let mut previous = None;
    for n in [64u64, 128, 256, 512] {
        let existing = counted(0..n, &work);
        let incoming = counted(n..2 * n, &work);
        work.reset();
        assert!(reference(&existing, &incoming).is_empty());
        let old_equalities = work.equalities.get();
        assert_eq!(old_equalities, (n * n) as usize);
        work.reset();
        let actual =
            intersect_with_hasher(&existing, &incoming, FxBuildHasher::default(), || false)
                .unwrap();
        assert!(actual.is_empty());
        let hashes = work.hashes.get();
        let equalities = work.equalities.get();
        let lookup_work = hashes + equalities;
        assert_eq!(work.clones.get(), 0);
        assert!(lookup_work <= 16 * n as usize, "{n}: {hashes} hashes + {equalities} equalities");
        if let Some(before) = previous {
            assert!(lookup_work <= 3 * before, "doubling {n}: {before} -> {lookup_work}");
        }
        previous = Some(lookup_work);
        eprintln!(
            "path-fact-membership n={n} old_equalities={old_equalities} hashes={hashes} equalities={equalities} clones=0"
        );
    }
}
