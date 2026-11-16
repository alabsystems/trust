//! Trust: credit admission for weighted and exclusive test actions.
//!
//! A test action of weight `w` holds `w` credits of the build's one CPU pool
//! and runs libtest with `w` threads. It takes all `w` credits at dispatch or
//! none. Tests start in the queue's priority order; a test that cannot start
//! holds back the tests behind it, so a heavy harness is not starved by light
//! ones. Ready compiler work is never held back by a waiting test, and the
//! compiler keeps its progress credit. A test above weight 1 asks for its
//! credits only once it fits in the pool beside the compiler work running or
//! ready, so the credits it collects do not sit idle while a running rustc
//! could use them. An exclusive test starts only once no compiler work can
//! become ready and nothing else runs, and nothing starts beside it.
//!
//! This is cooperative scheduling inside one Targo invocation, not
//! containment: a test can still create more threads or processes.

/// What a pending queue entry asks of admission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Demand {
    Compile,
    /// A separate verification node after the original compile graph closes.
    /// Admission credit only; never a compile process/timing registration.
    Verification,
    /// The action remains in the original graph, but its compiler workers
    /// and output bookkeeping have not positively retired yet. No credit is
    /// requested or dispatch made on behalf of this action.
    Parked,
    Test {
        weight: usize,
        exclusive: bool,
        /// Mebibytes counted against the memory budget; 0 counts nothing.
        memory: usize,
    },
}

/// The queue's running work at one admission decision.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Occupancy {
    /// Compiler jobs running.
    pub compiling: usize,
    /// Test actions running.
    pub testing: usize,
    /// Credits the running test actions hold: the sum of their weights.
    pub test_credits: usize,
    /// One of the running test actions is exclusive.
    pub exclusive: bool,
    /// The most credits test actions may hold together (`build.test-jobs`
    /// after the worker-budget and `-j` bounds).
    pub test_limit: usize,
    /// Compilation retired; no compiler entry may be dispatched.
    pub compiler_finalized: bool,
    /// The credits of the pool Targo created (`-j`). A weight above 1 is
    /// admitted only on such a pool.
    pub pool: usize,
    /// Mebibytes the running test actions are counted for.
    pub test_memory: usize,
    /// The most they may be counted for together, where memory is counted.
    pub memory_limit: Option<usize>,
}

impl Occupancy {
    /// Credits held by everything running. A compiler job holds one.
    pub(super) fn held(&self) -> usize {
        self.compiling + self.test_credits
    }

    /// Whether a test counted for `memory` fits beside the running tests.
    /// One that counts for nothing always does, and so does any test with
    /// no other running: a harness larger than the whole budget still runs,
    /// alone among tests, as the script lane's pool never went below one.
    pub(super) fn memory_fits(&self, testing: usize, held: usize, memory: usize) -> bool {
        memory == 0
            || testing == 0
            || self
                .memory_limit
                .is_none_or(|limit| held + memory <= limit)
    }

    /// What admitting `demand` changes; the coordinator learns the same from
    /// the work it starts, so only the model checks below replay it.
    #[cfg(test)]
    fn admit(&mut self, demand: Demand) {
        match demand {
            Demand::Parked => panic!("a parked action cannot be admitted"),
            Demand::Compile | Demand::Verification => self.compiling += 1,
            Demand::Test {
                weight,
                exclusive,
                memory,
            } => {
                self.testing += 1;
                self.test_credits += weight;
                self.test_memory += memory;
                self.exclusive |= exclusive;
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Choice {
    /// Dispatch the pending entry at this index.
    Dispatch(usize),
    /// Nothing can start now.
    Wait,
}

/// Choose the next pending entry to dispatch.
///
/// `pending` is in ascending priority, so the order of dispatch runs from its
/// end. `free` is the number of credits available without waiting, or `None`
/// when each dispatch acquires its own credits (and may still be refused).
pub(super) fn choose(occupancy: &Occupancy, pending: &[Demand], free: Option<usize>) -> Choice {
    let fits = |weight: usize| free.is_none_or(|free| weight <= free);
    if occupancy.exclusive {
        return Choice::Wait;
    }
    let compile_ready =
        !occupancy.compiler_finalized && pending.iter().any(|demand| *demand == Demand::Compile);
    // Preserve one compiler progress credit while compiler work remains:
    // with no compiler running, ready compiler work goes first.
    if occupancy.compiling == 0 && compile_ready {
        return match pending
            .iter()
            .rposition(|demand| *demand == Demand::Compile)
        {
            Some(index) if fits(1) => Choice::Dispatch(index),
            _ => Choice::Wait,
        };
    }
    // Completions are the only source of new ready work, and tests never
    // complete a compiler prerequisite. With no compiler running and none
    // ready, no compiler work can become ready during an exclusive test.
    let compile_quiet = occupancy.compiling == 0 && !compile_ready;
    let mut tests_held_back = false;
    for (index, demand) in pending.iter().enumerate().rev() {
        match *demand {
            Demand::Parked => {}
            Demand::Compile => {
                if !occupancy.compiler_finalized && fits(1) {
                    return Choice::Dispatch(index);
                }
            }
            Demand::Verification => {
                if occupancy.compiler_finalized && fits(1) {
                    return Choice::Dispatch(index);
                }
            }
            Demand::Test { .. } if tests_held_back => {}
            Demand::Test {
                weight,
                exclusive: true,
                ..
            } => {
                // Ready compiler work comes first, and must not be held back
                // by an exclusive test waiting for it; other tests may run.
                if !compile_quiet {
                    continue;
                }
                tests_held_back = true;
                if occupancy.compiling + occupancy.testing == 0 && fits(weight) {
                    return Choice::Dispatch(index);
                }
            }
            Demand::Test {
                weight,
                exclusive: false,
                memory,
            } => {
                tests_held_back = true;
                if occupancy.test_credits + weight <= occupancy.test_limit
                    && occupancy.memory_fits(occupancy.testing, occupancy.test_memory, memory)
                    && fits(weight)
                {
                    return Choice::Dispatch(index);
                }
            }
        }
    }
    Choice::Wait
}

#[cfg(test)]
#[test]
fn verification_never_reopens_compile_admission_or_invents_a_credit() {
    let before = Occupancy {
        pool: 1,
        ..Default::default()
    };
    assert_eq!(
        choose(&before, &[Demand::Verification], Some(1)),
        Choice::Wait
    );
    assert_eq!(wanted(&before, &[Demand::Verification]), 0);
    assert_eq!(
        choose(&before, &[Demand::Verification, Demand::Compile], Some(1)),
        Choice::Dispatch(1)
    );
    let closed = Occupancy {
        compiler_finalized: true,
        ..before
    };
    assert_eq!(
        choose(&closed, &[Demand::Compile, Demand::Verification], Some(1)),
        Choice::Dispatch(1)
    );
    assert_eq!(
        choose(&closed, &[Demand::Verification], Some(0)),
        Choice::Wait
    );
    assert_eq!(wanted(&closed, &[Demand::Compile, Demand::Verification]), 1);
    assert_eq!(
        choose(
            &Occupancy {
                exclusive: true,
                ..closed
            },
            &[Demand::Verification],
            None
        ),
        Choice::Wait
    );
}

#[cfg(test)]
#[test]
fn parked_workload_actions_keep_their_place_without_requesting_or_dispatching_credits() {
    let idle = Occupancy {
        test_limit: 1,
        ..Default::default()
    };
    assert_eq!(choose(&idle, &[Demand::Parked], None), Choice::Wait);
    assert_eq!(wanted(&idle, &[Demand::Parked]), 0);
    assert_eq!(
        choose(&idle, &[Demand::Parked, Demand::Compile], Some(1)),
        Choice::Dispatch(1)
    );
    assert_eq!(wanted(&idle, &[Demand::Parked, Demand::Compile]), 1);
    let finalized = Occupancy {
        compiler_finalized: true,
        ..idle
    };
    let runnable = Demand::Test {
        weight: 1,
        exclusive: false,
        memory: 0,
    };
    assert_eq!(
        choose(&finalized, &[runnable], Some(1)),
        Choice::Dispatch(0)
    );
}

/// A test action's cost in the dependency queue, which is its priority
/// among ready work (a test has no dependents but a later action on its own
/// target) and adds to the priority of everything it waits for.
///
/// The expected run time leads: a run is as long as its longest chain, so
/// the harness that takes ten minutes must be among the first to start, not
/// the 609th of 724 as inventory order had it. A second of expectation
/// outweighs any weight. Within one expectation (and where nothing states
/// one) the heavier harness goes first, since it is the harder to fit. An
/// exclusive harness costs nothing and goes last, when nothing else runs.
pub(super) fn cost(weight: usize, exclusive: bool, seconds: u64) -> usize {
    if exclusive {
        return 0;
    }
    // Weights are bounded by the pool, far below this factor.
    const SECOND: usize = 1_000_000;
    (seconds as usize)
        .saturating_mul(SECOND)
        .saturating_add(100 * weight)
}

/// Where an entry sits in the pending queue: its dependency-queue priority
/// and, for a test action, its inventory index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Rank {
    pub priority: usize,
    pub test: Option<usize>,
}

/// Whether `queued` stays ahead of (is dispatched after) a newly ready
/// entry `new`. Within one priority, tests sit before compiler work and in
/// descending inventory order, so dispatch from the end takes ready compiler
/// work first and equal tests in inventory order, the sequential runner's.
/// Readiness order alone comes from the dependency queue's address-hashed
/// units, and would let a one-credit fail-fast run start a later harness
/// before the earlier one that fails.
///
/// The queue keeps that order as its invariant, so this predicate is true
/// then false along it, as `partition_point` requires.
pub(super) fn stays_ahead(queued: Rank, new: Rank) -> bool {
    queued.priority < new.priority
        || queued.priority == new.priority
            && match (new.test, queued.test) {
                (None, _) => true,
                (Some(new), Some(queued)) => queued > new,
                (Some(_), None) => false,
            }
}

/// The credits the queue could use now if every one it asked for were
/// granted: those held, plus whatever `choose` would dispatch with unlimited
/// credits. A legacy jobserver keeps (and requests) tokens up to this figure
/// less the implicit one, so a test waiting for `w` credits accumulates them
/// instead of releasing each token on an idle wait.
///
/// Credits a test of weight above 1 collects sit idle until it has them all,
/// where a running rustc could have used them for its own parallel work. So
/// such a test is counted only once it fits in the pool beside every compiler
/// job running or ready; until then it holds back the tests behind it, as in
/// `choose`, and asks for nothing. Once compilation is quiet it always fits,
/// since its weight is within the test limit and the limit within the pool.
/// A weight-1 test uses a token the moment it arrives, as a compiler job
/// does, and is counted as before.
///
/// This is the closed form of dispatching with `choose(.., None)` until it
/// waits, a test above weight 1 not fitting the pool counting as a wait:
/// every ready compiler entry starts, then tests in order until one is held
/// back. It is linear in the pending queue, which the coordinator consults on
/// every idle wait.
pub(super) fn wanted(occupancy: &Occupancy, pending: &[Demand]) -> usize {
    if occupancy.exclusive {
        return occupancy.held();
    }
    let ready_compile = if occupancy.compiler_finalized {
        0
    } else {
        pending
            .iter()
            .filter(|demand| **demand == Demand::Compile)
            .count()
    };
    let ready_verification = if occupancy.compiler_finalized {
        pending
            .iter()
            .filter(|demand| **demand == Demand::Verification)
            .count()
    } else {
        0
    };
    let compiling = occupancy.compiling + ready_compile + ready_verification;
    let mut credits = occupancy.test_credits;
    let mut testing = occupancy.testing;
    let mut held = occupancy.test_memory;
    for demand in pending.iter().rev() {
        let Demand::Test {
            weight,
            exclusive,
            memory,
        } = *demand
        else {
            continue;
        };
        if exclusive {
            if compiling != 0 {
                continue;
            }
            if testing == 0 {
                credits += weight;
            }
            break;
        }
        if credits + weight > occupancy.test_limit
            || !fits_pool(compiling, credits, weight, occupancy.pool)
            // A test waiting for memory asks for no credit: it would hold
            // them idle until a running test ends.
            || !occupancy.memory_fits(testing, held, memory)
        {
            break;
        }
        credits += weight;
        held += memory;
        testing += 1;
    }
    compiling + credits
}

/// Whether a test of `weight` fits in the pool beside `compiling` compiler
/// jobs and `credits` held by tests; weight 1 always does (see `wanted`).
fn fits_pool(compiling: usize, credits: usize, weight: usize, pool: usize) -> bool {
    weight <= 1 || compiling + credits + weight <= pool
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test(weight: usize) -> Demand {
        Demand::Test {
            weight,
            exclusive: false,
            memory: 0,
        }
    }

    fn alone(weight: usize) -> Demand {
        Demand::Test {
            weight,
            exclusive: true,
            memory: 0,
        }
    }

    fn occupancy(limit: usize) -> Occupancy {
        Occupancy {
            test_limit: limit,
            pool: usize::MAX,
            ..Occupancy::default()
        }
    }

    /// Admit until nothing fits, with `credits` total, returning the order.
    fn drain(mut occupancy: Occupancy, mut pending: Vec<Demand>, credits: usize) -> Vec<Demand> {
        let mut order = Vec::new();
        loop {
            let free = credits.checked_sub(occupancy.held()).unwrap();
            let Choice::Dispatch(index) = choose(&occupancy, &pending, Some(free)) else {
                return order;
            };
            let demand = pending.remove(index);
            occupancy.admit(demand);
            assert!(occupancy.held() <= credits, "{order:?} then {demand:?}");
            assert!(occupancy.test_credits <= occupancy.test_limit);
            order.push(demand);
        }
    }

    #[test]
    fn weights_are_admitted_whole_and_within_the_test_limit() {
        // Highest priority last: the weight-3 test is at the head.
        let order = drain(occupancy(4), vec![test(1), test(1), test(3)], 8);
        assert_eq!(order, vec![test(3), test(1)]);
        // A head test that does not fit holds back lighter ones behind it.
        let mut held = occupancy(4);
        held.admit(test(2));
        assert_eq!(choose(&held, &[test(1), test(3)], Some(6)), Choice::Wait);
        // ... but never ready compiler work, which takes a free credit.
        held.admit(Demand::Compile);
        assert_eq!(
            choose(&held, &[Demand::Compile, test(3)], Some(1)),
            Choice::Dispatch(0)
        );
        // Credits, not the limit, decide when the jobserver is short.
        assert_eq!(choose(&occupancy(8), &[test(4)], Some(3)), Choice::Wait);
        assert_eq!(
            choose(&occupancy(8), &[test(4)], Some(4)),
            Choice::Dispatch(0)
        );
    }

    #[test]
    fn compiler_progress_credit_precedes_ready_tests() {
        let mut busy = occupancy(4);
        busy.admit(test(1));
        assert_eq!(
            choose(&busy, &[Demand::Compile, test(1)], Some(1)),
            Choice::Dispatch(0)
        );
        busy.compiler_finalized = true;
        assert_eq!(
            choose(&busy, &[Demand::Compile, test(1)], Some(1)),
            Choice::Dispatch(1)
        );
    }

    #[test]
    fn an_exclusive_test_runs_with_nothing_beside_it() {
        // While compilation can still produce ready work, an exclusive test
        // waits without holding other tests back.
        let mut compiling = occupancy(4);
        compiling.admit(Demand::Compile);
        assert_eq!(
            choose(&compiling, &[test(1), alone(1)], Some(3)),
            Choice::Dispatch(0)
        );
        // Once compilation is quiet it waits for running tests to drain and
        // holds back the tests behind it.
        let mut testing = occupancy(4);
        testing.admit(test(1));
        assert_eq!(
            choose(&testing, &[test(1), alone(1)], Some(3)),
            Choice::Wait
        );
        assert_eq!(
            choose(&occupancy(4), &[test(1), alone(2)], Some(4)),
            Choice::Dispatch(1)
        );
        // Nothing starts beside it, compiler work included.
        let mut exclusive = occupancy(4);
        exclusive.admit(alone(1));
        assert_eq!(
            choose(&exclusive, &[Demand::Compile, test(1)], None),
            Choice::Wait
        );
        // At the head of the order it holds back the tests behind it, so
        // the running tests drain before it starts.
        let order = drain(occupancy(4), vec![test(1), alone(1), test(1)], 4);
        assert_eq!(order, vec![test(1)]);
    }

    /// The reference `wanted`: dispatch with unlimited credits until a wait.
    /// A test above weight 1 that does not fit the pool beside all compiler
    /// work (running, or ready: every ready entry starts) is held back, as
    /// `choose` holds back a test short of credits: no test behind it
    /// starts, and compiler work still does.
    fn simulated(occupancy: &Occupancy, pending: &[Demand]) -> usize {
        let mut occupancy = *occupancy;
        let mut pending = pending.to_vec();
        while let Choice::Dispatch(index) = choose(&occupancy, &pending, None) {
            if let Demand::Test { weight, .. } = pending[index] {
                let ready = if occupancy.compiler_finalized {
                    0
                } else {
                    pending
                        .iter()
                        .filter(|demand| **demand == Demand::Compile)
                        .count()
                };
                let compiling = occupancy.compiling + ready;
                if !fits_pool(compiling, occupancy.test_credits, weight, occupancy.pool) {
                    pending.retain(|demand| *demand == Demand::Compile);
                    continue;
                }
            }
            occupancy.admit(pending.remove(index));
        }
        occupancy.held()
    }

    #[test]
    fn wanted_is_the_closed_form_of_unlimited_dispatch() {
        let alphabet = [
            Demand::Compile,
            test(1),
            test(2),
            test(3),
            alone(1),
            alone(2),
        ];
        let mut checked = 0;
        for len in 0..=4u32 {
            for code in 0..alphabet.len().pow(len) {
                let mut rest = code;
                let pending: Vec<_> = (0..len)
                    .map(|_| {
                        let demand = alphabet[rest % alphabet.len()];
                        rest /= alphabet.len();
                        demand
                    })
                    .collect();
                for running in [None, Some(Demand::Compile), Some(test(1)), Some(alone(1))] {
                    for finalized in [false, true] {
                        for pool in [4, 5, usize::MAX] {
                            let mut base = occupancy(4);
                            base.compiler_finalized = finalized;
                            base.pool = pool;
                            if let Some(running) = running {
                                base.admit(running);
                            }
                            assert_eq!(
                                wanted(&base, &pending),
                                simulated(&base, &pending),
                                "{base:?} {pending:?}"
                            );
                            checked += 1;
                        }
                    }
                }
            }
        }
        assert!(checked > 30_000);
    }

    #[test]
    fn equal_tests_dispatch_in_inventory_order_whatever_their_readiness_order() {
        let entries = [
            Rank {
                priority: 100,
                test: Some(2),
            },
            Rank {
                priority: 100,
                test: Some(0),
            },
            Rank {
                priority: 100,
                test: None,
            },
            Rank {
                priority: 100,
                test: Some(1),
            },
            Rank {
                priority: 300,
                test: Some(3),
            },
            Rank {
                priority: 50,
                test: None,
            },
        ];
        // Every readiness order of the entries yields one dispatch order.
        let mut orders = std::collections::BTreeSet::new();
        let mut permutation: Vec<usize> = (0..entries.len()).collect();
        loop {
            let mut queue: Vec<Rank> = Vec::new();
            for &entry in permutation.iter().map(|&i| &entries[i]) {
                let index = queue.partition_point(|&queued| stays_ahead(queued, entry));
                // partition_point needs the predicate to be true then false.
                assert!(
                    queue[index..]
                        .iter()
                        .all(|&queued| !stays_ahead(queued, entry))
                );
                queue.insert(index, entry);
            }
            let dispatched: Vec<_> = queue
                .iter()
                .rev()
                .map(|rank| (rank.priority, rank.test))
                .collect();
            orders.insert(dispatched);
            // Next lexicographic permutation.
            let Some(i) = (1..permutation.len())
                .rev()
                .find(|&i| permutation[i - 1] < permutation[i])
            else {
                break;
            };
            let j = (i..permutation.len())
                .rev()
                .find(|&j| permutation[i - 1] < permutation[j])
                .unwrap();
            permutation.swap(i - 1, j);
            permutation[i..].reverse();
        }
        assert_eq!(
            orders.into_iter().collect::<Vec<_>>(),
            vec![vec![
                (300, Some(3)),
                (100, None),
                (100, Some(0)),
                (100, Some(1)),
                (100, Some(2)),
                (50, None),
            ]]
        );
    }

    #[test]
    fn wanted_credits_cover_a_waiting_head_but_not_limit_blocked_tests() {
        let mut held = occupancy(4);
        held.admit(test(1));
        // The weight-3 head fits the limit once granted: keep tokens for it.
        assert_eq!(wanted(&held, &[test(1), test(3)]), 4);
        // A limit-blocked head gains nothing from more tokens.
        held.admit(test(2));
        assert_eq!(wanted(&held, &[test(1), test(3)]), 3);
        // Ready compiler work wants one credit each.
        assert_eq!(wanted(&held, &[Demand::Compile, Demand::Compile]), 5);
        // An exclusive test wants its weight once nothing else runs.
        assert_eq!(wanted(&occupancy(4), &[alone(3)]), 3);
        assert_eq!(wanted(&held, &[alone(3)]), 3);
    }

    #[test]
    fn a_weighted_test_asks_for_credits_only_once_it_fits_beside_compilation() {
        let mut pool = occupancy(3);
        pool.pool = 3;
        pool.admit(Demand::Compile);
        // Running compilation and the head's weight exceed the pool: the
        // head cannot start before compilation shrinks, so collecting tokens
        // now would only idle them. It holds back the test behind it.
        assert_eq!(wanted(&pool, &[test(1), test(3)]), 1);
        // Ready compiler work counts as running: every ready entry starts.
        let mut quiet = occupancy(3);
        quiet.pool = 3;
        assert_eq!(wanted(&quiet, &[test(3), Demand::Compile]), 1);
        // With compilation quiet it fits, so its credits are asked for.
        assert_eq!(wanted(&quiet, &[test(3)]), 3);
        // A weight-1 test is counted beside compilation, as before.
        assert_eq!(wanted(&pool, &[test(1), test(1)]), 3);
    }

    fn sized(memory: usize) -> Demand {
        Demand::Test {
            weight: 1,
            exclusive: false,
            memory,
        }
    }

    fn budget(limit: usize, memory_limit: usize) -> Occupancy {
        Occupancy {
            memory_limit: Some(memory_limit),
            ..occupancy(limit)
        }
    }

    #[test]
    fn tests_are_admitted_within_the_memory_budget_as_well_as_the_credits() {
        // Four credits and 40 units of memory: three 16-unit tests would be
        // 48, so two run and the third waits, though credits are free.
        let order = drain(budget(4, 40), vec![sized(16), sized(16), sized(16)], 8);
        assert_eq!(order, vec![sized(16), sized(16)]);
        let mut two = budget(4, 40);
        two.admit(sized(16));
        two.admit(sized(16));
        assert_eq!(two.test_memory, 32);
        assert_eq!(choose(&two, &[sized(16)], Some(6)), Choice::Wait);
        // One that fits what is left starts; the head that does not fit
        // holds back what is behind it, as a head short of credits does.
        assert_eq!(choose(&two, &[sized(8)], Some(6)), Choice::Dispatch(0));
        assert_eq!(choose(&two, &[sized(8), sized(16)], Some(6)), Choice::Wait);
        // A test counted for nothing is never held by memory.
        assert_eq!(choose(&two, &[sized(0)], Some(6)), Choice::Dispatch(0));
        // Without a budget the count admits nothing and refuses nothing.
        let mut unbounded = occupancy(4);
        unbounded.admit(sized(16));
        unbounded.admit(sized(16));
        assert_eq!(choose(&unbounded, &[sized(16)], Some(6)), Choice::Dispatch(0));
    }

    #[test]
    fn a_test_larger_than_the_whole_budget_runs_with_no_other_test() {
        // It never fits beside another test, and never waits forever.
        assert_eq!(choose(&budget(4, 8), &[sized(16)], Some(4)), Choice::Dispatch(0));
        let mut running = budget(4, 8);
        running.admit(sized(16));
        assert_eq!(choose(&running, &[sized(1)], Some(3)), Choice::Wait);
        // A host with no budget at all runs its counted tests one at a time.
        let order = drain(budget(4, 0), vec![sized(16), sized(16)], 8);
        assert_eq!(order, vec![sized(16)]);
        // Compiler work is not a test: it runs beside the oversized one.
        assert_eq!(
            choose(&running, &[Demand::Compile, sized(1)], Some(3)),
            Choice::Dispatch(0)
        );
    }

    #[test]
    fn a_test_waiting_for_memory_asks_for_no_credit() {
        let mut two = budget(4, 40);
        two.admit(sized(16));
        two.admit(sized(16));
        // The head does not fit the budget: no token is collected for it,
        // nor for the test it holds back.
        assert_eq!(wanted(&two, &[sized(4), sized(16)]), 2);
        // What fits is asked for, up to the budget.
        assert_eq!(wanted(&two, &[sized(16), sized(4), sized(4)]), 4);
        // With no test running the head is admitted whatever its size.
        assert_eq!(wanted(&budget(4, 8), &[sized(16), sized(16)]), 1);
    }

    #[test]
    fn the_longest_expected_harness_costs_most_and_an_exclusive_one_nothing() {
        // Expectation leads, then weight; an exclusive harness goes last.
        assert!(cost(1, false, 647) > cost(8, false, 60));
        assert!(cost(8, false, 60) > cost(1, false, 60));
        assert!(cost(1, false, 1) > cost(64, false, 0));
        assert_eq!(cost(3, false, 0), 300);
        assert_eq!(cost(3, true, 647), 0);
    }
}
