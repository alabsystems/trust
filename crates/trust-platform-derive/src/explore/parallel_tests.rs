//! Differential oracle: the pre-batching FIFO explorer from 2221ce0b30.

use rayon::{ThreadPool, ThreadPoolBuilder};
use trust_platform::{Call, Host, Pid, Rlimit};

use super::*;
use crate::derive::{init_config, rl_init_tables};
use crate::env::{Limits, Slot};
use crate::fixtures::{self, Fixture};
use crate::lower::{CoreProgram, lower};
use crate::partition::Partition;
use crate::program::{Bind, Operand, ProgramBuilder};

// Keep this oracle serial and independent of frontier batching. Compare the
// entire graph, including numbering, first-occurrence event logs and refusals.
fn serial(interp: &Interp<'_>, inits: Vec<Config>, budget: usize) -> Result<Graph, ExploreError> {
    let mut index: HashMap<Config, usize> = HashMap::new();
    let mut configs: Vec<Config> = Vec::new();
    let mut queue = VecDeque::new();
    let mut g = Graph {
        configs: Vec::new(),
        edges: Vec::new(),
        actions: Vec::new(),
        action_logs: Vec::new(),
        inits: Vec::new(),
        horizon_states: 0,
        stuck: Vec::new(),
    };
    let mut action_index: HashMap<ActionKey, usize> = HashMap::new();
    let mut intern = |g: &mut Graph, key: ActionKey, log: Vec<Fired>| -> usize {
        *action_index.entry(key.clone()).or_insert_with(|| {
            g.actions.push(key);
            g.action_logs.push(log);
            g.actions.len() - 1
        })
    };
    for (k, c) in inits.into_iter().enumerate() {
        let id = *index.entry(c.clone()).or_insert_with(|| {
            configs.push(c.clone());
            queue.push_back(configs.len() - 1);
            configs.len() - 1
        });
        g.inits.push((k, id));
        intern(&mut g, ActionKey::Init(k), Vec::new());
    }
    while let Some(s) = queue.pop_front() {
        if configs.len() > budget {
            return Err(ExploreError::Budget { states: configs.len() });
        }
        let cfg = configs[s].clone();
        let horizon = interp.horizon(&cfg);
        if horizon {
            g.horizon_states += 1;
        }
        let succ = interp.successors(&cfg)?;
        if succ.is_empty() && !horizon && cfg.actors.iter().any(|a| !a.done()) {
            g.stuck.push(s);
        }
        for (key, next, log) in succ {
            let t = match index.get(&next) {
                Some(t) => *t,
                None => {
                    configs.push(next.clone());
                    index.insert(next, configs.len() - 1);
                    queue.push_back(configs.len() - 1);
                    configs.len() - 1
                }
            };
            let a = intern(&mut g, key, log);
            g.edges.push((s, a, t));
        }
    }
    g.configs = configs;
    g.edges.sort_unstable();
    g.edges.dedup();
    Ok(g)
}

fn small_fixture(mut f: Fixture) -> (CoreProgram, Vec<Config>, Option<i64>) {
    // RL-INIT packs socket peers above the partition's small points. Keep
    // the resource limits outside that interval so both argument layouts
    // have room for their peers instead of silently enumerating no tables.
    f.env.limits = Limits { soft: 64, hard: 128, max_files_per_proc: 128 };
    f.env.param_slots = vec![Slot::Exact(3), Slot::Exact(4)];
    f.env.foreign = false;
    f.env.foreign_at.clear();
    let mut core = lower(&f.program).expect("fixture lowers");
    for class in f.env.class_names() {
        core.intern_class(class);
    }
    let interp = Interp { core: &core, root: Pid(1), fd_bound_cap: f.env.fd_bound_cap };
    let partition =
        Partition::new([0, 1, 2, 3, 4, 5, 6, 65_536].into_iter().chain(f.env.constants()), [-1]);
    let inits = rl_init_tables(&core, &f.env, &partition)
        .into_iter()
        .map(|(_, placed)| init_config(&interp, &f.env, &placed).expect("initial table"))
        .collect();
    (core, inits, f.env.fd_bound_cap)
}

fn compare(pools: &[ThreadPool], interp: &Interp<'_>, inits: &[Config], budget: usize) {
    let expected = serial(interp, inits.to_vec(), budget);
    for pool in pools {
        let actual = pool.install(|| interp.explore(inits.to_vec(), budget));
        assert_eq!(actual, expected, "workers={} budget={budget}", pool.current_num_threads());
    }
}

#[test]
fn bounded_parallel_frontiers_preserve_serial_graphs_and_refusals() {
    // One harness case keeps these independent pools from multiplying the
    // admitted runtime share while the differential matrix executes.
    let pools: Vec<_> = [1, 2, 7]
        .into_iter()
        .map(|workers| ThreadPoolBuilder::new().num_threads(workers).build().expect("test pool"))
        .collect();
    for fixture in [
        fixtures::spawnfd::no_strip(),
        fixtures::spawnfd::strip_first_premise(),
        fixtures::spawnfd::original_dup_only(),
    ] {
        let (core, mut inits, fd_bound_cap) = small_fixture(fixture);
        assert_eq!(inits.len(), 2, "both descriptor argument permutations must be explored");
        inits.push(inits[0].clone());
        let interp = Interp { core: &core, root: Pid(1), fd_bound_cap };
        let full = serial(&interp, inits.clone(), 100_000).expect("complete small fixture");
        assert!(full.configs.len() > MAX_EXPANSION_BATCH, "exercise more than one frontier");
        assert!(full.actions.iter().any(|action| matches!(action, ActionKey::Child { .. })));
        assert!(full.action_logs.iter().any(|events| !events.is_empty()));
        for budget in [0, inits.len(), inits.len() + 1, full.configs.len() - 1, full.configs.len()]
        {
            compare(&pools, &interp, &inits, budget);
        }
        compare(&pools, &interp, &[], 0);
    }

    // Two distinct unsupported resources give different interpreter refusals.
    // Public initial configurations may start at either valid event position.
    // Return the FIFO state's refusal, regardless of which worker finishes first.
    let mut p = ProgramBuilder::new("parallel_refusal_order");
    let body = p.body("main", Vec::new(), |b| {
        b.event("parallel:close", "close", Call::Close { fd: Operand::Lit(9) }, Bind::none());
        b.event("parallel:first", "getrlimit", Call::Getrlimit { resource: 123 }, Bind::none());
        b.event("parallel:second", "getrlimit", Call::Getrlimit { resource: 456 }, Bind::none());
    });
    p.root("main", body);
    let core = lower(&p.build()).expect("modeled symbols");
    let interp = Interp { core: &core, root: Pid(1), fd_bound_cap: None };
    let mut host = Host::new(32);
    host.add_root(Rlimit { soft: 16, hard: 32 });
    let first = interp.initial(host, Vec::new(), &[]).expect("initial state");
    let mut bad1 = first.clone();
    bad1.actors[0].frames[0].idx = 1;
    let mut bad2 = first.clone();
    bad2.actors[0].frames[0].idx = 2;
    let refusal1 = serial(&interp, vec![bad1.clone()], 10).expect_err("first resource refused");
    let refusal2 = serial(&interp, vec![bad2.clone()], 10).expect_err("second resource refused");
    assert_ne!(refusal1, refusal2, "the first-error assertion must distinguish the two states");
    compare(&pools, &interp, &[bad1.clone(), bad2.clone()], 10);
    compare(&pools, &interp, &[bad2.clone(), bad1], 10);

    // The first successful expansion adds a third state. Serial execution must
    // hit its state budget before inspecting the second state's ready refusal.
    let inits = vec![first, bad2];
    assert_eq!(serial(&interp, inits.clone(), 2), Err(ExploreError::Budget { states: 3 }));
    compare(&pools, &interp, &inits, 2);
}
