//! Explicit-state exploration of an event program at the real constants.
//!
//! Interleaving points are platform events (D2): at every state each thread
//! root settled at an event may take it, under every oracle choice its event
//! lists — and a `fork`/`posix_spawn`, under every torn table copy the other
//! threads' pending events allow ([`Interp::torn_variants`]); a forked child,
//! once created, runs to its exec as one macro step before anyone else moves
//! (SD-3). Exploration stops at the **horizon**
//! ([`Interp::horizon`]): once no policy child is running and no actor can
//! reach a policy spawn again, nothing can change the fd-inherit verdict
//! (exec'd images are not modeled, an exec'd child's table is frozen), so
//! such states are terminal. The horizon and the state budget are printed
//! into the model's notes (I-BOUND-DISCLOSED).
//!
//! M2: a forked child interleaves from its first split point
//! ([`Interp::at_split`]); an exec'd image (whose code is not modeled) may
//! exit at any time ([`ActionKey::ImageExit`], RL-IMAGE-EXIT) in a program
//! that uses M2 features; and a program under P-LOCK-RELEASE or fd-identity
//! has no horizon (its atoms are not frozen there).
//!
//! M2 review: a call that has not returned (a split `posix_spawn`, a waiting
//! `open`, a sleeping `flock`) is continued by a later action of its actor
//! ([`ActionKey::Event`] with `resume`); under fd-identity, RL-FOREIGN may
//! squat on any number an actor retired ([`ActionKey::ForeignSquat`]); and a
//! state in which some actor has not finished yet nothing can move is
//! counted ([`Graph::stuck`]) and named in the model's notes — a model
//! deadlock is never a silent halt.

use std::collections::{HashMap, VecDeque};

use rayon::prelude::*;
use trust_platform::{Call, Host, OfdId, Oracle, Phase};

use crate::interp::{Actor, Binding, Config, Fired, Interp, InterpError, Role};
use crate::program::{StmtKind, StmtRef};

/// What a machine transition is.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ActionKey {
    /// RL-INIT chose initial table `k`.
    Init(usize),
    /// A thread root took the event at `at` under `oracle` (a fork/spawn
    /// whose table copy `missed` these slots); `resume`: it continued a call
    /// of its that had not returned.
    Event { role: Role, at: StmtRef, oracle: Oracle, missed: Vec<i32>, resume: bool },
    /// RL-FOREIGN: foreign code made a descriptor of its own at `fd` (a number
    /// an actor retired).
    ForeignSquat { fd: i32 },
    /// A forked child ran from its fork to its end — or, under child split
    /// points, to its next split point — along `path`.
    Child { role: Role, path: Vec<(StmtRef, Oracle)> },
    /// RL-IMAGE-EXIT: the image the `nth` child of `site` exec'd exits (its
    /// code is not modeled; `_exit(0)` closes every descriptor it holds).
    ImageExit { site: usize, nth: u32 },
    /// X1: an actor settled at an undecided guard (`Cond::Nondet`, the
    /// branch at `at`) took its then-arm (`then`) or its else-arm
    /// (`crate::nondet`; an over-approximating step).
    Nondet { role: Role, at: StmtRef, then: bool },
}

/// The explored graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Graph {
    pub configs: Vec<Config>,
    /// `(from, action, to)`.
    pub edges: Vec<(usize, usize, usize)>,
    pub actions: Vec<ActionKey>,
    /// The event log of each action's first occurrence (child macros carry
    /// all their events).
    pub action_logs: Vec<Vec<Fired>>,
    /// `(initial table index, config)`.
    pub inits: Vec<(usize, usize)>,
    pub horizon_states: usize,
    /// Explored states with no successor in which some actor has not
    /// finished: everything left waits (a deadlock of the program, or of the
    /// model) — counted, never silent.
    pub stuck: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExploreError {
    Interp(InterpError),
    /// More than the budget of states (counted in states, not wall time).
    Budget {
        states: usize,
    },
}

impl std::fmt::Display for ExploreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExploreError::Interp(e) => write!(f, "{e}"),
            ExploreError::Budget { states } => {
                write!(f, "state budget exhausted after {states} states (refusing a partial model)")
            }
        }
    }
}

impl From<InterpError> for ExploreError {
    fn from(e: InterpError) -> Self {
        ExploreError::Interp(e)
    }
}

// Bound speculative successor storage independently of the size of the caller's
// Rayon pool. The pool, including an admitted RAYON_NUM_THREADS share, still owns
// concurrency; this is not a second worker pool or a larger state budget.
const MAX_EXPANSION_BATCH: usize = 8;

/// Renumber descriptions in first-reference order (as `Host::canonical`
/// does) and carry the class map along.
#[must_use]
pub fn canonicalize(c: &Config) -> Config {
    let mut map: std::collections::BTreeMap<OfdId, OfdId> = std::collections::BTreeMap::new();
    let mut next = 1u32;
    for (_, p) in c.host.procs() {
        for e in p.table.values() {
            map.entry(e.ofd).or_insert_with(|| {
                let id = OfdId(next);
                next += 1;
                id
            });
        }
    }
    let host: Host = c.host.canonical();
    // `Host::canonical` uses the same order; check it rather than trust it.
    let consistent = c.host.procs().all(|(pid, p)| {
        p.table
            .iter()
            .all(|(fd, e)| host.entry(pid, *fd).map(|x| x.ofd) == map.get(&e.ofd).copied())
    });
    if !consistent {
        return c.clone();
    }
    let classes = c.classes.iter().filter_map(|(o, k)| map.get(o).map(|n| (*n, *k))).collect();
    let mut actors = c.actors.clone();
    for a in &mut actors {
        for b in a.bindings.values_mut() {
            if let Binding::Ofd(o) = *b {
                *b = map.get(&o).map_or(Binding::Gone, |n| Binding::Ofd(*n));
            }
        }
    }
    let remap_set = |s: &std::collections::BTreeSet<OfdId>| {
        s.iter().filter_map(|o| map.get(o).copied()).collect()
    };
    Config {
        host,
        classes,
        actors,
        released: remap_set(&c.released),
        owner_locks: remap_set(&c.owner_locks),
        ..c.clone()
    }
}

impl Interp<'_> {
    /// The fd-inherit horizon: no policy child is still running and no
    /// actor can reach a policy spawn site again (a static reachability over
    /// the CFG and its calls). From here on no state can gain a violation —
    /// an exec'd child's table is frozen, an exited one is empty — so such
    /// states are terminal. A program without a policy site has no horizon.
    #[must_use]
    pub fn horizon(&self, cfg: &Config) -> bool {
        if !self.core.declared.iter().any(Option::is_some) {
            return false;
        }
        let p = &self.core.prog.policies;
        if p.lock_release || !p.fd_identity.is_empty() {
            return false;
        }
        cfg.actors.iter().all(|a| match a.role {
            Role::Child { site, .. } => {
                a.done() || !matches!(self.core.declared.get(site), Some(Some(_)))
            }
            Role::Thread(_) => {
                a.frames.iter().all(|f| !self.core.reaches_policy(f.body, f.block, f.idx))
            }
        })
    }

    /// Every successor of `cfg`.
    pub fn successors(
        &self,
        cfg: &Config,
    ) -> Result<Vec<(ActionKey, Config, Vec<Fired>)>, InterpError> {
        if self.horizon(cfg) {
            return Ok(Vec::new());
        }
        // X1: an actor at an undecided guard takes its choice first (a local
        // step; `crate::nondet`).
        if let Some(out) = self.nondet_successors(cfg)? {
            return Ok(out);
        }
        let mut out = Vec::new();
        // A child that is not at a split point runs (as one macro step) before
        // anyone else moves (SD-3).
        if let Some(i) = cfg.actors.iter().enumerate().position(|(j, a)| {
            matches!(a.role, Role::Child { .. }) && !a.done() && !self.at_split(cfg, j)
        }) {
            let role = cfg.actors[i].role;
            for (c, log) in self.run_child(cfg, i)? {
                let path = log.iter().map(|f| (f.at, f.oracle)).collect();
                out.push((ActionKey::Child { role, path }, self.finish(c), log));
            }
            return Ok(out);
        }
        if self.core.extended {
            for r in &cfg.spawns {
                if r.gone || !r.execd {
                    continue;
                }
                if !matches!(cfg.host.proc(r.pid).map(|p| p.phase), Some(Phase::Execd)) {
                    continue;
                }
                let call = Call::Exit { status: 0 };
                let step = trust_platform::step(&cfg.host, r.pid, &call, Oracle::Nominal).map_err(
                    |refusal| InterpError::Unsupported {
                        at: None,
                        detail: format!("an exec'd image's exit was refused: {refusal}"),
                    },
                )?;
                let mut c = cfg.clone();
                c.host = step.host;
                c.classes.retain(|o, _| c.host.ofd(*o).is_some());
                let fired = Fired {
                    role: Role::Child { site: r.site, nth: r.nth },
                    at: crate::program::StmtRef { body: usize::MAX, block: 0, idx: 0 },
                    oracle: Oracle::Nominal,
                    missed: Vec::new(),
                    pid: r.pid,
                    call: Some(call),
                    result: Some(step.result),
                    note: "RL-IMAGE-EXIT: the exec'd image exits".to_string(),
                };
                out.push((
                    ActionKey::ImageExit { site: r.site, nth: r.nth },
                    self.finish(c),
                    vec![fired],
                ));
            }
        }
        for (i, a) in cfg.actors.iter().enumerate() {
            if a.done() {
                continue;
            }
            if matches!(a.role, Role::Child { .. }) && !self.at_split(cfg, i) {
                continue;
            }
            let Some(at) = a.pc() else { continue };
            let copies = match (self.at(a), a.pending) {
                (Some((_, StmtKind::Fork { .. })), _) => self.torn_variants(cfg, i)?,
                (Some((_, StmtKind::Event(ev))), None) if matches!(ev.call, Call::Spawn { .. }) => {
                    self.torn_variants(cfg, i)?
                }
                _ => vec![Vec::new()],
            };
            let resume = a.pending.is_some();
            for o in self.oracles(a) {
                for missed in &copies {
                    if let Some((c, f)) = self.fire(cfg, i, o, missed)? {
                        out.push((
                            ActionKey::Event {
                                role: a.role,
                                at,
                                oracle: o,
                                missed: missed.clone(),
                                resume,
                            },
                            self.finish(c),
                            vec![f],
                        ));
                    }
                }
            }
        }
        for fd in self.squat_targets(cfg) {
            let c = self.squat(cfg, fd)?;
            let fired = Fired {
                role: Role::Thread(0),
                at: crate::program::StmtRef { body: usize::MAX, block: 0, idx: 0 },
                oracle: Oracle::Nominal,
                missed: Vec::new(),
                pid: self.root,
                call: None,
                result: None,
                note: format!(
                    "RL-FOREIGN: foreign code makes a descriptor of its own at {fd} (dup2 onto \
                     it, or F_DUPFD with that floor)"
                ),
            };
            out.push((ActionKey::ForeignSquat { fd }, self.finish(c), vec![fired]));
        }
        Ok(out)
    }

    /// Post-transition bookkeeping: a reaped child's record names it no more
    /// (its pid may be reused); canonical form.
    #[must_use]
    pub fn finish(&self, mut c: Config) -> Config {
        for r in &mut c.spawns {
            if !r.gone && c.host.proc(r.pid).is_none() {
                r.gone = true;
            }
        }
        // P-LOCK-RELEASE: a release mark lets go of every live description of
        // its classes (as the transition left them); a dropped description
        // leaves the sets.
        if c.actors.iter().any(|a| !a.released.is_empty()) {
            let marked: std::collections::BTreeSet<usize> =
                c.actors.iter_mut().flat_map(|a| std::mem::take(&mut a.released)).collect();
            for (o, _) in c.host.ofds() {
                if c.classes.get(&o).is_some_and(|k| marked.contains(k)) {
                    c.released.insert(o);
                }
            }
        }
        c.released.retain(|o| c.host.ofd(*o).is_some());
        c.owner_locks.retain(|o| c.host.ofd(*o).is_some());
        if self.core.extended {
            // Actors in role order: a thread started before or after a child
            // was forked is the same state. (An M1 program's actors are
            // created in one order only, so its states are unchanged.)
            c.actors.sort_by_key(|a| a.role);
            // A reaped child's record only counts its site's children (the
            // next one's `nth`): forget the rest of its history.
            for r in &mut c.spawns {
                if r.gone {
                    r.pid = trust_platform::Pid(0);
                    r.execd = false;
                    r.premise = true;
                    r.declared.clear();
                }
            }
            c.spawns.sort_by_key(|r| (r.site, r.nth));
        }
        canonicalize(&c)
    }

    /// A settled initial configuration.
    pub fn initial(
        &self,
        host: Host,
        classes: Vec<(OfdId, usize)>,
        params: &[(usize, i64)],
    ) -> Result<Config, InterpError> {
        let mut actors = Vec::new();
        for (t, root) in self.core.prog.roots.iter().enumerate() {
            if root.dormant {
                continue;
            }
            let mut vars: Vec<i64> = self.core.prog.vars.iter().map(|v| v.init).collect();
            for (var, fd) in params {
                vars[*var] = *fd;
            }
            let mut a = Actor {
                role: Role::Thread(t),
                pid: self.root,
                frames: vec![crate::interp::Frame { body: root.body, block: 0, idx: 0, ret: None }],
                vars,
                bindings: std::collections::BTreeMap::new(),
                wrote: std::collections::BTreeSet::new(),
                checked: self.listed(t),
                released: std::collections::BTreeSet::new(),
                pending: None,
            };
            // fd-identity: a descriptor argument is bound from the start.
            if self.tracks() {
                for (_, fd) in params {
                    if let Ok(n) = i32::try_from(*fd)
                        && let Some(e) = host.entry(self.root, n)
                    {
                        a.bindings.insert(n, Binding::Ofd(e.ofd));
                    }
                }
            }
            self.settle(&mut a)?;
            actors.push(a);
        }
        let c = Config {
            host,
            classes: classes.into_iter().collect(),
            actors,
            spawns: Vec::new(),
            identity_violation: None,
            released: std::collections::BTreeSet::new(),
            owner_locks: std::collections::BTreeSet::new(),
        };
        Ok(self.finish(c))
    }

    /// Breadth-first exploration from the initial configurations.
    pub fn explore(&self, inits: Vec<Config>, budget: usize) -> Result<Graph, ExploreError> {
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
            if let Some(&id) = action_index.get(&key) {
                return id;
            }
            let id = g.actions.len();
            action_index.insert(key.clone(), id);
            g.actions.push(key);
            g.action_logs.push(log);
            id
        };
        for (k, c) in inits.into_iter().enumerate() {
            let id = match index.get(&c) {
                Some(&id) => id,
                None => {
                    let id = configs.len();
                    configs.push(c.clone());
                    index.insert(c, id);
                    queue.push_back(id);
                    id
                }
            };
            g.inits.push((k, id));
            intern(&mut g, ActionKey::Init(k), Vec::new());
        }
        let batch_size = rayon::current_num_threads().min(MAX_EXPANSION_BATCH);
        while !queue.is_empty() {
            if configs.len() > budget {
                return Err(ExploreError::Budget { states: configs.len() });
            }
            let batch: Vec<_> = queue.drain(..queue.len().min(batch_size)).collect();
            let expand = |s: &usize| {
                let cfg = &configs[*s];
                (self.horizon(cfg), self.successors(cfg))
            };
            // Indexed collection retains FIFO order. In particular, collect a
            // Vec of Results: parallel Result collection could choose a later
            // state's error instead of the serial explorer's first refusal.
            let expanded: Vec<_> = if batch.len() == 1 {
                batch.iter().map(expand).collect()
            } else {
                batch.par_iter().map(expand).collect()
            };
            for (s, (horizon, successors)) in batch.into_iter().zip(expanded) {
                // Earlier results may have grown the graph beyond the budget.
                // Observe the exact serial boundary before this state's result;
                // speculative work never contributes states, actions or evidence.
                if configs.len() > budget {
                    return Err(ExploreError::Budget { states: configs.len() });
                }
                if horizon {
                    g.horizon_states += 1;
                }
                let succ = successors?;
                if succ.is_empty() && !horizon && configs[s].actors.iter().any(|a| !a.done()) {
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
        }
        g.configs = configs;
        g.edges.sort_unstable();
        g.edges.dedup();
        Ok(g)
    }
}

#[cfg(test)]
mod parallel_tests;
