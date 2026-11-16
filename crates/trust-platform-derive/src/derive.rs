//! The derivation driver and emission (plan D7).
//!
//! `derive` = lower -> partition -> RL-INIT tables -> explore (at the real
//! constants) -> scalar encoding -> quotient -> `StateMachineMetadata` +
//! event map.
//!
//! **Scalar encoding.** A state is a vector of scalars: per actor its
//! program counter and variables; per process (the root, each spawned
//! child) its phase, its `RLIMIT_NOFILE` (soft, hard) and, for every
//! descriptor number any explored state
//! occupies, `open`, `cloexec` and the class of description it names (the
//! allocation-site abstraction of OFDs); per spawned child and class a
//! `holds` Boolean (child-holds-a-reference), its premise bit and its
//! declared set. The emitted machine's states are the distinct vectors; its
//! transitions are the images of the explored transitions.
//! `Stats::encoding_exact` records whether the encoding is injective on the
//! explored states (then that machine is isomorphic to the explored graph).
//! A program that uses M2 features ([`crate::lower::CoreProgram::extended`])
//! adds, per process, its thread count and per descriptor its description's
//! lock, node, `F_GETFL`, peer state and pending data; per path name its
//! node and kind; per actor its release marks and fd-identity bindings; and
//! the node counter and the identity-violation bit.
//!
//! **Emission.** The machine ty checks is the STRONG-BISIMULATION QUOTIENT of
//! that machine with respect to its state labels (partition refinement):
//! bisimilar states satisfy the same CTL formulas, so every verdict is the
//! same, and the thousands of horizon states that differ only in program
//! counters collapse. A ty counterexample over the quotient is lifted back
//! to a path of the explored machine (bisimulation guarantees each step
//! lifts) before it is explained and replayed.
//!
//! **What a verdict over the machine means.** The payload is
//! REFUTATION-ONLY (`TY_TEMPORAL_MODEL_SCHEMA_REFUTATION_ONLY`): the RL-INIT
//! enumeration, the RL-FOREIGN stand-in and the SD-3 reduction are argued,
//! not proved, so ty's "no counterexample" is reported `Unknown`, never
//! `Proved` (SD-8). A refutation carries a trace the replay re-executes.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use trust_platform::{Oracle, PLATFORM_SPEC, Phase, Pid};
use trust_types::fx::FxHashMap;
use trust_types::{StateMachineMetadata, TyTemporalModelPayload, VcKind};

use crate::env::{EnvSpec, InitConfig, ParamShape, Placed};
use crate::explore::{ActionKey, ExploreError, Graph};
use crate::interp::{Config, Interp, InterpError, Role};
use crate::lower::{self, CoreProgram, LowerError};
use crate::partition::Partition;
use crate::program::{Cond, EventProgram, Expr, Operand, StmtKind, StmtRef, Term};
use crate::property::{self, FormulaError};

/// Knobs of the derivation, printed into the model's notes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeriveOptions {
    /// State budget (counted in states, not wall time; D-15(D5)).
    pub budget: usize,
}

impl Default for DeriveOptions {
    fn default() -> Self {
        DeriveOptions { budget: 1_000_000 }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeriveError {
    Lower(LowerError),
    Explore(ExploreError),
    Env(String),
    /// The serialized model exceeds the obligation-metadata transport limit.
    TooLarge {
        bytes: usize,
    },
}

impl std::fmt::Display for DeriveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeriveError::Lower(e) => write!(f, "{e}"),
            DeriveError::Explore(e) => write!(f, "{e}"),
            DeriveError::Env(e) => write!(f, "environment: {e}"),
            DeriveError::TooLarge { bytes } => write!(
                f,
                "the derived model serializes to {bytes} bytes, over the {MAX_PAYLOAD_BYTES}-byte \
                 obligation-metadata limit"
            ),
        }
    }
}

impl From<InterpError> for DeriveError {
    fn from(e: InterpError) -> Self {
        DeriveError::Explore(ExploreError::Interp(e))
    }
}

/// The kind of one scalar of the encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScalarKind {
    Bool,
    Int,
    Enum(Vec<String>),
}

/// The D7 scalar encoding: one named scalar per position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarSchema {
    pub names: Vec<String>,
    pub kinds: Vec<ScalarKind>,
    roles: Vec<Role>,
    pcs: Vec<String>,
    procs: Vec<ProcSlot>,
    /// Every descriptor number any explored process holds.
    fds: Vec<i32>,
    /// M2: the extended columns are present.
    extended: bool,
    /// M2: every path name any explored state has.
    paths: Vec<String>,
    /// M2: every descriptor number any actor has a binding for.
    bind_fds: Vec<i32>,
    /// M2 review: every in-flight call any explored state holds, rendered
    /// (canonical ids), so the encoding distinguishes them.
    inflights: Vec<String>,
    /// M2 review: every fd-identity violation any explored state carries,
    /// rendered (which actor, statement, number, believed and found).
    violations: Vec<String>,
}

/// A process position of the encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ProcSlot {
    Root,
    Spawned { site: usize, nth: u32 },
}

/// One source event of a machine action.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EventSite {
    pub at: String,
    pub symbol: String,
    pub loc: String,
    /// `ROW step k (std source)` when the event is a std summary row step.
    pub std_row: Option<String>,
    pub oracle: String,
}

/// The event-map entry of one machine action label.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActionInfo {
    /// The transition label in the machine (`a<k>`, `halt`).
    pub label: String,
    /// `actor:stmt[>stmt…]` with oracle suffixes, for reading.
    pub text: String,
    pub actor: String,
    pub events: Vec<EventSite>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stats {
    pub init_tables: usize,
    /// Explored configurations.
    pub concrete_states: usize,
    /// Distinct scalar vectors (the machine's states, minus `rl_init`).
    pub abstract_states: usize,
    /// States of the full machine (explored, encoded, plus `rl_init`).
    pub full_states: usize,
    /// States and transitions of the emitted (quotient) machine.
    pub machine_states: usize,
    pub machine_transitions: usize,
    pub actions: usize,
    pub horizon_states: usize,
    /// Explored states in which some actor has not finished and nothing can
    /// move (a deadlock of the program or of the model; named in the notes).
    pub stuck_states: usize,
    pub encoding_exact: bool,
    /// Bytes of the serialized `TyTemporalModelPayload` (for the property
    /// `AG !fd_inherit_violation`); NativeTyEngine's transport caps an
    /// obligation-metadata value at 1 MiB.
    pub payload_bytes: usize,
}

/// A derived model: exactly what [`derive`] built, READ-ONLY outside this
/// crate. Every part is reachable through its accessor ([`Derived::core`],
/// [`Derived::machine`], …); none can be assigned or mutated, so a
/// [`Derived::payload`] or a [`crate::trace::ReplayToken`] is always minted
/// from the derivation `derive` built, never from one whose program Locs,
/// std rows, event map, vocabulary or machine were edited afterwards
/// (red-team H4: with `pub` fields a clone could be rewritten and a token
/// minted from it citing no std row, an attacker's Locs, or a relabelled
/// step that re-executed nothing). Each edit is a compile error:
///
/// ```compile_fail,E0616
/// # use trust_platform_derive::derive::{DeriveOptions, derive};
/// # use trust_platform_derive::fixtures;
/// # let f = fixtures::spawnfd::no_strip();
/// let mut d = derive(&f.program, &f.env, &DeriveOptions::default()).unwrap();
/// // C7a: erase the std origins the replay cites.
/// d.core.prog.bodies.clear();
/// ```
///
/// ```compile_fail,E0616
/// # use trust_platform_derive::derive::{DeriveOptions, derive};
/// # use trust_platform_derive::fixtures;
/// # let f = fixtures::spawnfd::no_strip();
/// let mut d = derive(&f.program, &f.env, &DeriveOptions::default()).unwrap();
/// // C7d: relabel a step as the horizon stutter.
/// d.event_map.clear();
/// ```
///
/// ```compile_fail,E0616
/// # use trust_platform_derive::derive::{DeriveOptions, derive};
/// # use trust_platform_derive::fixtures;
/// # let f = fixtures::spawnfd::no_strip();
/// let mut d = derive(&f.program, &f.env, &DeriveOptions::default()).unwrap();
/// // H1: declare a misspelt atom real.
/// d.vocabulary.insert("fd_inherit_violaton".to_string());
/// ```
///
/// ```compile_fail,E0616
/// # use trust_platform_derive::derive::{DeriveOptions, derive};
/// # use trust_platform_derive::fixtures;
/// # let f = fixtures::spawnfd::no_strip();
/// let mut d = derive(&f.program, &f.env, &DeriveOptions::default()).unwrap();
/// // Erase the machine's labels before the payload is built.
/// d.machine.labels.clear();
/// ```
#[derive(Clone, Debug)]
pub struct Derived {
    pub(crate) name: String,
    pub(crate) core: CoreProgram,
    pub(crate) env: EnvSpec,
    pub(crate) partition: Partition,
    pub(crate) inits: Vec<InitConfig>,
    pub(crate) init_descs: Vec<String>,
    pub(crate) graph: Graph,
    pub(crate) schema: ScalarSchema,
    /// Explored config -> abstract state (machine state = abstract + 1).
    pub(crate) abs_of: Vec<usize>,
    /// Abstract state -> representative explored config.
    pub(crate) reps: Vec<usize>,
    pub(crate) vectors: Vec<Vec<i64>>,
    /// The emitted machine: the bisimulation quotient of the full machine.
    pub(crate) machine: StateMachineMetadata,
    /// The full machine's transitions (state 0 is `rl_init`, state `k + 1`
    /// is abstract state `k`).
    pub(crate) full_transitions: Vec<(usize, String, usize)>,
    /// Full machine state -> emitted (quotient) machine state.
    pub(crate) block_of: Vec<usize>,
    /// Full machine state -> its full rendering (the machine's own state
    /// names are short ids, to keep the transported payload small).
    pub(crate) state_texts: Vec<String>,
    /// Machine action label -> its source events.
    pub(crate) event_map: BTreeMap<String, ActionInfo>,
    /// Graph action index -> machine label.
    pub(crate) action_labels: Vec<String>,
    /// Every atom a formula over this machine may name.
    pub(crate) vocabulary: BTreeSet<String>,
    pub(crate) notes: Vec<String>,
    pub(crate) stats: Stats,
}

pub const INIT_STATE: &str = "rl_init";
pub const HALT: &str = "halt";

/// Every constant the program compares or computes descriptor numbers with,
/// and every additive literal (`x + k`) — the partition's points.
fn collect_constants(core: &CoreProgram, env: &EnvSpec) -> (Vec<i64>, Vec<i64>) {
    let mut v = env.constants();
    let mut offsets = Vec::new();
    fn op(o: &Operand, v: &mut Vec<i64>) {
        if let Operand::Lit(x) = o {
            v.push(*x);
        }
    }
    fn cond_ops(c: &Cond, out: &mut Vec<i64>) {
        match c {
            Cond::Cmp(_, a, b) => {
                op(a, out);
                op(b, out);
            }
            Cond::And(a, b) | Cond::Or(a, b) => {
                cond_ops(a, out);
                cond_ops(b, out);
            }
            Cond::Not(a) => cond_ops(a, out),
            Cond::Const(_) | Cond::Nondet => {}
        }
    }
    for (_, s) in core.prog.stmts() {
        match &s.kind {
            StmtKind::Event(ev) => {
                let _ = ev.call.map(|o| op(o, &mut v));
                match &ev.call {
                    trust_platform::Call::Fcntl { cmd, arg, .. }
                        if *cmd == trust_platform::darwin::F_DUPFD
                            || *cmd == trust_platform::darwin::F_DUPFD_CLOEXEC =>
                    {
                        v.push(*arg);
                    }
                    trust_platform::Call::Setrlimit { soft, hard, .. } => {
                        v.push(i64::try_from(*soft).unwrap_or(i64::MAX));
                        v.push(i64::try_from(*hard).unwrap_or(i64::MAX));
                    }
                    trust_platform::Call::StdStatusFd { .. } => v.push(10),
                    trust_platform::Call::StdMarkCloexec => v.push(3),
                    _ => {}
                }
            }
            StmtKind::Assign { expr, .. } => match expr {
                Expr::Use(a) => op(a, &mut v),
                Expr::Min(a, b) | Expr::BitAnd(a, b) => {
                    op(a, &mut v);
                    op(b, &mut v);
                }
                Expr::Add(a, b) => {
                    op(a, &mut v);
                    op(b, &mut v);
                    op(a, &mut offsets);
                    op(b, &mut offsets);
                }
                Expr::Opaque => {}
            },
            StmtKind::Call { args, .. } => args.iter().for_each(|(_, a)| op(a, &mut v)),
            StmtKind::ForRange { lo, hi, .. } => {
                op(lo, &mut v);
                op(hi, &mut v);
            }
            _ => {}
        }
    }
    for body in &core.prog.bodies {
        for block in &body.blocks {
            if let Term::Branch { cond, .. } = &block.term {
                cond_ops(cond, &mut v);
            }
            if let Term::Return(Some(Operand::Lit(x))) = &block.term {
                v.push(*x);
            }
        }
    }
    for d in core.declared.iter().flatten() {
        v.extend(d.allowed.iter().map(|fd| i64::from(*fd)));
    }
    // Two literals summed into one value (`10 + 1000`) are a point too.
    for (_, s) in core.prog.stmts() {
        if let StmtKind::Assign { expr: Expr::Add(Operand::Lit(a), Operand::Lit(b)), .. } = &s.kind
        {
            v.push(a.saturating_add(*b));
        }
    }
    (v, offsets)
}

/// Shapes of the program's descriptor arguments.
fn param_shapes(core: &CoreProgram) -> Vec<ParamShape> {
    core.prog
        .fd_params
        .iter()
        .map(|p| ParamShape { class: p.class.clone(), peer_class: p.peer_class.clone() })
        .collect()
}

/// Every RL-INIT table of `env` for `core`, with its placement.
pub fn rl_init_tables(
    core: &CoreProgram,
    env: &EnvSpec,
    partition: &Partition,
) -> Vec<(InitConfig, Vec<Placed>)> {
    let shapes = param_shapes(core);
    let mut out = Vec::new();
    // The foreign descriptor's range: below kern.maxfilesperproc, the soft
    // limit notwithstanding (`Limits::foreign_limit`).
    let limit = env.limits.foreign_limit();
    for slots in InitConfig::layouts(env, shapes.len()) {
        let base = InitConfig { slots: slots.clone(), foreign: None };
        let Ok((placed, next_mid)) = base.layout(env, &shapes, partition.mid_lo()) else {
            continue;
        };
        out.push((base, placed));
        let mut at_set: std::collections::BTreeSet<i64> = if env.foreign {
            partition.positions(3, limit, &[next_mid]).into_iter().collect()
        } else {
            std::collections::BTreeSet::new()
        };
        at_set.extend(env.foreign_at.iter().copied().filter(|p| *p >= 3 && *p < limit));
        for at in at_set {
            let ic = InitConfig { slots: slots.clone(), foreign: Some(at) };
            if let Ok((placed, _)) = ic.layout(env, &shapes, partition.mid_lo()) {
                out.push((ic, placed));
            }
        }
    }
    out
}

/// Build the RL-INIT configuration of `placed`.
pub fn init_config(
    interp: &Interp<'_>,
    env: &EnvSpec,
    placed: &[Placed],
) -> Result<Config, DeriveError> {
    let core = interp.core;
    let threads = u32::try_from(core.prog.roots.iter().filter(|r| !r.dormant).count()).unwrap_or(1);
    let (mut host, classes) =
        InitConfig::host(placed, &env.limits, threads).map_err(DeriveError::Env)?;
    for (path, kind) in &env.names {
        host.add_name(path, *kind).map_err(|e| DeriveError::Env(format!("{e:?}")))?;
    }
    let classes = classes
        .into_iter()
        .map(|(o, name)| {
            core.class_idx(&name)
                .map(|k| (o, k))
                .ok_or_else(|| DeriveError::Env(format!("class {name} not interned")))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let params: Vec<(usize, i64)> =
        placed.iter().filter_map(|p| p.param.map(|i| (core.prog.fd_params[i].var, p.fd))).collect();
    Ok(interp.initial(host, classes, &params)?)
}

/// Derive the model of `prog` under `env`.
pub fn derive(
    prog: &EventProgram,
    env: &EnvSpec,
    opts: &DeriveOptions,
) -> Result<Derived, DeriveError> {
    let mut core = lower::lower(prog).map_err(DeriveError::Lower)?;
    for name in env.class_names() {
        core.intern_class(name);
    }
    let (consts, offsets) = collect_constants(&core, env);
    let partition = Partition::new(consts, offsets);
    let interp = Interp { core: &core, root: Pid(1), fd_bound_cap: env.fd_bound_cap };
    let tables = rl_init_tables(&core, env, &partition);
    let mut inits = Vec::new();
    let mut init_cfgs = Vec::new();
    let mut init_descs = Vec::new();
    for (ic, placed) in tables {
        init_cfgs.push(init_config(&interp, env, &placed)?);
        init_descs.push(ic.describe(&placed, &env.limits));
        inits.push(ic);
    }
    let graph = interp.explore(init_cfgs, opts.budget).map_err(DeriveError::Explore)?;
    // Transport labels are short ids (the obligation-metadata value is capped
    // at 1 MiB); the event map gives each id its actor, events and sources.
    let action_labels: Vec<String> = (0..graph.actions.len()).map(|a| format!("a{a}")).collect();
    let schema = schema_of(&interp, &graph.configs);
    let mut quotient: HashMap<Vec<i64>, usize> = HashMap::new();
    let mut vectors = Vec::new();
    let mut reps = Vec::new();
    let mut abs_of = Vec::with_capacity(graph.configs.len());
    for (i, c) in graph.configs.iter().enumerate() {
        let v = encode(&interp, &schema, c).ok_or_else(|| {
            DeriveError::Env(format!("explored state {i} has no scalar encoding"))
        })?;
        let k = match quotient.get(&v) {
            Some(&k) => k,
            None => {
                let k = vectors.len();
                quotient.insert(v.clone(), k);
                vectors.push(v);
                reps.push(i);
                k
            }
        };
        abs_of.push(k);
    }
    let encoding_exact = vectors.len() == graph.configs.len();

    // The machine: state 0 is the RL-INIT choice point.
    let mut states = vec![INIT_STATE.to_string()];
    let mut label_sets: Vec<BTreeSet<String>> = vec![BTreeSet::new(); vectors.len()];
    for (i, c) in graph.configs.iter().enumerate() {
        label_sets[abs_of[i]].extend(property::labels(&core, c));
    }
    let mut state_texts = vec![INIT_STATE.to_string()];
    for (k, rep) in reps.iter().enumerate() {
        states.push(format!("s{}", k + 1));
        state_texts.push(render(&interp, &graph.configs[*rep]));
    }
    let mut transitions: BTreeSet<(usize, String, usize)> = BTreeSet::new();
    for (k, cfg_idx) in &graph.inits {
        transitions.insert((0, action_labels[*k].clone(), 1 + abs_of[*cfg_idx]));
    }
    let mut has_out = vec![false; vectors.len()];
    for (from, a, to) in &graph.edges {
        let (f, t) = (abs_of[*from], abs_of[*to]);
        has_out[f] = true;
        transitions.insert((1 + f, action_labels[*a].clone(), 1 + t));
    }
    for (k, out) in has_out.iter().enumerate() {
        if !out {
            transitions.insert((1 + k, HALT.to_string(), 1 + k));
        }
    }
    let full_transitions: Vec<(usize, String, usize)> = transitions.into_iter().collect();
    let mut full_labels: Vec<BTreeSet<String>> = vec![BTreeSet::new()];
    full_labels.extend(label_sets);
    let (block_of, nblocks) = bisimulation(states.len(), &full_transitions, &full_labels);
    let mut q_transitions: BTreeMap<(usize, usize), String> = BTreeMap::new();
    for (f, l, t) in &full_transitions {
        q_transitions
            .entry((block_of[*f], block_of[*t]))
            .and_modify(|cur| {
                if l < cur {
                    cur.clone_from(l);
                }
            })
            .or_insert_with(|| l.clone());
    }
    let mut labels: FxHashMap<usize, Vec<String>> = FxHashMap::default();
    for (s, set) in full_labels.iter().enumerate() {
        if !set.is_empty() {
            labels.entry(block_of[s]).or_insert_with(|| set.iter().cloned().collect());
        }
    }
    let machine = StateMachineMetadata {
        states: (0..nblocks)
            .map(|b| if b == 0 { INIT_STATE.to_string() } else { format!("q{b}") })
            .collect(),
        init_states: vec![0],
        transitions: q_transitions.into_iter().map(|((f, t), l)| (f, l, t)).collect(),
        labels,
    };
    let _ = states;

    let mut event_map = BTreeMap::new();
    for (a, key) in graph.actions.iter().enumerate() {
        let label = action_labels[a].clone();
        let info = match key {
            ActionKey::Init(k) => ActionInfo {
                label: label.clone(),
                text: action_label(&interp, key),
                actor: "environment".to_string(),
                events: vec![EventSite {
                    at: "-".to_string(),
                    symbol: "RL-INIT".to_string(),
                    loc: init_descs.get(*k).cloned().unwrap_or_default(),
                    std_row: None,
                    oracle: "-".to_string(),
                }],
            },
            ActionKey::Event { role, at, oracle, missed, resume } => {
                let mut site = event_site(&core, *at, *oracle);
                if !missed.is_empty() {
                    site.oracle.push_str(&format!("; torn table copy missed fds {missed:?}"));
                }
                if *resume {
                    site.oracle.push_str("; continues a call that had not returned");
                }
                ActionInfo {
                    label: label.clone(),
                    text: action_label(&interp, key),
                    actor: interp.role_name(*role),
                    events: vec![site],
                }
            }
            ActionKey::Child { role, path } => ActionInfo {
                label: label.clone(),
                text: action_label(&interp, key),
                actor: interp.role_name(*role),
                events: path.iter().map(|(at, o)| event_site(&core, *at, *o)).collect(),
            },
            ActionKey::ForeignSquat { fd } => ActionInfo {
                label: label.clone(),
                text: action_label(&interp, key),
                actor: "environment (RL-FOREIGN)".to_string(),
                events: vec![EventSite {
                    at: "-".to_string(),
                    symbol: "dup2 / F_DUPFD (RL-FOREIGN)".to_string(),
                    loc: format!(
                        "foreign code makes a descriptor of its own at {fd}, a number an actor \
                         retired"
                    ),
                    std_row: None,
                    oracle: "-".to_string(),
                }],
            },
            ActionKey::ImageExit { site, nth } => ActionInfo {
                label: label.clone(),
                text: action_label(&interp, key),
                actor: interp.role_name(Role::Child { site: *site, nth: *nth }),
                events: vec![EventSite {
                    at: "-".to_string(),
                    symbol: "_exit (RL-IMAGE-EXIT)".to_string(),
                    loc: format!(
                        "the image child[{}] exec'd exits; its code is not modeled",
                        core.prog.sites.get(*site).map_or("?", |s| s.name.as_str())
                    ),
                    std_row: None,
                    oracle: "-".to_string(),
                }],
            },
            ActionKey::Nondet { role, at, then } => ActionInfo {
                label: label.clone(),
                text: action_label(&interp, key),
                actor: interp.role_name(*role),
                events: vec![EventSite {
                    at: at.to_string(),
                    symbol: "undecided guard (Cond::Nondet)".to_string(),
                    loc: core.prog.loc_at(*at).map(|l| l.0.clone()).unwrap_or_default(),
                    std_row: None,
                    oracle: format!(
                        "takes the {} (an over-approximating choice)",
                        crate::nondet::arm(*then)
                    ),
                }],
            },
        };
        event_map.insert(label, info);
    }
    event_map.insert(
        HALT.to_string(),
        ActionInfo {
            label: HALT.to_string(),
            text: HALT.to_string(),
            actor: "-".to_string(),
            events: vec![EventSite {
                at: "-".to_string(),
                symbol: "stutter".to_string(),
                loc: "every actor finished, the fd-inherit horizon (no policy child running and \
                      none to come), or STUCK: some actor waits and nothing can move (counted in \
                      the notes)"
                    .to_string(),
                std_row: None,
                oracle: "-".to_string(),
            }],
        },
    );

    let mut stats = Stats {
        init_tables: inits.len(),
        concrete_states: graph.configs.len(),
        abstract_states: vectors.len(),
        full_states: full_labels.len(),
        machine_states: machine.states.len(),
        machine_transitions: machine.transitions.len(),
        actions: graph.actions.len(),
        horizon_states: graph.horizon_states,
        stuck_states: graph.stuck.len(),
        encoding_exact,
        payload_bytes: 0,
    };
    let mut notes = notes(&core, env, &partition, opts, &stats);
    if let Some(first) = graph.stuck.first() {
        let waiting: Vec<String> = graph.configs[*first]
            .actors
            .iter()
            .filter(|a| !a.done())
            .map(|a| format!("{}@{}", interp.role_name(a.role), pc_string(a)))
            .collect();
        notes.push(format!(
            "STUCK: {} explored states have an unfinished actor and nothing enabled (first: \
             {waiting:?} wait) — a deadlock of the program or of the model; the states after \
             it are not explored",
            graph.stuck.len()
        ));
    }
    let vocabulary = property::vocabulary(&core);
    let mut d = Derived {
        name: prog.name.clone(),
        env: env.clone(),
        partition,
        inits,
        init_descs,
        schema,
        abs_of,
        reps,
        vectors,
        machine,
        full_transitions,
        block_of,
        state_texts,
        event_map,
        action_labels,
        vocabulary,
        notes,
        stats,
        graph,
        core,
    };
    stats.payload_bytes = d
        .payload(&property::fd_inherit_formula(&[]))
        .ok()
        .and_then(|p| p.to_metadata_value().ok())
        .map_or(usize::MAX, |v| v.len());
    d.stats = stats;
    if d.stats.payload_bytes > MAX_PAYLOAD_BYTES {
        return Err(DeriveError::TooLarge { bytes: d.stats.payload_bytes });
    }
    Ok(d)
}

/// The coarsest strong bisimulation of a labelled transition system (action
/// names ignored: CTL does not see them), by partition refinement from the
/// label partition. State 0 (`rl_init`, the one initial state) keeps a block
/// of its own, which is block 0. Returns (state -> block, block count).
fn bisimulation(
    n: usize,
    transitions: &[(usize, String, usize)],
    labels: &[BTreeSet<String>],
) -> (Vec<usize>, usize) {
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (f, _, t) in transitions {
        succ[*f].push(*t);
    }
    for v in &mut succ {
        v.sort_unstable();
        v.dedup();
    }
    // Initial partition: state 0 alone, then by label set.
    let mut block = vec![0usize; n];
    let mut ids: HashMap<&BTreeSet<String>, usize> = HashMap::new();
    for s in 1..n {
        let next = ids.len() + 1;
        block[s] = *ids.entry(&labels[s]).or_insert(next);
    }
    let mut count = ids.len() + 1;
    let mut sigs: HashMap<(usize, Vec<usize>), usize> = HashMap::new();
    let mut next = vec![0usize; n];
    loop {
        sigs.clear();
        // Number blocks in state order so state 0's block stays 0.
        for s in 0..n {
            let mut out: Vec<usize> = succ[s].iter().map(|t| block[*t]).collect();
            out.sort_unstable();
            out.dedup();
            let k = sigs.len();
            next[s] = *sigs.entry((block[s], out)).or_insert(k);
        }
        let new_count = sigs.len();
        std::mem::swap(&mut block, &mut next);
        if new_count == count {
            return (block, count);
        }
        count = new_count;
    }
}

/// `trust_verifier_api::MAX_METADATA_VALUE_BYTES`: the largest metadata value
/// a `TrustObligation` may carry (the bundle validation drops the request
/// otherwise, and the engine never sees it).
pub const MAX_PAYLOAD_BYTES: usize = 1024 * 1024;

fn notes(
    core: &CoreProgram,
    env: &EnvSpec,
    partition: &Partition,
    opts: &DeriveOptions,
    stats: &Stats,
) -> Vec<String> {
    let mut n = vec![
        format!("platform: {PLATFORM_SPEC} (crates/trust-platform; every step is its `step`)"),
        "verdict grade: REFUTATION-ONLY payload — ty's 'no counterexample' is Unknown, never a \
         pass (SD-8); a refutation is replayed by re-execution"
            .to_string(),
        format!(
            "explored at the real constants; partition points {:?}, additive offsets {:?}, mid \
             interval from {}",
            partition.constants(),
            partition.offsets(),
            partition.mid_lo()
        ),
        if core.child_splits {
            "SD-3: a forked child runs as one macro step up to its next split point (below); a \
             descriptor loop over closed slots is run once per gap between interesting indices \
             (exact: a gap is skipped only after an iteration in it changed nothing)"
                .to_string()
        } else {
            "SD-3: a forked child runs from fork to execvp/_exit as one macro step; a descriptor \
             loop over closed slots is run once per gap between interesting indices (exact: a gap \
             is skipped only after an iteration in it changed nothing)"
                .to_string()
        },
        "fork/posix_spawn: atomic copy, plus every torn copy missing a slot another thread is \
         about to dup2 onto or move (measured, trust_platform::clauses::step_torn)"
            .to_string(),
        if core.prog.policies.lock_release || !core.prog.policies.fd_identity.is_empty() {
            "horizon: none — the P-LOCK-RELEASE / fd-identity atoms are not frozen anywhere, so \
             every reachable state is explored"
                .to_string()
        } else {
            "horizon: a state where no policy child is running and no actor can reach a policy \
             spawn again is terminal; formulas may name only the fd-inherit atoms, which are \
             frozen there"
                .to_string()
        },
        format!(
            "RL-INIT: {} initial tables (stdio open; descriptor arguments on {:?}; {}{}; at \
             most one foreign descriptor, unflagged, of unknown kind)",
            stats.init_tables,
            env.param_slots,
            if env.foreign {
                "one unflagged foreign descriptor at every partition position"
            } else if env.foreign_at.is_empty() {
                "no foreign descriptor"
            } else {
                "no foreign descriptor at the partition positions"
            },
            if env.foreign_at.is_empty() {
                String::new()
            } else {
                format!("; one at each measured position {:?}", env.foreign_at)
            }
        ),
        if core.prog.policies.fd_identity.is_empty() {
            "RL-FOREIGN: represented by the RL-INIT foreign descriptor and the program's thread \
             roots; no create-anywhere generator yet"
                .to_string()
        } else {
            "RL-FOREIGN: the RL-INIT foreign descriptor, the program's thread roots, and a squat \
             generator (below)"
                .to_string()
        },
        "oracles: every event explores exactly the failures its census lists (execvp and \
         posix_spawn their exec failures); std row steps are nominal only"
            .to_string(),
        format!(
            "scalar encoding exact on the explored states: {} ({} explored, {} encoded)",
            stats.encoding_exact, stats.concrete_states, stats.abstract_states
        ),
        format!("state budget: {}", opts.budget),
    ];
    if core.extended {
        n.push(
            "M2: locks live on the description (Trust.Platform/darwin flock); the namespace \
             is flat — one canonical absolute spelling per file, every other spelling refused by \
             name; an exec'd image's code is not modeled and it may exit at any time \
             (RL-IMAGE-EXIT)"
                .to_string(),
        );
        n.push(
            "M2 review: a posix_spawn is two events — the child's copy of the whole table \
             (close-on-exec entries included) is held while other threads act, then its file \
             actions and image (or its failure); an open that waits (a FIFO peer, a lock) \
             reserves its number and a waiting FIFO opener counts as a reader/writer; a sleeping \
             flock holds its number (close/dup2 of it wait); each is continued by a later \
             action of its actor"
                .to_string(),
        );
        if !env.names.is_empty() {
            n.push(format!("RL-INIT namespace: {:?}", env.names));
        }
    }
    if core.extended {
        let roots: Vec<String> = core
            .prog
            .roots
            .iter()
            .map(|r| {
                if r.dormant {
                    format!("{} (started by std::thread::spawn)", r.name)
                } else {
                    r.name.clone()
                }
            })
            .collect();
        n.push(format!("thread roots of the process: {roots:?}"));
    }
    if core.child_splits {
        n.push(
            "SD-3 split points: a forked child interleaves at every event that can change what \
             another process sees (a dropped reference to a lockable or locked description, the \
             last reference to a pipe/socket end, flock, I/O, the namespace, exec, _exit)"
                .to_string(),
        );
    }
    let pol = &core.prog.policies;
    if pol.lock_release {
        n.push(
            "P-LOCK-RELEASE: a release mark lets go of every live description of its classes \
             (the owner's exit, of every live description); from then on none may hold a lock \
             the owner took where someone can see it (a name reaches its node, or another \
             description or pending open is on it), unless it was handed off (no copy in the \
             owner, every other copy at a number declared for its holder)"
                .to_string(),
        );
    }
    if !pol.fd_identity.is_empty() {
        let roots: Vec<&str> = pol
            .fd_identity
            .iter()
            .filter_map(|t| core.prog.roots.get(*t).map(|r| r.name.as_str()))
            .collect();
        n.push(format!(
            "fd-identity over {roots:?} and the children they fork: every event on a descriptor \
             number must reach the description the actor bound there (or none, after its own \
             close); fstat is exempt (its answer is the identity); every actor keeps bindings — \
             a thread starts with its creator's, a forked child with its parent's, a join takes \
             the joined thread's writes (happens-before)"
        ));
        n.push(
            "RL-FOREIGN (fd-identity): foreign code may make a descriptor of its own at any \
             number an actor of the root retired, at any interleaving point (dup2 onto it, or \
             F_DUPFD with that floor) — lowest-free over the modeled table is not all the reuse \
             there is"
                .to_string(),
        );
    }
    if let Some(cap) = env.fd_bound_cap {
        n.push(format!(
            "premise fd-bound (cap {cap}) is evaluated per policy child at its table copy; the \
             `*_under_fd_bound` atoms condition the formula and remove no state"
        ));
    }
    n.extend(core.assumptions.iter().map(|a| format!("assumption: {a}")));
    // X1 (Critique C-1, C-23: every approximation is printed).
    let guards = core.prog.nondet_guards();
    if !guards.is_empty() {
        let at: Vec<&str> = guards.iter().map(|l| l.0.as_str()).collect();
        n.push(format!(
            "over-approximation: {} undecided guard(s) (Cond::Nondet) explored both ways, at {}; \
             a refutation whose replay takes one is not an error (C-9)",
            guards.len(),
            at.join(", ")
        ));
    }
    let untracked = crate::track::untracked(&core.prog);
    if !untracked.vars.is_empty() {
        n.push(format!(
            "untracked values (Expr::Opaque): {} variable(s), checked to reach no event operand, \
             guard or loop bound, so the value the model gives them decides nothing",
            untracked.vars.len()
        ));
    }
    n.extend(core.prog.disclosures.iter().map(|a| format!("hand census: {a}")));
    n.push(format!(
        "census: {} platform names joined with trust_platform::symbols",
        core.census.len()
    ));
    n
}

fn oracle_suffix(o: Oracle) -> String {
    match o {
        Oracle::Nominal => String::new(),
        Oracle::Fail(e) => format!("!{e}"),
    }
}

fn action_label(interp: &Interp<'_>, a: &ActionKey) -> String {
    match a {
        ActionKey::Init(k) => format!("init_{k}"),
        ActionKey::Event { role, at, oracle, missed, resume } => {
            let torn = if missed.is_empty() { String::new() } else { format!("~torn{missed:?}") };
            let cont = if *resume { "~resume" } else { "" };
            format!("{}:{at}{}{torn}{cont}", interp.role_name(*role), oracle_suffix(*oracle))
        }
        ActionKey::ForeignSquat { fd } => format!("rl-foreign:squat@{fd}"),
        ActionKey::Child { role, path } => {
            let p: Vec<String> =
                path.iter().map(|(at, o)| format!("{at}{}", oracle_suffix(*o))).collect();
            format!("{}:{}", interp.role_name(*role), p.join(">"))
        }
        ActionKey::ImageExit { site, nth } => {
            format!("{}:image-exit", interp.role_name(Role::Child { site: *site, nth: *nth }))
        }
        ActionKey::Nondet { role, at, then } => {
            format!("{}:{at}?{}", interp.role_name(*role), if *then { "then" } else { "else" })
        }
    }
}

fn event_site(core: &CoreProgram, at: StmtRef, oracle: Oracle) -> EventSite {
    let s = core.prog.stmt(at);
    let (symbol, std_row) = match s.map(|s| &s.kind) {
        Some(StmtKind::Event(ev)) => (
            ev.symbol.clone(),
            ev.std_origin.as_ref().map(|o| format!("{} step {} ({})", o.row, o.step, o.source)),
        ),
        Some(StmtKind::Fork { std_origin, .. }) => (
            "fork".to_string(),
            std_origin.as_ref().map(|o| format!("{} step {} ({})", o.row, o.step, o.source)),
        ),
        Some(StmtKind::ForRange { .. }) => {
            ("for-range (descriptor loop, SD-3 one step)".to_string(), None)
        }
        Some(StmtKind::SpawnThread { .. }) => ("std::thread::spawn".to_string(), None),
        Some(StmtKind::Join { .. }) => ("JoinHandle::join".to_string(), None),
        _ => ("?".to_string(), None),
    };
    EventSite {
        at: at.to_string(),
        symbol,
        loc: s.map(|s| s.loc.0.clone()).unwrap_or_default(),
        std_row,
        oracle: match oracle {
            Oracle::Nominal => "nominal".to_string(),
            Oracle::Fail(e) => format!("fails {e}"),
        },
    }
}

fn pc_string(a: &crate::interp::Actor) -> String {
    use std::fmt::Write as _;
    if a.done() {
        return "done".to_string();
    }
    let mut out = String::with_capacity(a.frames.len() * 8);
    for (i, f) in a.frames.iter().enumerate() {
        if i > 0 {
            out.push('>');
        }
        let _ = write!(out, "b{}.{}.{}", f.body, f.block, f.idx);
    }
    out
}

fn proc_slot_of(cfg: &Config, root: Pid, pid: Pid) -> Option<ProcSlot> {
    if pid == root {
        return Some(ProcSlot::Root);
    }
    cfg.record(pid).map(|r| ProcSlot::Spawned { site: r.site, nth: r.nth })
}

fn schema_of(interp: &Interp<'_>, configs: &[Config]) -> ScalarSchema {
    let mut roles: BTreeSet<Role> = BTreeSet::new();
    let mut pcs: BTreeSet<String> = BTreeSet::new();
    let mut procs: BTreeSet<ProcSlot> = BTreeSet::new();
    let mut fds: BTreeSet<i32> = BTreeSet::new();
    let mut declared: BTreeSet<i32> = BTreeSet::new();
    let mut paths: BTreeSet<String> = BTreeSet::new();
    let mut bind_fds: BTreeSet<i32> = BTreeSet::new();
    let mut inflights: BTreeSet<String> = BTreeSet::new();
    let mut violations: BTreeSet<String> = BTreeSet::new();
    let extended = interp.core.extended;
    for c in configs {
        for a in &c.actors {
            roles.insert(a.role);
            pcs.insert(pc_string(a));
            bind_fds.extend(a.bindings.keys().copied());
            bind_fds.extend(a.wrote.iter().copied());
        }
        paths.extend(c.host.names().map(|(p, _)| p.to_string()));
        for (pid, p) in c.host.procs() {
            if let Some(s) = proc_slot_of(c, interp.root, pid) {
                procs.insert(s);
            }
            fds.extend(p.table.keys().copied());
            fds.extend(p.inflight.keys().copied());
            inflights.extend(p.inflight.values().map(|f| format!("{f:?}")));
        }
        if let Some(v) = &c.identity_violation {
            violations.insert(format!("{v:?}"));
        }
        for r in &c.spawns {
            declared.extend(r.declared.iter().copied());
        }
    }
    pcs.insert("absent".to_string());
    let roles: Vec<Role> = roles.into_iter().collect();
    let pcs: Vec<String> = pcs.into_iter().collect();
    let procs: Vec<ProcSlot> = procs.into_iter().collect();
    let fds: Vec<i32> = fds.into_iter().collect();
    let mut names = Vec::new();
    let mut kinds = Vec::new();
    let classes: Vec<String> =
        std::iter::once("none".to_string()).chain(interp.core.classes.iter().cloned()).collect();
    let path_names: Vec<String> = paths.into_iter().collect();
    let bind_fds: Vec<i32> = bind_fds.into_iter().collect();
    for r in &roles {
        let rn = interp.role_name(*r);
        names.push(format!("pc[{rn}]"));
        kinds.push(ScalarKind::Enum(pcs.clone()));
        for v in &interp.core.prog.vars {
            names.push(format!("var[{rn}].{}", v.name));
            kinds.push(ScalarKind::Int);
        }
        if extended {
            names.push(format!("checked[{rn}]"));
            kinds.push(ScalarKind::Bool);
            names.push(format!("pending[{rn}]"));
            kinds.push(ScalarKind::Int);
            for fd in &bind_fds {
                names.push(format!("binding[{rn}][{fd}]"));
                kinds.push(ScalarKind::Int);
                names.push(format!("wrote[{rn}][{fd}]"));
                kinds.push(ScalarKind::Bool);
            }
        }
    }
    let phases: Vec<String> = ["absent", "run", "forked", "execd", "exited", "spawning"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    for p in &procs {
        let pn = proc_name(interp, *p);
        names.push(format!("phase[{pn}]"));
        kinds.push(ScalarKind::Enum(phases.clone()));
        // The process's RLIMIT_NOFILE: a program reads it (getrlimit) and
        // another thread may change it (setrlimit), so two states that differ
        // only in it are different states.
        names.push(format!("nofile_soft[{pn}]"));
        kinds.push(ScalarKind::Int);
        names.push(format!("nofile_hard[{pn}]"));
        kinds.push(ScalarKind::Int);
        if extended {
            names.push(format!("threads[{pn}]"));
            kinds.push(ScalarKind::Int);
            // DR-1 reads the parent's thread count at the fork.
            names.push(format!("fork_threads[{pn}]"));
            kinds.push(ScalarKind::Int);
        }
        for fd in &fds {
            names.push(format!("open[{pn}][{fd}]"));
            kinds.push(ScalarKind::Bool);
            names.push(format!("cloexec[{pn}][{fd}]"));
            kinds.push(ScalarKind::Bool);
            names.push(format!("ofd[{pn}][{fd}]"));
            kinds.push(ScalarKind::Enum(classes.clone()));
            if extended {
                for col in [
                    "ofd_id",
                    "lock",
                    "node",
                    "getfl",
                    "peer",
                    "unread",
                    "released",
                    "owner_lock",
                    "inflight",
                ] {
                    names.push(format!("{col}[{pn}][{fd}]"));
                    kinds.push(ScalarKind::Int);
                }
            }
        }
        if *p != ProcSlot::Root {
            for cl in &interp.core.classes {
                names.push(format!("holds[{pn}][{cl}]"));
                kinds.push(ScalarKind::Bool);
            }
            names.push(format!("premise[{pn}]"));
            kinds.push(ScalarKind::Bool);
            for fd in &declared {
                names.push(format!("declared[{pn}][{fd}]"));
                kinds.push(ScalarKind::Bool);
            }
        }
    }
    if extended {
        for path in &path_names {
            names.push(format!("name[{path}]"));
            kinds.push(ScalarKind::Int);
            names.push(format!("name_kind[{path}]"));
            kinds.push(ScalarKind::Int);
        }
        names.push("next_node".to_string());
        kinds.push(ScalarKind::Int);
        names.push("identity_violation".to_string());
        kinds.push(ScalarKind::Int);
    }
    ScalarSchema {
        names,
        kinds,
        roles,
        pcs,
        procs,
        fds: declared_merge(fds, &declared),
        extended,
        paths: path_names,
        bind_fds,
        inflights: inflights.into_iter().collect(),
        violations: violations.into_iter().collect(),
    }
}

/// The encoding of an actor's pending call.
fn pending_code(p: Option<crate::interp::Pending>) -> i64 {
    match p {
        None => 0,
        Some(crate::interp::Pending::Resume { fd }) => 1 + i64::from(fd),
        Some(crate::interp::Pending::Spawn { child }) => -1 - i64::from(child.0),
    }
}

/// The encoding of a lock mode.
fn lock_code(l: Option<trust_platform::LockMode>) -> i64 {
    match l {
        None => 0,
        Some(trust_platform::LockMode::Shared) => 1,
        Some(trust_platform::LockMode::Exclusive) => 2,
    }
}

fn node_kind_code(k: Option<trust_platform::NodeKind>) -> i64 {
    use trust_platform::NodeKind;
    match k {
        None => 0,
        Some(NodeKind::Regular) => 1,
        Some(NodeKind::Directory) => 2,
        Some(NodeKind::CharDevice) => 3,
        Some(NodeKind::Fifo) => 4,
        Some(NodeKind::Symlink) => 5,
    }
}

fn binding_code(b: Option<&crate::interp::Binding>) -> i64 {
    use crate::interp::Binding;
    match b {
        None => 0,
        Some(Binding::Closed) => 1,
        Some(Binding::Gone) => 2,
        Some(Binding::Ofd(o)) => 3 + i64::from(o.0),
    }
}

/// The schema's descriptor columns, followed by the declared columns' numbers
/// (kept in one list so `encode` can find both).
fn declared_merge(fds: Vec<i32>, declared: &BTreeSet<i32>) -> Vec<i32> {
    let mut v = fds;
    v.push(i32::MIN);
    v.extend(declared.iter().copied());
    v
}

fn proc_name(interp: &Interp<'_>, p: ProcSlot) -> String {
    match p {
        ProcSlot::Root => "root".to_string(),
        ProcSlot::Spawned { site, nth } => interp.role_name(Role::Child { site, nth }),
    }
}

/// Encode `cfg`. `None`: the state is not expressible in `schema` (a state
/// the exploration did not produce).
pub fn encode(interp: &Interp<'_>, schema: &ScalarSchema, cfg: &Config) -> Option<Vec<i64>> {
    let mut v = Vec::with_capacity(schema.names.len());
    let absent =
        i64::try_from(schema.pcs.binary_search_by(|p| p.as_str().cmp("absent")).ok()?).ok()?;
    let split = schema.fds.iter().position(|f| *f == i32::MIN)?;
    let (fds, declared) = (&schema.fds[..split], &schema.fds[split + 1..]);
    for r in &schema.roles {
        let actor = cfg.actors.iter().find(|a| a.role == *r);
        match actor {
            Some(a) => {
                let pc = pc_string(a);
                v.push(i64::try_from(schema.pcs.binary_search(&pc).ok()?).ok()?);
                v.extend(a.vars.iter().copied());
            }
            None => {
                v.push(absent);
                v.extend(interp.core.prog.vars.iter().map(|_| 0));
            }
        }
        if schema.extended {
            v.push(i64::from(actor.is_some_and(|a| a.checked)));
            v.push(pending_code(actor.and_then(|a| a.pending)));
            if let Some(a) = actor
                && (a.bindings.keys().chain(a.wrote.iter()))
                    .any(|fd| schema.bind_fds.binary_search(fd).is_err())
            {
                return None;
            }
            for fd in &schema.bind_fds {
                v.push(binding_code(actor.and_then(|a| a.bindings.get(fd))));
                v.push(i64::from(actor.is_some_and(|a| a.wrote.contains(fd))));
            }
        }
    }
    for slot in &schema.procs {
        let pid = cfg
            .host
            .procs()
            .map(|(p, _)| p)
            .find(|p| proc_slot_of(cfg, interp.root, *p) == Some(*slot));
        let proc = pid.and_then(|p| cfg.host.proc(p));
        let phase = match proc.map(|p| p.phase) {
            None => 0,
            Some(Phase::Running) => 1,
            Some(Phase::ForkedPreExec { .. }) => 2,
            Some(Phase::Execd) => 3,
            Some(Phase::Exited { .. }) => 4,
            Some(Phase::Spawning { .. }) => 5,
        };
        v.push(phase);
        let as_i64 = |x: u64| i64::try_from(x).unwrap_or(i64::MAX);
        v.push(proc.map_or(0, |p| as_i64(p.nofile.soft)));
        v.push(proc.map_or(0, |p| as_i64(p.nofile.hard)));
        if schema.extended {
            v.push(proc.map_or(0, |p| i64::from(p.threads)));
            v.push(match proc.map(|p| p.phase) {
                Some(
                    Phase::ForkedPreExec { parent_threads } | Phase::Spawning { parent_threads },
                ) => i64::from(parent_threads),
                _ => 0,
            });
        }
        let mut holds = vec![0i64; interp.core.classes.len()];
        if let Some(p) = proc
            && p.table.keys().chain(p.inflight.keys()).any(|fd| fds.binary_search(fd).is_err())
        {
            return None;
        }
        let inflight_code = |fd: &i32| -> Option<i64> {
            match proc.and_then(|p| p.inflight.get(fd)) {
                None => Some(0),
                Some(f) => {
                    let k = schema.inflights.binary_search(&format!("{f:?}")).ok()?;
                    i64::try_from(k + 1).ok()
                }
            }
        };
        for fd in fds {
            match proc.and_then(|p| p.table.get(fd)) {
                Some(e) => {
                    let cls = cfg.classes.get(&e.ofd).copied();
                    v.extend([
                        1,
                        i64::from(e.cloexec),
                        cls.map_or(0, |k| i64::try_from(k + 1).unwrap_or(0)),
                    ]);
                    if let Some(k) = cls {
                        holds[k] = 1;
                    }
                    if schema.extended {
                        let o = cfg.host.ofd(e.ofd);
                        v.extend([
                            i64::from(e.ofd.0),
                            lock_code(o.and_then(|o| o.lock)),
                            o.and_then(|o| o.node).map_or(0, |n| i64::from(n.0)),
                            o.map_or(0, |o| i64::from(o.getfl())),
                            o.map_or(0, |o| match o.peer {
                                trust_platform::Peer::None => 0,
                                trust_platform::Peer::Open(_) => 1,
                                trust_platform::Peer::Closed => 2,
                            }),
                            i64::from(o.is_some_and(|o| o.unread)),
                            i64::from(cfg.released.contains(&e.ofd)),
                            i64::from(cfg.owner_locks.contains(&e.ofd)),
                            inflight_code(fd)?,
                        ]);
                    }
                }
                None => {
                    v.extend([0, 0, 0]);
                    if schema.extended {
                        v.extend([0, 0, 0, 0, 0, 0, 0, 0, inflight_code(fd)?]);
                    }
                }
            }
        }
        if *slot != ProcSlot::Root {
            v.extend(holds);
            let rec = pid.and_then(|p| cfg.record(p));
            v.push(i64::from(rec.is_some_and(|r| r.premise)));
            for fd in declared {
                v.push(i64::from(rec.is_some_and(|r| r.declared.contains(fd))));
            }
        }
    }
    if schema.extended {
        if cfg
            .host
            .names()
            .any(|(p, _)| schema.paths.binary_search_by(|x| x.as_str().cmp(p)).is_err())
        {
            return None;
        }
        for path in &schema.paths {
            let n = cfg.host.name(path);
            v.push(n.map_or(0, |n| i64::from(n.0)));
            v.push(node_kind_code(n.and_then(|n| cfg.host.node(n)).map(|n| n.kind)));
        }
        v.push(i64::from(cfg.host.next_node()));
        v.push(match &cfg.identity_violation {
            None => 0,
            Some(x) => {
                let text = format!("{x:?}");
                i64::try_from(schema.violations.binary_search(&text).ok()? + 1).ok()?
            }
        });
    }
    Some(v)
}

/// A stable one-line state name.
#[must_use]
pub fn render(interp: &Interp<'_>, c: &Config) -> String {
    use std::fmt::Write as _;
    let mut s = String::new();
    for a in &c.actors {
        let _ = write!(s, "{}@{} ", interp.role_name(a.role), pc_string(a));
    }
    s.push('|');
    for (pid, p) in c.host.procs() {
        let name = proc_slot_of(c, interp.root, pid)
            .map_or_else(|| format!("pid{}", pid.0), |slot| proc_name(interp, slot));
        let phase = match p.phase {
            Phase::Running => "run",
            Phase::ForkedPreExec { .. } => "forked",
            Phase::Spawning { .. } => "spawning",
            Phase::Execd => "execd",
            Phase::Exited { .. } => "exited",
        };
        let premise = match c.record(pid) {
            Some(r) if !r.premise => " (spawned outside fd-bound)",
            _ => "",
        };
        let _ = write!(s, " {name}:{phase}{premise}[");
        for (idx, (fd, e)) in p.table.iter().enumerate() {
            if idx > 0 {
                s.push(' ');
            }
            let cls = c
                .classes
                .get(&e.ofd)
                .and_then(|k| interp.core.classes.get(*k))
                .map_or("?", String::as_str);
            let _ = write!(s, "{fd}:{cls}{}", if e.cloexec { "^" } else { "" });
        }
        s.push(']');
    }
    s
}

impl Derived {
    /// The program's name.
    #[must_use]
    pub fn name(&self) -> &String {
        &self.name
    }

    /// The lowered program the derivation explored and every replay re-executes.
    #[must_use]
    pub fn core(&self) -> &CoreProgram {
        &self.core
    }

    /// The library environment.
    #[must_use]
    pub fn env(&self) -> &EnvSpec {
        &self.env
    }

    /// The partition of descriptor numbers RL-INIT places at.
    #[must_use]
    pub fn partition(&self) -> &Partition {
        &self.partition
    }

    /// The RL-INIT tables.
    #[must_use]
    pub fn inits(&self) -> &[InitConfig] {
        &self.inits
    }

    /// Each RL-INIT table, in words.
    #[must_use]
    pub fn init_descs(&self) -> &[String] {
        &self.init_descs
    }

    /// The explored graph.
    #[must_use]
    pub fn graph(&self) -> &Graph {
        &self.graph
    }

    /// The scalar encoding's schema.
    #[must_use]
    pub fn schema(&self) -> &ScalarSchema {
        &self.schema
    }

    /// Explored config -> abstract state (machine state = abstract + 1).
    #[must_use]
    pub fn abs_of(&self) -> &[usize] {
        &self.abs_of
    }

    /// Abstract state -> representative explored config.
    #[must_use]
    pub fn reps(&self) -> &[usize] {
        &self.reps
    }

    /// Abstract state -> its scalar vector.
    #[must_use]
    pub fn vectors(&self) -> &[Vec<i64>] {
        &self.vectors
    }

    /// The emitted machine: the bisimulation quotient of the full machine.
    #[must_use]
    pub fn machine(&self) -> &StateMachineMetadata {
        &self.machine
    }

    /// The full machine's transitions (state 0 is `rl_init`, state `k + 1` is abstract state `k`).
    #[must_use]
    pub fn full_transitions(&self) -> &[(usize, String, usize)] {
        &self.full_transitions
    }

    /// Full machine state -> emitted (quotient) machine state.
    #[must_use]
    pub fn block_of(&self) -> &[usize] {
        &self.block_of
    }

    /// Full machine state -> its full rendering.
    #[must_use]
    pub fn state_texts(&self) -> &[String] {
        &self.state_texts
    }

    /// Machine action label -> its source events.
    #[must_use]
    pub fn event_map(&self) -> &BTreeMap<String, ActionInfo> {
        &self.event_map
    }

    /// Graph action index -> machine label.
    #[must_use]
    pub fn action_labels(&self) -> &[String] {
        &self.action_labels
    }

    /// Every atom a formula over this machine may name.
    #[must_use]
    pub fn vocabulary(&self) -> &BTreeSet<String> {
        &self.vocabulary
    }

    /// The model's notes.
    #[must_use]
    pub fn notes(&self) -> &[String] {
        &self.notes
    }

    /// The derivation's statistics.
    #[must_use]
    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// The interpreter (real constants: exploration and replay alike).
    #[must_use]
    pub fn interp(&self) -> Interp<'_> {
        Interp { core: &self.core, root: Pid(1), fd_bound_cap: self.env.fd_bound_cap }
    }

    /// The REFUTATION-ONLY ty payload checking `property` over this machine
    /// (exactly what NativeTyEngine reads from obligation metadata). The
    /// formula is parsed with ty's CTL parser and every atom must be in the
    /// model's vocabulary ([`property::vocabulary`]): an unknown atom is
    /// false in every state, so a misspelling would otherwise check
    /// vacuously. The payload declares that vocabulary, and NativeTyEngine
    /// vets the formula against it again (it answers nothing for a payload
    /// without one).
    pub fn payload(&self, property: &str) -> Result<TyTemporalModelPayload, FormulaError> {
        property::check_formula(property, &self.vocabulary)?;
        let kind = VcKind::Temporal {
            property: property.to_string(),
            machine: Some(self.machine.clone()),
        };
        Ok(TyTemporalModelPayload::refutation_only(&kind)
            .ok_or_else(|| FormulaError::Parse("internal: non-temporal VcKind".to_string()))?
            .with_vocabulary(self.vocabulary.iter().cloned()))
    }

    /// The scalar valuation of machine state `m` (`None` for `rl_init`).
    #[must_use]
    pub fn scalars(&self, m: usize) -> Option<Vec<(String, i64)>> {
        let v = self.vectors.get(m.checked_sub(1)?)?;
        Some(self.schema.names.iter().cloned().zip(v.iter().copied()).collect())
    }
}
