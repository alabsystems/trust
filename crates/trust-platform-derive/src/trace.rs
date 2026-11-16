//! From a ty counterexample back to the program.
//!
//! * [`Derived::explain`] maps the machine-state sequence ty returns
//!   (NativeTyEngine's `Failed` trace: one machine state id per step) to the
//!   action labels between consecutive states and, through the event map, to
//!   every source event and location.
//! * [`Derived::replay`] re-executes that schedule from scratch — from the
//!   RL-INIT table it names, at the real constants, through the same
//!   interpreter and the same `trust_platform::step` (torn table copies
//!   included) — and checks after every step that the re-executed state IS
//!   the machine state ty named (a mismatch is a spurious counterexample and
//!   is reported, never admitted). The final state must carry the refuted
//!   proposition.
//!
//! * [`Derived::replay_token`] (X2) mints a [`ReplayToken`] from a replay
//!   only when it is a REFUTATION (it wants at least one violation
//!   proposition of the derivation and the final state is a concrete
//!   violation of that property), every step re-executed, every environment
//!   step cites its RL clause and every std-origin step cites its row. The
//!   token records the program and environment it was replayed on
//!   ([`ReplayToken::is_of`]). Its fields are private, so nothing outside
//!   this crate can build one without a replay, rebuild one from a genuine
//!   one, or take one apart:
//!
//! ```compile_fail,E0451
//! use trust_platform_derive::trace::ReplayToken;
//! let forged = ReplayToken {
//!     blocks: Vec::new(),
//!     steps: Vec::new(),
//!     replay: unimplemented!(),
//!     want: Vec::new(),
//!     program: unimplemented!(),
//!     env: unimplemented!(),
//! };
//! ```
//!
//! ```compile_fail,E0451
//! use trust_platform_derive::trace::ReplayToken;
//! fn forge(tok: ReplayToken) -> ReplayToken {
//!     ReplayToken { want: vec!["fd_inherit_violation".to_string()], ..tok }
//! }
//! ```
//!
//! ```compile_fail,E0451
//! use trust_platform_derive::trace::{Replay, ReplayToken};
//! fn swap(tok: ReplayToken, other: Replay) -> Replay {
//!     let ReplayToken { replay, .. } = tok;
//!     let _ = replay;
//!     other
//! }
//! ```
//!
//! What this is not: RF-L or RF-I (no Clean kernel evaluation, no literal
//! translation of the bodies), and no forcing test on the OS. Those are M1b
//! and the landing gate.

use std::collections::BTreeMap;

use trust_platform::{Call, Ret, SysResult, darwin};

use crate::derive::{ActionInfo, Derived, HALT, encode, init_config, rl_init_tables};
use crate::env::EnvSpec;
use crate::explore::ActionKey;
use crate::interp::{Config, Fired, Interp};
use crate::program::{EventProgram, Loc, StdOrigin, StmtKind, StmtRef};
use crate::property::{self, Refutes, Violation};

/// RL-INIT: the initial descriptor table the library environment hands the
/// program (stdio, descriptor arguments, a foreign descriptor).
pub const RL_INIT: &str = "RL-INIT";
/// RL-FOREIGN: foreign code makes a descriptor of its own at a number.
pub const RL_FOREIGN: &str = "RL-FOREIGN";
/// RL-IMAGE-EXIT: an exec'd image (whose code is not modeled) exits.
pub const RL_IMAGE_EXIT: &str = "RL-IMAGE-EXIT";
/// Every environment clause the derivation's generators implement: the
/// clauses an environment step of a replay may cite (X2 (b)).
pub const RL_CLAUSES: [&str; 3] = [RL_INIT, RL_FOREIGN, RL_IMAGE_EXIT];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraceError {
    /// Two consecutive states with no transition between them.
    NoTransition {
        from: usize,
        to: usize,
    },
    /// The trace does not start with an RL-INIT choice.
    BadStart,
    /// The re-execution could not take the action the trace names.
    Diverged {
        step: usize,
        detail: String,
    },
    /// The re-executed state differs from the machine state ty named.
    Spurious {
        step: usize,
        detail: String,
    },
    /// The final state lacks the refuted proposition.
    NotReproduced {
        missing: String,
        labels: Vec<String>,
    },
    Derive(String),
}

impl std::fmt::Display for TraceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

/// One step of an explained trace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceStep {
    pub from: usize,
    pub to: usize,
    pub info: ActionInfo,
    /// The machine state reached (its name).
    pub state: String,
}

/// One step of the replay.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReplayStep {
    pub label: String,
    pub actor: String,
    /// The concrete events, at the real constants.
    pub events: Vec<String>,
    /// Where each event fired, typed: `sites[k]` is `events[k]`'s (L1c).
    pub sites: Vec<FiredSite>,
}

/// Where one event of a replay step fired (L1c): the typed twin of an
/// event line, which a host maps to a source span (`loc` through the
/// census's `RootProgram::locs`) or prints as an environment note.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiredSite {
    /// The program position that fired: a statement, or a block's
    /// terminator (an undecided guard's choice). `None` for an environment
    /// step.
    pub at: Option<StmtRef>,
    /// The program's Loc of `at`. An environment step has no source
    /// location by design: `<environment RL-…>`.
    pub loc: Loc,
    /// An environment step (RL-INIT's table, an RL-FOREIGN squat, an
    /// RL-IMAGE-EXIT), not code of the program.
    pub environment: bool,
    /// The RL clause an environment step re-executes (one of
    /// [`RL_CLAUSES`]).
    pub rl_clause: Option<&'static str>,
    /// The std summary row a std-origin step is a step of
    /// ([`StdOrigin::row`]).
    pub std_row: Option<&'static str>,
}

impl FiredSite {
    /// An environment step justified by `clause` (`None`: by nothing, which
    /// [`Derived::replay_token`] refuses).
    fn environment(clause: Option<&'static str>) -> FiredSite {
        FiredSite {
            at: None,
            loc: Loc(format!("<environment {}>", clause.unwrap_or("(no RL clause)"))),
            environment: true,
            rl_clause: clause,
            std_row: None,
        }
    }
}

/// The std summary row step a program position was expanded from.
fn std_origin(prog: &EventProgram, at: StmtRef) -> Option<&StdOrigin> {
    match prog.stmt(at).map(|s| &s.kind) {
        Some(StmtKind::Event(ev)) => ev.std_origin.as_ref(),
        Some(StmtKind::Fork { std_origin, .. }) => std_origin.as_ref(),
        _ => None,
    }
}

/// The typed site of a fired event. A position the program does not have
/// is an environment step; `clause` is the RL clause of the action that
/// fired it, if that action is an environment generator.
fn fired_site(interp: &Interp<'_>, f: &Fired, clause: Option<&'static str>) -> FiredSite {
    let prog = &interp.core.prog;
    match prog.loc_at(f.at) {
        Some(loc) => FiredSite {
            at: Some(f.at),
            loc: loc.clone(),
            environment: false,
            rl_clause: None,
            std_row: std_origin(prog, f.at).map(|o| o.row),
        },
        None => FiredSite::environment(clause),
    }
}

/// Why [`Derived::replay_token`] minted no token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenError {
    /// The trace did not explain or replay.
    Replay(TraceError),
    /// X2 (a): a step of the trace was not re-executed.
    NotReexecuted { step: usize, detail: String },
    /// X2 (b): an environment step cites no RL clause the derivation
    /// implements.
    UncitedEnvironment { step: usize, detail: String },
    /// X2 (c): a std-origin step does not cite its row.
    UncitedStdRow { step: usize, detail: String },
    /// The replay refutes nothing (red-team H3): it wants no violation
    /// proposition of the derivation, or its final state is not a concrete
    /// violation of the property the proposition names.
    NotARefutation { detail: String },
}

impl std::fmt::Display for TokenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

/// X2: a replayed refutation. Its fields are private and it is minted only
/// by [`Derived::replay_token`], so holding one means the trace re-executed
/// at the real constants and ends in a concrete violation of the property
/// its wanted propositions name, every environment step cites its RL clause
/// and every std-origin step cites its row. A refutation diagnostic takes
/// one by value: no error can be built without a replay, and it checks
/// [`ReplayToken::is_of`] against the site's derivation, so a token of
/// another program or environment is not that site's.
#[derive(Debug)]
pub struct ReplayToken {
    blocks: Vec<usize>,
    steps: Vec<TraceStep>,
    replay: Replay,
    want: Vec<String>,
    /// The program the trace was replayed on (the derivation's).
    program: EventProgram,
    /// The library environment it was replayed in.
    env: EnvSpec,
}

impl ReplayToken {
    /// The ty trace (emitted-machine state ids) this token replayed.
    #[must_use]
    pub fn blocks(&self) -> &[usize] {
        &self.blocks
    }

    /// The trace explained: the action between each pair of states.
    #[must_use]
    pub fn steps(&self) -> &[TraceStep] {
        &self.steps
    }

    /// The replay: one step per explained step, events and their sites.
    #[must_use]
    pub fn replay(&self) -> &Replay {
        &self.replay
    }

    /// The propositions the final state carries (the refuted ones): never
    /// empty, each a violation proposition ([`property::refutes`]).
    #[must_use]
    pub fn want(&self) -> &[String] {
        &self.want
    }

    /// Whether this token was replayed on `d`'s program in `d`'s
    /// environment: a refutation diagnostic for a site admits only a token
    /// of that site's derivation.
    #[must_use]
    pub fn is_of(&self, d: &Derived) -> bool {
        self.program == d.core.prog && self.env == d.env
    }

    /// The replay, giving up the token.
    #[must_use]
    pub fn into_replay(self) -> Replay {
        self.replay
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Replay {
    pub steps: Vec<ReplayStep>,
    /// The fd-inherit violations of the final state.
    pub violations: Vec<Violation>,
    /// The M2 findings of the final state (P-LOCK-RELEASE leaks, the
    /// fd-identity violation), in words.
    pub findings: Vec<String>,
    pub final_labels: Vec<String>,
    /// Every over-approximating choice the trace takes (X1: an arm of an
    /// undecided guard, `Cond::Nondet`). Empty iff the refutation relies on
    /// none; otherwise it may follow a path the program cannot take, and it
    /// is not an error (Critique C-9: `PC-OVERAPPROX`, printed with these).
    /// The same holds for a refutation used as evidence of anything else: a
    /// non-vacuity witness (`AG !policy_exec` refuted) that lists a choice
    /// does not show that the PROGRAM reaches the exec (C-1).
    pub overapprox: Vec<crate::nondet::Overapprox>,
}

/// Render a concrete call the way the source spells it.
#[must_use]
pub fn show_call(call: &Call<i32>) -> String {
    let fcntl_cmd =
        |cmd: i32| darwin::fcntl_name(cmd).map_or_else(|| format!("cmd {cmd}"), str::to_string);
    match call {
        Call::Fcntl { fd, cmd, arg } => format!("fcntl({fd}, {}, {arg})", fcntl_cmd(*cmd)),
        Call::Dup2 { from, to } => format!("dup2({from}, {to})"),
        Call::Dup { fd } => format!("dup({fd})"),
        Call::Close { fd } => format!("close({fd})"),
        Call::Ioctl { fd, request, .. } => {
            let r = if *request == darwin::FIOCLEX {
                "FIOCLEX"
            } else if *request == darwin::FIONCLEX {
                "FIONCLEX"
            } else {
                "request"
            };
            format!("ioctl({fd}, {r})")
        }
        Call::Socketpair { .. } => "socketpair(AF_UNIX, SOCK_STREAM)".to_string(),
        Call::Pipe => "pipe()".to_string(),
        Call::Open { flags } => format!(
            "open(\"/dev/null\", {:#x}{})",
            flags & !darwin::O_CLOEXEC,
            if flags & darwin::O_CLOEXEC != 0 { " | O_CLOEXEC" } else { "" }
        ),
        Call::OpenAlias { fd, flags } => format!("open(\"/dev/fd/{fd}\", {flags:#x})"),
        Call::Fork => "fork()".to_string(),
        Call::Exec => "execvp()".to_string(),
        Call::Exit { status } => format!("_exit({status})"),
        Call::Getrlimit { .. } => "getrlimit(RLIMIT_NOFILE)".to_string(),
        Call::Setrlimit { soft, hard, .. } => {
            format!("setrlimit(RLIMIT_NOFILE, {{soft {soft}, hard {hard}}})")
        }
        Call::ReadSome { fd } => format!("read({fd}) (a few bytes)"),
        Call::WriteSome { fd } => format!("write({fd}) (a few bytes)"),
        Call::SocketOp { fd, .. } => format!("{}({fd})", call.symbol()),
        Call::Waitpid { pid, options } => format!("waitpid({pid}, {options:#x})"),
        Call::Spawn { actions, flags } => format!("posix_spawn({actions:?}, flags {flags:#x})"),
        Call::Flock { fd, op } => format!("flock({fd}, {})", flock_op(*op)),
        Call::OpenPath { at, path, flags } => {
            let f = open_flags(*flags);
            match at {
                None => format!("open({path:?}, {f})"),
                Some(d) => format!("openat({d}, {path:?}, {f})"),
            }
        }
        Call::Fstat { fd } => format!("fstat({fd})"),
        Call::Mkfifo { path } => format!("mkfifo({path:?})"),
        Call::Unlink { path } => format!("unlink({path:?})"),
        Call::Symlink { target, path } => format!("symlink({target:?}, {path:?})"),
        Call::ThreadCreate => "pthread_create()".to_string(),
        Call::SpawnBegin => "posix_spawn(): the child's copy of the table".to_string(),
        Call::SpawnEnd { child, actions, flags } => format!(
            "posix_spawn(): child {child}'s file actions {actions:?} and image, flags {flags:#x}"
        ),
        Call::Resume { fd } => format!("... the call holding {fd} continues"),
        other => format!("{other:?}"),
    }
}

fn flock_op(op: i32) -> String {
    let mut parts = Vec::new();
    for (bit, name) in [
        (darwin::LOCK_SH, "LOCK_SH"),
        (darwin::LOCK_EX, "LOCK_EX"),
        (darwin::LOCK_UN, "LOCK_UN"),
        (darwin::LOCK_NB, "LOCK_NB"),
    ] {
        if op & bit != 0 {
            parts.push(name);
        }
    }
    if parts.is_empty() { format!("{op}") } else { parts.join("|") }
}

fn open_flags(flags: i32) -> String {
    let mut parts = vec![match flags & darwin::O_ACCMODE {
        darwin::O_WRONLY => "O_WRONLY",
        darwin::O_RDWR => "O_RDWR",
        _ => "O_RDONLY",
    }];
    for (bit, name) in [
        (darwin::O_NONBLOCK, "O_NONBLOCK"),
        (darwin::O_CREAT, "O_CREAT"),
        (darwin::O_TRUNC, "O_TRUNC"),
        (darwin::O_EXCL, "O_EXCL"),
        (darwin::O_NOFOLLOW, "O_NOFOLLOW"),
        (darwin::O_DIRECTORY, "O_DIRECTORY"),
        (darwin::O_EXLOCK, "O_EXLOCK"),
        (darwin::O_SHLOCK, "O_SHLOCK"),
        (darwin::O_CLOEXEC, "O_CLOEXEC"),
    ] {
        if flags & bit != 0 {
            parts.push(name);
        }
    }
    parts.join("|")
}

fn show_result(r: &SysResult) -> String {
    match r {
        Ok(Ret::Int(n)) => format!(" = {n}"),
        Ok(Ret::Pair(a, b)) => format!(" = ({a}, {b})"),
        Ok(Ret::Rlimit { soft, hard }) => format!(" = {{soft {soft}, hard {hard}}}"),
        Ok(Ret::Stat { node, ftype }) => format!(" = {{node n{node}, type {ftype:#o}}}"),
        Ok(Ret::NoReturn) => " (does not return)".to_string(),
        Ok(Ret::Pending { fd }) => format!(" ... (has not returned: it waits holding {fd})"),
        Err(e) => format!(" = -1 {e}"),
    }
}

fn show_fired(interp: &Interp<'_>, f: &Fired) -> String {
    let stmt = interp.core.prog.stmt(f.at);
    let mut loc = interp.core.prog.loc_at(f.at).map(|l| l.0.clone()).unwrap_or_default();
    let origin = match stmt.map(|s| &s.kind) {
        Some(crate::program::StmtKind::Event(ev)) => ev.std_origin.as_ref(),
        Some(crate::program::StmtKind::Fork { std_origin, .. }) => std_origin.as_ref(),
        _ => None,
    };
    if let Some(o) = origin {
        loc.push_str(&format!(" via {} step {}", o.row, o.step));
    }
    let mut what = match (&f.call, &f.result) {
        (Some(c), Some(r)) => format!("{}{}", show_call(c), show_result(r)),
        _ => f.note.clone(),
    };
    // `show_call` knows the call, not the census row: name an `open`'s real
    // path and an exec's real symbol where the program recorded them.
    if let Some(crate::program::StmtKind::Event(ev)) = stmt.map(|s| &s.kind) {
        if let (Some(path), Some(Call::Open { .. })) = (&ev.path, &f.call) {
            what = what.replacen("\"/dev/null\"", &format!("\"{path}\""), 1);
        }
        if matches!(f.call, Some(Call::Exec)) {
            what = what.replacen("execvp()", &format!("{}()", ev.symbol), 1);
        }
    }
    if !f.missed.is_empty() {
        what.push_str(&format!(
            " [torn table copy: the child's copy missed fds {:?}, which another thread was \
             replacing]",
            f.missed
        ));
    }
    format!("{}: {what}   [{loc}]", interp.role_name(f.role))
}

impl Derived {
    fn transition_index(&self) -> BTreeMap<(usize, usize), Vec<&str>> {
        let mut m: BTreeMap<(usize, usize), Vec<&str>> = BTreeMap::new();
        for (f, l, t) in &self.full_transitions {
            m.entry((*f, *t)).or_default().push(l.as_str());
        }
        m
    }

    /// Lift a path of the emitted (quotient) machine to a path of the full
    /// machine from `rl_init`: each step of a bisimulation quotient has a
    /// matching step from every member of its source block.
    pub fn lift(&self, blocks: &[usize]) -> Result<Vec<usize>, TraceError> {
        let Some((&b0, rest)) = blocks.split_first() else { return Err(TraceError::BadStart) };
        if b0 != 0 || self.block_of.first() != Some(&0) {
            return Err(TraceError::BadStart);
        }
        let mut succ: Vec<Vec<usize>> = vec![Vec::new(); self.block_of.len()];
        for (f, _, t) in &self.full_transitions {
            succ[*f].push(*t);
        }
        let mut path = vec![0usize];
        for (k, b) in rest.iter().enumerate() {
            let cur = *path.last().unwrap_or(&0);
            let next = succ[cur]
                .iter()
                .copied()
                .find(|t| self.block_of.get(*t) == Some(b))
                .ok_or(TraceError::NoTransition { from: blocks[k], to: *b })?;
            path.push(next);
        }
        Ok(path)
    }

    /// The actions between consecutive states of a ty trace over the
    /// emitted machine (lifted to the full machine).
    pub fn explain(&self, blocks: &[usize]) -> Result<Vec<TraceStep>, TraceError> {
        let states = self.lift(blocks)?;
        let idx = self.transition_index();
        let mut out = Vec::new();
        for w in states.windows(2) {
            let (from, to) = (w[0], w[1]);
            let label = idx
                .get(&(from, to))
                .and_then(|ls| ls.iter().find(|l| **l != HALT).or_else(|| ls.first()))
                .ok_or(TraceError::NoTransition { from, to })?;
            let info =
                self.event_map.get(*label).cloned().ok_or(TraceError::NoTransition { from, to })?;
            out.push(TraceStep {
                from,
                to,
                info,
                state: self.state_texts.get(to).cloned().unwrap_or_default(),
            });
        }
        Ok(out)
    }

    /// Re-execute a ty trace; `want` are the propositions the final state
    /// must carry (e.g. `fd_inherit_violation`).
    pub fn replay(&self, states: &[usize], want: &[&str]) -> Result<Replay, TraceError> {
        self.replay_final(states, want).map(|(replay, _)| replay)
    }

    /// [`Derived::replay`], with the final configuration it re-executed to.
    fn replay_final(
        &self,
        states: &[usize],
        want: &[&str],
    ) -> Result<(Replay, Config), TraceError> {
        let steps = self.explain(states)?;
        let ri = self.interp();
        let tables = rl_init_tables(&self.core, &self.env, &self.partition);
        let mut cfg: Option<Config> = None;
        let mut out = Vec::new();
        let mut overapprox = Vec::new();
        for (j, st) in steps.iter().enumerate() {
            if st.info.label == HALT {
                // The horizon stutter: nothing happens.
                out.push(ReplayStep {
                    label: HALT.to_string(),
                    actor: "-".to_string(),
                    events: Vec::new(),
                    sites: Vec::new(),
                });
                continue;
            }
            let a = self
                .action_labels
                .iter()
                .position(|l| *l == st.info.label)
                .and_then(|i| self.graph.actions.get(i))
                .ok_or_else(|| TraceError::Diverged {
                    step: j,
                    detail: format!("label {} is not an action", st.info.label),
                })?;
            let mut events = Vec::new();
            let mut sites = Vec::new();
            let next = match (a, cfg.take()) {
                (ActionKey::Init(k), None) => {
                    let (ic, placed) = tables.get(*k).ok_or(TraceError::BadStart)?;
                    let c = init_config(&ri, &self.env, placed)
                        .map_err(|e| TraceError::Derive(e.to_string()))?;
                    events.push(ic.describe(placed, &self.env.limits));
                    sites.push(FiredSite::environment(Some(RL_INIT)));
                    c
                }
                (ActionKey::Event { role, at, oracle, missed, .. }, Some(c)) => {
                    let i = c.actors.iter().position(|x| x.role == *role).ok_or_else(|| {
                        TraceError::Diverged { step: j, detail: "actor missing".to_string() }
                    })?;
                    if c.actors[i].pc() != Some(*at) {
                        return Err(TraceError::Diverged {
                            step: j,
                            detail: format!("actor at {:?}, trace says {at}", c.actors[i].pc()),
                        });
                    }
                    let (c2, f) = ri
                        .fire(&c, i, *oracle, missed)
                        .map_err(|e| TraceError::Diverged { step: j, detail: e.to_string() })?
                        .ok_or_else(|| TraceError::Diverged {
                            step: j,
                            detail: "event not enabled".to_string(),
                        })?;
                    events.push(show_fired(&ri, &f));
                    sites.push(fired_site(&ri, &f, None));
                    ri.finish(c2)
                }
                (ActionKey::Child { role, path }, Some(c)) => {
                    let i = c.actors.iter().position(|x| x.role == *role).ok_or_else(|| {
                        TraceError::Diverged { step: j, detail: "child missing".to_string() }
                    })?;
                    let outcomes = ri
                        .run_child(&c, i)
                        .map_err(|e| TraceError::Diverged { step: j, detail: e.to_string() })?;
                    let (c2, log) = outcomes
                        .into_iter()
                        .find(|(_, log)| {
                            log.len() == path.len()
                                && log
                                    .iter()
                                    .zip(path)
                                    .all(|(f, (at, o))| f.at == *at && f.oracle == *o)
                        })
                        .ok_or_else(|| TraceError::Diverged {
                            step: j,
                            detail: "the child took another path".to_string(),
                        })?;
                    events.extend(log.iter().map(|f| show_fired(&ri, f)));
                    sites.extend(log.iter().map(|f| fired_site(&ri, f, None)));
                    ri.finish(c2)
                }
                (ActionKey::ForeignSquat { fd }, Some(c)) => {
                    if !ri.squat_targets(&c).contains(fd) {
                        return Err(TraceError::Diverged {
                            step: j,
                            detail: format!("RL-FOREIGN cannot squat on {fd} here"),
                        });
                    }
                    let c2 = ri
                        .squat(&c, *fd)
                        .map_err(|e| TraceError::Diverged { step: j, detail: e.to_string() })?;
                    events.push(format!(
                        "environment (RL-FOREIGN): foreign code makes a descriptor of its own at \
                         {fd} (dup2 onto it, or F_DUPFD with that floor)"
                    ));
                    sites.push(FiredSite::environment(Some(RL_FOREIGN)));
                    ri.finish(c2)
                }
                (ActionKey::ImageExit { site, nth }, Some(c)) => {
                    let outcomes = ri
                        .successors(&c)
                        .map_err(|e| TraceError::Diverged { step: j, detail: e.to_string() })?;
                    let (_, c2, log) = outcomes
                        .into_iter()
                        .find(|(k, _, _)| *k == ActionKey::ImageExit { site: *site, nth: *nth })
                        .ok_or_else(|| TraceError::Diverged {
                            step: j,
                            detail: "the image is not running".to_string(),
                        })?;
                    events.extend(log.iter().map(|f| show_fired(&ri, f)));
                    sites.extend(log.iter().map(|f| fired_site(&ri, f, Some(RL_IMAGE_EXIT))));
                    c2
                }
                (ActionKey::Nondet { role, at, then }, Some(c)) => {
                    let i = c.actors.iter().position(|x| x.role == *role).ok_or_else(|| {
                        TraceError::Diverged { step: j, detail: "actor missing".to_string() }
                    })?;
                    if c.actors[i].pc() != Some(*at) {
                        return Err(TraceError::Diverged {
                            step: j,
                            detail: format!("actor at {:?}, trace says {at}", c.actors[i].pc()),
                        });
                    }
                    let (c2, f) = ri
                        .choose(&c, i, *then)
                        .map_err(|e| TraceError::Diverged { step: j, detail: e.to_string() })?;
                    overapprox.push(crate::nondet::Overapprox {
                        step: j,
                        actor: ri.role_name(*role),
                        loc: self.core.prog.loc_at(*at).map(|l| l.0.clone()).unwrap_or_default(),
                        then: *then,
                    });
                    events.push(show_fired(&ri, &f));
                    sites.push(fired_site(&ri, &f, None));
                    ri.finish(c2)
                }
                _ => return Err(TraceError::BadStart),
            };
            // The re-executed state IS the machine state ty named.
            let got = encode(&ri, &self.schema, &next);
            let want_v = st.to.checked_sub(1).and_then(|k| self.vectors.get(k));
            match (got, want_v) {
                (Some(g), Some(w)) if g == *w => {}
                (Some(g), Some(w)) => {
                    let k = g.iter().zip(w).position(|(a, b)| a != b).unwrap_or(0);
                    return Err(TraceError::Spurious {
                        step: j,
                        detail: format!(
                            "{} is {} in the re-execution, {} in machine state {}",
                            self.schema.names.get(k).map_or("?", String::as_str),
                            g.get(k).copied().unwrap_or_default(),
                            w.get(k).copied().unwrap_or_default(),
                            st.to
                        ),
                    });
                }
                _ => {
                    return Err(TraceError::Spurious {
                        step: j,
                        detail: "the re-executed state has no encoding in the model".to_string(),
                    });
                }
            }
            out.push(ReplayStep {
                label: st.info.text.clone(),
                actor: st.info.actor.clone(),
                events,
                sites,
            });
            cfg = Some(next);
        }
        let last = cfg.ok_or(TraceError::BadStart)?;
        let final_labels = property::labels(&self.core, &last);
        for w in want {
            if !final_labels.iter().any(|l| l == w) {
                return Err(TraceError::NotReproduced {
                    missing: (*w).to_string(),
                    labels: final_labels,
                });
            }
        }
        let mut findings = Vec::new();
        if self.core.prog.policies.lock_release {
            let name_of = |p: trust_platform::Pid| {
                if p == ri.root {
                    return "the owner".to_string();
                }
                last.record(p).map_or_else(
                    || format!("pid {}", p.0),
                    |r| ri.role_name(crate::interp::Role::Child { site: r.site, nth: r.nth }),
                )
            };
            let (leaks, _) = property::lock_leaks(&self.core, &last, ri.root, &name_of);
            findings.extend(leaks.iter().map(ToString::to_string));
        }
        if let Some(v) = &last.identity_violation {
            let at = self.core.prog.stmt(v.at).map(|s| s.loc.0.clone()).unwrap_or_default();
            findings.push(format!(
                "{} acted on fd {} believing it named {}, but it named {} [{at}]",
                ri.role_name(v.role),
                v.fd,
                v.believed,
                v.found
            ));
        }
        let replay = Replay {
            steps: out,
            violations: property::violations(&self.core, &last),
            findings,
            final_labels,
            overapprox,
        };
        Ok((replay, last))
    }

    /// X2: replay a ty trace and mint a [`ReplayToken`] — only when the
    /// replay is a REFUTATION (`want` is not empty, each wanted proposition
    /// is a violation proposition of this derivation, [`property::refutes`],
    /// the final state carries it, and the final state is a concrete
    /// violation of that property: a fd-inherit violation of a policy
    /// child, a leaked lock, an fd-identity violation), and (a) every step
    /// of the explained trace re-executed (one replay step per explained
    /// step, each non-halt step's events re-executed with a typed site
    /// apiece, the program positions it names having the Locs it gives, a
    /// horizon stutter only where the machine stutters), (b) every
    /// environment step cites an RL clause the derivation implements
    /// ([`RL_CLAUSES`]), and (c) every std-origin step cites its row.
    pub fn replay_token(&self, blocks: &[usize], want: &[&str]) -> Result<ReplayToken, TokenError> {
        let refuted = self.refuted_by(want)?;
        let steps = self.explain(blocks).map_err(TokenError::Replay)?;
        let (replay, last) = self.replay_final(blocks, want).map_err(TokenError::Replay)?;
        self.check_x2(&steps, &replay)?;
        self.check_refutation(&refuted, &replay, &last)?;
        Ok(ReplayToken {
            blocks: blocks.to_vec(),
            steps,
            replay,
            want: want.iter().map(|w| (*w).to_string()).collect(),
            program: self.core.prog.clone(),
            env: self.env.clone(),
        })
    }

    /// The property each wanted proposition is a violation of, or why the
    /// wanted set does not name a refutation (H3: a token with nothing
    /// wanted, or wanting `policy_exec`, would witness a trace that refutes
    /// nothing).
    fn refuted_by<'w>(&self, want: &[&'w str]) -> Result<Vec<(&'w str, Refutes)>, TokenError> {
        if want.is_empty() {
            return Err(TokenError::NotARefutation {
                detail: "no violation proposition is wanted: a token witnesses a refutation"
                    .to_string(),
            });
        }
        let violations = property::violation_atoms(&self.core);
        want.iter()
            .map(|w| match property::refutes(w) {
                Some(r) if violations.contains(*w) => Ok((*w, r)),
                _ => Err(TokenError::NotARefutation {
                    detail: format!(
                        "`{w}` is not a violation proposition of this derivation (one of \
                         {violations:?})"
                    ),
                }),
            })
            .collect()
    }

    /// The final state of a replay is a concrete violation of each wanted
    /// property (beyond carrying its label, which the replay checks).
    fn check_refutation(
        &self,
        refuted: &[(&str, Refutes)],
        replay: &Replay,
        last: &Config,
    ) -> Result<(), TokenError> {
        let ri = self.interp();
        for (w, r) in refuted {
            let witnessed = match r {
                Refutes::FdInherit => !replay.violations.is_empty(),
                Refutes::LockRelease => {
                    let (leaks, _) =
                        property::lock_leaks(&self.core, last, ri.root, &|p| format!("pid{}", p.0));
                    leaks.iter().any(|l| {
                        *w == property::LOCK_LEAK
                            || *w == format!("{}_{}", property::LOCK_LEAK, property::atom(&l.class))
                    })
                }
                Refutes::FdIdentity => last.identity_violation.is_some(),
            };
            if !witnessed {
                return Err(TokenError::NotARefutation {
                    detail: format!(
                        "the final state carries `{w}` but is no concrete {r:?} violation"
                    ),
                });
            }
        }
        Ok(())
    }

    /// X2's three conditions on a replay of the explained `steps`.
    pub(crate) fn check_x2(&self, steps: &[TraceStep], replay: &Replay) -> Result<(), TokenError> {
        let prog = &self.core.prog;
        if steps.is_empty() || replay.steps.len() != steps.len() {
            return Err(TokenError::NotReexecuted {
                step: replay.steps.len().min(steps.len()),
                detail: format!(
                    "{} replay steps for {} explained steps",
                    replay.steps.len(),
                    steps.len()
                ),
            });
        }
        for (j, (st, r)) in steps.iter().zip(&replay.steps).enumerate() {
            let not_reexecuted = |detail: String| TokenError::NotReexecuted { step: j, detail };
            if st.info.label == HALT {
                // The derivation adds the horizon stutter as a self-loop
                // only: a "stutter" that moves is a step nothing re-executed.
                if st.from != st.to {
                    return Err(not_reexecuted(format!(
                        "a horizon stutter moves the machine from {} to {}",
                        st.from, st.to
                    )));
                }
                if !r.events.is_empty() || !r.sites.is_empty() {
                    return Err(not_reexecuted("the horizon stutter fired events".to_string()));
                }
                continue;
            }
            if r.label != st.info.text {
                return Err(not_reexecuted(format!(
                    "replay step `{}` is not the explained step `{}`",
                    r.label, st.info.text
                )));
            }
            if r.sites.is_empty() || r.sites.len() != r.events.len() {
                return Err(not_reexecuted(format!(
                    "{} typed sites for {} re-executed events",
                    r.sites.len(),
                    r.events.len()
                )));
            }
            for site in &r.sites {
                if site.environment {
                    match site.rl_clause {
                        Some(c) if RL_CLAUSES.contains(&c) && site.at.is_none() => {}
                        _ => {
                            return Err(TokenError::UncitedEnvironment {
                                step: j,
                                detail: format!(
                                    "an environment step of `{}` cites {:?}, not one of {RL_CLAUSES:?}",
                                    r.label, site.rl_clause
                                ),
                            });
                        }
                    }
                    continue;
                }
                let Some(at) = site.at else {
                    return Err(TokenError::UncitedEnvironment {
                        step: j,
                        detail: format!("a step of `{}` names no program position", r.label),
                    });
                };
                if site.rl_clause.is_some() || prog.loc_at(at) != Some(&site.loc) {
                    return Err(not_reexecuted(format!(
                        "the site {site:?} is not the program's position {at}"
                    )));
                }
                let row = std_origin(prog, at).map(|o| o.row);
                if site.std_row != row || row.is_some_and(str::is_empty) {
                    return Err(TokenError::UncitedStdRow {
                        step: j,
                        detail: format!(
                            "the step at {at} [{}] is a step of std row {row:?} and cites {:?}",
                            site.loc, site.std_row
                        ),
                    });
                }
            }
        }
        Ok(())
    }
}
