//! P-FD-INHERIT (plan §2.4) as atomic propositions on states.
//!
//! A child of a policy site that has exec'd violates `fd-inherit` when its
//! table is not `Declared(site)`: it holds a descriptor outside the declared
//! set (an inherited leak), or a policy lane is missing (closed at exec), or
//! a lane names a description of the wrong class (crossed). The declared set
//! is `{0,1,2}`, the policy's lanes, and every descriptor the child's own
//! setup placed or un-flagged, recorded by number as it ran.
//!
//! **The fd-bound premise is evaluated per child, at its snapshot**: a child
//! is "under fd-bound" iff every descriptor of the parent was below
//! `min(soft RLIMIT_NOFILE, cap)` at the moment the parent's table was copied
//! for it (its `fork` or `posix_spawn`) — the moment that decides what it
//! inherits. A premise CONDITIONS the verdict, it never removes states: the
//! premised atoms are separate propositions, the unpremised ones stay in the
//! model (I-NO-DECLARED-SHRINK), and a later violation of the premise cannot
//! excuse an earlier child.
//!
//! Propositions (CTL atoms the emitted machine labels its states with); each
//! also comes as `<atom>_under_fd_bound` (some child under the premise):
//!
//! * `fd_inherit_violation` — some policy child violates fd-inherit;
//! * `inherits_<class>` — it holds an undeclared descriptor of that class;
//! * `lane_missing`, `lane_crossed`;
//! * `policy_exec` — some policy child has exec'd (non-vacuity).
//!
//! Every atom is a property of exec'd policy children only, so it is FROZEN
//! after the exploration's horizon (no policy child running, none to come):
//! a formula over these atoms means the same on the horizon-cut machine as
//! on the system. [`check_formula`] refuses any other atom.
//!
//! # M2: P-LOCK-RELEASE and fd-identity
//!
//! Atoms of a program under [`crate::program::Policies`] (its exploration has
//! no horizon, so they are exact on every reachable state):
//!
//! * `lock_leak` (and `lock_leak_<class>`): a description the owner let go of
//!   — every live description of a class a release mark
//!   ([`crate::program::StmtKind::Release`]) names, at the mark; every live
//!   description when the owner process exits — still holds a lock the OWNER
//!   took ([`crate::interp::Config::owner_locks`]; a lock a child took on its
//!   own copy is the child's), where someone can see it (a name of the
//!   namespace still reaches its node, or another description — or a pending
//!   open — is on the node), and not handed off (some holder is the owner
//!   itself — a copy it kept — or a holder holds it at a number not DECLARED
//!   for it: its site's policy lane of that class, or a number its own setup
//!   placed or un-flagged). A forked child's copy, an exec'd image, a
//!   `posix_spawn` child between its halves, or a clone the owner forgot can
//!   each hold it past the owner's release point (M2 review: the owner's own
//!   copies and the observability and hand-off conditions are new);
//! * `released_shared` (non-vacuity): a released description is still
//!   referenced by another process — the situation in which only `LOCK_UN`
//!   keeps the lock from leaking;
//! * `fd_identity_violation`: a checked actor's event on a descriptor number
//!   reached a description other than the one it bound there (or "closed");
//! * `number_reused` (non-vacuity): a number a checked actor closed, or whose
//!   description is gone, is open again — someone else's allocation took it.

use std::collections::BTreeSet;

use trust_platform::Phase;

use crate::interp::Config;
use crate::lower::CoreProgram;

pub const VIOLATION: &str = "fd_inherit_violation";
pub const LANE_MISSING: &str = "lane_missing";
pub const LANE_CROSSED: &str = "lane_crossed";
pub const POLICY_EXEC: &str = "policy_exec";
pub const LOCK_LEAK: &str = "lock_leak";
pub const RELEASED_SHARED: &str = "released_shared";
pub const FD_IDENTITY_VIOLATION: &str = "fd_identity_violation";
pub const NUMBER_REUSED: &str = "number_reused";

/// P-LOCK-RELEASE as CTL.
#[must_use]
pub fn lock_release_formula() -> String {
    format!("AG !{LOCK_LEAK}")
}

/// fd-identity as CTL.
#[must_use]
pub fn fd_identity_formula() -> String {
    format!("AG !{FD_IDENTITY_VIOLATION}")
}
/// The suffix of an atom restricted to children spawned under fd-bound.
pub const UNDER_FD_BOUND: &str = "_under_fd_bound";

/// A policy premise.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Premise {
    /// `fd-bound`: every open descriptor of the root is below
    /// `min(soft RLIMIT_NOFILE, cap)` when a policy child's table is copied;
    /// aterm's cap is 65536 (`inherited_fd_ceiling`, spawnfd.rs).
    FdBound,
}

/// `atom`, restricted to children spawned under `premises`.
#[must_use]
pub fn premised(atom: &str, premises: &[Premise]) -> String {
    if premises.contains(&Premise::FdBound) {
        format!("{atom}{UNDER_FD_BOUND}")
    } else {
        atom.to_string()
    }
}

/// The CTL formula for fd-inherit under `premises`.
#[must_use]
pub fn fd_inherit_formula(premises: &[Premise]) -> String {
    format!("AG !{}", premised(VIOLATION, premises))
}

/// The non-vacuity check, as a REFUTATION (the only verdict a derived model
/// can give): `AG !policy_exec` must be refuted, with a trace to a policy
/// child's exec (under the premises).
#[must_use]
pub fn non_vacuity_formula(premises: &[Premise]) -> String {
    format!("AG !{}", premised(POLICY_EXEC, premises))
}

/// A CTL identifier from a class name.
#[must_use]
pub fn atom(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect()
}

/// Every atom a state of `core`'s model can carry (whether or not one does).
#[must_use]
pub fn vocabulary(core: &CoreProgram) -> BTreeSet<String> {
    let mut base: Vec<String> = vec![
        VIOLATION.to_string(),
        LANE_MISSING.to_string(),
        LANE_CROSSED.to_string(),
        POLICY_EXEC.to_string(),
    ];
    base.extend(core.classes.iter().map(|c| format!("inherits_{}", atom(c))));
    base.push("inherits__".to_string());
    let mut out: BTreeSet<String> = BTreeSet::new();
    for a in base {
        out.insert(format!("{a}{UNDER_FD_BOUND}"));
        out.insert(a);
    }
    let p = &core.prog.policies;
    if p.lock_release {
        out.insert(LOCK_LEAK.to_string());
        out.insert(RELEASED_SHARED.to_string());
        out.extend(core.classes.iter().map(|c| format!("{LOCK_LEAK}_{}", atom(c))));
    }
    if !p.fd_identity.is_empty() {
        out.insert(FD_IDENTITY_VIOLATION.to_string());
        out.insert(NUMBER_REUSED.to_string());
    }
    out
}

/// Which property a VIOLATION atom refutes (red-team H3: a replay token
/// witnesses a refutation, so what it wants must be one of these).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refutes {
    /// `fd_inherit_violation`, `inherits_<class>`, `lane_missing`,
    /// `lane_crossed` (and each `…_under_fd_bound`).
    FdInherit,
    /// `lock_leak`, `lock_leak_<class>`.
    LockRelease,
    /// `fd_identity_violation`.
    FdIdentity,
}

/// The property `atom` is a violation of, or `None` for a non-vacuity atom
/// (`policy_exec`, `released_shared`, `number_reused`) and anything else.
/// Positive: an atom is a violation only by matching one of the shapes the
/// labelling ([`labels`]) gives violations.
#[must_use]
pub fn refutes(atom: &str) -> Option<Refutes> {
    let base = atom.strip_suffix(UNDER_FD_BOUND).unwrap_or(atom);
    if base == VIOLATION
        || base == LANE_MISSING
        || base == LANE_CROSSED
        || base.strip_prefix("inherits_").is_some_and(|c| !c.is_empty())
    {
        return Some(Refutes::FdInherit);
    }
    if atom == LOCK_LEAK
        || atom
            .strip_prefix(LOCK_LEAK)
            .and_then(|c| c.strip_prefix('_'))
            .is_some_and(|c| !c.is_empty())
    {
        return Some(Refutes::LockRelease);
    }
    if atom == FD_IDENTITY_VIOLATION {
        return Some(Refutes::FdIdentity);
    }
    None
}

/// Every atom of `core`'s vocabulary that names a violation ([`refutes`]).
#[must_use]
pub fn violation_atoms(core: &CoreProgram) -> BTreeSet<String> {
    vocabulary(core).into_iter().filter(|a| refutes(a).is_some()).collect()
}

/// One P-LOCK-RELEASE finding of a state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockLeak {
    pub class: String,
    /// `(process, descriptor)` entries that still name the locked description.
    pub holders: Vec<(String, i32)>,
    pub mode: String,
}

impl std::fmt::Display for LockLeak {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let who: Vec<String> = self.holders.iter().map(|(p, fd)| format!("{p} fd {fd}")).collect();
        write!(
            f,
            "the {} lock of a `{}` description outlives its owner's release point: held by {}",
            self.mode,
            self.class,
            who.join(", ")
        )
    }
}

/// Whether someone can see description `o`'s lock: a name of the namespace
/// still resolves to its node, or another description (or an `open` that has
/// not returned) is on that node. A node no name reaches and nothing else has
/// open is contended by no one: its lock, leaked or not, is unobservable.
fn observable(cfg: &Config, o: trust_platform::OfdId) -> bool {
    let Some(n) = cfg.host.ofd(o).and_then(|x| x.node) else { return false };
    cfg.host.reachable_by_name(n)
        || cfg.host.ofds_on(n).any(|(id, _)| id != o)
        || cfg.host.pending_on(n)
}

/// Whether description `o` was HANDED OFF: the owner holds no copy, and every
/// other holder holds it at a number declared for it — a policy lane of its
/// spawn site naming `o`'s class, or a number its own setup placed or
/// un-flagged (`dup2`, `F_SETFD` without `FD_CLOEXEC`, `addinherit_np`, …).
fn handed_off(
    core: &CoreProgram,
    cfg: &Config,
    o: trust_platform::OfdId,
    root: trust_platform::Pid,
) -> bool {
    let holders = cfg.host.holders(o);
    if holders.is_empty() || holders.iter().any(|(p, _)| *p == root) {
        return false;
    }
    let class = cfg.classes.get(&o).copied();
    holders.iter().all(|(p, fd)| {
        cfg.record(*p).is_some_and(|r| {
            r.declared.contains(fd)
                || core.declared.get(r.site).and_then(Option::as_ref).is_some_and(|d| {
                    d.required
                        .iter()
                        .any(|(lane, want)| lane == fd && want.is_some() && *want == class)
                })
        })
    })
}

/// The P-LOCK-RELEASE findings of `cfg` (`root`: the owner process), and
/// whether some released description is still shared with another process.
pub fn lock_leaks(
    core: &CoreProgram,
    cfg: &Config,
    root: trust_platform::Pid,
    name_of: &dyn Fn(trust_platform::Pid) -> String,
) -> (Vec<LockLeak>, bool) {
    let mut leaks = Vec::new();
    let mut shared = false;
    for o in &cfg.released {
        let Some(x) = cfg.host.ofd(*o) else { continue };
        let holders = cfg.host.holders(*o);
        if holders.iter().any(|(p, _)| *p != root) {
            shared = true;
        }
        let Some(mode) = x.lock else { continue };
        if !cfg.owner_locks.contains(o) || !observable(cfg, *o) || handed_off(core, cfg, *o, root) {
            continue;
        }
        let class =
            cfg.classes.get(o).and_then(|k| core.classes.get(*k)).cloned().unwrap_or_default();
        leaks.push(LockLeak {
            class,
            holders: holders.iter().map(|(p, fd)| (name_of(*p), *fd)).collect(),
            mode: format!("{mode:?}").to_lowercase(),
        });
    }
    (leaks, shared)
}

/// Whether a number some checked actor closed (or whose description is
/// gone) is open again in its process.
#[must_use]
pub fn number_reused(cfg: &Config) -> bool {
    cfg.actors.iter().any(|a| {
        a.bindings.iter().any(|(n, b)| {
            matches!(b, crate::interp::Binding::Closed | crate::interp::Binding::Gone)
                && cfg.host.entry(a.pid, *n).is_some()
        })
    })
}

/// Why a formula is not checked over a derived model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FormulaError {
    /// Not CTL ty can parse.
    Parse(String),
    /// An atom no state can carry (a misspelling is otherwise a vacuous
    /// pass: an unknown atom is false everywhere).
    UnknownAtom(String),
}

impl std::fmt::Display for FormulaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FormulaError::Parse(e) => write!(f, "not a CTL formula ty parses: {e}"),
            FormulaError::UnknownAtom(a) => write!(
                f,
                "atom `{a}` is not in the derived model's vocabulary (fd-inherit atoms of exec'd \
                 policy children only; they are frozen after the exploration horizon)"
            ),
        }
    }
}

/// Parse `formula` with ty's own CTL parser and check every atom against
/// `vocabulary`.
pub fn check_formula(formula: &str, vocabulary: &BTreeSet<String>) -> Result<(), FormulaError> {
    use trust_temporal::ctl::CtlFormula;
    fn check_atoms(f: &CtlFormula, vocabulary: &BTreeSet<String>) -> Result<(), FormulaError> {
        match f {
            CtlFormula::Atom(a) => {
                if !vocabulary.contains(a) {
                    return Err(FormulaError::UnknownAtom(a.clone()));
                }
            }
            CtlFormula::True | CtlFormula::False => {}
            CtlFormula::Not(x)
            | CtlFormula::EX(x)
            | CtlFormula::EF(x)
            | CtlFormula::EG(x)
            | CtlFormula::AX(x)
            | CtlFormula::AF(x)
            | CtlFormula::AG(x) => check_atoms(x, vocabulary)?,
            CtlFormula::And(x, y)
            | CtlFormula::Or(x, y)
            | CtlFormula::EU(x, y)
            | CtlFormula::AU(x, y) => {
                check_atoms(x, vocabulary)?;
                check_atoms(y, vocabulary)?;
            }
            // A connective this check does not know: its atoms cannot be
            // vetted, so the formula is refused (fail-closed).
            other => {
                return Err(FormulaError::Parse(format!("unvetted CTL connective in `{other}`")));
            }
        }
        Ok(())
    }
    let f =
        trust_temporal::ctl::parse_ctl(formula).map_err(|e| FormulaError::Parse(e.to_string()))?;
    check_atoms(&f, vocabulary)
}

/// One way a policy child's table differs from `Declared`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Violation {
    /// It holds `fd` (a description of `class`) that is not declared.
    Extra { site: String, fd: i32, class: String, cloexec: bool },
    /// A required descriptor is closed at exec.
    Missing { site: String, fd: i32 },
    /// A lane names a description of the wrong class.
    Crossed { site: String, fd: i32, want: String, got: String },
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Violation::Extra { site, fd, class, .. } => {
                write!(f, "child[{site}] execs holding fd {fd} ({class}), which is not declared")
            }
            Violation::Missing { site, fd } => {
                write!(f, "child[{site}] execs with lane fd {fd} closed")
            }
            Violation::Crossed { site, fd, want, got } => {
                write!(f, "child[{site}] execs with fd {fd} naming {got}, not {want}")
            }
        }
    }
}

/// Every fd-inherit violation in `cfg`, with whether the violating child was
/// spawned under fd-bound.
pub fn violations_premised(core: &CoreProgram, cfg: &Config) -> Vec<(Violation, bool)> {
    let mut out = Vec::new();
    for r in &cfg.spawns {
        let Some(Some(decl)) = core.declared.get(r.site) else { continue };
        if !r.execd || r.gone {
            continue;
        }
        let Some(p) = cfg.host.proc(r.pid) else { continue };
        if p.phase != Phase::Execd {
            continue;
        }
        let site = core.prog.sites[r.site].name.clone();
        let class_of = |o| {
            cfg.classes
                .get(&o)
                .and_then(|k| core.classes.get(*k))
                .cloned()
                .unwrap_or_else(|| "?".to_string())
        };
        for (fd, e) in &p.table {
            if !decl.allowed.contains(fd) && !r.declared.contains(fd) {
                let v = Violation::Extra {
                    site: site.clone(),
                    fd: *fd,
                    class: class_of(e.ofd),
                    cloexec: e.cloexec,
                };
                out.push((v, r.premise));
            }
        }
        for (fd, want) in &decl.required {
            match p.table.get(fd) {
                None => out.push((Violation::Missing { site: site.clone(), fd: *fd }, r.premise)),
                Some(e) => {
                    if let Some(k) = want
                        && cfg.classes.get(&e.ofd) != Some(k)
                    {
                        let v = Violation::Crossed {
                            site: site.clone(),
                            fd: *fd,
                            want: core.classes.get(*k).cloned().unwrap_or_default(),
                            got: class_of(e.ofd),
                        };
                        out.push((v, r.premise));
                    }
                }
            }
        }
    }
    out
}

/// Every fd-inherit violation in `cfg`.
pub fn violations(core: &CoreProgram, cfg: &Config) -> Vec<Violation> {
    violations_premised(core, cfg).into_iter().map(|(v, _)| v).collect()
}

/// The atomic propositions of `cfg`.
#[must_use]
pub fn labels(core: &CoreProgram, cfg: &Config) -> Vec<String> {
    let mut l: BTreeSet<String> = BTreeSet::new();
    let mut add = |a: String, under: bool| {
        if under {
            l.insert(format!("{a}{UNDER_FD_BOUND}"));
        }
        l.insert(a);
    };
    for (v, under) in violations_premised(core, cfg) {
        add(VIOLATION.to_string(), under);
        let s = match v {
            Violation::Extra { class, .. } => format!("inherits_{}", atom(&class)),
            Violation::Missing { .. } => LANE_MISSING.to_string(),
            Violation::Crossed { .. } => LANE_CROSSED.to_string(),
        };
        add(s, under);
    }
    for r in &cfg.spawns {
        if r.execd && !r.gone && matches!(core.declared.get(r.site), Some(Some(_))) {
            add(POLICY_EXEC.to_string(), r.premise);
        }
    }
    let p = &core.prog.policies;
    if p.lock_release {
        let (leaks, shared) =
            lock_leaks(core, cfg, trust_platform::Pid(1), &|p| format!("pid{}", p.0));
        for leak in &leaks {
            l.insert(LOCK_LEAK.to_string());
            l.insert(format!("{LOCK_LEAK}_{}", atom(&leak.class)));
        }
        if shared {
            l.insert(RELEASED_SHARED.to_string());
        }
    }
    if !p.fd_identity.is_empty() {
        if cfg.identity_violation.is_some() {
            l.insert(FD_IDENTITY_VIOLATION.to_string());
        }
        if number_reused(cfg) {
            l.insert(NUMBER_REUSED.to_string());
        }
    }
    l.into_iter().collect()
}
