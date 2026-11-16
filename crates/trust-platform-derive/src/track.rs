//! X1: which scalars of an event program are untracked
//! ([`Expr::Opaque`]), and the check that none of them reaches a place whose
//! value the model executes.
//!
//! The model runs every event at the concrete values of its operands, takes
//! every branch by evaluating its guard and runs every `ForRange` over its
//! bounds. An untracked value has no concrete value: it may flow through
//! assignments, call arguments and returns into variables that are read in
//! none of those places, but nowhere else. If it can reach one, the program
//! is refused ([`LowerError::Untracked`], which the census reports as
//! `PC-UNTRACKED-FD`), and an untracked guard must be written
//! [`Cond::Nondet`] instead.
//!
//! The analysis is flow-insensitive. A variable is untracked if ANY
//! assignment to it can carry an untracked value: for a parameter, any call's
//! argument; for a call's result, any return of the callee. For census
//! output (one variable per SSA value or block parameter) that is the phi
//! semantics. For a reused variable it errs toward refusing, never toward
//! admitting. Each refusal names the untracked variable, the place it
//! reached, and the `Expr::Opaque` its value came from.

use std::collections::BTreeMap;

use crate::lower::LowerError;
use crate::program::{
    BodyId, Cond, EventProgram, Expr, Loc, Operand, StdCall, StmtKind, Term, VarId,
};

/// The value an untracked variable holds in a state. [`check`] proves it is
/// never an event operand, a guard operand or a loop bound, so it decides
/// nothing. It lies outside `i32`, so if it were ever converted to an
/// operand the interpreter would refuse it as "not an int" instead of
/// running on a real descriptor number.
pub const OPAQUE_VALUE: i64 = i64::MIN;

/// The untracked variables of a program, each with the `Expr::Opaque` its
/// value can come from.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Untracked {
    pub vars: BTreeMap<VarId, Loc>,
    /// Bodies whose return value can be untracked.
    pub returns: BTreeMap<BodyId, Loc>,
}

impl Untracked {
    /// The `Expr::Opaque` an operand's value can come from, if any.
    #[must_use]
    pub fn origin(&self, op: &Operand) -> Option<&Loc> {
        match op {
            Operand::Var(v) => self.vars.get(v),
            Operand::Lit(_) => None,
        }
    }

    fn first<'a>(&'a self, ops: &[&Operand]) -> Option<&'a Loc> {
        ops.iter().find_map(|o| self.origin(o))
    }
}

/// Apply what a statement may make untracked, given what is untracked so
/// far. Every statement kind is named: a new kind must say whether it moves
/// values.
fn apply_flows(kind: &StmtKind, loc: &Loc, u: &mut Untracked) -> bool {
    match kind {
        StmtKind::Assign { var, expr } => {
            if u.vars.contains_key(var) {
                return false;
            }
            let origin = match expr {
                Expr::Opaque => Some(loc.clone()),
                Expr::Use(a) => u.origin(a).cloned(),
                Expr::Add(a, b) | Expr::Min(a, b) | Expr::BitAnd(a, b) => {
                    u.first(&[a, b]).cloned()
                }
            };
            if let Some(o) = origin {
                u.vars.insert(*var, o);
                true
            } else {
                false
            }
        }
        StmtKind::Call { body, args, ret } => {
            let mut changed = false;
            for (p, op) in args {
                if !u.vars.contains_key(p)
                    && let Some(o) = u.origin(op).cloned()
                {
                    u.vars.insert(*p, o);
                    changed = true;
                }
            }
            if let Some(r) = ret
                && !u.vars.contains_key(r)
                && let Some(o) = u.returns.get(body).cloned()
            {
                u.vars.insert(*r, o);
                changed = true;
            }
            changed
        }
        // Event results, fork pids, loop indices over checked bounds, std row
        // results, spawned pids and a std open's descriptor are values the
        // model computes. A started thread copies its creator's variables
        // under the SAME ids (M2), so the flow-insensitive analysis already
        // covers it; a join and a release mark move no value.
        StmtKind::Event(_)
        | StmtKind::ForRange { .. }
        | StmtKind::Fork { .. }
        | StmtKind::Neutral { .. }
        | StmtKind::Std(
            StdCall::Row { .. } | StdCall::CommandSpawn { .. } | StdCall::OpenFile { .. },
        )
        | StmtKind::Skip
        | StmtKind::Release { .. }
        | StmtKind::SpawnThread { .. }
        | StmtKind::Join { .. } => false,
    }
}

/// The least fixpoint of `apply_flows` (what each statement moves) over the
/// whole program.
#[must_use]
pub fn untracked(prog: &EventProgram) -> Untracked {
    let mut u = Untracked::default();
    loop {
        let mut changed = false;
        for (bi, body) in prog.bodies.iter().enumerate() {
            for block in &body.blocks {
                for s in &block.stmts {
                    if apply_flows(&s.kind, &s.loc, &mut u) {
                        changed = true;
                    }
                }
                if let Term::Return(Some(op)) = &block.term
                    && !u.returns.contains_key(&bi)
                    && let Some(o) = u.origin(op).cloned()
                {
                    u.returns.insert(bi, o);
                    changed = true;
                }
            }
        }
        if !changed {
            return u;
        }
    }
}

/// The first untracked operand a statement's execution READS as a concrete
/// value, with what it is for and its origin. Every statement kind is named.
fn find_untracked_read<'a>(
    kind: &StmtKind,
    u: &'a Untracked,
) -> Option<(Operand, String, &'a Loc)> {
    match kind {
        StmtKind::Event(ev) => {
            let mut found = None;
            let mut k = 0usize;
            let _ = ev.call.map(|o| {
                if found.is_none()
                    && let Some(origin) = u.origin(o)
                {
                    found = Some((
                        *o,
                        format!("descriptor/pid operand {k} of `{}`", ev.symbol),
                        origin,
                    ));
                }
                k += 1;
            });
            found
        }
        StmtKind::ForRange { lo, hi, .. } => {
            if let Some(origin) = u.origin(lo) {
                return Some((*lo, "lower bound of a descriptor loop".to_string(), origin));
            }
            if let Some(origin) = u.origin(hi) {
                return Some((*hi, "upper bound of a descriptor loop".to_string(), origin));
            }
            None
        }
        StmtKind::Std(StdCall::Row { path, args, .. }) => {
            args.iter().enumerate().find_map(|(k, o)| {
                u.origin(o).map(|origin| (*o, format!("argument {k} of the std row `{path}`"), origin))
            })
        }
        // Values these move are followed by `apply_flows`; they read nothing
        // the model executes. A std open's path and flags are literals; a
        // release mark names classes; a thread start or join names a root index.
        StmtKind::Assign { .. }
        | StmtKind::Call { .. }
        | StmtKind::Fork { .. }
        | StmtKind::Neutral { .. }
        | StmtKind::Std(StdCall::CommandSpawn { .. } | StdCall::OpenFile { .. })
        | StmtKind::Skip
        | StmtKind::Release { .. }
        | StmtKind::SpawnThread { .. }
        | StmtKind::Join { .. } => None,
    }
}

/// The first untracked operand a guard compares (an `Opaque`-fed operand
/// there must be a [`Cond::Nondet`] instead).
fn find_untracked_guard_read<'a>(c: &Cond, u: &'a Untracked) -> Option<(Operand, &'a Loc)> {
    match c {
        Cond::Cmp(_, a, b) => {
            if let Some(origin) = u.origin(a) {
                return Some((*a, origin));
            }
            if let Some(origin) = u.origin(b) {
                return Some((*b, origin));
            }
            None
        }
        Cond::And(a, b) | Cond::Or(a, b) => {
            find_untracked_guard_read(a, u).or_else(|| find_untracked_guard_read(b, u))
        }
        Cond::Not(a) => find_untracked_guard_read(a, u),
        Cond::Const(_) | Cond::Nondet => None,
    }
}

/// Refuse `prog` if an untracked value can reach an event operand, a guard
/// or a loop bound.
pub fn check(prog: &EventProgram) -> Result<(), LowerError> {
    let u = untracked(prog);
    if u.vars.is_empty() {
        return Ok(());
    }
    let name = |op: &Operand| match op {
        Operand::Var(v) => prog.vars.get(*v).map_or_else(|| format!("var {v}"), |x| x.name.clone()),
        Operand::Lit(x) => x.to_string(),
    };
    let refuse = |op: &Operand, used_as: String, loc: &Loc, origin: &Loc| LowerError::Untracked {
        var: name(op),
        used_as,
        loc: loc.clone(),
        origin: origin.clone(),
    };
    for body in &prog.bodies {
        for block in &body.blocks {
            for s in &block.stmts {
                if let Some((op, used_as, origin)) = find_untracked_read(&s.kind, &u) {
                    return Err(refuse(&op, used_as, &s.loc, origin));
                }
            }
            if let Term::Branch { cond, .. } = &block.term
                && let Some((op, origin)) = find_untracked_guard_read(cond, &u)
            {
                return Err(refuse(
                    &op,
                    "operand of a branch guard (an untracked guard must be Cond::Nondet)"
                        .to_string(),
                    &block.term_loc,
                    origin,
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use trust_platform::Call;

    use super::*;
    use crate::program::{Bind, CmpOp, ProgramBuilder};

    fn refusal(prog: &EventProgram) -> (String, String, String) {
        match check(prog) {
            Err(LowerError::Untracked { var, used_as, origin, .. }) => (var, used_as, origin.0),
            other => panic!("expected Untracked, got {other:?}"),
        }
    }

    #[test]
    fn an_opaque_descriptor_operand_is_refused_with_its_origin() {
        let mut p = ProgramBuilder::new("opaque_fd");
        let fd = p.var("fd", -1);
        let main = p.body("main", Vec::new(), |b| {
            b.assign("t.rs:1", fd, Expr::Opaque);
            b.event("t.rs:2", "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
        });
        p.root("main", main);
        let (var, used_as, origin) = refusal(&p.build());
        assert_eq!(var, "fd");
        assert!(used_as.contains("operand 0 of `close`"), "{used_as}");
        assert_eq!(origin, "t.rs:1");
    }

    /// Through `Add`, a call argument, the callee's return and the caller's
    /// result variable into a guard.
    #[test]
    fn untracked_flows_through_calls_and_returns_into_a_guard() {
        let mut p = ProgramBuilder::new("flow");
        let x = p.var("x", 0);
        let param = p.var("param", 0);
        let sum = p.var("sum", 0);
        let r = p.var("r", 0);
        let callee = p.body("callee", vec![param], |b| {
            b.assign("t.rs:10", sum, Expr::Add(Operand::Var(param), Operand::Lit(1)));
            b.ret("t.rs:11", Some(Operand::Var(sum)));
        });
        let main = p.body("main", Vec::new(), |b| {
            b.assign("t.rs:1", x, Expr::Opaque);
            b.call("t.rs:2", callee, vec![(param, Operand::Var(x))], Some(r));
            b.when("t.rs:3", Cond::Cmp(CmpOp::Lt, Operand::Var(r), Operand::Lit(3)), |_| {});
        });
        p.root("main", main);
        let prog = p.build();
        let u = untracked(&prog);
        for v in [x, param, sum, r] {
            assert_eq!(u.vars.get(&v).map(|l| l.0.as_str()), Some("t.rs:1"), "var {v}");
        }
        let (var, used_as, _) = refusal(&prog);
        assert_eq!(var, "r");
        assert!(used_as.contains("guard"), "{used_as}");
    }

    #[test]
    fn untracked_loop_bounds_and_std_row_arguments_are_refused() {
        let mut p = ProgramBuilder::new("bounds");
        let hi = p.var("hi", 0);
        let i = p.var("i", 0);
        let one = p.body("one", Vec::new(), |_| {});
        let main = p.body("main", Vec::new(), |b| {
            b.assign("t.rs:1", hi, Expr::Opaque);
            b.for_range("t.rs:2", i, Operand::Lit(3), Operand::Var(hi), one);
        });
        p.root("main", main);
        assert!(refusal(&p.build()).1.contains("upper bound"));

        let mut p = ProgramBuilder::new("row");
        let fd = p.var("fd", 0);
        let main = p.body("main", Vec::new(), |b| {
            b.assign("t.rs:1", fd, Expr::Opaque);
            b.std_row("t.rs:2", "some::row", vec![Operand::Var(fd)], Vec::new(), Vec::new());
        });
        p.root("main", main);
        assert!(refusal(&p.build()).1.contains("argument 0 of the std row `some::row`"));
    }

    /// An untracked value nobody executes is admitted; a guard over it
    /// written `Nondet` is admitted; an event RESULT bound into a variable is
    /// tracked.
    #[test]
    fn unobserved_untracked_values_and_nondet_guards_are_admitted() {
        let mut p = ProgramBuilder::new("ok");
        let junk = p.var("junk", 0);
        let copy = p.var("copy", 0);
        let fd = p.var("fd", -1);
        let main = p.body("main", Vec::new(), |b| {
            b.assign("t.rs:1", junk, Expr::Opaque);
            b.assign("t.rs:2", copy, Expr::Min(Operand::Var(junk), Operand::Lit(9)));
            b.event("t.rs:3", "dup", Call::Dup { fd: Operand::Lit(0) }, Bind::ret(fd));
            b.if_(
                "t.rs:4",
                Cond::And(
                    Box::new(Cond::Nondet),
                    Box::new(Cond::Cmp(CmpOp::Ge, Operand::Var(fd), Operand::Lit(0))),
                ),
                |b| b.event("t.rs:5", "close", Call::Close { fd: Operand::Var(fd) }, Bind::none()),
                |_| {},
            );
            b.ret("t.rs:6", Some(Operand::Var(copy)));
        });
        p.root("main", main);
        let prog = p.build();
        assert_eq!(check(&prog), Ok(()));
        let u = untracked(&prog);
        assert!(u.vars.contains_key(&junk) && u.vars.contains_key(&copy));
        assert!(!u.vars.contains_key(&fd));
    }
}
