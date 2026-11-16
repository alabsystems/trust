//! X1: undecided guards ([`Cond::Nondet`]) as explicit choice steps.
//!
//! A branch whose guard evaluates to "undecided" (three-valued, Kleene
//! logic over `Cond::Nondet`) stops the actor at its block's terminator,
//! like an event does. The exploration then takes the choice as a step of
//! its own ([`ActionKey::Nondet`]): one successor per arm.
//!
//! That step is local: it moves one actor's program counter (and runs the
//! local statements after it), and no other actor's step reads either —
//! except a fork or spawn by another thread, which reads the event this
//! actor is about to take (a torn table copy). So the exploration resolves
//! choices EAGERLY: while any actor sits at a choice, its two arms are the
//! state's only successors. That is the treatment the interpreter gives
//! every other local statement, which it runs while settling (D2:
//! interleaving points are platform events). Resolving first can only make a
//! pending event visible to a concurrent fork earlier, and the atomic table
//! copy stays among every fork's outcomes. No interleaving of platform
//! events is lost, and a forked child's macro step (SD-3) still runs before
//! anyone else's next event.
//!
//! A choice is an OVER-approximation: the model takes an arm the program
//! might never take. Every choice is therefore a visible step of the
//! machine, with its own event-map entry, and
//! [`crate::derive::Derived::replay`] re-executes it and lists it in
//! [`crate::trace::Replay::overapprox`]. A refutation that lists one is not
//! an error (Critique C-9, `PC-OVERAPPROX`).

use trust_platform::Oracle;

use crate::explore::ActionKey;
use crate::interp::{Actor, Config, Fired, Interp, InterpError};
use crate::program::{BlockId, Cond, EventProgram, Loc, StmtRef, Term};

/// One successor of a state: the action, the state it reaches, its events.
pub type Successor = (ActionKey, Config, Vec<Fired>);

/// An actor settled at an undecided guard.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Choice {
    /// The branch: `idx` is the block's statement count (its terminator).
    pub at: StmtRef,
    pub then: BlockId,
    pub els: BlockId,
}

/// One over-approximating choice a replayed trace took.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Overapprox {
    /// The replay step (index into [`crate::trace::Replay::steps`]).
    pub step: usize,
    pub actor: String,
    /// The branch's location.
    pub loc: String,
    /// `true`: the then-arm.
    pub then: bool,
}

impl std::fmt::Display for Overapprox {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "step {}: {} took the {} of an undecided guard (Cond::Nondet) at {}",
            self.step,
            self.actor,
            arm(self.then),
            self.loc
        )
    }
}

/// `then-arm` / `else-arm`.
#[must_use]
pub fn arm(then: bool) -> &'static str {
    if then { "then-arm" } else { "else-arm" }
}

impl EventProgram {
    /// The location of a statement, or of a block's terminator when `at`
    /// is one past its last statement.
    #[must_use]
    pub fn loc_at(&self, at: StmtRef) -> Option<&Loc> {
        let block = self.bodies.get(at.body)?.blocks.get(at.block)?;
        match block.stmts.get(at.idx) {
            Some(s) => Some(&s.loc),
            None if at.idx == block.stmts.len() => Some(&block.term_loc),
            None => None,
        }
    }

    /// The location of every branch whose guard contains [`Cond::Nondet`].
    #[must_use]
    pub fn nondet_guards(&self) -> Vec<&Loc> {
        fn has(c: &Cond) -> bool {
            match c {
                Cond::Nondet => true,
                Cond::And(a, b) | Cond::Or(a, b) => has(a) || has(b),
                Cond::Not(a) => has(a),
                Cond::Cmp(..) | Cond::Const(_) => false,
            }
        }
        self.bodies
            .iter()
            .flat_map(|b| &b.blocks)
            .filter(|k| matches!(&k.term, Term::Branch { cond, .. } if has(cond)))
            .map(|k| &k.term_loc)
            .collect()
    }
}

impl Interp<'_> {
    /// The undecided guard actor `a` is settled at, if any.
    pub fn pending_choice(&self, a: &Actor) -> Result<Option<Choice>, InterpError> {
        let Some(f) = a.frames.last() else { return Ok(None) };
        let Some(block) = self.core.prog.bodies.get(f.body).and_then(|b| b.blocks.get(f.block))
        else {
            return Err(InterpError::Malformed(format!("pc b{}.{}", f.body, f.block)));
        };
        if f.idx != block.stmts.len() {
            return Ok(None);
        }
        match &block.term {
            Term::Branch { cond, then, els } if Self::cond3(a, cond)?.is_none() => {
                Ok(Some(Choice {
                    at: StmtRef { body: f.body, block: f.block, idx: f.idx },
                    then: *then,
                    els: *els,
                }))
            }
            _ => Ok(None),
        }
    }

    /// Take the `then` (or else) arm of the undecided guard actor `i` is
    /// settled at, and settle it again.
    pub fn choose(
        &self,
        cfg: &Config,
        i: usize,
        then: bool,
    ) -> Result<(Config, Fired), InterpError> {
        let a = cfg.actors.get(i).ok_or_else(|| InterpError::Malformed("actor".into()))?;
        let ch = self.pending_choice(a)?.ok_or_else(|| {
            InterpError::Malformed(
                "choosing an arm for an actor that is not at an undecided guard".into(),
            )
        })?;
        let (role, pid) = (a.role, a.pid);
        let mut c = cfg.clone();
        let actor = &mut c.actors[i];
        Self::jump(actor, if then { ch.then } else { ch.els });
        self.settle(actor)?;
        let loc = self.core.prog.loc_at(ch.at).map(|l| l.0.clone()).unwrap_or_default();
        Ok((
            c,
            Fired {
                role,
                at: ch.at,
                oracle: Oracle::Nominal,
                missed: Vec::new(),
                pid,
                call: None,
                result: None,
                note: format!(
                    "undecided guard (Cond::Nondet) at {loc}: the model takes the {} — an \
                     over-approximating choice",
                    arm(then)
                ),
            },
        ))
    }

    /// The successors of `cfg` when some actor is settled at an undecided
    /// guard: that actor's two arms, and nothing else (the module doc says
    /// why that loses no interleaving). `None`: no actor is.
    pub fn nondet_successors(&self, cfg: &Config) -> Result<Option<Vec<Successor>>, InterpError> {
        for (i, a) in cfg.actors.iter().enumerate() {
            let Some(ch) = self.pending_choice(a)? else { continue };
            let mut out = Vec::with_capacity(2);
            for then in [true, false] {
                let (c, f) = self.choose(cfg, i, then)?;
                out.push((
                    ActionKey::Nondet { role: a.role, at: ch.at, then },
                    self.finish(c),
                    vec![f],
                ));
            }
            return Ok(Some(out));
        }
        Ok(None)
    }
}
