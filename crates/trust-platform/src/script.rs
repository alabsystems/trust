//! Straight-line platform programs over the clauses: the shared shape of a
//! std summary row, a conformance probe, and a derivation's event sequence.
//!
//! A [`Program`] is a list of [`ProgramStep`]s, each a call made by an
//! [`Actor`] — the root process, or the child some earlier `fork`/`spawn`
//! step created — whose descriptor operands may name earlier results
//! ([`Operand::Ret`]) or the program's arguments ([`Operand::Arg`]).
//! [`run`] evaluates it against any [`Semantics`] and returns, per step, the
//! acting pid, the concrete call, the result and the host after the step:
//! the trace an explicit-state checker or a replay compares against.
//!
//! A step can carry std's own branches on its descriptors (Trust's spawn,
//! DECISION_QUEUE SP-1, [`crate::std_summaries`]): a [`When`] makes it only
//! where a [`Guard`] holds and otherwise skips it with a stated result, and
//! an [`Assumed`] names the branch a program IS, so [`run`] refuses (by name)
//! a run that reaches another. A program with neither is straight-line.

use crate::call::{Call, Oracle, Refusal, Ret, Semantics, SysResult};
use crate::host::{Host, Pid};

/// A descriptor or pid operand.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Operand {
    Lit(i32),
    /// Component `comp` of step `step`'s successful result (`Ret::Int` is
    /// component 0; `Ret::Pair` has 0 and 1).
    Ret {
        step: usize,
        comp: u8,
    },
    /// The program's `i`-th argument.
    Arg(usize),
}

/// Who makes a call.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Actor {
    Root,
    /// The process step `k` (a `Fork` or `Spawn`) created.
    Child(usize),
}

/// A condition on a program's arguments and earlier results.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Guard {
    /// The operand resolves to a number below the bound.
    Below(Operand, i32),
    /// Both operands resolve, to different numbers.
    Differ(Operand, Operand),
    /// Step `step` succeeded with an `Int` none of whose `mask` bits is set
    /// (`mask` 0: it succeeded with an `Int`).
    Clear { step: usize, mask: i64 },
}

impl Guard {
    /// Whether the guard holds; an operand that does not resolve (a failed
    /// or missing step) makes it false.
    #[must_use]
    pub fn holds(&self, args: &[i32], results: &[SysResult]) -> bool {
        match *self {
            Guard::Below(a, bound) => a.resolve(args, results).is_some_and(|v| v < bound),
            Guard::Differ(a, b) => match (a.resolve(args, results), b.resolve(args, results)) {
                (Some(x), Some(y)) => x != y,
                _ => false,
            },
            Guard::Clear { step, mask } => {
                matches!(results.get(step), Some(Ok(Ret::Int(v))) if v & mask == 0)
            }
        }
    }
}

/// A step the real function makes only where `guard` holds; elsewhere it is
/// skipped (no event, the host unchanged) and its result is
/// `Ok(Int(otherwise))`, which later steps read in its place.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct When {
    pub guard: Guard,
    pub otherwise: Operand,
}

/// The branch of the real function a program is, checked once its step is
/// made (or skipped): [`run`] refuses a run where `guard` does not hold, as
/// `Refusal::Unmodeled` naming `what`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Assumed {
    pub guard: Guard,
    pub what: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramStep {
    pub actor: Actor,
    pub call: Call<Operand>,
    pub oracle: Oracle,
    /// Made only where its guard holds ([`When`]); `None`: always made.
    pub when: Option<When>,
    /// What the program assumes after this step ([`Assumed`]).
    pub assume: Option<Assumed>,
}

impl ProgramStep {
    #[must_use]
    pub fn root(call: Call<Operand>) -> ProgramStep {
        ProgramStep::by(Actor::Root, call)
    }

    #[must_use]
    pub fn by(actor: Actor, call: Call<Operand>) -> ProgramStep {
        ProgramStep { actor, call, oracle: Oracle::Nominal, when: None, assume: None }
    }

    #[must_use]
    pub fn with_oracle(mut self, oracle: Oracle) -> ProgramStep {
        self.oracle = oracle;
        self
    }

    /// Made only where `guard` holds, else skipped with `otherwise` as its
    /// result.
    #[must_use]
    pub fn when(mut self, guard: Guard, otherwise: Operand) -> ProgramStep {
        self.when = Some(When { guard, otherwise });
        self
    }

    /// The program is the branch where `guard` holds after this step.
    #[must_use]
    pub fn assuming(mut self, guard: Guard, what: &'static str) -> ProgramStep {
        self.assume = Some(Assumed { guard, what });
        self
    }

    /// Whether the step branches ([`When`] or [`Assumed`]): a consumer that
    /// only lowers straight-line programs must refuse one that does.
    #[must_use]
    pub fn branches(&self) -> bool {
        self.when.is_some() || self.assume.is_some()
    }

    /// Step `step`'s skip ([`When`]): `Ok(None)` when it is made, `Ok(Some(v))`
    /// when it is skipped with result `Ok(Int(v))`.
    pub fn skipped(
        &self,
        step: usize,
        args: &[i32],
        results: &[SysResult],
    ) -> Result<Option<i32>, ProgramError> {
        match self.when {
            Some(w) if !w.guard.holds(args, results) => w
                .otherwise
                .resolve(args, results)
                .map(Some)
                .ok_or(ProgramError::Unresolved { step }),
            _ => Ok(None),
        }
    }

    /// Step `step`'s [`Assumed`], against the results INCLUDING its own.
    pub fn check_assumed(
        &self,
        step: usize,
        args: &[i32],
        results: &[SysResult],
    ) -> Result<(), ProgramError> {
        match self.assume {
            Some(a) if !a.guard.holds(args, results) => Err(ProgramError::Refused {
                step,
                refusal: Refusal::Unmodeled {
                    symbol: self.call.symbol(),
                    detail: format!(
                        "the summary assumes {} ({:?}); the real function takes another branch \
                         here, which it does not describe",
                        a.what, a.guard
                    ),
                },
            }),
            _ => Ok(()),
        }
    }
}

pub type Program = Vec<ProgramStep>;

/// One evaluated step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Traced {
    pub pid: Pid,
    pub call: Call,
    pub result: SysResult,
    pub host: Host,
}

/// Why a program could not be evaluated to the end.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramError {
    /// Step `step`'s operand names a result that failed or does not exist.
    Unresolved { step: usize },
    /// Step `step`'s actor is not a process the program created.
    BadActor { step: usize },
    /// The semantics declined step `step`.
    Refused { step: usize, refusal: Refusal },
}

impl Operand {
    /// Resolve against the program's arguments and earlier results.
    #[must_use]
    pub fn resolve(&self, args: &[i32], results: &[SysResult]) -> Option<i32> {
        match *self {
            Operand::Lit(v) => Some(v),
            Operand::Arg(i) => args.get(i).copied(),
            Operand::Ret { step, comp } => results.get(step)?.as_ref().ok()?.component(comp),
        }
    }
}

/// The pid `actor` denotes, given the root and the results so far.
#[must_use]
pub fn actor_pid(actor: Actor, root: Pid, results: &[SysResult]) -> Option<Pid> {
    match actor {
        Actor::Root => Some(root),
        Actor::Child(k) => {
            let raw = results.get(k)?.as_ref().ok()?.component(0)?;
            u32::try_from(raw).ok().map(Pid)
        }
    }
}

/// Evaluate `program` from `host`, with `root` as [`Actor::Root`].
pub fn run<S: Semantics + ?Sized>(
    sem: &S,
    host: &Host,
    root: Pid,
    program: &[ProgramStep],
    args: &[i32],
) -> Result<Vec<Traced>, ProgramError> {
    let mut h = host.clone();
    let mut results: Vec<SysResult> = Vec::with_capacity(program.len());
    let mut trace = Vec::with_capacity(program.len());
    for (i, ps) in program.iter().enumerate() {
        let pid = actor_pid(ps.actor, root, &results).ok_or(ProgramError::BadActor { step: i })?;
        if let Some(v) = ps.skipped(i, args, &results)? {
            let result = Ok(Ret::Int(i64::from(v)));
            let call = ps.call.map(|op| op.resolve(args, &results).unwrap_or(-1));
            results.push(result);
            trace.push(Traced { pid, call, result, host: h.clone() });
            ps.check_assumed(i, args, &results)?;
            continue;
        }
        let mut unresolved = false;
        let call = ps.call.map(|op| {
            op.resolve(args, &results).unwrap_or_else(|| {
                unresolved = true;
                -1
            })
        });
        if unresolved {
            return Err(ProgramError::Unresolved { step: i });
        }
        let mut step = sem
            .step(&h, pid, &call, ps.oracle)
            .map_err(|refusal| ProgramError::Refused { step: i, refusal })?;
        // A straight-line program has no other thread: a call that has not
        // returned (`Ret::Pending`) is continued at once, and one that still
        // waits then is refused (`Blocks`).
        while let Ok(Ret::Pending { fd }) = step.result {
            step = sem
                .step(&step.host, pid, &Call::Resume { fd }, Oracle::Nominal)
                .map_err(|refusal| ProgramError::Refused { step: i, refusal })?;
        }
        h = step.host.clone();
        results.push(step.result);
        trace.push(Traced { pid, call, result: step.result, host: step.host });
        ps.check_assumed(i, args, &results)?;
    }
    Ok(trace)
}
