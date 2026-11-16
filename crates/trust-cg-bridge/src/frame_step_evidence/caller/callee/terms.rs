// Copyright 2026 Andrew Yates | Apache-2.0
use std::collections::BTreeMap;

use clean_kernel::{Expr, FVarId, Level, Name};
use trust_types::{Formula, Sort};

use super::super::super::terms::{self as t, Binder, a, c, close, eq, mem, n, render};
use super::binding::CalleeTrace;

fn and_goals(goals: &[Expr]) -> Result<Expr, String> {
    match goals {
        [goal] => Ok(goal.clone()),
        [first, rest @ ..] => Ok(a("And", [first.clone(), and_goals(rest)?])),
        [] => Err("empty callee goal".into()),
    }
}

fn and_proofs(goals: &[Expr], proofs: &[Expr]) -> Result<Expr, String> {
    match (goals, proofs) {
        ([_], [proof]) => Ok(proof.clone()),
        ([first, rest @ ..], [proof, more @ ..]) => Ok(a(
            "And.intro",
            [first.clone(), and_goals(rest)?, proof.clone(), and_proofs(rest, more)?],
        )),
        _ => Err("callee goal/proof census".into()),
    }
}

struct Equation {
    ty: Expr,
    left: Expr,
    right: Expr,
}

impl Equation {
    fn goal(&self) -> Expr {
        eq(self.ty.clone(), self.left.clone(), self.right.clone())
    }

    fn proof(&self) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [self.ty.clone(), self.left.clone()],
        )
    }
}

pub(super) struct Goal {
    pub goal: Expr,
    binders: Vec<Binder>,
    arguments: Vec<Expr>,
    core: Expr,
    equations: Vec<Equation>,
}

impl Goal {
    fn produce_with(&self, arguments: Vec<Expr>) -> Result<Expr, String> {
        let mut goals = vec![self.core.clone()];
        goals.extend(self.equations.iter().map(Equation::goal));
        let mut proofs = vec![mem("FrameCaller.separate_store_agreement", arguments)];
        proofs.extend(self.equations.iter().map(Equation::proof));
        Ok(close(and_proofs(&goals, &proofs)?, &self.binders, true))
    }

    pub fn produce(&self) -> Result<Expr, String> {
        t::require_production();
        self.produce_with(self.arguments.clone())
    }

    #[cfg(test)]
    pub fn bad_proof(&self, which: usize) -> Result<Expr, String> {
        let mut arguments = self.arguments.clone();
        match which {
            0 => arguments[6] = c("True.intro"),
            1 => arguments.swap(2, 3),
            2 => {
                arguments[4] = a(
                    "BitVec.add",
                    [
                        n(64),
                        arguments[1].clone(),
                        a("BitVec.ofInt", [n(64), a("Int.negSucc", [n(7)])]),
                    ],
                )
            }
            _ => return Ok(c("True.intro")),
        }
        self.produce_with(arguments)
    }
}

pub(super) fn build(trace: &CalleeTrace) -> Result<Goal, String> {
    let values = [
        &trace.entry.memory,
        &trace.entry.sp,
        &trace.entry.gpr[29],
        &trace.entry.gpr[30],
        &trace.before.memory,
        &trace.before.sp,
        &trace.before.gpr[29],
        &trace.before.gpr[30],
        &trace.after.memory,
        &trace.after.sp,
        &trace.after.gpr[29],
        &trace.after.gpr[30],
        &trace.destination,
        &trace.byte,
        &trace.call_return,
        &trace.return_target,
    ];
    let mut context = BTreeMap::new();
    let mut count = 0;
    for value in values {
        trust_types::check_formula_sort(value)
            .map_err(|error| format!("callee formula sort: {error:?}"))?;
        t::collect(value, &mut context, &mut count)?;
    }
    let mut variables = BTreeMap::new();
    let mut binders = Vec::new();
    for (name, sort) in context {
        let id = FVarId::new(binders.len() as u64);
        variables.insert(name, id);
        binders.push(Binder { id, ty: t::sort(&sort)? });
    }
    let r = |value: &Formula| render(value, &variables);
    let raw = r(&trace.entry.memory)?;
    let sp = r(&trace.entry.sp)?;
    let fp = r(&trace.entry.gpr[29])?;
    let lr = r(&trace.entry.gpr[30])?;
    let destination = r(&trace.destination)?;
    let byte = r(&trace.byte)?;
    let id = FVarId::new(binders.len() as u64);
    binders.push(Binder {
        id,
        ty: mem("FrameCaller.SeparateFrameStore", [sp.clone(), destination.clone()]),
    });
    let separate = Expr::fvar(id);
    let saved =
        mem("FrameStep.saveMemoryEffect", [raw.clone(), sp.clone(), fp.clone(), lr.clone()]);
    let after = r(&trace.after.memory)?;
    let base_after = mem("FrameStep.arrayStore", [raw.clone(), destination.clone(), byte.clone()]);
    let modeled =
        mem("FrameStep.saveMemoryEffect", [base_after, sp.clone(), fp.clone(), lr.clone()]);
    let frame_sp =
        a("BitVec.add", [n(64), sp.clone(), a("BitVec.ofInt", [n(64), a("Int.negSucc", [n(15)])])]);
    let core = mem(
        "FrameCaller.ActualCallAgreement",
        [after.clone(), modeled, r(&trace.after.sp)?, frame_sp.clone()],
    );
    let memory_type = t::sort(&Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))))?;
    let word = a("BitVec", [n(64)]);
    let equations = vec![
        Equation { ty: memory_type.clone(), left: r(&trace.before.memory)?, right: saved.clone() },
        Equation {
            ty: memory_type,
            left: after,
            right: mem("FrameStep.arrayStore", [saved, destination.clone(), byte.clone()]),
        },
        Equation { ty: word.clone(), left: r(&trace.before.sp)?, right: frame_sp },
        Equation { ty: word.clone(), left: r(&trace.after.sp)?, right: r(&trace.before.sp)? },
        Equation {
            ty: word.clone(),
            left: r(&trace.after.gpr[29])?,
            right: r(&trace.before.gpr[29])?,
        },
        Equation {
            ty: word.clone(),
            left: r(&trace.after.gpr[30])?,
            right: r(&trace.call_return)?,
        },
        Equation { ty: word, left: r(&trace.return_target)?, right: r(&trace.call_return)? },
    ];
    let mut goals = vec![core.clone()];
    goals.extend(equations.iter().map(Equation::goal));
    Ok(Goal {
        goal: close(and_goals(&goals)?, &binders, false),
        binders,
        arguments: vec![raw, sp, fp, lr, destination, byte, separate],
        core,
        equations,
    })
}

#[cfg(test)]
mod conjunction_tests {
    use super::*;

    // An empty or unequal callee conjunction is refused as an error, never a panic.
    #[test]
    fn empty_or_unequal_conjunctions_are_refused() {
        let (goal, proof) = (c("True"), c("True.intro"));
        assert_eq!(and_goals(&[]).unwrap_err(), "empty callee goal");
        for (goals, proofs) in [
            (vec![], vec![]),
            (vec![goal.clone()], vec![]),
            (vec![], vec![proof.clone()]),
            (vec![goal.clone()], vec![proof.clone(), proof.clone()]),
            (vec![goal.clone(), goal.clone()], vec![proof.clone()]),
        ] {
            assert!(
                and_proofs(&goals, &proofs).is_err(),
                "{} goals, {} proofs",
                goals.len(),
                proofs.len()
            );
        }
        assert_eq!(and_proofs(&[], &[]).unwrap_err(), "callee goal/proof census");
        assert_eq!(and_goals(std::slice::from_ref(&goal)).unwrap(), goal);
        assert_eq!(
            and_goals(&[goal.clone(), goal.clone()]).unwrap(),
            a("And", [goal.clone(), goal.clone()])
        );
        assert_eq!(
            and_proofs(&[goal.clone(), goal.clone()], &[proof.clone(), proof.clone()]).unwrap(),
            a("And.intro", [goal.clone(), goal, proof.clone(), proof])
        );
    }
}
