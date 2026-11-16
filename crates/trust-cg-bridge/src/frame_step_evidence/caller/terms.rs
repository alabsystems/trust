// Copyright 2026 Andrew Yates | Apache-2.0
use std::collections::BTreeMap;

use clean_kernel::{Expr, FVarId, Level, Name};
use trust_types::{Formula, Sort};

use super::super::terms::{self as t, Binder, a, c, close, eq, mem, n, render};
use super::binding::CallerTrace;

fn and_goals(items: &[Expr]) -> Result<Expr, String> {
    match items {
        [single] => Ok(single.clone()),
        [first, rest @ ..] => Ok(a("And", [first.clone(), and_goals(rest)?])),
        [] => Err("empty caller conjunction".into()),
    }
}
fn and_proofs(goals: &[Expr], proofs: &[Expr]) -> Result<Expr, String> {
    match (goals, proofs) {
        ([_], [single]) => Ok(single.clone()),
        ([first, rest @ ..], [proof, more @ ..]) => Ok(a(
            "And.intro",
            [first.clone(), and_goals(rest)?, proof.clone(), and_proofs(rest, more)?],
        )),
        _ => Err("caller conjunction/proof census".into()),
    }
}
fn read(memory: Expr, address: Expr) -> Expr {
    mem("FrameCaller.effectRead64", [memory, address])
}
fn bv() -> Expr {
    a("BitVec", [n(64)])
}
fn add(left: Expr, right: Expr) -> Expr {
    a("BitVec.add", [n(64), left, right])
}
fn lit(value: u64) -> Expr {
    a("BitVec.ofNat", [n(64), n(value)])
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
    model_goal: Expr,
    model_parts: Vec<Expr>,
    model_arguments: Vec<Expr>,
    equations: Vec<Equation>,
}
impl Goal {
    fn produce_with(&self, args: Vec<Expr>) -> Result<Expr, String> {
        let mut goals = vec![self.core.clone(), self.model_goal.clone()];
        goals.extend(self.equations.iter().map(Equation::goal));
        let mut model = mem("FrameCaller.save_call_restore", self.model_arguments.clone());
        for index in 0..3 {
            model = a(
                "And.right",
                [
                    self.model_parts[index].clone(),
                    and_goals(&self.model_parts[index + 1..])?,
                    model,
                ],
            );
        }
        let mut proofs = vec![mem("FrameCaller.save_call_restore", args), model];
        proofs.extend(self.equations.iter().map(Equation::proof));
        Ok(close(and_proofs(&goals, &proofs)?, &self.binders, true))
    }
    pub fn produce(&self) -> Result<Expr, String> {
        t::require_production();
        self.produce_with(self.arguments.clone())
    }
    #[cfg(test)]
    pub fn bad_proof(&self, which: usize) -> Result<Expr, String> {
        let mut args = self.arguments.clone();
        match which {
            0 => args.swap(7, 8),
            1 => args[6] = add(args[6].clone(), lit(16)),
            2 => args[18] = c("True.intro"),
            _ => return Ok(c("True.intro")),
        };
        self.produce_with(args)
    }
}

pub(super) fn build(trace: &CallerTrace<'_>) -> Result<Goal, String> {
    let mut values: Vec<&Formula> = Vec::new();
    for value in [
        &trace.entry.sp,
        &trace.entry.gpr[29],
        &trace.entry.gpr[30],
        &trace.entry.memory,
        &trace.save_after.sp,
        &trace.save_after.memory,
        &trace.call_before.sp,
        &trace.call_before.memory,
        &trace.modeled_after.sp,
        &trace.modeled_after.memory,
        &trace.restore_before.sp,
        &trace.restore_before.memory,
        &trace.restore_after.sp,
        &trace.restore_after.memory,
        &trace.restore_after.gpr[29],
        &trace.restore_after.gpr[30],
        &trace.return_before.sp,
        &trace.return_before.memory,
        &trace.return_target,
        trace.fresh_post,
    ] {
        if !values.iter().any(|old| *old == value) {
            values.push(value)
        }
    }
    let mut context = BTreeMap::new();
    let mut count = 0;
    for value in values {
        trust_types::check_formula_sort(value)
            .map_err(|e| format!("caller formula sort: {e:?}"))?;
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
    let sp = r(&trace.entry.sp)?;
    let fp = r(&trace.entry.gpr[29])?;
    let lr = r(&trace.entry.gpr[30])?;
    let raw = r(&trace.entry.memory)?;
    let fresh = r(trace.fresh_post)?;
    let modeled = r(&trace.modeled_after.memory)?;
    let modeled_sp = r(&trace.modeled_after.sp)?;
    let mut parameter = |ty: Expr| {
        let id = FVarId::new(binders.len() as u64);
        binders.push(Binder { id, ty });
        Expr::fvar(id)
    };
    let source_before = parameter(c("SemR.Mem"));
    let source_after = parameter(c("SemR.Mem"));
    let memory_before = parameter(c("TrustIr.Memory"));
    let memory_after = parameter(c("TrustIr.Memory"));
    let ids = parameter(Expr::arrow(c("Nat"), c("TrustIr.AllocId")));
    let frame = parameter(c("TrustIr.Allocation"));
    let raw_type = t::sort(&Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))))?;
    // Distinct unrestricted physical callee post-state. These are NOT the
    // modeled array/SP or an invented execution witness.
    let actual = parameter(raw_type.clone());
    let actual_sp = parameter(bv());
    let before_input = parameter(mem(
        "PlacedFrameInput",
        [
            source_before.clone(),
            memory_before.clone(),
            ids.clone(),
            frame.clone(),
            a("BitVec.toNat", [n(64), sp.clone()]),
            n(16),
        ],
    ));
    let after_input = parameter(mem(
        "PlacedFrameInput",
        [
            source_after.clone(),
            memory_after.clone(),
            ids.clone(),
            frame.clone(),
            a("BitVec.toNat", [n(64), sp.clone()]),
            n(16),
        ],
    ));
    let size = parameter(eq(c("Nat"), a("TrustIr.Allocation.size", [frame.clone()]), n(16)));
    let before_rep =
        parameter(mem("FramePair.RawRepresents", [memory_before.clone(), raw.clone()]));
    let after_rep =
        parameter(mem("FramePair.RawRepresents", [memory_after.clone(), fresh.clone()]));
    let call = parameter(mem(
        "FrameCaller.ActualCallAgreement",
        [actual.clone(), modeled.clone(), actual_sp.clone(), modeled_sp.clone()],
    ));
    let saved = |memory: Expr| {
        mem(
            "FramePair.saveMemory",
            [memory, a("TrustIr.Allocation.base", [frame.clone()]), fp.clone(), lr.clone()],
        )
    };
    let parts = |image: Expr, image_sp: Expr| {
        vec![
            mem("Embeds", [source_before.clone(), saved(memory_before.clone()), ids.clone()]),
            mem("Embeds", [source_after.clone(), saved(memory_after.clone()), ids.clone()]),
            mem("FramePair.RawRepresents", [saved(memory_after.clone()), image.clone()]),
            eq(bv(), read(image.clone(), image_sp.clone()), fp.clone()),
            eq(bv(), read(image.clone(), add(image_sp.clone(), lit(8))), lr.clone()),
            eq(bv(), add(image_sp, lit(16)), sp.clone()),
        ]
    };
    let core = and_goals(&parts(actual.clone(), actual_sp.clone()))?;
    let model_parts = parts(modeled.clone(), modeled_sp.clone());
    // These are the authentic modeled LDP outputs. The actual physical
    // restoration remains separately conditional on the supplied call relation.
    let model_goal = and_goals(&[
        eq(bv(), r(&trace.restore_after.gpr[29])?, fp.clone()),
        eq(bv(), r(&trace.restore_after.gpr[30])?, lr.clone()),
        eq(bv(), r(&trace.restore_after.sp)?, sp.clone()),
    ])?;
    let expected_save =
        mem("FrameStep.saveMemoryEffect", [raw.clone(), sp.clone(), fp.clone(), lr.clone()]);
    let expected_model =
        mem("FrameStep.saveMemoryEffect", [fresh.clone(), sp.clone(), fp.clone(), lr.clone()]);
    let save_sp = r(&trace.save_after.sp)?;
    let negative = a("BitVec.ofInt", [n(64), a("Int.negSucc", [n(15)])]);
    let mut equations = Vec::new();
    let mut memory_eq =
        |left: Expr, right: Expr| equations.push(Equation { ty: raw_type.clone(), left, right });
    memory_eq(r(&trace.save_after.memory)?, expected_save);
    memory_eq(r(&trace.call_before.memory)?, r(&trace.save_after.memory)?);
    memory_eq(r(&trace.restore_before.memory)?, modeled.clone());
    memory_eq(modeled.clone(), expected_model);
    memory_eq(r(&trace.restore_after.memory)?, modeled.clone());
    memory_eq(r(&trace.return_before.memory)?, r(&trace.restore_after.memory)?);
    let mut word_eq = |left: Expr, right: Expr| equations.push(Equation { ty: bv(), left, right });
    word_eq(save_sp.clone(), add(sp.clone(), negative));
    word_eq(r(&trace.call_before.sp)?, save_sp.clone());
    word_eq(r(&trace.restore_before.sp)?, modeled_sp.clone());
    word_eq(modeled_sp.clone(), save_sp);
    word_eq(r(&trace.restore_after.sp)?, add(r(&trace.restore_before.sp)?, lit(16)));
    word_eq(r(&trace.restore_after.gpr[29])?, read(modeled.clone(), r(&trace.restore_before.sp)?));
    word_eq(
        r(&trace.restore_after.gpr[30])?,
        read(modeled.clone(), add(r(&trace.restore_before.sp)?, lit(8))),
    );
    word_eq(r(&trace.return_before.sp)?, r(&trace.restore_after.sp)?);
    word_eq(r(&trace.return_target)?, r(&trace.restore_after.gpr[30])?);
    let mut goals = vec![core.clone(), model_goal.clone()];
    goals.extend(equations.iter().map(Equation::goal));
    let arguments = vec![
        source_before,
        source_after,
        memory_before,
        memory_after,
        ids,
        frame,
        sp,
        fp,
        lr,
        raw,
        fresh,
        actual,
        actual_sp,
        before_input,
        after_input,
        size,
        before_rep,
        after_rep,
        call,
    ];
    let refl = |ty: Expr, value: Expr| Equation { ty, left: value.clone(), right: value }.proof();
    let model_call = mem(
        "FrameCaller.ActualCallAgreement.mk",
        [
            modeled.clone(),
            modeled.clone(),
            modeled_sp.clone(),
            modeled_sp.clone(),
            refl(raw_type, modeled.clone()),
            refl(bv(), modeled_sp.clone()),
        ],
    );
    let mut model_arguments = arguments.clone();
    model_arguments[11] = modeled;
    model_arguments[12] = modeled_sp;
    model_arguments[18] = model_call;
    Ok(Goal {
        goal: close(and_goals(&goals)?, &binders, false),
        binders,
        arguments,
        core,
        model_goal,
        model_parts,
        model_arguments,
        equations,
    })
}

#[cfg(test)]
mod conjunction_tests {
    use super::*;

    // An empty or unequal caller conjunction is refused as an error, never a panic.
    #[test]
    fn empty_or_unequal_conjunctions_are_refused() {
        let (goal, proof) = (c("True"), c("True.intro"));
        assert_eq!(and_goals(&[]).unwrap_err(), "empty caller conjunction");
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
        assert_eq!(and_proofs(&[], &[]).unwrap_err(), "caller conjunction/proof census");
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
