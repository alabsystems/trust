// Copyright 2026 Andrew Yates | Apache-2.0
use std::collections::BTreeMap;

use clean_kernel::{BinderInfo, Expr, FVarId, Level, Name};
use trust_machine_sem::frame_pair::CheckedPairEffects;
use trust_types::{Formula, Sort};

const PREFIX: &str = "SemR.MemoryEmbedding.";
pub(super) fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
pub(super) fn a(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
pub(super) fn n(value: u64) -> Expr {
    Expr::nat_lit(value)
}
pub(super) fn mem(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    a(&format!("{PREFIX}{name}"), args)
}
pub(super) fn eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, lhs, rhs],
    )
}
pub(super) fn sort(ty: &Sort) -> Result<Expr, String> {
    match ty {
        Sort::BitVec(width) if matches!(*width, 8 | 32 | 64) => {
            Ok(a("BitVec", [n(u64::from(*width))]))
        }
        Sort::Array(i, v) if **i == Sort::BitVec(64) && **v == Sort::BitVec(8) => {
            Ok(Expr::arrow(sort(i)?, sort(v)?))
        }
        _ => Err("unsupported frame-step formula sort".into()),
    }
}
pub(super) fn collect(
    value: &Formula,
    vars: &mut BTreeMap<String, Sort>,
    count: &mut usize,
) -> Result<(), String> {
    *count += 1;
    if *count > 8192 {
        return Err("frame-step formula budget".into());
    }
    match value {
        Formula::Var(name, ty) => {
            let _ = sort(ty)?;
            if vars.len() >= 64 && !vars.contains_key(name) {
                return Err("frame-step variable budget".into());
            }
            if let Some(old) = vars.insert(name.clone(), ty.clone()) {
                if old != *ty {
                    return Err("variable sort collision".into());
                }
            }
        }
        Formula::BitVec { width, .. } if matches!(*width, 8 | 32 | 64) => {}
        Formula::BvAdd(l, r, _)
        | Formula::BvOr(l, r, _)
        | Formula::BvShl(l, r, _)
        | Formula::Select(l, r) => {
            collect(l, vars, count)?;
            collect(r, vars, count)?;
        }
        Formula::Store(m, i, v) => {
            collect(m, vars, count)?;
            collect(i, vars, count)?;
            collect(v, vars, count)?;
        }
        Formula::BvExtract { inner, .. } | Formula::BvZeroExt(inner, _) => {
            collect(inner, vars, count)?
        }
        _ => return Err("frame-step formula outside the exact store fragment".into()),
    }
    Ok(())
}
pub(super) fn render(value: &Formula, vars: &BTreeMap<String, FVarId>) -> Result<Expr, String> {
    Ok(match value {
        Formula::Var(name, _) => Expr::fvar(*vars.get(name).ok_or("unbound frame variable")?),
        Formula::BitVec { value, width } => {
            if *value >= 0 {
                a(
                    "BitVec.ofNat",
                    [
                        n(u64::from(*width)),
                        Expr::nat_lit(
                            u64::try_from(*value).map_err(|_| "large bitvector literal")?,
                        ),
                    ],
                )
            } else {
                a(
                    "BitVec.ofInt",
                    [
                        n(u64::from(*width)),
                        a(
                            "Int.negSucc",
                            [n(u64::try_from(-(*value + 1))
                                .map_err(|_| "large negative bitvector literal")?)],
                        ),
                    ],
                )
            }
        }
        Formula::BvAdd(l, r, width) => {
            a("BitVec.add", [n(u64::from(*width)), render(l, vars)?, render(r, vars)?])
        }
        Formula::BvOr(l, r, width) => {
            a("BitVec.or", [n(u64::from(*width)), render(l, vars)?, render(r, vars)?])
        }
        Formula::BvShl(l, r, width) => a(
            "BitVec.shiftLeft",
            [
                n(u64::from(*width)),
                render(l, vars)?,
                a("BitVec.toNat", [n(u64::from(*width)), render(r, vars)?]),
            ],
        ),
        Formula::BvZeroExt(inner, added) => {
            let Sort::BitVec(width) = trust_types::check_formula_sort(inner)
                .map_err(|e| format!("extension sort: {e:?}"))?
            else {
                return Err("non-BV extension".into());
            };
            let target = width.checked_add(*added).ok_or("extension width overflow")?;
            if !matches!(target, 8 | 32 | 64) {
                return Err("unsupported frame extension width".into());
            }
            a("BitVec.setWidth", [n(u64::from(width)), n(u64::from(target)), render(inner, vars)?])
        }
        Formula::Select(m, i) => Expr::app(render(m, vars)?, render(i, vars)?),
        Formula::Store(m, i, v) => {
            mem("FrameStep.arrayStore", [render(m, vars)?, render(i, vars)?, render(v, vars)?])
        }
        Formula::BvExtract { inner, high, low } => {
            let Sort::BitVec(width) = trust_types::check_formula_sort(inner)
                .map_err(|e| format!("extract sort: {e:?}"))?
            else {
                return Err("non-BV extract".into());
            };
            a(
                "BitVec.extractLsb'",
                [
                    n(u64::from(width)),
                    n(u64::from(*low)),
                    n(u64::from(high - low + 1)),
                    render(inner, vars)?,
                ],
            )
        }
        _ => return Err("unsupported frame-step expression".into()),
    })
}
pub(super) struct Binder {
    pub id: FVarId,
    pub ty: Expr,
}
pub(super) fn close(mut term: Expr, binders: &[Binder], proof: bool) -> Expr {
    for binder in binders.iter().rev() {
        let body = term.abstract_fvar(binder.id);
        term = if proof {
            Expr::lam(BinderInfo::Default, binder.ty.clone(), body)
        } else {
            Expr::pi(BinderInfo::Default, binder.ty.clone(), body)
        };
    }
    term
}

pub(super) struct Goal {
    pub goal: Expr,
    binders: Vec<Binder>,
    proof_arguments: Vec<Expr>,
}
impl Goal {
    pub fn produce(&self) -> Expr {
        #[cfg(test)]
        FORBID_PRODUCTION
            .with(|flag| assert!(!flag.get(), "proof production forbidden during replay"));
        close(mem("FrameStep.save_step", self.proof_arguments.clone()), &self.binders, true)
    }
}

pub(super) fn build(step: &CheckedPairEffects<'_>) -> Result<Goal, String> {
    use trust_machine_sem::frame_pair::PairRole;
    if step.role() != PairRole::Save {
        return Err("first checked step fragment is FP/LR save".into());
    }
    let pre = step.pre();
    let post = step.post();
    let mut context = BTreeMap::new();
    let mut count = 0;
    for value in [&pre.sp, &pre.gpr[29], &pre.gpr[30], &pre.memory, &post.memory, &post.sp] {
        trust_types::check_formula_sort(value).map_err(|e| format!("formula sort: {e:?}"))?;
        collect(value, &mut context, &mut count)?;
    }
    let mut vars = BTreeMap::new();
    let mut binders = Vec::new();
    for (name, ty) in context {
        let id = FVarId::new(binders.len() as u64);
        vars.insert(name, id);
        binders.push(Binder { id, ty: sort(&ty)? });
    }
    let sp = render(&pre.sp, &vars)?;
    let fp = render(&pre.gpr[29], &vars)?;
    let lr = render(&pre.gpr[30], &vars)?;
    let raw = render(&pre.memory, &vars)?;
    let output = render(&post.memory, &vars)?;
    let output_sp = render(&post.sp, &vars)?;
    let mut new_var = |ty: Expr| {
        let id = FVarId::new(binders.len() as u64);
        binders.push(Binder { id, ty });
        Expr::fvar(id)
    };
    let source = new_var(c("SemR.Mem"));
    let memory = new_var(c("TrustIr.Memory"));
    let ids = new_var(Expr::arrow(c("Nat"), c("TrustIr.AllocId")));
    let frame = new_var(c("TrustIr.Allocation"));
    let placement = new_var(mem(
        "PlacedFrameInput",
        [
            source.clone(),
            memory.clone(),
            ids.clone(),
            frame.clone(),
            a("BitVec.toNat", [n(64), sp.clone()]),
            n(16),
        ],
    ));
    let size = new_var(eq(c("Nat"), a("TrustIr.Allocation.size", [frame.clone()]), n(16)));
    let represented = new_var(mem("FramePair.RawRepresents", [memory.clone(), raw.clone()]));
    let canonical = mem(
        "FramePair.saveMemory",
        [memory.clone(), a("TrustIr.Allocation.base", [frame.clone()]), fp.clone(), lr.clone()],
    );
    let conclusion = a(
        "And",
        [
            mem("Embeds", [source.clone(), canonical.clone(), ids.clone()]),
            a(
                "And",
                [
                    mem("FramePair.RawRepresents", [canonical, output]),
                    eq(
                        a("BitVec", [n(64)]),
                        output_sp,
                        a("BitVec.ofNat", [n(64), a("TrustIr.Allocation.base", [frame.clone()])]),
                    ),
                ],
            ),
        ],
    );
    let proof_arguments =
        vec![source, memory, ids, frame, sp, fp, lr, raw, placement, size, represented];
    Ok(Goal { goal: close(conclusion, &binders, false), binders, proof_arguments })
}

#[cfg(test)]
thread_local! {static FORBID_PRODUCTION:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};}
#[cfg(test)]
pub(super) fn forbid_production<T>(f: impl FnOnce() -> T) -> T {
    struct Reset(bool);
    impl Drop for Reset {
        fn drop(&mut self) {
            FORBID_PRODUCTION.with(|flag| flag.set(self.0));
        }
    }
    let prior = FORBID_PRODUCTION.with(|flag| flag.replace(true));
    let _reset = Reset(prior);
    f()
}
#[cfg(test)]
impl Goal {
    pub(super) fn bad_proof(&self, mutation: usize) -> Expr {
        let mut args = self.proof_arguments.clone();
        match mutation {
            0 => args.swap(5, 6),
            1 => {
                args[4] =
                    a("BitVec.add", [n(64), args[4].clone(), a("BitVec.ofNat", [n(64), n(16)])])
            }
            _ => return c("True.intro"),
        };
        close(mem("FrameStep.save_step", args), &self.binders, true)
    }
}

pub(super) fn require_production() {
    #[cfg(test)]
    FORBID_PRODUCTION.with(|flag| assert!(!flag.get(), "proof production forbidden during replay"));
    #[cfg(test)]
    crate::original_conjunction_certificate::require_production_allowed();
}
