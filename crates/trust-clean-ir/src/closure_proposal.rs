//! Untrusted, bounded CIC-to-typed-closure proposal construction.
//!
//! Nothing in this module is a semantic checker. The caller must retain the
//! exact accepted context and complete owned roster separately. A successful
//! producer only supplies candidate Module DATA for a future Lean relation.

use std::collections::BTreeSet;

use clean_kernel::env::{ConstantInfo, ConstantKind, Environment};
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;
use trust_ir::ty::{ClosureTy, Ty};
use trust_ir::value::{ClosureTyId, FuncId, FuncTyId, ValueId};
use trust_ir::{BodyGate, CallingConv, Module};
use trust_ir_build::builder::{FunctionBuilder, ModuleBuilder};

/// An exact source payload and its proposed generated function association.
#[derive(Clone, Debug)]
pub struct OriginalFunction {
    pub constant: ConstantInfo,
    pub function: FuncId,
    pub role: &'static str,
}

/// Source applications whose type/instance prefix the producer proposes erasing.
/// The complete original Expr remains here; no erasure theorem is asserted.
#[derive(Clone, Debug)]
pub struct ArithmeticProposal {
    pub owner: Name,
    pub source: Expr,
    pub erased_prefix: Vec<Expr>,
    pub result: ValueId,
    pub operation: &'static str,
}

#[derive(Clone, Debug)]
pub struct TypedClosureProposal {
    pub module: Module,
    pub originals: Vec<OriginalFunction>,
    pub lifted_owner: Name,
    pub lifted_function: FuncId,
    pub closure_type: ClosureTyId,
    pub apparent_signature: FuncTyId,
    /// Maker parameter indices, in declaration order. Only live values occur.
    pub captures: Vec<usize>,
    pub maker_supplied: usize,
    pub arithmetic: Vec<ArithmeticProposal>,
}

fn strip(mut e: &Expr) -> &Expr {
    while let ExprKind::MData(_, inner) = e.kind() {
        e = inner;
    }
    e
}

fn lambdas(mut e: &Expr) -> Result<(Vec<Expr>, &Expr), String> {
    let mut types = Vec::new();
    loop {
        match strip(e).kind() {
            ExprKind::Lam(_, ty, body) if types.len() < 16 => {
                types.push((**ty).clone());
                e = body;
            }
            ExprKind::Lam(..) => return Err("candidate lambda bound".into()),
            _ => return Ok((types, strip(e))),
        }
    }
}

fn uint64(e: &Expr) -> bool {
    matches!(strip(e).kind(), ExprKind::Const(n, levels)
        if *n == Name::from_string("UInt64") && levels.is_empty())
}

fn arrow(e: &Expr) -> bool {
    matches!(strip(e).kind(), ExprKind::Pi(_, a, b) if uint64(a) && uint64(b))
}

fn variable(locals: &[ValueId], e: &Expr) -> Result<ValueId, String> {
    let ExprKind::BVar(index) = strip(e).kind() else {
        return Err("candidate requires a source variable".into());
    };
    locals.get(*index as usize).copied().ok_or("candidate unbound variable".into())
}

fn named_call(e: &Expr) -> Result<(Name, Vec<&Expr>), String> {
    let e = strip(e);
    let ExprKind::Const(name, levels) = strip(e.get_app_fn()).kind() else {
        return Err("candidate requires a named source call".into());
    };
    if !levels.is_empty() {
        return Err("candidate does not specialize polymorphic source calls".into());
    }
    Ok((name.clone(), e.get_app_args().into_iter().collect()))
}

fn definition<'a>(env: &'a Environment, name: &Name) -> Result<&'a ConstantInfo, String> {
    let c = env.get_const(name).ok_or_else(|| format!("missing source definition {name}"))?;
    if c.kind != ConstantKind::Definition || !c.level_params.is_empty() || c.value.is_none() {
        return Err(format!("unsupported source definition {name}"));
    }
    Ok(c)
}

fn entry(f: &mut FunctionBuilder<'_>, types: &[Ty]) -> Vec<ValueId> {
    f.set_calling_conv(CallingConv::Rust);
    f.set_body_gate(BodyGate::Ungated);
    let block = f.create_block();
    let values = types.iter().map(|ty| f.add_block_param(block, ty.clone())).collect();
    f.switch_to_block(block);
    values
}

/// Proposed arithmetic is derived from the actual application tree. Its
/// retained prefix is DATA, not a Rust validation of Prelude/erasure semantics.
fn arithmetic(
    f: &mut FunctionBuilder<'_>,
    locals: &[ValueId],
    e: &Expr,
    owner: &Name,
    rows: &mut Vec<ArithmeticProposal>,
    budget: &mut usize,
    used: &mut BTreeSet<usize>,
) -> Result<ValueId, String> {
    *budget = budget.checked_sub(1).ok_or("candidate arithmetic node bound")?;
    let e = strip(e);
    if let ExprKind::BVar(index) = e.kind() {
        used.insert(*index as usize);
        return variable(locals, e);
    }
    let args: Vec<_> = e.get_app_args().into_iter().collect();
    let ExprKind::Const(head, _) = strip(e.get_app_fn()).kind() else {
        return Err("unsupported candidate arithmetic head".into());
    };
    let operation = [
        (["HAdd.hAdd", "UInt64.add"], "Add"),
        (["HSub.hSub", "UInt64.sub"], "Sub"),
        (["HMul.hMul", "UInt64.mul"], "Mul"),
    ]
    .into_iter()
    .find_map(|(names, op)| names.iter().any(|s| *head == Name::from_string(s)).then_some(op))
    .ok_or_else(|| format!("unsupported candidate arithmetic head {head}"))?;
    let split = args.len().checked_sub(2).ok_or("candidate arithmetic arity")?;
    // An untrusted grammar bound, not a proof of the named instance's meaning.
    // Do not silently discard an arbitrary dictionary that can itself capture
    // source values. The future Lean relation must justify even these exact
    // retained Prelude/type arguments against the actual accepted environment.
    let direct = *head == Name::from_string(&format!("UInt64.{}", operation.to_lowercase()));
    if direct {
        if split != 0 {
            return Err("candidate direct arithmetic prefix unsupported".into());
        }
    } else {
        let instance = Name::from_string(&format!("instH{operation}UInt64"));
        if split != 4
            || !args[..3].iter().all(|ty| uint64(ty))
            || !matches!(strip(args[3]).kind(), ExprKind::Const(name, levels)
                if *name == instance && levels.is_empty())
        {
            return Err("candidate arithmetic dictionary/type prefix unsupported".into());
        }
    }
    let left = arithmetic(f, locals, args[split], owner, rows, budget, used)?;
    let right = arithmetic(f, locals, args[split + 1], owner, rows, budget, used)?;
    let result = match operation {
        "Add" => f.add(Ty::U64, left, right),
        "Sub" => f.sub(Ty::U64, left, right),
        "Mul" => f.mul(Ty::U64, left, right),
        _ => return Err("unsupported proposed operation".into()),
    };
    rows.push(ArithmeticProposal {
        owner: owner.clone(),
        source: e.clone(),
        erased_prefix: args[..split].iter().map(|e| (*e).clone()).collect(),
        result,
        operation,
    });
    Ok(result)
}

/// Construct an untrusted candidate for a bounded maker/application/caller
/// family. The owned set is a full denominator, never a reachable-name filter.
/// A success is not source faithfulness, structural validation or permission.
pub fn propose(
    env: &Environment,
    owned: &BTreeSet<Name>,
    selected: &Name,
) -> Result<TypedClosureProposal, String> {
    if owned.len() != 3 || !owned.contains(selected) {
        return Err(
            "typed closure candidate requires exactly three complete owned definitions".into()
        );
    }
    let caller = definition(env, selected)?;
    let (caller_types, caller_body) = lambdas(caller.value.as_ref().ok_or("caller body absent")?)?;
    if caller_types.is_empty() || !caller_types.iter().all(uint64) {
        return Err("candidate caller parameters must be UInt64".into());
    }
    let ExprKind::Let(_, held_type, maker_call, apply_call, _) = caller_body.kind() else {
        return Err("candidate caller must retain its returned function let".into());
    };
    if !arrow(held_type) {
        return Err("candidate returned function must be UInt64 -> UInt64".into());
    }
    let (maker_name, maker_args) = named_call(maker_call)?;
    let (apply_name, apply_args) = named_call(apply_call)?;
    let roles: BTreeSet<_> = [selected.clone(), maker_name.clone(), apply_name.clone()].into();
    if roles.len() != 3 || &roles != owned {
        return Err("candidate discovered calls do not cover the complete owned roster".into());
    }
    let maker = definition(env, &maker_name)?;
    let application = definition(env, &apply_name)?;
    let (maker_types, maker_body) = lambdas(maker.value.as_ref().ok_or("maker body absent")?)?;
    let supplied = maker_args.len();
    if supplied == 0
        || supplied > 8
        || maker_types.len() != supplied + 1
        || !maker_types.iter().all(uint64)
    {
        return Err("candidate maker staging or UInt64 parameters unsupported".into());
    }
    let (apply_types, apply_body) =
        lambdas(application.value.as_ref().ok_or("application body absent")?)?;
    if apply_types.len() != 2 || !arrow(&apply_types[0]) || !uint64(&apply_types[1]) {
        return Err("candidate application helper signature unsupported".into());
    }
    let ExprKind::App(function, argument) = apply_body.kind() else {
        return Err("candidate application helper must apply its function parameter".into());
    };
    if !matches!(strip(function).kind(), ExprKind::BVar(1)) {
        return Err("candidate application must retain its dynamic function parameter".into());
    }
    // Discover live captures from the genuine body before constructing its
    // final lifted IR parameter list. This scratch proposal is discarded DATA.
    let mut scratch = ModuleBuilder::new("closure-capture-discovery-data");
    let signature = scratch.add_func_type(vec![Ty::U64; maker_types.len()], vec![Ty::U64]);
    let mut probe = scratch.function("probe", signature);
    let values = entry(&mut probe, &vec![Ty::U64; maker_types.len()]);
    let mut used = BTreeSet::new();
    arithmetic(
        &mut probe,
        &values.into_iter().rev().collect::<Vec<_>>(),
        maker_body,
        &maker_name,
        &mut Vec::new(),
        &mut 64,
        &mut used,
    )?;
    let captures: Vec<_> = (0..supplied).filter(|i| used.contains(&(supplied - i))).collect();
    let mut builder = ModuleBuilder::new("untrusted-accepted-cic-typed-closure-candidate");
    let apparent = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let closure = builder
        .add_closure_type(ClosureTy { func: apparent, captures: vec![Ty::U64; captures.len()] });
    let caller_sig = builder.add_func_type(vec![Ty::U64; caller_types.len()], vec![Ty::U64]);
    let maker_sig = builder.add_func_type(vec![Ty::U64; supplied], vec![Ty::Closure(closure)]);
    let app_sig = builder.add_func_type(vec![Ty::Closure(closure), Ty::U64], vec![Ty::U64]);
    let target_sig = builder.add_func_type(vec![Ty::U64; captures.len() + 1], vec![Ty::U64]);
    let symbol = trust_clean_origin::symbol::declaration_symbol;
    let caller_id = builder.declare_function(symbol(selected), caller_sig);
    let maker_id = builder.declare_function(symbol(&maker_name), maker_sig);
    let application_id = builder.declare_function(symbol(&apply_name), app_sig);
    let lifted_name = maker_name.clone().str("__typed_closure_target");
    if owned.contains(&lifted_name) {
        return Err("candidate lifted identity collides with an original".into());
    }
    let target_id = builder.declare_function(symbol(&lifted_name), target_sig);
    let mut rows = Vec::new();
    {
        let mut f = builder.define_function(target_id).map_err(|e| format!("{e:?}"))?;
        let params = entry(&mut f, &vec![Ty::U64; captures.len() + 1]);
        let mut locals = vec![params[captures.len()]; supplied + 1];
        for (slot, source_index) in captures.iter().enumerate() {
            locals[supplied - source_index] = params[slot];
        }
        let result = arithmetic(
            &mut f,
            &locals,
            maker_body,
            &maker_name,
            &mut rows,
            &mut 64,
            &mut BTreeSet::new(),
        )?;
        f.ret(vec![result]);
        f.build();
    }
    {
        let mut f = builder.define_function(maker_id).map_err(|e| format!("{e:?}"))?;
        let params = entry(&mut f, &vec![Ty::U64; supplied]);
        let result =
            f.make_closure(closure, target_id, captures.iter().map(|i| params[*i]).collect());
        f.ret(vec![result]);
        f.build();
    }
    {
        let mut f = builder.define_function(application_id).map_err(|e| format!("{e:?}"))?;
        let params = entry(&mut f, &[Ty::Closure(closure), Ty::U64]);
        let x = arithmetic(
            &mut f,
            &[params[1], params[0]],
            argument,
            &apply_name,
            &mut rows,
            &mut 64,
            &mut BTreeSet::new(),
        )?;
        let result = f.call_indirect_cc(params[0], apparent, vec![x], CallingConv::Rust);
        f.ret(vec![result]);
        f.build();
    }
    {
        let mut f = builder.define_function(caller_id).map_err(|e| format!("{e:?}"))?;
        let params = entry(&mut f, &vec![Ty::U64; caller_types.len()]);
        let locals: Vec<_> = params.into_iter().rev().collect();
        let args = maker_args.iter().map(|e| variable(&locals, e)).collect::<Result<_, _>>()?;
        let held = f.call(maker_id, args);
        let mut locals = locals;
        locals.insert(0, held);
        let args =
            apply_args.iter().map(|e| variable(&locals, e)).collect::<Result<Vec<_>, _>>()?;
        if args.len() != 2 || args[0] != held {
            return Err("candidate application must consume the returned closure".into());
        }
        let result = f.call(application_id, args);
        f.ret(vec![result]);
        f.build();
    }
    Ok(TypedClosureProposal {
        module: builder.build().map_err(|e| format!("{e:?}"))?,
        originals: vec![
            OriginalFunction { constant: caller.clone(), function: caller_id, role: "caller" },
            OriginalFunction { constant: maker.clone(), function: maker_id, role: "maker" },
            OriginalFunction {
                constant: application.clone(),
                function: application_id,
                role: "application",
            },
        ],
        lifted_owner: maker_name,
        lifted_function: target_id,
        closure_type: closure,
        apparent_signature: apparent,
        captures,
        maker_supplied: supplied,
        arithmetic: rows,
    })
}

#[cfg(test)]
mod tests;
