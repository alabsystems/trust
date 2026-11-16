// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Candidate reflection for Lean calling Rust. This reader consumes actual SSA,
//! never a source plan or the emitter's call tree. Its output is an untrusted
//! term: it grants no gate token, purity, termination, ABI or callee identity
//! authority. Admission must separately bind the supplied names/signatures to
//! module-owned definitions and kernel-check the entire term in the live source
//! environment. Existing production gate targets are unchanged.
//! SSA bindings remain explicit CIC lets; kernel normalization is not evidence
//! of execution order or once-evaluation. The separate source trace check
//! compares those properties without granting permission.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use clean_kernel::name::NameInner;
use clean_kernel::{BinderInfo, Environment, Expr, Name, TypeChecker};
use trust_clean_carrier::CleanType;
use trust_clean_origin::{CleanOriginPlan, CleanOriginShape};
use trust_ir::ty::FuncTy;
use trust_ir::value::{FuncId, ValueId};
use trust_ir::{CallingConv, Constant, Function, Inst, Module, Producer, Ty};

use crate::{GateRefusal, UIntCarrier};

mod call_trace;

const MAX_PARAMETERS: usize = 64;
const MAX_INTERPRETATIONS: usize = 32;
const MAX_APPLICATIONS: usize = 256;

/// A caller-supplied interpretation, not an authenticated Rust definition.
pub struct CalleeInterpretation {
    pub id: FuncId,
    pub name: Name,
    pub signature: FuncTy,
}

/// A source roster index paired with an actual module function. This data
/// does not authenticate the compiler registry that supplied either identity.
#[derive(Clone, Copy)]
pub struct RustCallBinding {
    pub plan_index: usize,
    pub function: FuncId,
}

/// Retain the immutable source snapshot across deferred module assembly.
/// Cloning shares the environment and plan; it never clones a proof token.
/// Construction is deliberately data-only and grants no admission permission.
#[derive(Clone)]
pub struct RetainedRustCallSource {
    environment: Arc<Environment>,
    plan: Arc<CleanOriginPlan>,
}

impl RetainedRustCallSource {
    /// Keep the exact supplied snapshot, without asserting that this pair is
    /// checked or belongs to any compiler session or source definition.
    pub fn retain(environment: Arc<Environment>, plan: Arc<CleanOriginPlan>) -> Self {
        Self { environment, plan }
    }

    /// The retained source plan, not a codegen permission.
    pub fn plan(&self) -> &CleanOriginPlan {
        &self.plan
    }

    /// Fingerprint this immutable source closure using the existing gate's
    /// environment reader. The fingerprint itself carries no authority.
    pub fn environment_binding(&self) -> Result<crate::GateEnvironment, GateRefusal> {
        crate::GateEnvironment::of(&self.environment, self.plan.declaration())
    }

    /// Compare source call evaluation with actual SSA, in addition to checking
    /// the kernel model. The source reader walks the original declaration,
    /// preserving let evaluation instead of performing kernel zeta reduction.
    /// The independent SSA reader records physical call order and operands.
    ///
    /// This bounded direct-call comparison returns no token or permission. It
    /// authenticates neither the supplied registry bindings nor Rust meaning,
    /// purity, termination, ABI or final code placement. It is not the separate
    /// kernel-TV companion required for production admission. Unsupported
    /// source helpers, reductions and control flow refuse rather than disappear.
    pub fn check_module_call_trace(
        &self,
        module: &Module,
        root: FuncId,
        bindings: &[RustCallBinding],
    ) -> Result<(), GateRefusal> {
        self.check_module_model(module, root, bindings)?;
        // The model check above validated these indices, names and complete
        // actual module signatures against the retained source roster.
        let interpretations = bindings
            .iter()
            .map(|binding| {
                let source = &self.plan.callees()[binding.plan_index];
                let function = module.function_by_id(binding.function).unwrap();
                CalleeInterpretation {
                    id: binding.function,
                    name: Name::from_string(&source.clean_name),
                    signature: module.func_types[function.ty.index() as usize].clone(),
                }
            })
            .collect::<Vec<_>>();
        call_trace::check(
            &self.environment,
            self.plan.declaration(),
            module,
            root,
            &interpretations,
        )
    }

    /// Check a candidate against the retained CIC declaration's call MODEL.
    ///
    /// Replanning authenticates the plan against this snapshot, not against a
    /// compiler registry. Bindings select source names/types only; the reader
    /// independently reconstructs every computational operand from actual IR.
    /// The kernel typechecks the complete term before comparing its body.
    ///
    /// Success returns no Faithful token, summary, gate stamp or permission.
    /// It establishes nothing about what a Rust callee returns, whether it
    /// returns, its effects, source identity or physical ABI. Independent TV,
    /// actual Rust evidence and publication/placement binding remain owed.
    /// Kernel equality can erase or duplicate let-bound source calls; this
    /// check does not establish source/IR call-trace equivalence.
    /// Source replanning and kernel checking retain their ordinary resource
    /// policies; scalar-reader limits are not a source-environment-wide budget.
    pub fn check_module_model(
        &self,
        module: &Module,
        root: FuncId,
        bindings: &[RustCallBinding],
    ) -> Result<(), GateRefusal> {
        if bindings.len() > MAX_INTERPRETATIONS {
            return Err(refuse("too many source bindings"));
        }
        let CleanOriginShape::RustCallChain { nodes } = self.plan.shape() else {
            return Err(refuse("retained plan is not a Rust call chain"));
        };
        if nodes.is_empty() || nodes.len() > 32 {
            return Err(refuse("source call chain exceeds reader scope"));
        }
        bounded_name(self.plan.declaration())?;
        let signature = self.plan.signature();
        if signature.arguments().len() > MAX_PARAMETERS
            || !signature.hypotheses().is_empty()
            || !signature.preconditions().is_empty()
        {
            return Err(refuse("source telescope exceeds scope or has erased premises"));
        }
        let fresh = trust_clean_origin::emit::plan_clean_origin_body_with_rust_callees_for_name(
            &self.environment,
            self.plan.declaration(),
            self.plan.callees(),
        )
        .map_err(|_| refuse("retained declaration cannot be freshly planned"))?;
        if fresh.shape() != self.plan.shape() || fresh.signature() != signature {
            return Err(refuse("retained plan disagrees with its source snapshot"));
        }
        let root_function = module.function_by_id(root).ok_or_else(|| refuse("missing root"))?;
        let actual = module
            .func_types
            .get(root_function.ty.index() as usize)
            .ok_or_else(|| refuse("missing root type"))?;
        let expected_params = signature
            .arguments()
            .iter()
            .map(|arg| clean_ir_type(arg.clean()))
            .collect::<Result<Vec<_>, _>>()?;
        let expected_result = clean_ir_type(signature.result().clean())?;
        if actual.is_vararg
            || actual.params != expected_params
            || actual.returns.as_slice() != [expected_result.clone()]
        {
            return Err(refuse("actual root type differs from the source telescope"));
        }
        let used: HashSet<_> = nodes.iter().map(|node| node.callee).collect();
        let mut bound = HashSet::new();
        let mut interpretations = Vec::with_capacity(bindings.len());
        for binding in bindings {
            if !used.contains(&binding.plan_index) || !bound.insert(binding.plan_index) {
                return Err(refuse("source binding is unused or repeated"));
            }
            let source = self
                .plan
                .callees()
                .get(binding.plan_index)
                .ok_or_else(|| refuse("binding exceeds the source roster"))?;
            if source.params.len() > MAX_PARAMETERS
                || source.clean_name.len() > 4096
                || source.clean_name.split('.').take(65).count() > 64
            {
                return Err(refuse("source callee exceeds interpretation limits"));
            }
            let callee = module
                .function_by_id(binding.function)
                .ok_or_else(|| refuse("binding names no actual module function"))?;
            let ty = module
                .func_types
                .get(callee.ty.index() as usize)
                .ok_or_else(|| refuse("callee has no actual module type"))?;
            let params = source.params.iter().map(rust_ir_type).collect::<Result<Vec<_>, _>>()?;
            if ty.is_vararg
                || ty.params != params
                || ty.returns.as_slice() != [rust_ir_type(&source.result)?]
            {
                return Err(refuse("actual callee type differs from its source roster"));
            }
            interpretations.push(CalleeInterpretation {
                id: binding.function,
                name: Name::from_string(&source.clean_name),
                signature: ty.clone(),
            });
        }
        if bound != used {
            return Err(refuse("source bindings are incomplete"));
        }
        let candidate = reflect_module_candidate(module, root, &interpretations)?;
        let mut expected_type = carrier(&expected_result)?;
        for ty in expected_params.iter().rev() {
            expected_type = Expr::arrow(carrier(ty)?, expected_type);
        }
        let checker = TypeChecker::new(&self.environment);
        let inferred = checker
            .infer_type(&candidate)
            .map_err(|_| refuse("kernel refused the complete reflected term"))?;
        let source_type = checker
            .infer_type(&Expr::const_(self.plan.declaration().clone(), vec![]))
            .map_err(|_| refuse("kernel refused the source declaration type"))?;
        if !checker.is_def_eq(&inferred, &expected_type)
            || !checker.is_def_eq(&source_type, &expected_type)
            || checker.heartbeat_spent()
        {
            return Err(refuse(
                "kernel source/candidate telescope disagrees or exhausted its budget",
            ));
        }
        let _model_only = trust_clean_origin::gate::check_faithful_for_name(
            &self.environment,
            self.plan.declaration(),
            &candidate,
            self.plan.result_carrier(),
        )
        .map_err(|_| refuse("kernel refused source/candidate model equality"))?;
        Ok(())
    }
}

fn clean_ir_type(clean: CleanType) -> Result<Ty, GateRefusal> {
    match clean {
        CleanType::Bool => Ok(Ty::Bool),
        other => UIntCarrier::from_clean(other)
            .map(UIntCarrier::ir_ty)
            .ok_or_else(|| refuse("unsupported source carrier")),
    }
}

fn rust_ir_type(rust: &trust_types::Ty) -> Result<Ty, GateRefusal> {
    match rust {
        trust_types::Ty::Bool => Ok(Ty::Bool),
        trust_types::Ty::Int { width, signed: false } => clean_ir_type(CleanType::UInt(*width)),
        _ => Err(refuse("unsupported Rust source carrier")),
    }
}

/// Reflect using the root's actual module type and module-owned Rust callees.
///
/// The ordinary semantic validator must accept the entire module. Each supplied
/// interpretation must then name a defined Rust-convention `TRust` function
/// whose actual type-table entry equals the complete supplied signature,
/// including ABI metadata. The root must be a defined Clean function. There is
/// no independently supplied root signature that could disagree with its type
/// id. The scalar reader still checks all actual call edges and dataflow.
///
/// This is structural input binding, not source identity or proof authority:
/// producer labels, names and signatures in arbitrary IR do not authenticate a
/// compiler registry, metadata owner, source declaration or actual Rust meaning.
/// Module validation supplies neither conservation, purity nor termination.
/// The result remains an untrusted term; no gate token is constructed.
/// Whole-module validation has its ordinary cost and resource policy; the
/// scalar reader's limits do not impose a new module-wide validation budget.
pub fn reflect_module_candidate(
    module: &Module,
    root: FuncId,
    interpretations: &[CalleeInterpretation],
) -> Result<Expr, GateRefusal> {
    if interpretations.len() > MAX_INTERPRETATIONS {
        return Err(refuse("too many callee interpretations"));
    }
    for interpretation in interpretations {
        signature_types(&interpretation.signature)?;
        bounded_name(&interpretation.name)?;
    }
    if !trust_ir_build::validate_module(module).is_empty() {
        return Err(refuse("actual module failed semantic validation"));
    }
    let function = module.function_by_id(root).ok_or_else(|| refuse("missing module root"))?;
    if function.is_declaration() || function.producer != Some(Producer::Clean) {
        return Err(refuse("module root is not a defined Clean function"));
    }
    let signature = module
        .func_types
        .get(function.ty.index() as usize)
        .ok_or_else(|| refuse("root has no actual module signature"))?;
    for interpretation in interpretations {
        let callee = module
            .function_by_id(interpretation.id)
            .ok_or_else(|| refuse("interpretation has no module-owned function"))?;
        if callee.is_declaration()
            || callee.producer != Some(Producer::TRust)
            || callee.calling_conv != CallingConv::Rust
        {
            return Err(refuse("interpretation does not name a defined Rust-convention Rust body"));
        }
        if module.func_types.get(callee.ty.index() as usize) != Some(&interpretation.signature) {
            return Err(refuse("interpretation signature differs from its actual module entry"));
        }
    }
    reflect_candidate(signature, function, interpretations)
}

fn carrier(ty: &Ty) -> Result<Expr, GateRefusal> {
    let name = if *ty == Ty::Bool {
        "Bool"
    } else {
        UIntCarrier::from_ir(ty)
            .ok_or_else(|| refuse("only Bool and exact UInt8/16/32/64 carriers are reflectable"))?
            .clean_name()
    };
    Ok(Expr::const_(Name::from_string(name), vec![]))
}

fn refuse(note: impl Into<String>) -> GateRefusal {
    GateRefusal::new("rust-call-reader", note)
}

fn signature_types(signature: &FuncTy) -> Result<(), GateRefusal> {
    if signature.params.len() > MAX_PARAMETERS
        || signature.is_vararg
        || signature.returns.len() != 1
    {
        return Err(refuse("call reflection requires a non-variadic single-result signature"));
    }
    for ty in signature.params.iter().chain(&signature.returns) {
        let _carrier = carrier(ty)?;
    }
    Ok(())
}

// Check structural names before hashing or equality can traverse them. Limits
// apply to components and total bytes, not a recursively rendered display name.
fn bounded_name(name: &Name) -> Result<(), GateRefusal> {
    let mut current = name;
    let mut bytes = 0;
    for _ in 0..64 {
        match current.inner() {
            NameInner::Anon => return Ok(()),
            NameInner::Str(parent, component) => {
                if component.len() > 4096 - bytes {
                    return Err(refuse("callee name exceeds byte budget"));
                }
                bytes += component.len();
                current = parent;
            }
            NameInner::Num(parent, _) => current = parent,
        }
    }
    Err(refuse("callee name exceeds component budget"))
}

struct Value {
    ty: Ty,
    /// Absolute position in the parameter/SSA-let telescope.
    slot: usize,
}

fn operand(
    values: &HashMap<ValueId, Value>,
    id: ValueId,
    ty: &Ty,
    depth: usize,
) -> Result<Expr, GateRefusal> {
    let value = values.get(&id).ok_or_else(|| refuse("use before definition"))?;
    if value.ty != *ty {
        return Err(refuse("SSA operand disagrees with the actual callee/result carrier"));
    }
    let index = depth
        .checked_sub(value.slot + 1)
        .ok_or_else(|| refuse("SSA operand is outside its let telescope"))?;
    Ok(Expr::bvar(index as u32))
}

/// Reconstruct a closed lambda from bounded, single-block call SSA. Each
/// computed instruction becomes its own CIC let, in actual instruction order;
/// uses refer to that binding instead of copying its defining computation.
/// Shared and unused results retain their defining calls syntactically.
///
/// Kernel zeta reduction can erase or duplicate these lets: this is a MODEL,
/// not an execution trace. Source evaluation must independently match through
/// `check_module_call_trace`; no proof or codegen permission is returned here.
pub fn reflect_candidate(
    signature: &FuncTy,
    function: &Function,
    interpretations: &[CalleeInterpretation],
) -> Result<Expr, GateRefusal> {
    if interpretations.len() > MAX_INTERPRETATIONS {
        return Err(refuse("too many callee interpretations"));
    }
    signature_types(signature)?;
    if function.calling_conv != CallingConv::Rust || function.blocks.len() != 1 {
        return Err(refuse("requires one block and the Rust calling convention"));
    }
    let block = &function.blocks[0];
    if block.id != function.entry
        || block.params.len() != signature.params.len()
        || block.body.len() > 257
    {
        return Err(refuse("entry parameters or bounded body shape disagree"));
    }
    let mut callees = HashMap::new();
    let mut names = HashSet::new();
    for callee in interpretations {
        signature_types(&callee.signature)?;
        bounded_name(&callee.name)?;
        if callees.insert(callee.id, callee).is_some() || !names.insert(callee.name.clone()) {
            return Err(refuse("ambiguous callee interpretation"));
        }
    }
    let mut values = HashMap::new();
    for (index, ((id, actual), expected)) in block.params.iter().zip(&signature.params).enumerate()
    {
        if actual != expected
            || values.insert(*id, Value { ty: actual.clone(), slot: index }).is_some()
        {
            return Err(refuse("entry parameter types or SSA identities disagree"));
        }
    }
    let mut returned = None;
    let mut bindings = Vec::new();
    let mut calls = 0;
    let mut applications = 0;
    for node in &block.body {
        if returned.is_some() {
            return Err(refuse("instruction after Return"));
        }
        let depth = signature.params.len() + bindings.len();
        let (ty, term) = match &node.inst {
            Inst::Const { ty, value } => {
                let _carrier = carrier(ty)?;
                let term = match (ty, value) {
                    (Ty::Bool, Constant::Bool(value)) => Expr::const_(
                        Name::from_string(if *value { "Bool.true" } else { "Bool.false" }),
                        vec![],
                    ),
                    (_, Constant::Int(value)) => {
                        let width = UIntCarrier::from_ir(ty)
                            .ok_or_else(|| refuse("integer literal at a non-UInt carrier"))?;
                        if *value < 0 || (*value as u128) >= (1u128 << width.bits()) {
                            return Err(refuse("literal outside its exact unsigned carrier"));
                        }
                        Expr::app(width.member("ofNat"), Expr::nat_lit(*value as u64))
                    }
                    _ => return Err(refuse("noncanonical call literal")),
                };
                (ty.clone(), term)
            }
            Inst::Call { callee, args } => {
                if args.len() > MAX_PARAMETERS || applications > MAX_APPLICATIONS - args.len() {
                    return Err(refuse("call arguments exceed the application budget"));
                }
                applications += args.len();
                calls += 1;
                if calls > 32 {
                    return Err(refuse("call SSA exceeds 32 calls"));
                }
                let callee = callees.get(callee).ok_or_else(|| refuse("unmapped call target"))?;
                if args.len() != callee.signature.params.len() {
                    return Err(refuse("call arity disagrees with the callee signature"));
                }
                let mut term = Expr::const_(callee.name.clone(), vec![]);
                for (arg, ty) in args.iter().zip(&callee.signature.params) {
                    term = Expr::app(term, operand(&values, *arg, ty, depth)?);
                }
                (callee.signature.returns[0].clone(), term)
            }
            Inst::Return { values: operands } => {
                if !node.results.is_empty() || operands.len() != 1 || calls == 0 {
                    return Err(refuse("requires a single-value Return after at least one call"));
                }
                returned = Some(operand(&values, operands[0], &signature.returns[0], depth)?);
                continue;
            }
            _ => return Err(refuse("instruction outside the direct-call SSA vocabulary")),
        };
        let [id] = node.results.as_slice() else {
            return Err(refuse("computed instruction must define exactly one result"));
        };
        if values.insert(*id, Value { ty: ty.clone(), slot: depth }).is_some() {
            return Err(refuse("SSA value defined twice"));
        }
        bindings.push((ty, term));
    }
    let mut term = returned.ok_or_else(|| refuse("missing Return"))?;
    for (ty, value) in bindings.into_iter().rev() {
        term = Expr::let_named(Name::from_string("ssa"), carrier(&ty)?, value, term, false);
    }
    for ty in signature.params.iter().rev() {
        term = Expr::lam(BinderInfo::Default, carrier(ty)?, term);
    }
    Ok(term)
}
