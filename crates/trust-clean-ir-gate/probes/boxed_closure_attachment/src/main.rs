// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Untrusted DATA observation of the maintained source/boxing/backend pipeline.
//! Neither this program nor its output grants source, ABI or object authority.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use clean_compiler::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
use clean_compiler::ir::{IRBody, IRDecl, IRExpr};
use clean_compiler::lcnf::{Code, Decl, DeclValue, LetValue};
use clean_compiler::pass_manager::{
    PipelineConfig, compile_lcnf_decls_in_runtime_closure,
    compile_lcnf_to_trust_ir_in_runtime_closure_with_artifacts,
};
use clean_kernel::{Environment, Name};
use trust_certify::lean_source_batch::{LeanSourceInput, PinnedLeanSourceWorld};

type Error = Box<dyn std::error::Error + Send + Sync>;

// Exact runtime source DATA associated with this producer build. Retaining
// these bytes does not prove the C implementation, layout, ABI or ownership.
const RUNTIME_SOURCE: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../../first-party/clean/crates/clean-runtime/src/clean_runtime.c"
));
const RUNTIME_HEADER: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../../first-party/clean/crates/clean-runtime/include/clean_runtime.h"
));
const RUNTIME_EXTERNS: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../../first-party/clean/crates/clean-runtime/src/runtime_extern.c"
));

fn json(path: &Path, value: &impl serde::Serialize) -> Result<(), Error> {
    std::fs::write(path, serde_json::to_vec_pretty(value)?)?;
    Ok(())
}

fn prepare_output(source: &str, output: &Path) -> Result<(), Error> {
    // The directory must be new: failures and earlier observations survive.
    std::fs::create_dir(output)?;
    std::fs::write(output.join("Original.lean"), source)?;
    std::fs::write(output.join("clean_runtime.c"), RUNTIME_SOURCE)?;
    std::fs::write(output.join("clean_runtime.h"), RUNTIME_HEADER)?;
    std::fs::write(output.join("runtime_extern.c"), RUNTIME_EXTERNS)?;
    Ok(())
}

fn produce(source: &str, output: &Path) -> Result<(), Error> {
    prepare_output(source, output)?;
    eprintln!("initializing genuine pinned source world");
    let mut world = PinnedLeanSourceWorld::new()?;
    produce_checked(&mut world, source, output)
}

fn produce_checked(
    world: &mut PinnedLeanSourceWorld,
    source: &str,
    output: &Path,
) -> Result<(), Error> {
    eprintln!("checking the complete original source batch from empty");
    let checked = world.check_with_runtime_baseline(
        vec![LeanSourceInput {
            module: "ActualBoxedClosureInput".to_owned(),
            path: "Original.lean".to_owned(),
            source: source.to_owned(),
        }],
        true,
    );
    let diagnostics: Vec<_> = checked
        .attempt()
        .into_iter()
        .flat_map(|batch| batch.outcomes.iter())
        .flat_map(|outcome| outcome.errors.iter().map(|error| error.message.clone()))
        .collect();
    json(
        &output.join("SourceCheck.json"),
        &serde_json::json!({
            "framing_errors": checked.errors(), "diagnostics": diagnostics,
            "timing": format!("{:?}", checked.timing()),
            "accepted": checked.accepted_context().is_some(),
        }),
    )?;
    let accepted = checked.accepted_context().ok_or("complete original source batch refused")?;
    let environment = accepted.environment();
    let owned = accepted.owned_declarations();
    let payloads: Vec<_> = owned.iter().map(|name| environment.get_const(name)).collect();
    json(
        &output.join("AcceptedSource.json"),
        &serde_json::json!({
            "scope": "actual accepted source-context DATA; no erasure/runtime/ABI/object authority",
            "world": format!("{:?}", accepted.source_world()),
            "source_closure_sha256": accepted.source_closure_sha256(),
            "owned_declarations_sha256": accepted.owned_declarations_sha256(),
            "owned": payloads,
            "sources": accepted.sources().iter().map(|input| serde_json::json!({
                "module":input.module,"path":input.path,"source":input.source,
            })).collect::<Vec<_>>(),
        }),
    )?;
    json(&output.join("SourceAliases.json"), &accepted.aliases().iter().map(|alias| serde_json::json!({"module":alias.module,"source_index":alias.source_index})).collect::<Vec<_>>())?;
    if owned.is_empty() {
        return Err("accepted source has no owned definitions to compile".into());
    }
    let mut dependency_names = BTreeSet::new();
    for name in owned {
        dependency_names.extend(environment.dependency_closure(name)?);
    }
    let dependencies: Vec<_> = dependency_names
        .iter()
        .map(|name| {
            serde_json::json!({
                "constant": environment.get_const(name),
                "inductive": environment.get_inductive(name),
                "constructor": environment.get_constructor(name),
                "recursor": environment.get_recursor(name),
                "quotient": environment.get_quot(name),
                "implemented_by": environment.get_implemented_by(name),
                "external": environment.get_extern(name),
                "unsafe": environment.is_unsafe(name),
                "partial": environment.is_partial(name),
                "noncomputable": environment.is_noncomputable(name),
                "csimp_rules": clean_kernel::env::csimp::rules_for(&environment, Some(name)),
            })
        })
        .collect();
    json(&output.join("SourceContext.json"), &dependencies)?;
    // This is the maintained persisted-environment DAG DTO, not a promise
    // about transient providers or arbitrary future lazy imports. It is raw
    // DATA and is never deserialized into an accepted-source owner here.
    std::fs::write(output.join("RawEnvironment.dag"), environment.to_bincode()?)?;
    observe_pipeline(environment, owned, output)
}

fn observe_pipeline(
    environment: &Environment,
    owned: &BTreeSet<Name>,
    output: &Path,
) -> Result<(), Error> {
    // Every actual eager source addition is submitted. No role/name whitelist
    // can silently drop an original or generated sibling from this population.
    let roots: Vec<_> = owned.iter().cloned().collect();
    let closure = clean_compiler::RuntimeBindingClosure::check(environment, &roots)?;
    let mut lowered = Vec::new();
    let mut refused = Vec::new();
    for name in owned {
        let info = environment.get_const(name).ok_or("missing original payload")?;
        match clean_compiler::to_lcnf::constant_to_decl_in_runtime_closure(
            environment,
            info,
            &closure,
        ) {
            Ok(Some(declaration)) => lowered.push(declaration),
            Ok(None) => refused.push(format!("{name}: no executable declaration")),
            Err(error) => refused.push(format!("{name}: {error}")),
        }
    }
    json(&output.join("OriginalLcnf.json"), &lowered)?;
    json(&output.join("LoweringRefusals.json"), &refused)?;
    if !refused.is_empty() {
        return Err("one or more owned originals refused executable lowering".into());
    }
    let population = populate_runtime_dependency_data(environment, &closure, lowered, output)?;
    let expected_native_inputs = population.native_requests;
    let lowered = population.declarations;
    let config = PipelineConfig::default();
    let emit = TrustIrConfig {
        module_name: "actual_boxed_closure_data".into(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    // One maintained full invocation owns both its actual stages and final TV
    // output. No independently repeated pass run supplies the stage DATA.
    eprintln!("running the complete boxed pipeline with every ordinary gate");
    let data = compile_lcnf_to_trust_ir_in_runtime_closure_with_artifacts(
        &lowered,
        environment,
        &config,
        &emit,
        &closure,
    )?;
    let final_supplied = record_native_supply_data(
        &data.module,
        &data.native_arithmetic_supplies,
        &output.join("FinalNativeArithmeticSupplies.json"),
    )?;
    record_native_use_data(
        &data.module,
        &data.artifacts.boxed_ir_decls,
        &data.native_arithmetic_supplies,
        &data.native_arithmetic_uses,
        &output.join("FinalNativeArithmeticUses.json"),
    )?;
    if final_supplied != expected_native_inputs {
        return Err(
            "final actual emitter supply differs from the retained dependency requests".into()
        );
    }
    let final_raw_demands =
        observed_runtime_demands(&data.artifacts.ir_decls, &data.artifacts.boxed_ir_decls);
    let final_demands: BTreeSet<_> =
        final_raw_demands.difference(&final_supplied).cloned().collect();
    json(
        &output.join("FinalRuntimeReferenceCensus.json"),
        &serde_json::json!({
            "scope":"actual final pipeline named-input DATA; not source-erasure/runtime/ABI permission",
            "observed_demands":final_raw_demands,"emitter_supplied_inputs":final_supplied,
            "unsupplied_demands":final_demands,
        }),
    )?;
    if !final_demands.is_empty() {
        return Err(format!(
            "final maintained pipeline still names unpopulated runtime inputs: {final_demands:?}"
        )
        .into());
    }
    let artifacts = data.artifacts;
    let module = data.module;
    json(&output.join("Monomorphized.json"), &artifacts.mono_decls)?;
    json(&output.join("Optimized.json"), &artifacts.optimized_decls)?;
    json(&output.join("ReferenceCounted.json"), &artifacts.rc_decls)?;
    json(&output.join("BeforeBoxing.json"), &artifacts.ir_decls)?;
    json(&output.join("Boxed.json"), &artifacts.boxed_ir_decls)?;
    json(&output.join("PipelineWarnings.json"), &artifacts.warnings)?;
    json(
        &output.join("TvStatus.json"),
        &serde_json::json!({
            "certified":data.tv_report.certified,"skipped":data.tv_report.skipped,
            "refused":data.tv_report.refused,"source_equation_count":data.tv_report.source_equations.len(),
            "final_module_digest":format!("{:?}",data.tv_report.final_module_digest),
        }),
    )?;
    std::fs::write(output.join("TvReport.debug.txt"), format!("{:#?}", data.tv_report))?;
    std::fs::write(output.join("Module.compact.json"), serde_json::to_vec(&module)?)?;
    json(&output.join("Module.json"), &module)?;
    std::fs::write(
        output.join("Module.tmbc"),
        clean_compiler::emit_trust_ir::serialize_tmbc(&module)?,
    )?;
    Ok(())
}

/// Untrusted discovery from actual executable LCNF references, not kernel
/// type/proof dependencies and not reverse-parsed linker display strings.
fn runtime_references(declaration: &Decl) -> BTreeSet<Name> {
    let mut result = BTreeSet::new();
    let DeclValue::Code(body) = &declaration.body else { return result };
    let mut pending = vec![body.as_ref()];
    while let Some(code) = pending.pop() {
        match code {
            Code::Let(binding, rest) => {
                if let LetValue::Const { name, .. } = &binding.value {
                    result.insert(name.clone());
                }
                pending.push(rest);
            }
            Code::Fun(function, rest) | Code::JoinPoint(function, rest) => {
                pending.push(&function.body);
                pending.push(rest);
            }
            Code::Cases(cases) => pending.extend(cases.alts.iter().map(|alt| alt.body())),
            Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
        }
    }
    result
}

/// Named input census of actual maintained IR, never source-erasure or ABI
/// authority. Dynamic closure arguments do not invent a global callee owner.
fn ir_runtime_demands(declarations: &[IRDecl]) -> BTreeSet<Name> {
    let defined: BTreeSet<_> = declarations.iter().map(|decl| decl.name.clone()).collect();
    let mut demands = BTreeSet::new();
    let mut pending: Vec<_> = declarations.iter().map(|decl| &decl.body).collect();
    while let Some(body) = pending.pop() {
        match body {
            IRBody::VDecl { value, rest, .. } => {
                let name = match value {
                    IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } => {
                        Some(&fn_id.0)
                    }
                    IRExpr::Ctor { info, .. } | IRExpr::Reuse { ctor: info, .. } => {
                        Some(&info.name)
                    }
                    IRExpr::Proj { .. }
                    | IRExpr::Tag(_)
                    | IRExpr::Box { .. }
                    | IRExpr::Unbox { .. }
                    | IRExpr::Lit(_)
                    | IRExpr::ClosureApply { .. }
                    | IRExpr::UProj { .. }
                    | IRExpr::SProj { .. }
                    | IRExpr::IsShared(_)
                    | IRExpr::String(_)
                    | IRExpr::Reset(_) => None,
                };
                if let Some(name) = name {
                    if !defined.contains(name) {
                        demands.insert(name.clone());
                    }
                }
                pending.push(rest);
            }
            IRBody::JDecl { body, rest, .. } => {
                pending.push(body);
                pending.push(rest);
            }
            IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => pending.push(rest),
            IRBody::Case { alts, default, .. } => {
                for alt in alts {
                    if !defined.contains(&alt.ctor.name) {
                        demands.insert(alt.ctor.name.clone());
                    }
                    pending.push(&alt.body);
                }
                if let Some(default) = default {
                    pending.push(default);
                }
            }
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
        }
    }
    demands
}

fn observed_runtime_demands(before_boxing: &[IRDecl], boxed: &[IRDecl]) -> BTreeSet<Name> {
    let mut demands = ir_runtime_demands(before_boxing);
    demands.extend(ir_runtime_demands(boxed));
    demands
}

/// Producer DATA consistency only. The existing emitter created these rows;
/// exact module membership is not a source/extern/ABI semantic theorem.
fn record_native_supply_data(
    module: &clean_compiler::emit_trust_ir_lane::Module,
    supplies: &[clean_compiler::emit_trust_ir::NativeArithmeticSupplyData],
    path: &Path,
) -> Result<BTreeSet<Name>, Error> {
    let mut inputs = BTreeSet::new();
    let mut rows = Vec::new();
    for supply in supplies {
        let functions: Vec<_> =
            module.functions.iter().filter(|f| f.id == supply.function).collect();
        let [function] = functions.as_slice() else {
            return Err("native supply does not identify one actual emitted function".into());
        };
        if function.blocks.is_empty()
            || function.ty != supply.signature
            || function.name != supply.wrapper_link_symbol()
        {
            return Err(
                "native supply actual body, signature or maintained wrapper symbol changed".into(),
            );
        }
        let signature =
            module.func_type(function.ty).ok_or("native supply signature is missing")?;
        if !inputs.insert(supply.primitive.clone()) {
            return Err("duplicate actual primitive supply".into());
        }
        rows.push(serde_json::json!({"supply":supply,"actual_function":function,"actual_signature":signature}));
    }
    json(
        path,
        &serde_json::json!({
            "scope":"same-invocation untrusted native-emitter supply DATA only; no source/extern/ownership/ABI/refinement/proof/codegen permission",
            "rows":rows,
        }),
    )?;
    Ok(inputs)
}

// Receipt self-consistency over actual final nodes. This is untrusted DATA
// orchestration; it establishes no source operation, ownership, ABI or proof.
fn actual_value_index(
    function: &trust_ir::Function,
) -> Result<BTreeMap<trust_ir::value::ValueId, (&trust_ir::inst::Inst, usize, usize)>, Error> {
    let mut values = BTreeMap::new();
    for (block, body) in function.blocks.iter().enumerate() {
        for (position, node) in body.body.iter().enumerate() {
            for result in &node.results {
                if values.insert(*result, (&node.inst, block, position)).is_some() {
                    return Err("duplicate actual result identity in native-use caller".into());
                }
            }
        }
    }
    Ok(values)
}

fn actual_input_binding<'a>(
    inputs: &'a [IRDecl],
    name: &Name,
    var: clean_compiler::ir::VarId,
) -> Result<(&'a clean_compiler::ir::IRType, &'a IRExpr), Error> {
    let declarations: Vec<_> = inputs.iter().filter(|d| &d.name == name).collect();
    let [declaration] = declarations.as_slice() else {
        return Err("native use has no unique actual input declaration".into());
    };
    let mut pending = vec![&declaration.body];
    let mut matches = Vec::new();
    while let Some(body) = pending.pop() {
        match body {
            IRBody::VDecl { var: bound, ty, value, rest } => {
                if *bound == var {
                    matches.push((ty, value));
                }
                pending.push(rest);
            }
            IRBody::JDecl { body, rest, .. } => {
                pending.push(body);
                pending.push(rest);
            }
            IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => pending.push(rest),
            IRBody::Case { alts, default, .. } => {
                pending.extend(alts.iter().map(|alt| alt.body.as_ref()));
                if let Some(body) = default {
                    pending.push(body);
                }
            }
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
        }
    }
    let [binding] = matches.as_slice() else {
        return Err("native use has no unique input result binding".into());
    };
    Ok(*binding)
}

fn record_native_use_data(
    module: &clean_compiler::emit_trust_ir_lane::Module,
    inputs: &[IRDecl],
    supplies: &[clean_compiler::emit_trust_ir::NativeArithmeticSupplyData],
    uses: &[clean_compiler::emit_trust_ir::NativeArithmeticUseData],
    path: &Path,
) -> Result<(), Error> {
    use clean_compiler::emit_trust_ir::NativeArithmeticUseKind;
    use clean_compiler::ir::IRType;
    use trust_ir::Constant;
    use trust_ir::inst::{CastOp, Inst};
    use trust_ir::ty::Ty;
    let mut occurrences = BTreeSet::new();
    let mut rows = Vec::new();
    for use_ in uses {
        if !occurrences.insert((use_.caller, use_.call_result)) {
            return Err("duplicate native-use occurrence".into());
        }
        let supply = supplies
            .iter()
            .find(|s| {
                s.primitive == use_.primitive
                    && s.function == use_.target
                    && s.signature == use_.signature
            })
            .ok_or("native use is not bound to an actual factory supply")?;
        let targets: Vec<_> = module.functions.iter().filter(|f| f.id == use_.target).collect();
        let [target] = targets.as_slice() else {
            return Err("native use target identity is not unique".into());
        };
        if target.blocks.is_empty()
            || target.ty != use_.signature
            || target.name != supply.wrapper_link_symbol()
        {
            return Err("native use target body/signature/symbol differs".into());
        }
        let callers: Vec<_> = module.functions.iter().filter(|f| f.id == use_.caller).collect();
        let [caller] = callers.as_slice() else {
            return Err("native use caller identity is not unique".into());
        };
        if caller.blocks.is_empty() || caller.name != use_.caller_link_symbol() {
            return Err("native use caller body/symbol differs".into());
        }
        let source_result = use_.source_result.ok_or("native use has no actual input binding")?;
        let (input_type, input_expr) =
            actual_input_binding(inputs, &use_.caller_name, source_result)?;
        let index = actual_value_index(caller)?;
        let (call, call_block, call_position) = *index
            .get(&use_.call_result)
            .ok_or("native use call result is absent from actual caller")?;
        let Inst::Call { callee, args } = call else {
            return Err("native use call result does not name an actual Call".into());
        };
        if args != &use_.call_args {
            return Err("native-use actual Call operands differ".into());
        }
        let result_node = if use_.result == use_.call_result {
            Some(call)
        } else {
            index.get(&use_.result).map(|(inst, _, _)| *inst)
        };
        match &use_.kind {
            NativeArithmeticUseKind::BoxedApply { result_type } => {
                if *callee != use_.target
                    || use_.runtime_entry.is_some()
                    || use_.code_pointer.is_some()
                    || args.len() != 2
                    || input_type != result_type
                {
                    return Err("boxed native use Call/type/target differs".into());
                }
                if !matches!(input_expr, IRExpr::Apply { fn_id, args } if fn_id.0 == use_.primitive && args.len() == 2)
                {
                    return Err("boxed native use input expression differs".into());
                }
                if *result_type == IRType::Object {
                    if use_.scalar_read.is_some() {
                        return Err("boxed pointer result unexpectedly has scalar-read DATA".into());
                    }
                    if use_.result != use_.call_result {
                        return Err("boxed result pointer identity differs".into());
                    }
                } else {
                    if use_.result == use_.call_result {
                        return Err(
                            "scalar native use names the boxed pointer as its result".into()
                        );
                    }
                    let read = use_
                        .scalar_read
                        .as_ref()
                        .ok_or("native scalar result has no same-invocation scalar-reader DATA")?;
                    if read.object != use_.call_result
                        || read.result != use_.result
                        || read.scalar_type != *result_type
                    {
                        return Err(
                            "native scalar-reader input/type/result identity differs".into()
                        );
                    }
                    let (reader_inst, reader_block, reader_position) = *index
                        .get(&read.read_result)
                        .ok_or("native scalar-reader actual result is absent")?;
                    if reader_block != call_block
                        || reader_position <= call_position
                        || !matches!(reader_inst, Inst::Call { callee, args } if *callee == read.reader && args.as_slice() == [read.object])
                    {
                        return Err("native scalar-reader actual Call differs from same-invocation reader DATA".into());
                    }
                    let mut value = use_.result;
                    let mut visited = BTreeSet::new();
                    loop {
                        if !visited.insert(value) {
                            return Err("native result path cycles".into());
                        }
                        let (inst, block, position) = *index
                            .get(&value)
                            .ok_or("native result has no actual defining node")?;
                        if block != call_block || position <= call_position {
                            return Err(
                                "native result is not after its actual call in the same block"
                                    .into(),
                            );
                        }
                        if value == read.read_result {
                            break;
                        }
                        match inst {
                            Inst::Cast { operand, .. } => value = *operand,
                            _ => return Err("native scalar result is not on the actual returned-box read/cast path".into()),
                        }
                    }
                    let (_, block, position) =
                        *index.get(&use_.result).ok_or("native scalar result absent")?;
                    if !caller.blocks[block].body[position + 1..]
                        .iter()
                        .any(|n| matches!(n.inst, Inst::Release { ptr } if ptr == use_.call_result))
                    {
                        return Err("native returned box has no subsequent actual release".into());
                    }
                }
            }
            NativeArithmeticUseKind::FunctionValue
            | NativeArithmeticUseKind::PartialApply { .. } => {
                if use_.scalar_read.is_some() {
                    return Err("closure allocation unexpectedly has scalar-reader DATA".into());
                }
                if Some(*callee) != use_.runtime_entry
                    || use_.result != use_.call_result
                    || args.len() < 3
                {
                    return Err("native closure use allocation/result differs".into());
                }
                let pointer =
                    use_.code_pointer.ok_or("native closure has no recorded code operand")?;
                if args[0] != pointer {
                    return Err("native closure actual code operand differs".into());
                }
                let mut value = pointer;
                let mut visited = BTreeSet::new();
                loop {
                    if !visited.insert(value) {
                        return Err("native code-pointer data path cycles".into());
                    }
                    let (inst, _, _) =
                        *index.get(&value).ok_or("native code-pointer node absent")?;
                    match inst {
                        Inst::Cast { op: CastOp::PtrToPtr, operand, .. } => value = *operand,
                        Inst::Const { ty: Ty::Func(signature), value: Constant::FnDef(target) }
                            if *signature == use_.signature && *target == use_.target =>
                        {
                            break;
                        }
                        _ => return Err(
                            "native closure code operand does not name the actual target/signature"
                                .into(),
                        ),
                    }
                }
                let read_integer = |value| -> Result<i128, Error> {
                    match index.get(&value).map(|(inst, _, _)| *inst) {
                        Some(Inst::Const { ty: Ty::U32, value: Constant::Int(n) }) => Ok(*n),
                        _ => Err(
                            "native closure arity/capture operand is not its actual U32 constant"
                                .into(),
                        ),
                    }
                };
                let (arity, captured) = match &use_.kind {
                    NativeArithmeticUseKind::FunctionValue => {
                        if !matches!(input_expr, IRExpr::Apply { fn_id, args } if fn_id.0 == use_.primitive && args.is_empty())
                        {
                            return Err("native function-value input differs".into());
                        }
                        (
                            module
                                .func_type(use_.signature)
                                .ok_or("native signature absent")?
                                .params
                                .len(),
                            0,
                        )
                    }
                    NativeArithmeticUseKind::PartialApply { arity, captured } => {
                        if !matches!(input_expr, IRExpr::PartialApply { fn_id, arity: a, args } if fn_id.0 == use_.primitive && *a == *arity && args.len() == *captured)
                        {
                            return Err("native partial-application input differs".into());
                        }
                        (*arity as usize, *captured)
                    }
                    _ => unreachable!(),
                };
                if arity
                    != module
                        .func_type(use_.signature)
                        .ok_or("native target signature absent")?
                        .params
                        .len()
                    || read_integer(args[1])? != arity as i128
                    || read_integer(args[2])? != captured as i128
                    || args.len() != 3 + captured
                {
                    return Err("native closure actual arity/capture data differs".into());
                }
            }
        }
        rows.push(serde_json::json!({"use":use_,"input_type":input_type,"input_expression":input_expr,"actual_call":call,"actual_result":result_node,"actual_target":target.id,"actual_signature":module.func_type(target.ty)}));
    }
    json(
        path,
        &serde_json::json!({"scope":"actual per-use input/caller/Call/target/signature/result associations only; no source, runtime ownership/ABI/NoUB/proof permission","rows":rows}),
    )?;
    Ok(())
}

struct RuntimePopulationData {
    declarations: Vec<Decl>,
    native_requests: BTreeSet<Name>,
}

#[cfg(test)]
fn populate_runtime_dependencies(
    environment: &Environment,
    closure: &clean_compiler::RuntimeBindingClosure,
    declarations: Vec<Decl>,
    output: &Path,
) -> Result<Vec<Decl>, Error> {
    populate_runtime_dependency_data(environment, closure, declarations, output)
        .map(|data| data.declarations)
}

fn populate_runtime_dependency_data(
    environment: &Environment,
    closure: &clean_compiler::RuntimeBindingClosure,
    mut declarations: Vec<Decl>,
    output: &Path,
) -> Result<RuntimePopulationData, Error> {
    let original_roster: Vec<_> = declarations.iter().map(|decl| decl.name.clone()).collect();
    let mut attempted: BTreeSet<Name> = declarations.iter().map(|decl| decl.name.clone()).collect();
    let mut rows = Vec::new();
    let mut errors = Vec::new();
    let mut pending_no_body = Vec::new();
    let mut pending_native = Vec::new();
    let mut cursor = 0;
    while cursor < declarations.len() {
        let references = runtime_references(&declarations[cursor]);
        cursor += 1;
        for name in references {
            if !attempted.insert(name.clone()) {
                continue;
            }
            let Some(info) = environment.get_const(&name) else {
                rows.push(
                    serde_json::json!({"name":name,"status":"missing actual constant payload"}),
                );
                errors.push(format!("runtime reference {name} has no actual constant payload"));
                continue;
            };
            let common = serde_json::json!({
                "constant":info,
                "name":name,"kind":info.kind,"value_present":info.value.is_some(),
                "inductive":environment.get_inductive(&name),
                "constructor":environment.get_constructor(&name),
                "constructor_parent":environment.get_constructor(&name).and_then(|ctor| environment.get_inductive(&ctor.inductive_name)),
                "recursor":environment.get_recursor(&name),
                "quotient":environment.get_quot(&name),
                "external":environment.get_extern(&name),
                "implemented_by":environment.get_implemented_by(&name),
                "noncomputable":environment.is_noncomputable(&name),
                "unsafe":environment.is_unsafe(&name),"partial":environment.is_partial(&name),
                "csimp_rules":clean_kernel::env::csimp::rules_for(environment,Some(&name)),
            });
            match clean_compiler::constant_to_decl_in_runtime_closure(environment, info, closure) {
                Ok(Some(declaration)) => {
                    rows.push(serde_json::json!({"input":common,"status":"actual declaration lowered","declaration":declaration}));
                    if declarations.iter().any(|old| old.name == declaration.name) {
                        errors.push(format!(
                            "runtime lowering produced duplicate declaration {}",
                            declaration.name
                        ));
                    } else {
                        declarations.push(declaration);
                    }
                }
                Ok(None) => {
                    // Dependency discovery runs before maintained erasure.
                    // Retain the complete original row; decide whether this
                    // input is still named only after an actual pipeline run.
                    let row = rows.len();
                    rows.push(serde_json::json!({"input":common,"status":"incomplete runtime dependency: maintained lowerer returned no code"}));
                    pending_no_body.push((name.clone(), row));
                }
                Err(error) => {
                    let row = rows.len();
                    rows.push(serde_json::json!({"input":common,"status":"lowering refused","error":error.to_string()}));
                    // Only this typed dependency-only refusal may request actual
                    // emitter DATA. Never compile the logical extern body, defer
                    // a generic error or apply this route to an explicit root.
                    if matches!(&error, clean_compiler::CompilerError::ExternWithBody { decl, .. } if decl == &name)
                    {
                        pending_native.push((
                            name.clone(),
                            row,
                            format!("runtime reference {name}: {error}"),
                        ));
                    } else {
                        errors.push(format!("runtime reference {name}: {error}"));
                    }
                }
            }
        }
    }
    let mut supplied_inputs = BTreeSet::new();
    if !pending_no_body.is_empty() || !pending_native.is_empty() {
        let mut observed = None;
        let mut pipeline_error = None;
        let observed_pipeline = (|| -> Result<_, Error> {
            if pending_native.is_empty() {
                Ok(compile_lcnf_decls_in_runtime_closure(
                    &declarations,
                    environment,
                    &PipelineConfig::default(),
                    closure,
                )?)
            } else {
                let emit = TrustIrConfig {
                    module_name: "actual_boxed_closure_data".into(),
                    runtime_lowering: RuntimeLowering::ExternCalls,
                    ..TrustIrConfig::default()
                };
                let data = compile_lcnf_to_trust_ir_in_runtime_closure_with_artifacts(
                    &declarations,
                    environment,
                    &PipelineConfig::default(),
                    &emit,
                    closure,
                )?;
                supplied_inputs = record_native_supply_data(
                    &data.module,
                    &data.native_arithmetic_supplies,
                    &output.join("PopulationNativeArithmeticSupplies.json"),
                )?;
                record_native_use_data(
                    &data.module,
                    &data.artifacts.boxed_ir_decls,
                    &data.native_arithmetic_supplies,
                    &data.native_arithmetic_uses,
                    &output.join("PopulationNativeArithmeticUses.json"),
                )?;
                Ok(data.artifacts)
            }
        })();
        match observed_pipeline {
            Ok(artifacts) => {
                let raw_demands =
                    observed_runtime_demands(&artifacts.ir_decls, &artifacts.boxed_ir_decls);
                let demands: BTreeSet<_> =
                    raw_demands.difference(&supplied_inputs).cloned().collect();
                json(&output.join("PopulationBeforeBoxing.json"), &artifacts.ir_decls)?;
                json(&output.join("PopulationBoxed.json"), &artifacts.boxed_ir_decls)?;
                for name in demands.difference(&attempted) {
                    rows.push(serde_json::json!({
                        "name":name,"constant":environment.get_const(name),
                        "constructor":environment.get_constructor(name),
                        "external":environment.get_extern(name),
                        "implemented_by":environment.get_implemented_by(name),
                        "status":"actual pipeline reference has no populated source body",
                    }));
                    errors.push(format!(
                        "post-pipeline runtime reference {name} has no populated actual body"
                    ));
                }
                observed = Some(demands);
            }
            Err(error) => pipeline_error = Some(error.to_string()),
        }
        for (name, row) in &pending_no_body {
            let present = observed.as_ref().map(|names| names.contains(name));
            rows[*row]["observed_in_retained_ir"] = serde_json::to_value(present)?;
            if present != Some(false) {
                errors.push(format!(
                    "runtime reference {name} has no emitted body or retained external owner"
                ));
            }
        }
        for (name, row, original_error) in &pending_native {
            let supplied = supplied_inputs.contains(name);
            rows[*row]["actual_native_emitter_supply_present"] = serde_json::json!(supplied);
            if supplied {
                rows[*row]["status"] = serde_json::json!(
                    "source lowerer refused; actual native emitter supply retained as DATA"
                );
            } else {
                errors.push(original_error.clone());
            }
        }
        let requested: BTreeSet<_> =
            pending_native.iter().map(|(name, _, _)| name.clone()).collect();
        if !supplied_inputs.is_subset(&requested) {
            errors.push(
                "actual emitter supplied a primitive outside the retained typed requests"
                    .to_owned(),
            );
        }
        json(
            &output.join("RuntimeReferenceCensus.json"),
            &serde_json::json!({
                "scope":"untrusted named-input census of actual maintained before-boxing/boxed IR only; no source-erasure/runtime/ABI/completeness authority",
                "original_roster":original_roster,"pending_no_body":pending_no_body,
                "unsupplied_demands":observed,"pipeline_error":pipeline_error,
                "pending_native":pending_native,"emitter_supplied_inputs":supplied_inputs,
            }),
        )?;
    }
    json(
        &output.join("RuntimePopulation.json"),
        &serde_json::json!({
            "scope":"untrusted runtime-call discovery; no semantic or executable-completeness authority",
            "rows":rows,"errors":errors,
        }),
    )?;
    json(&output.join("RuntimeLcnf.json"), &declarations)?;
    if !errors.is_empty() {
        // Diagnosis only: retain what the existing maintained artifact pipeline
        // actually does with these incomplete inputs. Never emit a Module or
        // mint TV evidence, and never clear any population refusal.
        record_incomplete_pipeline(environment, closure, &declarations, output)?;
        return Err("actual runtime dependency population refused".into());
    }
    Ok(RuntimePopulationData {
        declarations,
        native_requests: pending_native.into_iter().map(|(name, _, _)| name).collect(),
    })
}

/// Copy constructor and constant nodes as DATA, including their exact JSON
/// path in the retained maintained compiler output. This does not validate a
/// representation or decide that any dependency is supplied.
fn observed_constructor_nodes(
    value: &serde_json::Value,
    path: &str,
    rows: &mut Vec<serde_json::Value>,
) {
    match value {
        serde_json::Value::Object(fields) => {
            for (key, child) in fields {
                let child_path = format!("{path}/{key}");
                if key == "Ctor" || key == "Const" {
                    rows.push(serde_json::json!({"path":child_path,"kind":key,"data":child}));
                }
                observed_constructor_nodes(child, &child_path, rows);
            }
        }
        serde_json::Value::Array(values) => {
            for (index, child) in values.iter().enumerate() {
                observed_constructor_nodes(child, &format!("{path}/{index}"), rows);
            }
        }
        _ => {}
    }
}

fn record_incomplete_pipeline(
    environment: &Environment,
    closure: &clean_compiler::RuntimeBindingClosure,
    declarations: &[Decl],
    output: &Path,
) -> Result<(), Error> {
    let scope = "incomplete-input maintained compiler DATA diagnosis only; population refusals remain; no Module, TV, constructor-completeness, source, ABI or runtime permission";
    match compile_lcnf_decls_in_runtime_closure(
        declarations,
        environment,
        &PipelineConfig::default(),
        closure,
    ) {
        Ok(artifacts) => {
            let mut observations = Vec::new();
            for (phase, value) in [
                ("mono", serde_json::to_value(&artifacts.mono_decls)?),
                ("optimized", serde_json::to_value(&artifacts.optimized_decls)?),
                ("before_boxing", serde_json::to_value(&artifacts.ir_decls)?),
                ("boxed", serde_json::to_value(&artifacts.boxed_ir_decls)?),
            ] {
                observed_constructor_nodes(&value, phase, &mut observations);
                json(&output.join(format!("IncompletePipeline-{phase}.json")), &value)?;
            }
            json(
                &output.join("IncompletePipelineDiagnostic.json"),
                &serde_json::json!({
                    "scope":scope,"status":"maintained artifacts retained","observed_nodes":observations,"warnings":artifacts.warnings,
                }),
            )?;
        }
        Err(error) => json(
            &output.join("IncompletePipelineDiagnostic.json"),
            &serde_json::json!({
                "scope":scope,"status":"maintained pipeline refused","error":error.to_string(),
            }),
        )?,
    }
    Ok(())
}

fn main() -> Result<(), Error> {
    let arguments: Vec<_> = std::env::args_os().collect();
    if arguments.len() != 3 {
        return Err("usage: boxed-closure-attachment-probe SOURCE NEW_OUTPUT_DIRECTORY".into());
    }
    let source = std::fs::read_to_string(&arguments[1])?;
    let output = Path::new(&arguments[2]);
    match produce(&source, output) {
        Ok(()) => Ok(()),
        Err(error) => {
            if output.is_dir() {
                std::fs::write(output.join("REFUSAL.txt"), error.to_string())?;
            }
            Err(error)
        }
    }
}

#[cfg(test)]
mod tests {
    use clean_kernel::env::TrustedEnvExt;
    use clean_kernel::{BinderInfo, Declaration, Expr, FVarId};

    use super::*;

    #[test]
    fn genuine_original_native_wrapper_supply_produces_module_data() {
        let parent = match std::env::var_os("TRUST_BOXED_SUPPLY_TEST_OUTPUT") {
            Some(path) => std::path::PathBuf::from(path),
            None => tempfile::Builder::new().prefix("boxed-supply-").tempdir().unwrap().keep(),
        };
        std::fs::create_dir_all(&parent).unwrap();
        let output = parent.join("original");
        let mut world = PinnedLeanSourceWorld::new().unwrap();
        prepare_output(include_str!("../fixtures/Original.lean"), &output).unwrap();
        let result =
            produce_checked(&mut world, include_str!("../fixtures/Original.lean"), &output);
        if let Err(error) = &result {
            std::fs::write(output.join("ActualRefusal.txt"), error.to_string()).unwrap();
        }
        let source: serde_json::Value =
            serde_json::from_slice(&std::fs::read(output.join("AcceptedSource.json")).unwrap())
                .unwrap();
        let population: serde_json::Value =
            serde_json::from_slice(&std::fs::read(output.join("RuntimePopulation.json")).unwrap())
                .unwrap();
        assert_eq!(source["owned"].as_array().unwrap().len(), 3);
        assert_eq!(population["rows"].as_array().unwrap().len(), 14);
        assert!(
            result.is_ok(),
            "original actual source cannot yet reach maintained wrapper supply: {:?}",
            population["errors"]
        );
        assert!(output.join("Module.tmbc").is_file());
        assert!(output.join("TvStatus.json").is_file());
        record_ordinary_codegen_refusal(&output);
        actual_source_binding_controls(&mut world, &parent);
    }

    // These are hostile untrusted emitter inputs and receipts, not checked
    // source contexts, TV reports, certificates or backend permissions.
    fn native_supply_ir_fixture(
        primitive: &str,
        arity: u16,
    ) -> clean_compiler::pass_manager::PipelineArtifacts {
        use clean_compiler::ir::{FnId, IRArg, IRType, VarId};
        let (env, scope, declarations) = fixture();
        let mut artifacts = compile_lcnf_decls_in_runtime_closure(
            &declarations,
            &env,
            &PipelineConfig::default(),
            &scope,
        )
        .unwrap();
        let caller = IRDecl {
            name: Name::from_string("NativeSupplyReceiptCaller"),
            params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::Dec {
                var: VarId(0),
                rest: Box::new(IRBody::Dec {
                    var: VarId(1),
                    rest: Box::new(IRBody::VDecl {
                        var: VarId(2),
                        ty: IRType::Object,
                        value: IRExpr::PartialApply {
                            fn_id: FnId(Name::from_string(primitive)),
                            arity,
                            args: vec![],
                        },
                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
                    }),
                }),
            },
        };
        artifacts.ir_decls = vec![caller.clone()];
        artifacts.boxed_ir_decls = vec![caller];
        artifacts
    }

    fn native_supply_emit_config() -> TrustIrConfig {
        TrustIrConfig { runtime_lowering: RuntimeLowering::ExternCalls, ..TrustIrConfig::default() }
    }

    #[test]
    fn native_supply_receipts_bind_actual_body_signature_and_wrapper_symbol() {
        let root = std::env::var_os("TRUST_BOXED_SUPPLY_TEST_OUTPUT")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| tempfile::tempdir().unwrap().keep());
        std::fs::create_dir_all(&root).unwrap();
        let directory = root.join("native-receipt-controls");
        std::fs::create_dir(&directory).unwrap();
        let mut overaccepted = Vec::new();
        for primitive in ["UInt64.add", "UInt64.mul"] {
            let artifacts = native_supply_ir_fixture(primitive, 2);
            let config = native_supply_emit_config();
            let data = artifacts.emit_trust_ir_with_supply_data(&config).unwrap();
            json(&directory.join(format!("{primitive}-actual-module.json")), &data.module).unwrap();
            json(
                &directory.join(format!("{primitive}-actual-input-ir.json")),
                &artifacts.boxed_ir_decls,
            )
            .unwrap();
            assert_eq!(data.native_arithmetic_supplies.len(), 1);
            let supply = &data.native_arithmetic_supplies[0];
            assert_eq!(supply.primitive, Name::from_string(primitive));
            let target = data.module.functions.iter().find(|f| f.id == supply.function).unwrap();
            assert!(!target.blocks.is_empty());
            assert_eq!(target.name, supply.wrapper_link_symbol());
            let accepted = record_native_supply_data(
                &data.module,
                &data.native_arithmetic_supplies,
                &directory.as_path().join(format!("{primitive}-actual.json")),
            )
            .unwrap();
            assert_eq!(accepted, [supply.primitive.clone()].into_iter().collect());

            let wrong = data
                .module
                .functions
                .iter()
                .find(|f| f.name == "NativeSupplyReceiptCaller")
                .unwrap();
            assert!(!wrong.blocks.is_empty());
            assert_ne!(wrong.id, target.id);
            assert_eq!(data.module.func_type(wrong.ty), data.module.func_type(target.ty));
            let mut changed = data.native_arithmetic_supplies.clone();
            changed[0].function = wrong.id;
            changed[0].signature = wrong.ty;
            json(&directory.join(format!("{primitive}-wrong-function-input.json")), &changed)
                .unwrap();
            if record_native_supply_data(
                &data.module,
                &changed,
                &directory.as_path().join(format!("{primitive}-wrong-function.json")),
            )
            .is_ok()
            {
                overaccepted.push(format!("{primitive}: same-signature different actual function"));
            }
            let mut changed = data.native_arithmetic_supplies.clone();
            changed[0].wrapper.name = Name::from_string("DifferentRetainedWrapper");
            json(&directory.join(format!("{primitive}-wrong-wrapper-name-input.json")), &changed)
                .unwrap();
            if record_native_supply_data(
                &data.module,
                &changed,
                &directory.as_path().join(format!("{primitive}-wrong-wrapper-name.json")),
            )
            .is_ok()
            {
                overaccepted.push(format!("{primitive}: retained wrapper name changed"));
            }
            let mut missing = data.module.clone();
            missing.functions.iter_mut().find(|f| f.id == supply.function).unwrap().blocks.clear();
            json(&directory.join(format!("{primitive}-missing-body-module-input.json")), &missing)
                .unwrap();
            assert!(
                record_native_supply_data(
                    &missing,
                    &data.native_arithmetic_supplies,
                    &directory.as_path().join(format!("{primitive}-missing-body.json"))
                )
                .is_err()
            );
            let external = data.module.functions.iter().find(|f| f.blocks.is_empty()).unwrap();
            let mut changed = data.native_arithmetic_supplies.clone();
            changed[0].function = external.id;
            changed[0].signature = external.ty;
            json(&directory.join(format!("{primitive}-bodyless-target-input.json")), &changed)
                .unwrap();
            assert!(
                record_native_supply_data(
                    &data.module,
                    &changed,
                    &directory.as_path().join(format!("{primitive}-bodyless-function.json"))
                )
                .is_err()
            );
            let mut duplicate = data.native_arithmetic_supplies.clone();
            duplicate.push(supply.clone());
            json(&directory.join(format!("{primitive}-duplicate-input.json")), &duplicate).unwrap();
            assert!(
                record_native_supply_data(
                    &data.module,
                    &duplicate,
                    &directory.as_path().join(format!("{primitive}-duplicate.json"))
                )
                .is_err()
            );

            let mut imported = config.clone();
            imported.imported_callees.insert(
                supply.wrapper_link_symbol(),
                data.module.func_type(supply.signature).unwrap().clone(),
            );
            let imported = artifacts.emit_trust_ir_with_supply_data(&imported).unwrap();
            assert_eq!(imported.native_arithmetic_supplies.len(), 1);
            json(
                &directory.join(format!("{primitive}-actual-imported-module-input.json")),
                &imported.module,
            )
            .unwrap();
            json(
                &directory.join(format!("{primitive}-actual-imported-supply-input.json")),
                &imported.native_arithmetic_supplies,
            )
            .unwrap();
            assert!(
                imported
                    .module
                    .functions
                    .iter()
                    .find(|f| f.id == imported.native_arithmetic_supplies[0].function)
                    .unwrap()
                    .blocks
                    .is_empty()
            );
            assert!(
                record_native_supply_data(
                    &imported.module,
                    &imported.native_arithmetic_supplies,
                    &directory.as_path().join(format!("{primitive}-actual-imported-wrapper.json"))
                )
                .is_err()
            );
        }
        eprintln!("native supply receipt overacceptances: {overaccepted:?}");
        assert!(
            overaccepted.is_empty(),
            "native supply receipt association failed: {overaccepted:?}"
        );
    }

    #[test]
    fn native_supply_keeps_arity_unknown_callee_and_collision_boundaries() {
        use clean_compiler::ir::{IRArg, VarId};
        let root = std::env::var_os("TRUST_BOXED_SUPPLY_TEST_OUTPUT")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| tempfile::tempdir().unwrap().keep());
        std::fs::create_dir_all(&root).unwrap();
        let directory = root.join("native-boundary-controls");
        std::fs::create_dir(&directory).unwrap();
        for primitive in ["UInt64.add", "UInt64.mul"] {
            for arity in [1, 3] {
                let input = native_supply_ir_fixture(primitive, arity);
                json(
                    &directory.join(format!("{primitive}-arity-{arity}-input.json")),
                    &input.boxed_ir_decls,
                )
                .unwrap();
                let error =
                    input.emit_trust_ir_with_supply_data(&native_supply_emit_config()).unwrap_err();
                json(
                    &directory.join(format!("{primitive}-arity-{arity}-refusal.json")),
                    &error.to_string(),
                )
                .unwrap();
                assert!(error.to_string().contains("arity"), "{primitive}/{arity}: {error}");
            }
            let mut artifacts = native_supply_ir_fixture(primitive, 2);
            let first =
                artifacts.emit_trust_ir_with_supply_data(&native_supply_emit_config()).unwrap();
            let mut collision = first.native_arithmetic_supplies[0].wrapper.clone();
            collision.body =
                IRBody::Dec { var: VarId(1), rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))) };
            artifacts.boxed_ir_decls.push(collision);
            let data =
                artifacts.emit_trust_ir_with_supply_data(&native_supply_emit_config()).unwrap();
            json(
                &directory.join(format!("{primitive}-collision-input-ir.json")),
                &artifacts.boxed_ir_decls,
            )
            .unwrap();
            json(&directory.join(format!("{primitive}-collision-module.json")), &data.module)
                .unwrap();
            assert!(
                data.native_arithmetic_supplies.is_empty(),
                "existing arbitrary wrapper must not become a synthesized supply"
            );
            let supplied = record_native_supply_data(
                &data.module,
                &data.native_arithmetic_supplies,
                &directory.as_path().join(format!("{primitive}-collision.json")),
            )
            .unwrap();
            assert!(!supplied.contains(&Name::from_string(primitive)));
        }
        let artifacts = native_supply_ir_fixture("UnknownUInt64.notAPrimitive", 2);
        let data = artifacts.emit_trust_ir_with_supply_data(&native_supply_emit_config()).unwrap();
        json(&directory.join("unknown-callee-input-ir.json"), &artifacts.boxed_ir_decls).unwrap();
        json(&directory.join("unknown-callee-module.json"), &data.module).unwrap();
        assert!(data.native_arithmetic_supplies.is_empty());
        let supplied = record_native_supply_data(
            &data.module,
            &data.native_arithmetic_supplies,
            &directory.as_path().join("unknown-callee.json"),
        )
        .unwrap();
        assert!(supplied.is_empty());
        assert!(
            ir_runtime_demands(&artifacts.boxed_ir_decls)
                .contains(&Name::from_string("UnknownUInt64.notAPrimitive"))
        );
    }

    #[test]
    fn native_use_receipts_bind_actual_calls_results_and_partial_arity() {
        use clean_compiler::emit_trust_ir::NativeArithmeticUseKind;
        let root = std::env::var_os("TRUST_BOXED_SUPPLY_TEST_OUTPUT")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| tempfile::tempdir().unwrap().keep());
        std::fs::create_dir_all(&root).unwrap();
        let output = root.join("native-use-controls");
        std::fs::create_dir(&output).unwrap();
        let mut artifacts = native_supply_ir_fixture("UInt64.add", 2);
        let mut other = native_supply_ir_fixture("UInt64.mul", 2).boxed_ir_decls.remove(0);
        other.name = Name::from_string("OtherNativeReceiptCaller");
        artifacts.ir_decls.push(other.clone());
        artifacts.boxed_ir_decls.push(other);
        let data = artifacts.emit_trust_ir_with_supply_data(&native_supply_emit_config()).unwrap();
        assert_eq!(data.native_arithmetic_uses.len(), 2);
        json(&output.join("actual-module.json"), &data.module).unwrap();
        json(&output.join("actual-inputs.json"), &artifacts.boxed_ir_decls).unwrap();
        record_native_use_data(
            &data.module,
            &artifacts.boxed_ir_decls,
            &data.native_arithmetic_supplies,
            &data.native_arithmetic_uses,
            &output.join("actual-uses.json"),
        )
        .unwrap();
        let first = &data.native_arithmetic_uses[0];
        let alternative = data
            .native_arithmetic_supplies
            .iter()
            .find(|s| s.primitive != first.primitive)
            .unwrap();
        let mut supplies = data.native_arithmetic_supplies.clone();
        let swapped = supplies.iter_mut().find(|s| s.primitive == first.primitive).unwrap();
        swapped.function = alternative.function;
        swapped.signature = alternative.signature;
        swapped.wrapper = alternative.wrapper.clone();
        let mut changed = data.native_arithmetic_uses.clone();
        changed[0].target = alternative.function;
        changed[0].signature = alternative.signature;
        json(
            &output.join("swapped-existing-target-input.json"),
            &serde_json::json!({"supplies":supplies,"uses":changed}),
        )
        .unwrap();
        let error = record_native_use_data(
            &data.module,
            &artifacts.boxed_ir_decls,
            &supplies,
            &changed,
            &output.join("wrong-target.json"),
        )
        .unwrap_err();
        assert!(
            error.to_string().contains("code operand"),
            "must reach actual FnDef binding, not incidental membership: {error}"
        );
        for label in [
            "wrong-result",
            "wrong-partial-arity",
            "wrong-capture-count",
            "wrong-input-binding",
            "wrong-code-operand",
            "wrong-allocation-target",
        ] {
            let mut changed = data.native_arithmetic_uses.clone();
            match label {
                "wrong-result" => changed[0].result = trust_ir::value::ValueId::new(0),
                "wrong-partial-arity" => {
                    changed[0].kind =
                        NativeArithmeticUseKind::PartialApply { arity: 1, captured: 0 }
                }
                "wrong-capture-count" => {
                    changed[0].kind =
                        NativeArithmeticUseKind::PartialApply { arity: 2, captured: 1 }
                }
                "wrong-input-binding" => {
                    changed[0].source_result = Some(clean_compiler::ir::VarId(999))
                }
                "wrong-code-operand" => {
                    changed[0].code_pointer = Some(trust_ir::value::ValueId::new(0))
                }
                "wrong-allocation-target" => changed[0].runtime_entry = Some(changed[0].target),
                _ => unreachable!(),
            }
            json(&output.join(format!("{label}-input.json")), &changed).unwrap();
            assert!(
                record_native_use_data(
                    &data.module,
                    &artifacts.boxed_ir_decls,
                    &data.native_arithmetic_supplies,
                    &changed,
                    &output.join(format!("{label}-output.json"))
                )
                .is_err(),
                "{label}"
            );
        }
        let mut duplicate = data.native_arithmetic_uses.clone();
        duplicate.push(duplicate[0].clone());
        assert!(
            record_native_use_data(
                &data.module,
                &artifacts.boxed_ir_decls,
                &data.native_arithmetic_supplies,
                &duplicate,
                &output.join("duplicate-output.json")
            )
            .is_err()
        );
    }

    #[test]
    fn boxed_native_apply_reuses_factory_and_keeps_scalar_and_mixed_boundaries() {
        use clean_compiler::ir::{FnId, IRArg, IRType, VarId};
        let root = std::env::var_os("TRUST_BOXED_SUPPLY_TEST_OUTPUT")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| tempfile::tempdir().unwrap().keep());
        std::fs::create_dir_all(&root).unwrap();
        let output = root.join("boxed-apply-controls");
        std::fs::create_dir(&output).unwrap();
        for primitive in ["UInt64.add", "UInt64.mul"] {
            let mut artifacts = native_supply_ir_fixture(primitive, 2);
            let caller = IRDecl {
                name: Name::from_string("BoxedArithmeticCaller"),
                params: vec![
                    (VarId(0), IRType::Object),
                    (VarId(1), IRType::Object),
                    (VarId(5), IRType::UInt64),
                ],
                return_type: IRType::UInt64,
                body: IRBody::VDecl {
                    var: VarId(2),
                    ty: IRType::UInt64,
                    value: IRExpr::Apply {
                        fn_id: FnId(Name::from_string(primitive)),
                        args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
                },
            };
            artifacts.ir_decls = vec![caller.clone()];
            artifacts.boxed_ir_decls = vec![caller.clone()];
            let data =
                artifacts.emit_trust_ir_with_supply_data(&native_supply_emit_config()).unwrap();
            assert_eq!(data.native_arithmetic_supplies.len(), 1);
            assert_eq!(data.native_arithmetic_uses.len(), 1);
            json(&output.join(format!("{primitive}-actual-module.json")), &data.module).unwrap();
            json(&output.join(format!("{primitive}-input-ir.json")), &artifacts.boxed_ir_decls)
                .unwrap();
            record_native_use_data(
                &data.module,
                &artifacts.boxed_ir_decls,
                &data.native_arithmetic_supplies,
                &data.native_arithmetic_uses,
                &output.join(format!("{primitive}-actual-uses.json")),
            )
            .unwrap();
            let mut wrong = data.native_arithmetic_uses.clone();
            wrong[0].result = trust_ir::value::ValueId::new(2); // actual same-type scalar parameter
            json(&output.join(format!("{primitive}-wrong-scalar-result-input.json")), &wrong)
                .unwrap();
            assert!(
                record_native_use_data(
                    &data.module,
                    &artifacts.boxed_ir_decls,
                    &data.native_arithmetic_supplies,
                    &wrong,
                    &output.join(format!("{primitive}-wrong-result-output.json"))
                )
                .is_err()
            );
            let mut scalar = caller.clone();
            scalar.params = vec![(VarId(0), IRType::UInt64), (VarId(1), IRType::UInt64)];
            artifacts.ir_decls = vec![scalar.clone()];
            artifacts.boxed_ir_decls = vec![scalar];
            let data =
                artifacts.emit_trust_ir_with_supply_data(&native_supply_emit_config()).unwrap();
            assert!(data.native_arithmetic_supplies.is_empty());
            assert!(
                data.native_arithmetic_uses.is_empty(),
                "existing scalar path must gain no extra wrappers or uses"
            );
            json(&output.join(format!("{primitive}-unchanged-scalar-module.json")), &data.module)
                .unwrap();
            for label in ["mixed-operands", "wrong-result-type", "wrong-arity"] {
                let mut bad = caller.clone();
                match label {
                    "mixed-operands" => bad.params[1].1 = IRType::UInt64,
                    "wrong-result-type" => {
                        bad.return_type = IRType::Bool;
                        if let IRBody::VDecl { ty, .. } = &mut bad.body {
                            *ty = IRType::Bool;
                        }
                    }
                    "wrong-arity" => {
                        if let IRBody::VDecl { value: IRExpr::Apply { args, .. }, .. } =
                            &mut bad.body
                        {
                            args.pop();
                        }
                    }
                    _ => unreachable!(),
                }
                artifacts.ir_decls = vec![bad.clone()];
                artifacts.boxed_ir_decls = vec![bad];
                json(
                    &output.join(format!("{primitive}-{label}-input.json")),
                    &artifacts.boxed_ir_decls,
                )
                .unwrap();
                let error = artifacts
                    .emit_trust_ir_with_supply_data(&native_supply_emit_config())
                    .unwrap_err();
                json(&output.join(format!("{primitive}-{label}-refusal.json")), &error.to_string())
                    .unwrap();
            }
        }
    }

    #[test]
    fn native_scalar_read_receipt_rejects_a_different_actual_unary_call() {
        use clean_compiler::ir::{FnId, IRArg, IRType, VarId};
        use trust_ir::inst::Inst;
        let root = std::env::var_os("TRUST_BOXED_SUPPLY_TEST_OUTPUT")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| tempfile::tempdir().unwrap().keep());
        std::fs::create_dir_all(&root).unwrap();
        let output = root.join("scalar-read-controls");
        std::fs::create_dir(&output).unwrap();
        let mut overaccepted = Vec::new();
        for primitive in ["UInt64.add", "UInt64.mul"] {
            let mut artifacts = native_supply_ir_fixture(primitive, 2);
            let caller = IRDecl {
                name: Name::from_string("ScalarReadReceiptCaller"),
                params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
                return_type: IRType::UInt64,
                body: IRBody::VDecl {
                    var: VarId(2),
                    ty: IRType::UInt64,
                    value: IRExpr::Apply {
                        fn_id: FnId(Name::from_string(primitive)),
                        args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
                },
            };
            artifacts.ir_decls = vec![caller.clone()];
            artifacts.boxed_ir_decls = vec![caller];
            let data =
                artifacts.emit_trust_ir_with_supply_data(&native_supply_emit_config()).unwrap();
            assert_eq!(data.native_arithmetic_uses.len(), 1);
            record_native_use_data(
                &data.module,
                &artifacts.boxed_ir_decls,
                &data.native_arithmetic_supplies,
                &data.native_arithmetic_uses,
                &output.join(format!("{primitive}-actual-use.json")),
            )
            .unwrap();
            let use_ = &data.native_arithmetic_uses[0];
            let mut wrong = data.module.clone();
            let caller = wrong.functions.iter().find(|f| f.id == use_.caller).unwrap();
            let node = caller
                .blocks
                .iter()
                .flat_map(|block| &block.body)
                .find(|node| node.results.contains(&use_.result))
                .unwrap();
            let Inst::Call { callee: read, args } = &node.inst else {
                panic!("fixture scalar read must be an actual call");
            };
            assert_eq!(args.as_slice(), [use_.call_result]);
            let read_fn = wrong.functions.iter().find(|f| f.id == *read).unwrap();
            let alternate = wrong
                .functions
                .iter()
                .find(|f| f.id != *read && wrong.func_type(f.ty) == wrong.func_type(read_fn.ty))
                .unwrap()
                .id;
            let caller = wrong.functions.iter_mut().find(|f| f.id == use_.caller).unwrap();
            let node = caller
                .blocks
                .iter_mut()
                .flat_map(|block| &mut block.body)
                .find(|node| node.results.contains(&use_.result))
                .unwrap();
            let Inst::Call { callee, .. } = &mut node.inst else { unreachable!() };
            *callee = alternate;
            let errors = trust_ir_build::validate_module(&wrong);
            assert!(
                errors.is_empty(),
                "same-signature changed read must remain structurally valid: {errors:?}"
            );
            json(&output.join(format!("{primitive}-changed-actual-module.json")), &wrong).unwrap();
            json(
                &output.join(format!("{primitive}-unchanged-use.json")),
                &data.native_arithmetic_uses,
            )
            .unwrap();
            let result = record_native_use_data(
                &wrong,
                &artifacts.boxed_ir_decls,
                &data.native_arithmetic_supplies,
                &data.native_arithmetic_uses,
                &output.join(format!("{primitive}-changed-output.json")),
            );
            let accepted = result.is_ok();
            json(&output.join(format!("{primitive}-outcome.json")),&serde_json::json!({"accepted":accepted,"error":result.err().map(|e|e.to_string()),"alternate_actual_callee":alternate,"structural_errors":errors.iter().map(|e|format!("{e:?}")).collect::<Vec<_>>(),"scope":"actual alternate same-signature unary call DATA control, no runtime/source/ABI theorem"})).unwrap();
            if accepted {
                overaccepted.push(primitive);
            }
        }
        assert!(
            overaccepted.is_empty(),
            "different actual unary calls passed as the recorded scalar read: {overaccepted:?}"
        );
    }

    fn record_ordinary_codegen_refusal(output: &Path) {
        let bytes = std::fs::read(output.join("Module.compact.json")).unwrap();
        let module: clean_compiler::emit_trust_ir_lane::Module =
            serde_json::from_slice(&bytes).unwrap();
        let bodies: Vec<_> = module
            .functions
            .iter()
            .filter(|f| !f.blocks.is_empty())
            .map(|f| f.name.clone())
            .collect();
        let errors = trust_ir_build::validate_module_for_codegen(&module);
        json(&output.join("OrdinaryCodegenGuard.json"), &serde_json::json!({
            "scope":"actual existing normal codegen guard over exact produced Module DATA; no restamp/raw authority or alternate backend",
            "defined_subjects":bodies,"errors":errors.iter().map(|e| format!("{e:?}")).collect::<Vec<_>>(),
            "object_link_execution":"NOT RUN: ordinary codegen guard refused; no experimental unvalidated relabeling",
        })).unwrap();
        assert!(
            !errors.is_empty(),
            "native supply DATA must not silently acquire codegen permission"
        );
        assert_eq!(
            errors.len(),
            bodies.len(),
            "every emitted unproved body remains in the codegen denominator"
        );
        assert!(
            errors.iter().all(|e| matches!(
                e,
                trust_ir_build::ValidationError::UngatedBodyForCodegen { .. }
            ))
        );
    }

    fn actual_source_binding_controls(world: &mut PinnedLeanSourceWorld, parent: &Path) {
        let output = parent.join("binding-controls");
        std::fs::create_dir(&output).unwrap();
        let source = include_str!("../fixtures/Original.lean");
        let checked = world.check_with_runtime_baseline(
            vec![LeanSourceInput {
                module: "ActualBoxedClosureInput".into(),
                path: "Original.lean".into(),
                source: source.into(),
            }],
            true,
        );
        let accepted =
            checked.accepted_context().expect("actual original source must be accepted afresh");
        let environment = accepted.environment();
        let owned = accepted.owned_declarations();
        assert_eq!(owned.len(), 3);
        let roots: Vec<_> = owned.iter().cloned().collect();
        let scope = clean_compiler::RuntimeBindingClosure::check(environment, &roots).unwrap();
        let declarations: Vec<_> = roots
            .iter()
            .map(|n| {
                clean_compiler::constant_to_decl_in_runtime_closure(
                    environment,
                    environment.get_const(n).unwrap(),
                    &scope,
                )
                .unwrap()
                .unwrap()
            })
            .collect();
        json(&output.join("OriginalAcceptedInputs.json"), &serde_json::json!({
            "scope":"actual accepted source DATA and original held runtime closure; no token transfer to any mutated environment",
            "sources":accepted.sources().iter().map(|input| serde_json::json!({"module":input.module,"path":input.path,"source":input.source})).collect::<Vec<_>>(),"owned":roots.iter().map(|n| environment.get_const(n)).collect::<Vec<_>>(),
            "source_closure_sha256":accepted.source_closure_sha256(),
        })).unwrap();
        let primitive = Name::from_string("UInt64.add");
        let original_extern = environment.get_extern(&primitive).cloned();
        let original_source = environment
            .get_const(&Name::from_string("EscapingOriginal.makeAffine"))
            .unwrap()
            .clone();
        json(
            &output.join("ActualNativeSignatureProvenance.json"),
            &["UInt64.add", "UInt64.mul"].iter().map(|text| {
                let name = Name::from_string(text);
                serde_json::json!({
                    "name":name,"constant":environment.get_const(&name),
                    "declaration_verification":format!("{:?}",environment.declaration_verification(&name)),
                    "extern":environment.get_extern(&name),
                    "scope":"actual original compiler-environment metadata DATA; no verification flag is changed or inferred",
                })
            }).collect::<Vec<_>>(),
        ).unwrap();
        let mut explicit = owned.clone();
        explicit.insert(primitive.clone());
        let owned_dir = output.join("explicit-owned-primitive");
        std::fs::create_dir(&owned_dir).unwrap();
        assert!(observe_pipeline(environment, &explicit, &owned_dir).is_err());
        let refusals: Vec<String> = serde_json::from_slice(
            &std::fs::read(owned_dir.join("LoweringRefusals.json")).unwrap(),
        )
        .unwrap();
        assert!(refusals.iter().any(|r| r.contains("UInt64.add") && r.contains("extern-body")));
        assert!(!owned_dir.join("RuntimePopulation.json").exists());
        assert!(!owned_dir.join("Module.tmbc").exists());

        let mutant_source = source.replace("a * x + b", "a * x + a");
        assert_ne!(mutant_source, source);
        let mutant = world.check_with_runtime_baseline(
            vec![LeanSourceInput {
                module: "ActualBoxedClosureInput".into(),
                path: "Original.lean".into(),
                source: mutant_source.clone(),
            }],
            true,
        );
        let mutant_accepted = mutant
            .accepted_context()
            .expect("actual well-typed source body mutant must be accepted independently");
        assert_eq!(mutant_accepted.owned_declarations(), owned);
        let mutant_info = mutant_accepted.environment().get_const(&original_source.name).unwrap();
        assert_eq!(mutant_info.type_, original_source.type_);
        assert_eq!(mutant_info.kind, original_source.kind);
        assert_ne!(mutant_info.value, original_source.value);
        json(&output.join("MutantAcceptedInputs.json"), &serde_json::json!({
            "source":mutant_source,"owned":owned.iter().map(|n| mutant_accepted.environment().get_const(n)).collect::<Vec<_>>(),
            "source_closure_sha256":mutant_accepted.source_closure_sha256(),
            "scope":"independently checked actual source body mutation; original accepted bindings and duplicate-declaration fence unchanged",
        })).unwrap();
        let mut changed_extern = environment.clone();
        changed_extern.register_extern(primitive.clone(), "deliberately_changed_uint64_add".into());
        for (label, changed) in [
            ("changed-extern", &changed_extern),
            ("changed-source-body", mutant_accepted.environment()),
        ] {
            let directory = output.join(label);
            std::fs::create_dir(&directory).unwrap();
            json(&directory.join("AlteredInputs.json"), &serde_json::json!({
                "scope":"different source/body or attribute inputs; retained original RuntimeBindingClosure must refuse and grants no permission to the changed subject",
                "extern":changed.get_extern(&primitive),"source_constant":changed.get_const(&original_source.name),
            })).unwrap();
            assert!(
                populate_runtime_dependencies(changed, &scope, declarations.clone(), &directory)
                    .is_err()
            );
            let population: serde_json::Value = serde_json::from_slice(
                &std::fs::read(directory.join("RuntimePopulation.json")).unwrap(),
            )
            .unwrap();
            assert!(population["errors"].as_array().unwrap().iter().any(|e| {
                e.as_str()
                    .unwrap()
                    .contains("runtime closure declarations or compiler attributes changed")
            }));
            assert!(
                !directory.join("PopulationNativeArithmeticSupplies.json").exists(),
                "generic stale-closure errors must not become native requests"
            );
            assert!(!directory.join("Module.tmbc").exists());
            assert_eq!(environment.get_extern(&primitive), original_extern.as_ref());
            assert_eq!(environment.get_const(&original_source.name), Some(&original_source));
        }

        // A NEW runtime closure over deliberately altered raw environment DATA
        // may obtain the existing Name-based emitter candidate. This is NOT a
        // fresh accepted context, source equivalence or permission for that C
        // symbol. The real public source controls separately retain the imported
        // attribute refusal; this test records the narrower DATA boundary.
        let mut altered = environment.clone();
        altered.register_extern(primitive.clone(), "deliberately_changed_uint64_add".into());
        let directory = output.join("fresh-altered-environment-data");
        std::fs::create_dir(&directory).unwrap();
        json(&directory.join("InputKind.json"), &serde_json::json!({
            "accepted_context":false,"scope":"new RuntimeBindingClosure over altered Environment DATA only; no owner/mint/proof/admission claim",
            "original_extern":original_extern,"altered_extern":altered.get_extern(&primitive),
            "missing_relation":"Lean original-source/registered-extern/native-wrapper semantics, physical runtime ownership/ABI/NoUB and machine correspondence remain required",
        })).unwrap();
        observe_pipeline(&altered, owned, &directory).expect("existing Name-based primitive candidate DATA should remain distinguishable from a semantic grant");
        let tv: serde_json::Value =
            serde_json::from_slice(&std::fs::read(directory.join("TvStatus.json")).unwrap())
                .unwrap();
        assert!(tv["certified"].as_array().unwrap().is_empty());
        assert!(tv["refused"].as_array().unwrap().is_empty());
        assert_eq!(tv["source_equation_count"], 0);
        record_ordinary_codegen_refusal(&directory);
        assert_eq!(environment.get_extern(&primitive), original_extern.as_ref());
        assert_eq!(environment.get_const(&original_source.name), Some(&original_source));
    }

    fn fixture() -> (Environment, clean_compiler::RuntimeBindingClosure, Vec<Decl>) {
        let mut env = Environment::with_prelude();
        let nat = Expr::const_str("Nat");
        for (name, value) in [
            ("runtimeInner", Expr::bvar(0)),
            ("runtimeOuter", Expr::app(Expr::const_str("runtimeInner"), Expr::bvar(0))),
            ("ownedSibling", Expr::bvar(0)),
        ] {
            env.add_decl(Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_: Expr::arrow(nat.clone(), nat.clone()),
                value: Expr::lam(BinderInfo::Default, nat.clone(), value),
                is_reducible: false,
            })
            .unwrap();
        }
        let roots: Vec<_> =
            ["runtimeOuter", "ownedSibling"].iter().map(|s| Name::from_string(s)).collect();
        let scope = clean_compiler::RuntimeBindingClosure::check(&env, &roots).unwrap();
        let decls = roots
            .iter()
            .map(|name| {
                clean_compiler::constant_to_decl_in_runtime_closure(
                    &env,
                    env.get_const(name).unwrap(),
                    &scope,
                )
                .unwrap()
                .unwrap()
            })
            .collect();
        (env, scope, decls)
    }

    #[test]
    fn actual_runtime_fixpoint_keeps_owned_siblings_and_dependency_bodies() {
        let (env, scope, decls) = fixture();
        let directory = tempfile::tempdir().unwrap();
        let result = populate_runtime_dependencies(&env, &scope, decls, directory.path()).unwrap();
        let names: BTreeSet<_> = result.iter().map(|d| d.name.to_string()).collect();
        assert_eq!(
            names,
            ["runtimeInner", "runtimeOuter", "ownedSibling"]
                .iter()
                .map(|s| s.to_string())
                .collect()
        );
        let rows: serde_json::Value = serde_json::from_slice(
            &std::fs::read(directory.path().join("RuntimePopulation.json")).unwrap(),
        )
        .unwrap();
        assert!(rows["errors"].as_array().unwrap().is_empty());
        assert_eq!(rows["rows"].as_array().unwrap().len(), 1);
    }

    #[test]
    fn missing_actual_runtime_payload_refuses_without_fabricating_a_body() {
        let (env, scope, mut decls) = fixture();
        let result = FVarId::new(12345);
        decls[0].body = DeclValue::Code(Box::new(Code::let_bind(
            clean_compiler::lcnf::LetDecl::new(
                result,
                Name::anon(),
                Expr::const_str("Nat"),
                LetValue::const_simple(Name::from_string("absentRuntimeBody")),
            ),
            Code::Return(result),
        )));
        let directory = tempfile::tempdir().unwrap();
        assert!(populate_runtime_dependencies(&env, &scope, decls, directory.path()).is_err());
        let rows: serde_json::Value = serde_json::from_slice(
            &std::fs::read(directory.path().join("RuntimePopulation.json")).unwrap(),
        )
        .unwrap();
        assert!(
            rows["errors"]
                .as_array()
                .unwrap()
                .iter()
                .any(|v| v.as_str().unwrap().contains("absentRuntimeBody"))
        );
        let lowered: Vec<Decl> = serde_json::from_slice(
            &std::fs::read(directory.path().join("RuntimeLcnf.json")).unwrap(),
        )
        .unwrap();
        assert!(!lowered.iter().any(|decl| decl.name == Name::from_string("absentRuntimeBody")));
    }

    fn boundary_reference(
        env: &Environment,
        name: &Name,
    ) -> (clean_compiler::RuntimeBindingClosure, Vec<Decl>) {
        let (_, _, mut declarations) = fixture();
        let result = FVarId::new(12346);
        declarations[0].body = DeclValue::Code(Box::new(Code::let_bind(
            clean_compiler::lcnf::LetDecl::new(
                result,
                Name::anon(),
                Expr::const_str("Nat"),
                LetValue::const_simple(name.clone()),
            ),
            Code::Return(result),
        )));
        let closure = clean_compiler::RuntimeBindingClosure::check(env, &[name.clone()]).unwrap();
        (closure, declarations)
    }

    #[test]
    fn value_bearing_extern_keeps_actual_symbol_and_type_and_never_lowers_its_body() {
        for symbol in ["foreign_identity_alpha", "unrelated_runtime_beta"] {
            let (mut env, _, _) = fixture();
            let name = Name::from_string("runtimeInner");
            env.register_extern(name.clone(), symbol.to_string());
            let (closure, declarations) = boundary_reference(&env, &name);
            let info = env.get_const(&name).unwrap();
            assert!(info.value.is_some());
            assert!(
                matches!(clean_compiler::constant_to_decl_in_runtime_closure(&env, info, &closure),
                Err(clean_compiler::CompilerError::ExternWithBody { symbol: actual, .. }) if actual == symbol)
            );
            let directory = tempfile::tempdir().unwrap();
            assert!(
                populate_runtime_dependencies(&env, &closure, declarations, directory.path())
                    .is_err()
            );
            let rows: serde_json::Value = serde_json::from_slice(
                &std::fs::read(directory.path().join("RuntimePopulation.json")).unwrap(),
            )
            .unwrap();
            assert_eq!(rows["rows"][0]["input"]["external"], symbol);
            assert_eq!(rows["rows"][0]["input"]["constant"], serde_json::to_value(info).unwrap());
            assert_eq!(rows["rows"][0]["status"], "lowering refused");
            let kept: Vec<Decl> = serde_json::from_slice(
                &std::fs::read(directory.path().join("RuntimeLcnf.json")).unwrap(),
            )
            .unwrap();
            assert_eq!(kept.len(), 2);
            assert!(kept.iter().any(|d| d.name == Name::from_string("ownedSibling")));
            assert!(!kept.iter().any(|d| d.name == name));
        }
    }

    #[test]
    fn bodyless_runtime_references_are_incomplete_even_with_an_external_symbol() {
        use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility};
        for (kind, external) in [
            (ConstantKind::Opaque, None),
            (ConstantKind::Axiom, None),
            (ConstantKind::Axiom, Some("actual_external_no_owner")),
        ] {
            let (mut env, _, _) = fixture();
            let name = Name::from_string("bodylessDependency");
            env.extend_constants_unchecked(std::iter::once(ConstantInfo::new_with_reducibility(
                name.clone(),
                vec![],
                Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")),
                None,
                Reducibility::Opaque,
                kind,
            )));
            if let Some(symbol) = external {
                env.register_extern(name.clone(), symbol.to_string());
            }
            let (closure, declarations) = boundary_reference(&env, &name);
            let info = env.get_const(&name).unwrap();
            assert!(info.value.is_none());
            assert!(matches!(
                clean_compiler::constant_to_decl_in_runtime_closure(&env, info, &closure),
                Ok(None)
            ));
            let directory = tempfile::tempdir().unwrap();
            assert!(
                populate_runtime_dependencies(&env, &closure, declarations, directory.path())
                    .is_err()
            );
            let rows: serde_json::Value = serde_json::from_slice(
                &std::fs::read(directory.path().join("RuntimePopulation.json")).unwrap(),
            )
            .unwrap();
            assert_eq!(rows["rows"][0]["input"]["constant"], serde_json::to_value(info).unwrap());
            assert_eq!(
                rows["rows"][0]["input"]["external"],
                serde_json::to_value(external).unwrap()
            );
            assert!(
                rows["errors"][0]
                    .as_str()
                    .unwrap()
                    .contains("no emitted body or retained external owner")
            );
            let kept: Vec<Decl> = serde_json::from_slice(
                &std::fs::read(directory.path().join("RuntimeLcnf.json")).unwrap(),
            )
            .unwrap();
            assert_eq!(kept.len(), 2);
            assert!(kept.iter().any(|d| d.name == Name::from_string("ownedSibling")));
            assert!(!kept.iter().any(|d| d.name == name));
        }
    }

    #[test]
    fn constructor_none_keeps_refusal_but_records_real_maintained_representation() {
        use clean_compiler::lcnf::{Arg, LetDecl, Param};
        use clean_kernel::{Constructor, InductiveDecl, InductiveType};
        let (mut env, _, _) = fixture();
        let box_ty = Expr::const_str("WitnessBox");
        let nat = Expr::const_str("Nat");
        let ctor_name = Name::from_string("WitnessBox.second");
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("WitnessBox"),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("WitnessBox.first"),
                        type_: box_ty.clone(),
                    },
                    Constructor {
                        name: ctor_name.clone(),
                        type_: Expr::arrow(nat.clone(), box_ty.clone()),
                    },
                ],
            }],
        })
        .unwrap();
        let root = Name::from_string("ctorRoot");
        env.add_decl(Declaration::Definition {
            name: root.clone(),
            level_params: vec![],
            type_: Expr::arrow(nat.clone(), box_ty.clone()),
            value: Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::app(Expr::const_(ctor_name.clone(), vec![]), Expr::bvar(0)),
            ),
            is_reducible: false,
        })
        .unwrap();
        let scope = clean_compiler::RuntimeBindingClosure::check(&env, &[root.clone()]).unwrap();
        let argument = FVarId::new(12350);
        let result = FVarId::new(12351);
        let declaration = Decl::new(
            root,
            vec![],
            box_ty.clone(),
            vec![Param::new(argument, Name::from_string("n"), nat)],
            Code::let_bind(
                LetDecl::new(
                    result,
                    Name::anon(),
                    box_ty,
                    LetValue::Const {
                        name: ctor_name.clone(),
                        levels: vec![],
                        args: vec![Arg::FVar(argument)],
                    },
                ),
                Code::Return(result),
            ),
            false,
        );
        let constructor = env.get_constructor(&ctor_name).unwrap();
        assert_eq!(constructor.constructor_idx, 1);
        assert!(matches!(
            clean_compiler::constant_to_decl_in_runtime_closure(
                &env,
                env.get_const(&ctor_name).unwrap(),
                &scope
            ),
            Ok(None)
        ));
        let directory = tempfile::tempdir().unwrap();
        assert!(
            populate_runtime_dependencies(&env, &scope, vec![declaration], directory.path())
                .is_err()
        );
        let population: serde_json::Value = serde_json::from_slice(
            &std::fs::read(directory.path().join("RuntimePopulation.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(population["errors"].as_array().unwrap().len(), 1);
        assert_eq!(
            population["rows"][0]["input"]["constructor"],
            serde_json::to_value(constructor).unwrap()
        );
        assert_eq!(
            population["rows"][0]["input"]["constructor_parent"],
            serde_json::to_value(env.get_inductive(&constructor.inductive_name)).unwrap()
        );
        let diagnosis: serde_json::Value = serde_json::from_slice(
            &std::fs::read(directory.path().join("IncompletePipelineDiagnostic.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(diagnosis["status"], "maintained artifacts retained");
        assert!(diagnosis["observed_nodes"].as_array().unwrap().iter().any(|row| {
            row["path"].as_str().unwrap().starts_with("before_boxing/")
                && row["kind"] == "Ctor"
                && row["data"]["info"]["name"] == serde_json::to_value(&ctor_name).unwrap()
                && row["data"]["info"]["tag"] == 1
        }));
        for path in ["Module.compact.json", "Module.json", "Module.tmbc", "TvStatus.json"] {
            assert!(!directory.path().join(path).exists());
        }
    }

    #[test]
    fn erased_dependency_constructor_does_not_require_a_runtime_body() {
        use clean_compiler::lcnf::{Arg, LetDecl, Param};
        use clean_kernel::{Constructor, InductiveDecl, InductiveType};
        let (mut env, _, mut declarations) = fixture();
        let nat = Expr::const_str("Nat");
        let box_ty = Expr::const_str("ErasedWitnessBox");
        let ctor_name = Name::from_string("ErasedWitnessBox.mk");
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("ErasedWitnessBox"),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: ctor_name.clone(),
                    type_: Expr::arrow(nat.clone(), box_ty.clone()),
                }],
            }],
        })
        .unwrap();
        let root = Name::from_string("erasedCtorRoot");
        env.add_decl(Declaration::Definition {
            name: root.clone(),
            level_params: vec![],
            type_: Expr::arrow(nat.clone(), box_ty.clone()),
            value: Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::app(Expr::const_(ctor_name.clone(), vec![]), Expr::bvar(0)),
            ),
            is_reducible: false,
        })
        .unwrap();
        let owned_sibling = declarations.pop().unwrap();
        let argument = FVarId::new(12360);
        let result = FVarId::new(12361);
        let declaration = Decl::new(
            root.clone(),
            vec![],
            box_ty.clone(),
            vec![Param::new(argument, Name::from_string("n"), nat)],
            Code::let_bind(
                LetDecl::new(
                    result,
                    Name::anon(),
                    box_ty,
                    LetValue::Const {
                        name: ctor_name.clone(),
                        levels: vec![],
                        args: vec![Arg::FVar(argument)],
                    },
                ),
                Code::Return(result),
            ),
            false,
        );
        assert!(runtime_references(&declaration).contains(&ctor_name));
        let scope = clean_compiler::RuntimeBindingClosure::check(
            &env,
            &[root.clone(), owned_sibling.name.clone()],
        )
        .unwrap();
        assert!(matches!(
            clean_compiler::constant_to_decl_in_runtime_closure(
                &env,
                env.get_const(&ctor_name).unwrap(),
                &scope
            ),
            Ok(None)
        ));
        let originals = vec![declaration, owned_sibling];
        let artifacts = compile_lcnf_decls_in_runtime_closure(
            &originals,
            &env,
            &PipelineConfig::default(),
            &scope,
        )
        .unwrap();
        let mut observed = Vec::new();
        observed_constructor_nodes(
            &serde_json::to_value(&artifacts.ir_decls).unwrap(),
            "before_boxing",
            &mut observed,
        );
        observed_constructor_nodes(
            &serde_json::to_value(&artifacts.boxed_ir_decls).unwrap(),
            "boxed",
            &mut observed,
        );
        assert!(!observed.iter().any(|row| {
            row["kind"] == "Ctor"
                && row["data"]["info"]["name"] == serde_json::to_value(&ctor_name).unwrap()
        }));
        let directory = tempfile::tempdir().unwrap();
        let populated =
            populate_runtime_dependencies(&env, &scope, originals, directory.path()).unwrap();
        assert_eq!(populated.len(), 2);
        assert!(populated.iter().any(|decl| decl.name == root));
        assert!(populated.iter().any(|decl| decl.name == Name::from_string("ownedSibling")));
        let rows: serde_json::Value = serde_json::from_slice(
            &std::fs::read(directory.path().join("RuntimePopulation.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(rows["rows"].as_array().unwrap().len(), 1);
        assert!(rows["errors"].as_array().unwrap().is_empty());
        assert_eq!(
            rows["rows"][0]["input"]["constructor"],
            serde_json::to_value(env.get_constructor(&ctor_name)).unwrap()
        );
    }

    #[test]
    fn an_explicit_owned_bodyless_root_is_not_deferred_as_a_dependency() {
        use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility};
        let (mut env, _, _) = fixture();
        let missing = Name::from_string("ownedWithoutBody");
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new_with_reducibility(
            missing.clone(),
            vec![],
            Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")),
            None,
            Reducibility::Opaque,
            ConstantKind::Axiom,
        )));
        let owned = [Name::from_string("ownedSibling"), missing.clone()].into_iter().collect();
        let directory = tempfile::tempdir().unwrap();
        assert!(observe_pipeline(&env, &owned, directory.path()).is_err());
        let refusals: Vec<String> = serde_json::from_slice(
            &std::fs::read(directory.path().join("LoweringRefusals.json")).unwrap(),
        )
        .unwrap();
        assert!(refusals.iter().any(|row| row.contains("ownedWithoutBody")));
        assert!(!directory.path().join("RuntimePopulation.json").exists());
        assert!(!directory.path().join("Module.tmbc").exists());
    }

    #[test]
    fn genuine_erased_dictionary_module_and_complete_owned_refusals() {
        let directory = match std::env::var_os("TRUST_BOXED_PROBE_TEST_OUTPUT") {
            Some(path) => {
                let path = std::path::PathBuf::from(path);
                std::fs::create_dir(&path).unwrap();
                path
            }
            None => {
                let parent = std::env::temp_dir().join(".ubd");
                std::fs::create_dir_all(&parent).unwrap();
                tempfile::Builder::new().prefix("boxed-genuine-").tempdir_in(parent).unwrap().keep()
            }
        };
        eprintln!("retaining actual genuine producer cases at {}", directory.display());
        let mut world = match PinnedLeanSourceWorld::new() {
            Ok(world) => world,
            Err(error) => {
                std::fs::write(directory.join("WorldInitializationError.txt"), error.to_string())
                    .unwrap();
                panic!("genuine pinned source world refused: {error}");
            }
        };
        let cases = [
            ("original", include_str!("../fixtures/Original.lean"), 3, true),
            ("erased", include_str!("../fixtures/ErasedDictionary.lean"), 3, true),
            ("extra_owned", include_str!("../fixtures/ErasedDictionaryExtraExtern.lean"), 4, true),
            ("alias_reuse", include_str!("../fixtures/OriginalAliasReuse.lean"), 5, true),
            ("owned_extern", include_str!("../fixtures/OriginalOwnedExtern.lean"), 4, false),
        ];
        let mut observations = Vec::new();
        let mut failures = Vec::new();
        for (label, source, owned_count, should_emit) in cases {
            let output = directory.join(label);
            prepare_output(source, &output).unwrap();
            let outcome = produce_checked(&mut world, source, &output);
            let read = |name: &str| -> Option<serde_json::Value> {
                std::fs::read(output.join(name))
                    .ok()
                    .map(|bytes| serde_json::from_slice(&bytes).unwrap())
            };
            let source_check = read("SourceCheck.json");
            let accepted = read("AcceptedSource.json");
            let population = read("RuntimePopulation.json");
            let owned = accepted.as_ref().and_then(|value| value["owned"].as_array());
            let errors = population
                .as_ref()
                .and_then(|value| value["errors"].as_array())
                .cloned()
                .unwrap_or_default();
            let emitted = ["Module.compact.json", "Module.json", "Module.tmbc", "TvStatus.json"]
                .iter()
                .all(|name| output.join(name).is_file());
            if source_check.as_ref().and_then(|value| value["accepted"].as_bool()) != Some(true)
                || owned.map(Vec::len) != Some(owned_count)
            {
                failures.push(format!("{label}: actual source/whole-owned acceptance differs"));
            }
            if emitted != should_emit || outcome.is_ok() != should_emit {
                failures.push(format!("{label}: emitted={emitted}, outcome={outcome:?}"));
            }
            if label == "original" && !errors.is_empty() {
                failures.push(format!("original: unexpected runtime errors: {errors:?}"));
            }
            if label == "owned_extern" {
                let refusals = read("LoweringRefusals.json").unwrap();
                if !refusals.as_array().unwrap().iter().any(|r| {
                    r.as_str().unwrap().contains("ownedForeign")
                        && r.as_str().unwrap().contains("extern-body")
                }) {
                    failures.push(format!(
                        "owned_extern: missing actual owned extern refusal: {refusals:?}"
                    ));
                }
                if output.join("RuntimePopulation.json").exists() {
                    failures.push("owned_extern reached dependency deferral".into());
                }
            }
            let initial = read("OriginalLcnf.json");
            let initial_names: Vec<_> = initial
                .as_ref()
                .and_then(serde_json::Value::as_array)
                .into_iter()
                .flatten()
                .map(|decl| decl["name"].clone())
                .collect();
            if label != "owned_extern"
                && !owned.into_iter().flatten().all(|info| initial_names.contains(&info["name"]))
            {
                failures
                    .push(format!("{label}: initial actual LCNF roster lost an owned original"));
            }
            if should_emit && emitted {
                let boxed = read("Boxed.json");
                let boxed_names: Vec<_> = boxed
                    .as_ref()
                    .and_then(serde_json::Value::as_array)
                    .into_iter()
                    .flatten()
                    .map(|decl| decl["name"].clone())
                    .collect();
                if !owned.into_iter().flatten().all(|info| boxed_names.contains(&info["name"])) {
                    failures
                        .push("erased: final actual boxed roster lost an owned original".into());
                }
            }
            observations.push(serde_json::json!({
                "case":label,"output":output,"expected_owned":owned_count,
                "outcome":outcome.err().map(|error| error.to_string()),
                "source_check":source_check,"owned":owned,"emitted":emitted,
                "population_errors":errors,"tv_status":read("TvStatus.json"),
                "scope":"actual producer DATA and existing source checks; no source-erasure/runtime/ABI/object authority",
            }));
        }
        let mut attribute_controls = Vec::new();
        for (label, source, subject) in [
            (
                "changed_imported_add_extern",
                include_str!("../fixtures/OriginalChangedAddExtern.lean"),
                "UInt64.add",
            ),
            (
                "unknown_imported_hadd_extern",
                include_str!("../fixtures/OriginalUnknownHAddExtern.lean"),
                "HAdd.hAdd",
            ),
        ] {
            let output = directory.join(label);
            prepare_output(source, &output).unwrap();
            let outcome = produce_checked(&mut world, source, &output);
            let check: serde_json::Value =
                serde_json::from_slice(&std::fs::read(output.join("SourceCheck.json")).unwrap())
                    .unwrap();
            let description = check.to_string();
            if outcome.is_ok()
                || check["accepted"] != false
                || !description.contains("imported")
                || !description.contains("extern")
                || !description.contains(subject)
            {
                failures.push(format!("{label}: expected maintained imported-attribute source refusal, got {outcome:?}, {check}"));
            }
            if ["AcceptedSource.json", "Module.tmbc", "TvStatus.json"]
                .iter()
                .any(|f| output.join(f).exists())
            {
                failures
                    .push(format!("{label}: refused source obtained accepted/module/TV output"));
            }
            attribute_controls.push(serde_json::json!({"case":label,"output":output,"source_check":check,"outcome":outcome.err().map(|e|e.to_string()),"scope":"actual public source policy refusal; no altered accepted context or native permission"}));
        }
        json(&directory.join("ATTRIBUTE_CONTROL_OBSERVATIONS.json"), &attribute_controls).unwrap();
        json(&directory.join("CASE_OBSERVATIONS.json"), &observations).unwrap();
        assert!(failures.is_empty(), "actual genuine producer controls failed: {failures:?}");
    }

    #[test]
    fn final_actual_ir_census_catches_reintroduced_named_dependencies() {
        use clean_compiler::ir::{CtorInfo, FnId, IRAlt, IRArg, IRType, VarId};
        let (env, scope, declarations) = fixture();
        let directory = tempfile::tempdir().unwrap();
        let declarations =
            populate_runtime_dependencies(&env, &scope, declarations, directory.path()).unwrap();
        let actual = compile_lcnf_decls_in_runtime_closure(
            &declarations,
            &env,
            &PipelineConfig::default(),
            &scope,
        )
        .unwrap();
        assert!(observed_runtime_demands(&actual.ir_decls, &actual.boxed_ir_decls).is_empty());
        let name = Name::from_string("lateRuntimeDependency");
        let ctor = CtorInfo {
            name: name.clone(),
            tag: 7,
            num_scalars: 0,
            num_objects: 1,
            field_types: vec![IRType::Object],
        };
        for value in [
            IRExpr::Apply { fn_id: FnId(name.clone()), args: vec![] },
            IRExpr::PartialApply { fn_id: FnId(name.clone()), arity: 1, args: vec![] },
            IRExpr::Ctor { info: ctor.clone(), args: vec![IRArg::Var(VarId(0))] },
            IRExpr::Reuse { var: VarId(0), ctor: ctor.clone(), args: vec![IRArg::Var(VarId(0))] },
        ] {
            let mut changed = actual.boxed_ir_decls.clone();
            changed[0].body = IRBody::VDecl {
                var: VarId(12370),
                ty: IRType::Object,
                value,
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(12370)))),
            };
            assert_eq!(
                observed_runtime_demands(&actual.ir_decls, &changed),
                [name.clone()].into_iter().collect()
            );
        }
        let mut changed = actual.boxed_ir_decls.clone();
        changed[0].body = IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![IRAlt { ctor, body: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))) }],
            default: None,
        };
        assert_eq!(
            observed_runtime_demands(&actual.ir_decls, &changed),
            [name].into_iter().collect()
        );
    }
}
