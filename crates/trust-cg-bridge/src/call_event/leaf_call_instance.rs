//! Checked specialization of a real memory leaf at a sealed empty-frame tail.
//! This is NOT a caller verdict or a justification of CER's abstract call rely.
//! All trusted carriers have private constructors and cannot be deserialized.

use super::*;
use crate::original_conjunction_certificate::{CheckedOriginalConjunction, SubjectBinding};

#[derive(Clone)]
pub(super) struct ActualLeafProof {
    checked: Arc<CheckedOriginalConjunction>,
    binding: SubjectBinding,
    symbol: String,
    entry_memory: String,
    query: String,
}
impl ActualLeafProof {
    pub(super) fn from_closed(
        input: &CerInput<'_>,
        cert: &FunctionCertificate,
        closed: leaf_memory::Closed,
    ) -> Result<Self, String> {
        if !cert.is_kernel_proved() || !cert.assumptions.is_empty() || !cert.call_sites.is_empty() {
            return Err("instance provider is not a closed actual call-free memory leaf".into());
        }
        let checked =
            closed.checked_original().ok_or("actual leaf has no retained original proof")?;
        cert.original_proof
            .as_ref()
            .ok_or("actual leaf packet absent")?
            .require_subject(input, cert)?;
        let body = input.bodies.get(&cert.symbol).ok_or("actual leaf body absent")?;
        let producer = input.producers.get(body.producer).ok_or("actual leaf producer absent")?;
        let function =
            producer.module.function_by_id(body.func).ok_or("actual leaf function absent")?;
        let Formula::Var(entry_memory, _) = crate::cer_memory::shared_entry_memory(&format!(
            "{}:fn{}",
            producer.module.name,
            function.id.index()
        )) else {
            return Err("entry memory is not named".into());
        };
        Ok(Self {
            checked,
            binding: SubjectBinding::from_input(input, cert)?,
            symbol: cert.symbol.clone(),
            entry_memory,
            query: format!("CER_LEAF_QUERY@{}:{}", hex(&Sha256::digest(input.object)), cert.symbol),
        })
    }
}

/// Preparation performs ordinary actual CER verification once. Neither this
/// opaque provider set nor its private leaf tokens can be made from wire grades.
pub struct PreparedLeafCalls<'a> {
    input: CerInput<'a>,
    report: CerReport,
    providers: BTreeMap<String, ActualLeafProof>,
}
pub fn prepare_leaf_calls<'a>(
    input: &CerInput<'a>,
) -> Result<PreparedLeafCalls<'a>, ObjectRefusal> {
    let mut providers = BTreeMap::new();
    let report = super::verify_compiled_module_inner(input, None, Some(&mut providers), false)?;
    Ok(PreparedLeafCalls { input: *input, report, providers })
}
impl PreparedLeafCalls<'_> {
    pub fn report(&self) -> &CerReport {
        &self.report
    }
    /// No solver or original leaf proof producer is invoked by this method.
    /// Failure is an unsupported instance, never a Refuted caller verdict.
    pub fn specialize(&self, caller: &str) -> Result<CheckedLeafAtTailSite, String> {
        let input = &self.input;
        if matches!(
            self.report.certificate(caller).map(|row| &row.verdict),
            Some(crate::verify_output::OutputVerdict::Refuted { .. })
        ) {
            return Err("blocked or Refuted source caller cannot supply a tail instance".into());
        }
        let object = CompiledObject::parse(input.object).map_err(|e| e.to_string())?;
        let expect =
            ObjectExpectations::from_module(input.m_cg, object.format, input.relocation_model)
                .map_err(|e| e.to_string())?;
        let layout = ObjectLayout::bind(object, &expect).map_err(|e| e.to_string())?;
        let window = layout.windows.get(caller).ok_or("caller window absent")?;
        if layout.object.format != ObjectFormat::MachO
            || !window.unknown.is_empty()
            || window.sites.len() != 1
        {
            return Err("instance requires one actual qualified Darwin tail window".into());
        }
        let site = &window.sites[0];
        if site.kind != MachineSiteKind::Tail || site.in_trap_tail {
            return Err("instance requires an actual named Tail branch, not BL/trap".into());
        }
        if window
            .relocations
            .iter()
            .any(|relocation| relocation.role != "tail" || relocation.offset != site.offset)
        {
            return Err("tail instance rejects address/data or unrelated relocations".into());
        }
        let callee = site.callee.as_ref().ok_or("tail callee unnamed")?;
        let provider = self
            .providers
            .get(callee)
            .ok_or("tail target has no actual checked co-emitted leaf proof")?;
        if !layout.windows.get(callee).is_some_and(|w| w.expected.non_preemptible) {
            return Err("preemptible/external leaf is not an instance provider".into());
        }
        let callee_window = layout.windows.get(callee).ok_or("actual callee window absent")?;
        let actual_callee = fresh_certificate(input, &layout, callee_window)?;
        if provider.binding != SubjectBinding::from_input(input, &actual_callee)? {
            return Err("actual callee object/source/P/relocation subject changed".into());
        }
        let prefix = TailPrefixWitness::derive(input, &layout, window, provider)?;
        let bindings = prefix.bindings.clone();
        let checked = crate::original_conjunction_certificate::specialize_original_for_call(
            &provider.checked,
            &prefix.substitution,
            &bindings,
        )?;
        Ok(CheckedLeafAtTailSite { binding: prefix.binding, checked: Arc::new(checked) })
    }
}

#[derive(Debug, Clone, serde::Serialize)]
struct InstanceBinding {
    caller: SubjectBinding,
    callee: SubjectBinding,
    caller_symbol: String,
    callee_symbol: String,
    source_site: SiteKey,
    machine_pc: u64,
    relocation: String,
    query: String,
    ordinary_and_tail_pcs: Vec<u64>,
    prefix_abi_conjuncts: Vec<usize>,
}
/// A checked callee theorem at an actual tail site. No caller-license/grade API.
pub struct CheckedLeafAtTailSite {
    binding: InstanceBinding,
    checked: Arc<CheckedOriginalConjunction>,
}
impl CheckedLeafAtTailSite {
    pub fn original_equations(&self) -> &[(Formula, Formula)] {
        self.checked.original_equations()
    }
    /// Untrusted transport data; restoring it can never construct this type.
    pub fn to_untrusted_json(&self) -> Result<Vec<u8>, String> {
        serde_json::to_vec_pretty(&serde_json::json!({"schema":"trust.checked-leaf-tail-instance.v1","binding":self.binding,"packet":self.checked.packet()})).map_err(|e|e.to_string())
    }
}

struct TailPrefixWitness {
    binding: InstanceBinding,
    substitution: BTreeMap<String, Formula>,
    bindings: Vec<(Formula, Formula)>,
}
fn same_state(a: &MachineState, c: &MachineState) -> bool {
    a.gpr == c.gpr
        && a.fpr == c.fpr
        && a.sp == c.sp
        && a.pc == c.pc
        && a.memory == c.memory
        && a.flags.n == c.flags.n
        && a.flags.z == c.flags.z
        && a.flags.c == c.flags.c
        && a.flags.v == c.flags.v
}
fn scalar64(place: &FnPlacement) -> bool {
    let mut registers = BTreeSet::new();
    place.params.iter().all(|parameter| match parameter {
        ParamPlace::Scalar(s) if s.width == 64 && s.ext == AbiExt::None => match s.slot {
            Slot::Gpr(register @ 0..=7) => registers.insert(register),
            _ => false,
        },
        _ => false,
    }) && matches!(&place.ret,ReturnPlace::Scalar(s) if s.slot==Slot::Gpr(0)&&s.width==64&&s.ext==AbiExt::None)
}
pub(super) fn fresh_certificate(
    input: &CerInput<'_>,
    layout: &ObjectLayout,
    window: &FunctionWindow,
) -> Result<FunctionCertificate, String> {
    let body = input.bodies.get(&window.symbol).ok_or("source body missing")?;
    let producer = input.producers.get(body.producer).ok_or("source producer missing")?;
    let func = producer.module.function_by_id(body.func).ok_or("source function missing")?;
    let place = input.placements.get(&window.symbol).ok_or("actual P missing")?;
    let mut cert = blank_certificate(&window.symbol, &window.expected.linkage);
    cert.section =
        layout.object.section(window.section).ok_or("source section missing")?.name.clone();
    cert.extent = (window.start, window.end);
    cert.text_sha256 = window.text_sha256();
    cert.producer_ir_sha256 =
        hex(&Sha256::digest(serde_json::to_vec(func).map_err(|e| e.to_string())?));
    cert.placement_sha256.insert(window.symbol.clone(), place.digest());
    Ok(cert)
}
impl TailPrefixWitness {
    fn derive(
        input: &CerInput<'_>,
        layout: &ObjectLayout,
        window: &FunctionWindow,
        provider: &ActualLeafProof,
    ) -> Result<Self, String> {
        let query = format!(
            "CER_TAIL_QUERY@{}:{}:{:x}",
            layout.object.sha256_hex(),
            window.symbol,
            window.sites[0].offset
        );
        let context = TailContext::derive(input, layout, window, &provider.model(), query)?;
        let substitution = context.substitution(&provider.checked)?;
        if provider
            .checked
            .original_equations()
            .iter()
            .flat_map(|(a, c)| [a, c])
            .any(|term| mentions_name(term, &context.binding.query))
        {
            return Err("tail query contaminated by an actual provider input".into());
        }
        let mapped = map_original(provider.checked.original_equations(), &substitution)?;
        let mut binding = context.binding;
        for equation in &context.prefix_abi {
            let index = mapped
                .iter()
                .position(|actual| actual == equation)
                .ok_or("prefix raw ABI equation has no identical original callee conjunct")?;
            binding.prefix_abi_conjuncts.push(context.bindings.len() + index);
        }
        Ok(Self { binding, substitution, bindings: context.bindings })
    }
}

/// Independently reconstructed actual source/target identity; this grants NO
/// proof and cannot be used as an ActualLeafProof. Replay needs only this model.
struct LeafModel {
    binding: SubjectBinding,
    symbol: String,
    entry_memory: String,
    query: String,
}
impl ActualLeafProof {
    fn model(&self) -> LeafModel {
        LeafModel {
            binding: self.binding.clone(),
            symbol: self.symbol.clone(),
            entry_memory: self.entry_memory.clone(),
            query: self.query.clone(),
        }
    }
}
impl LeafModel {
    fn actual(input: &CerInput<'_>, layout: &ObjectLayout, symbol: &str) -> Result<Self, String> {
        let window = layout.windows.get(symbol).ok_or("tail callee actual window missing")?;
        let cert = fresh_certificate(input, layout, window)?;
        let body = input.bodies.get(symbol).ok_or("tail callee source body missing")?;
        let producer = input.producers.get(body.producer).ok_or("tail callee producer missing")?;
        let function =
            producer.module.function_by_id(body.func).ok_or("tail callee function missing")?;
        let Formula::Var(entry_memory, _) = crate::cer_memory::shared_entry_memory(&format!(
            "{}:fn{}",
            producer.module.name,
            function.id.index()
        )) else {
            return Err("tail entry array not named".into());
        };
        Ok(Self {
            binding: SubjectBinding::from_input(input, &cert)?,
            symbol: symbol.into(),
            entry_memory,
            query: format!("CER_LEAF_QUERY@{}:{}", layout.object.sha256_hex(), symbol),
        })
    }
}

/// Sealed complete typed source call/return and full-effect zero-frame prefix.
/// A raw state, diagnostic or wire record cannot construct this witness.
pub(super) struct TailContext {
    binding: InstanceBinding,
    bindings: Vec<(Formula, Formula)>,
    prefix_abi: Vec<(Formula, Formula)>,
    available: BTreeMap<String, Formula>,
    entry: MachineState,
    tail: MachineState,
}
impl TailContext {
    fn derive(
        input: &CerInput<'_>,
        layout: &ObjectLayout,
        window: &FunctionWindow,
        provider: &LeafModel,
        query: String,
    ) -> Result<Self, String> {
        if layout.object.format != ObjectFormat::MachO
            || !window.unknown.is_empty()
            || window.sites.len() != 1
            || window.sites[0].kind != MachineSiteKind::Tail
            || window.sites[0].in_trap_tail
            || window.sites[0].callee.as_deref() != Some(&provider.symbol)
            || window
                .relocations
                .iter()
                .any(|r| r.role != "tail" || r.offset != window.sites[0].offset)
        {
            return Err("transition requires one actual qualified named Tail window".into());
        }
        let callee =
            layout.windows.get(&provider.symbol).ok_or("transition actual leaf window missing")?;
        if !callee.expected.non_preemptible
            || !callee.unknown.is_empty()
            || !callee.sites.is_empty()
            || !callee.relocations.is_empty()
            || provider.binding
                != SubjectBinding::from_input(input, &fresh_certificate(input, layout, callee)?)?
        {
            return Err(
                "transition callee source/object/P/relocation or nonpreemptible binding differs"
                    .into(),
            );
        }
        let body = input.bodies.get(&window.symbol).ok_or("caller source body absent")?;
        let producer = input.producers.get(body.producer).ok_or("caller source producer absent")?;
        let module = producer.module.as_ref();
        let function = module.function_by_id(body.func).ok_or("caller function absent")?;
        let place = input.placements.get(&window.symbol).ok_or("caller P absent")?;
        let gp = input.placements.get(&provider.symbol).ok_or("callee P absent")?;
        let sig = signature_of(module, function.ty)?;
        if !scalar64(place)
            || !scalar64(gp)
            || !matches!(function.calling_conv, CallingConv::C | CallingConv::Rust)
            || function.blocks.len() != 1
            || function.blocks[0].id != function.entry
            || !abi_extensions::qualified_target(module)
            || !abi_extensions::qualified_target(input.m_cg)
        {
            return Err("instance source/P is outside one-block qualified scalar64 fragment".into());
        }
        check_placement(module, &sig, function.calling_conv, place, true)
            .map_err(|e| format!("caller placement: {e:?}"))?;
        let codegen = input
            .m_cg
            .functions
            .iter()
            .find(|f| f.name == window.symbol)
            .ok_or("caller codegen body absent")?;
        if codegen.calling_conv != function.calling_conv
            || signature_of(input.m_cg, codegen.ty)? != sig
        {
            return Err("caller source/codegen signature mismatch".into());
        }
        plain_signature(module, function)?;
        plain_signature(input.m_cg, codegen)?;
        let block = &function.blocks[0];
        let mut call = None;
        for (index, node) in block.body.iter().enumerate() {
            match &node.inst {
                Inst::Const { .. } | Inst::Copy { .. } | Inst::MakeClosure { .. }
                    if call.is_none() => {}
                Inst::Call { callee, .. } if call.is_none() && index + 2 == block.body.len() => {
                    call = Some(((block.id.index(), index), *callee));
                }
                Inst::Return { .. } if call.is_some() && index + 1 == block.body.len() => {}
                _ => return Err(
                    "instance source has control/memory/unsupported or missing prefix instructions"
                        .into(),
                ),
            }
        }
        let (source_site, callee_id) = call.ok_or("source has no unique final call")?;
        if producer.symbols.get(&callee_id) != Some(&provider.symbol) {
            return Err("source call target differs from authenticated tail provider".into());
        }
        let declaration =
            module.function_by_id(callee_id).ok_or("source callee declaration missing")?;
        let callee_body =
            input.bodies.get(&provider.symbol).ok_or("callee actual source missing")?;
        let callee_producer =
            input.producers.get(callee_body.producer).ok_or("callee producer missing")?;
        let callee_func = callee_producer
            .module
            .function_by_id(callee_body.func)
            .ok_or("callee source function missing")?;
        let gsig = signature_of(module, declaration.ty)?;
        let cg = input
            .m_cg
            .functions
            .iter()
            .find(|f| f.name == provider.symbol)
            .ok_or("callee codegen body missing")?;
        if gsig != signature_of(&callee_producer.module, callee_func.ty)?
            || gsig != signature_of(input.m_cg, cg.ty)?
            || declaration.calling_conv != callee_func.calling_conv
            || cg.calling_conv != callee_func.calling_conv
            || !abi_extensions::qualified_target(&callee_producer.module)
        {
            return Err("callee exact source/codegen/declaration signature differs".into());
        }
        plain_signature(module, declaration)?;
        plain_signature(&callee_producer.module, callee_func)?;
        plain_signature(input.m_cg, cg)?;
        for ty in sig.0.iter().chain(&gsig.0) {
            if let IrTy::Closure(nominal) = ty {
                closure_values::original_nominal(module, input.m_cg, *nominal)?;
                closure_values::original_nominal(&callee_producer.module, input.m_cg, *nominal)?;
            }
        }
        if gsig.0.iter().any(|ty| matches!(ty, IrTy::Closure(_))) {
            closure_values::direct_call_boundary(input, *body, callee_id, &provider.symbol, true)?;
        }
        for node in &block.body {
            if let Inst::MakeClosure { ty, .. } = &node.inst {
                closure_values::original_nominal(module, input.m_cg, *ty)?;
            }
        }
        validate_logical_prefix(module, function, &sig, &gsig, source_site)?;
        check_placement(module, &gsig, declaration.calling_conv, gp, false)
            .map_err(|e| format!("call placement: {e:?}"))?;
        abi_extensions::check_tail_transport(&place.ret, &gp.ret)?;
        let site = &window.sites[0];
        let decisions = BTreeMap::from([(
            source_site,
            SiteDecision::Called {
                symbol: provider.symbol.clone(),
                place: gp.clone(),
                result_width: Some(64),
            },
        )]);
        let spec = eval_spec(input, module, function, &sig, place, &decisions)?;
        let source_calls =
            spec.memory.calls.get(&source_site).ok_or("source call memory absent")?;
        let events = spec.events.get(&source_site).ok_or("source call arguments absent")?;
        let (return_name, width) =
            spec.result_vars.get(&source_site).ok_or("source result absent")?;
        if source_calls.len() != 1
            || events.len() != 1
            || spec.memory.calls.len() != 1
            || spec.events.len() != 1
            || source_calls[0].path != Formula::Bool(true)
            || events[0].path != Formula::Bool(true)
            || source_calls[0].before != spec.memory.entry
            || spec.memory.exits.len() != 1
            || spec.memory.exits[0].path != Formula::Bool(true)
            || spec.memory.exits[0].bytes
                != Formula::Var(
                    source_calls[0].after_variable.clone(),
                    Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
                )
            || !spec.memory.accesses.is_empty()
            || spec.memory.address_computation
            || spec.reach != Formula::Bool(true)
            || !spec.side.is_empty()
            || *width != 64
            || spec.value != Formula::Var(return_name.clone(), Sort::BitVec(64))
        {
            return Err(
                "source call occurrence/reach/pre-memory/return is not exact empty-frame tail form"
                    .into(),
            );
        }
        let mut entry = MachineState::symbolic();
        entry.memory = spec.memory.entry.clone();
        let own_abi =
            abi_extensions::Plan::new(module, function.calling_conv, &sig.0, &sig.1, place, true)?;
        own_abi.apply_entry(&mut entry);
        let callee_places = BTreeMap::from([(site.offset, gp.clone())]);
        let mut exec = CerExec::new(window, &callee_places, &place.ret, true);
        exec.tail_instance_trace = Some(PrefixTrace::begin(window, &entry)?);
        let _outcome =
            exec.run(window.start, entry.clone(), Vec::new(), 0, false, Formula::Bool(true))?;
        let trace =
            exec.tail_instance_trace.take().ok_or("actual tail prefix trace missing")?.finish()?;
        if !exec.o5_refuted.is_empty() || !exec.o5_unknown.is_empty() {
            return Err("tail prefix has frame/escape debt".into());
        }
        let actual_args = exec.read_args(&trace.state, gp)?;
        if events[0].args.len() != actual_args.len() {
            return Err("physical call arity differs".into());
        }
        let bindings: Vec<_> = events[0].args.iter().cloned().zip(actual_args).collect();
        let mut prefix_abi = Vec::new();
        for r in 19..=29 {
            prefix_abi.push((trace.state.read_gpr(r, 64), entry.read_gpr(r, 64)));
        }
        prefix_abi.push((trace.state.sp.clone(), entry.sp.clone()));
        for r in 8..=15 {
            prefix_abi.push((trace.state.read_fpr(r, 64), entry.read_fpr(r, 64)));
        }
        prefix_abi.push((trace.state.read_gpr(30, 64), entry.read_gpr(30, 64)));
        if bindings.iter().chain(&prefix_abi).any(|(a, c)| a != c) {
            return Err(
                "initial instance requires exact original argument/raw ABI prefix equalities"
                    .into(),
            );
        }
        let mut all: Vec<&Formula> = bindings.iter().flat_map(|(a, c)| [a, c]).collect();
        all.extend(entry.gpr.iter());
        all.extend(entry.fpr.iter());
        all.extend([&entry.sp, &entry.memory, &trace.state.memory]);
        if all.iter().any(|f| mentions_name(f, &query)) {
            return Err("tail query contaminated by an actual input".into());
        }
        let baseline = MachineState::symbolic();
        let mut available = BTreeMap::new();
        for (a, c) in baseline
            .gpr
            .iter()
            .zip(&trace.state.gpr)
            .chain(baseline.fpr.iter().zip(&trace.state.fpr))
            .chain([(&baseline.sp, &trace.state.sp), (&baseline.pc, &trace.state.pc)])
        {
            if let Formula::Var(name, _) = a {
                available.insert(name.clone(), c.clone());
            }
        }
        available.insert(provider.entry_memory.clone(), spec.memory.entry.clone());
        available.insert(provider.query.clone(), Formula::Var(query.clone(), Sort::BitVec(64)));
        let fresh = fresh_certificate(input, layout, window)?;
        Ok(Self {
            binding: InstanceBinding {
                caller: SubjectBinding::from_input(input, &fresh)?,
                callee: provider.binding.clone(),
                caller_symbol: window.symbol.clone(),
                callee_symbol: provider.symbol.clone(),
                source_site,
                machine_pc: site.offset,
                relocation: format!("{:?}", site.reloc),
                query,
                ordinary_and_tail_pcs: trace.pcs,
                prefix_abi_conjuncts: Vec::new(),
            },
            bindings,
            prefix_abi,
            available,
            entry,
            tail: trace.state,
        })
    }
    pub(super) fn entry(&self) -> &MachineState {
        &self.entry
    }
    pub(super) fn tail_entry(&self) -> &MachineState {
        &self.tail
    }
    pub(super) fn caller_symbol(&self) -> &str {
        &self.binding.caller_symbol
    }
    pub(super) fn callee_symbol(&self) -> &str {
        &self.binding.callee_symbol
    }
    pub(super) fn prefix_instructions(&self) -> usize {
        self.binding.ordinary_and_tail_pcs.len()
    }
    pub(super) fn instantiate(&self, formula: &Formula) -> Result<Formula, String> {
        let mut invalid = None;
        let value = formula.clone().map(&mut |node| match node {
            Formula::Var(ref name, ref sort) => match self.available.get(name) {
                Some(value)
                    if trust_types::smt_logic::check_formula_sort(value).ok().as_ref()
                        == Some(sort) =>
                {
                    value.clone()
                }
                _ => {
                    invalid = Some(format!(
                        "actual source tail data has missing/wrong-sort role {name:?}"
                    ));
                    node
                }
            },
            _ => node,
        });
        if let Some(error) = invalid { Err(error) } else { Ok(value) }
    }
    fn substitution(
        &self,
        checked: &CheckedOriginalConjunction,
    ) -> Result<BTreeMap<String, Formula>, String> {
        let mut substitution = BTreeMap::new();
        for (name, sort) in checked.variable_sorts() {
            let value =
                self.available.get(name).ok_or("callee data role has no actual caller binding")?;
            if trust_types::smt_logic::check_formula_sort(value)
                .map_err(|e| format!("caller binding sort: {e:?}"))?
                != *sort
            {
                return Err("actual typed data substitution sort differs".into());
            }
            substitution.insert(name.clone(), value.clone());
        }
        Ok(substitution)
    }
}
fn map_original(
    items: &[(Formula, Formula)],
    substitution: &BTreeMap<String, Formula>,
) -> Result<Vec<(Formula, Formula)>, String> {
    let mut invalid = false;
    let mut apply = |formula: &Formula| {
        formula.clone().map(&mut |node| match node {
            Formula::Var(ref name, _) => match substitution.get(name) {
                Some(value) => value.clone(),
                None => {
                    invalid = true;
                    node
                }
            },
            _ => node,
        })
    };
    let mapped = items.iter().map(|(a, c)| (apply(a), apply(c))).collect();
    if invalid {
        Err("original transition has an unbound typed variable".into())
    } else {
        Ok(mapped)
    }
}

fn plain_signature(module: &Module, function: &trust_ir::Function) -> Result<(), String> {
    let signature = module.func_type(function.ty).ok_or("actual signature missing")?;
    if signature.is_vararg || signature.abi.is_some() {
        return Err("tail instance refuses variadic/ABI metadata debt".into());
    }
    Ok(())
}
fn validate_logical_prefix(
    module: &Module,
    function: &trust_ir::Function,
    sig: &Signature,
    callee: &Signature,
    site: SiteKey,
) -> Result<(), String> {
    let ty = |value: ValueId| {
        function
            .typed_value(module, value)
            .map(|m| m.ty)
            .ok_or("prefix typed SSA value missing".to_string())
    };
    let body = &function.blocks[0].body;
    let mut defined = BTreeSet::new();
    for (value, _) in &function.blocks[0].params {
        if !defined.insert(*value) {
            return Err("duplicate SSA entry parameter".into());
        }
    }
    for (index, node) in body.iter().enumerate() {
        let mut results = BTreeSet::new();
        for value in &node.results {
            if defined.contains(value) || !results.insert(*value) {
                return Err("duplicate SSA definition in source prefix".into());
            }
        }
        let operands: Vec<ValueId> = match &node.inst {
            Inst::Const { .. } => Vec::new(),
            Inst::Copy { operand, .. } => vec![*operand],
            Inst::MakeClosure { captures, .. } => captures.clone(),
            Inst::Call { args, .. } => args.clone(),
            Inst::Return { values } => values.clone(),
            _ => return Err("unsupported SSA prefix node".into()),
        };
        if operands.iter().any(|value| !defined.contains(value)) {
            return Err("SSA prefix operand is used before its definition".into());
        }
        match &node.inst {
            Inst::Const { ty: declared, value } => {
                if !matches!(declared, IrTy::U64 | IrTy::I64)
                    || !matches!(value, Constant::Int(_))
                    || node.results.len() != 1
                    || ty(node.results[0])? != *declared
                {
                    return Err("prefix constant logical type/kind differs".into());
                }
            }
            Inst::Copy { ty: declared, operand } => {
                if node.results.len() != 1
                    || ty(*operand)? != *declared
                    || ty(node.results[0])? != *declared
                {
                    return Err(
                        "prefix Copy operand logical type differs from its declaration".into()
                    );
                }
            }
            Inst::MakeClosure { ty: nominal, func: target, captures } => {
                let closure =
                    module.closure_type(*nominal).ok_or("prefix nominal closure absent")?;
                let apparent =
                    module.func_type(closure.func).ok_or("prefix apparent signature absent")?;
                let target =
                    module.function_by_id(*target).ok_or("prefix closure target absent")?;
                let physical =
                    module.func_type(target.ty).ok_or("prefix target signature absent")?;
                let expected: Vec<_> =
                    closure.captures.iter().chain(&apparent.params).cloned().collect();
                if node.results.len() != 1
                    || ty(node.results[0])? != IrTy::Closure(*nominal)
                    || captures.len() != closure.captures.len()
                    || apparent.is_vararg
                    || physical.is_vararg
                    || physical.params != expected
                    || physical.returns != apparent.returns
                    || physical.abi != apparent.abi
                {
                    return Err(
                        "prefix MakeClosure whole nominal value/target signature differs".into()
                    );
                }
                for (value, expected) in captures.iter().zip(&closure.captures) {
                    if ty(*value)? != *expected {
                        return Err("prefix closure capture logical type differs".into());
                    }
                }
            }
            Inst::Call { args, .. } if index == site.1 => {
                if args.len() != callee.0.len() || node.results.len() != 1 || callee.1.len() != 1 {
                    return Err("call logical arity differs".into());
                }
                for (value, expected) in args.iter().zip(&callee.0) {
                    if ty(*value)? != *expected {
                        return Err(
                            "call argument logical type differs from exact callee signature".into(),
                        );
                    }
                }
                if ty(node.results[0])? != callee.1[0] {
                    return Err("call result logical type differs".into());
                }
            }
            Inst::Return { values } if index + 1 == body.len() => {
                if !node.results.is_empty()
                    || values != &body[site.1].results
                    || values.len() != sig.1.len()
                {
                    return Err("tail source return is not exactly the call result".into());
                }
                for (value, expected) in values.iter().zip(&sig.1) {
                    if ty(*value)? != *expected {
                        return Err("tail return logical type differs from caller signature".into());
                    }
                }
            }
            _ => return Err("unsupported typed prefix node".into()),
        }
        defined.extend(results);
    }
    Ok(())
}

fn mentions_name(formula: &Formula, name: &str) -> bool {
    let mut occurs = false;
    formula.visit(&mut |term| {
        if matches!(term,Formula::Var(n,_) if n==name)
            || matches!(term,Formula::SymVar(n,_) if n.as_str()==name)
        {
            occurs = true;
        }
    });
    occurs
}

/// Every step is checked against bound bytes and official complete effects,
/// including actual executor pre/post-state continuity. No complete flag input.
pub(super) struct PrefixTrace {
    window: FunctionWindow,
    expected: MachineState,
    next: u64,
    in_flight: Option<(u64, bool)>,
    terminal: bool,
    pcs: Vec<u64>,
    // Separate metadata mode; never supplies CompletePrefix/ordinary Execution.
    unwind: Option<(
        crate::cer_memory_machine::FunctionBinding,
        MachineState,
        Vec<(u64, MachineState)>,
    )>,
}
struct CompletePrefix {
    state: MachineState,
    pcs: Vec<u64>,
}
impl PrefixTrace {
    fn begin(window: &FunctionWindow, entry: &MachineState) -> Result<Self, String> {
        if window.sites.len() != 1 || window.sites[0].kind != MachineSiteKind::Tail {
            return Err("prefix has no unique named Tail site".into());
        }
        Ok(Self {
            window: window.clone(),
            expected: entry.clone(),
            next: window.start,
            in_flight: None,
            terminal: false,
            pcs: Vec::new(),
            unwind: None,
        })
    }
    pub(super) fn before(
        &mut self,
        pc: u64,
        path: &Formula,
        pre: &MachineState,
        effects: &[Effect],
    ) -> Result<(), String> {
        if self.terminal
            || self.in_flight.is_some()
            || pc != self.next
            || *path != Formula::Bool(true)
            || !same_state(pre, &self.expected)
            || self.pcs.len() >= 256
        {
            return Err("tail prefix traversal/state/path census is incomplete".into());
        }
        let index =
            usize::try_from(pc.checked_sub(self.window.start).ok_or("prefix precedes extent")?)
                .map_err(|_| "prefix index overflow")?;
        let bytes = self
            .window
            .code
            .get(index..index.checked_add(4).ok_or("prefix end overflow")?)
            .ok_or("prefix leaves actual extent")?;
        let decoded = decode_aarch64(bytes, pc).map_err(|e| format!("prefix decode: {e:?}"))?;
        if crate::pc_object_model::requires_runtime_placement(&decoded) {
            return Err("prefix has unplaced address data".into());
        }
        if Aarch64Semantics.effects(pre, &decoded).map_err(|e| format!("prefix effects: {e:?}"))?
            != effects
        {
            return Err("prefix effects differ from actual bound instruction".into());
        }
        let tail = pc == self.window.sites[0].offset;
        if tail
            && self.window.relocations.iter().any(|relocation| {
                relocation.offset == pc
                    && relocation.kind == crate::compiled_object::RelocKind::Branch26
            })
            && !crate::compiled_object::macho_branch26_operand_is_canonical(u32::from_le_bytes(
                bytes.try_into().map_err(|_| "short BR26 instruction")?,
            ))
        {
            return Err("tail BRANCH26 operand is not a zero-displacement placeholder".into());
        }
        let mut post = pre.clone();
        let mut branches = 0;
        let advance =
            Formula::BvAdd(b(pre.pc.clone()), b(Formula::BitVec { value: 4, width: 64 }), 64);
        let branch_target = effects.iter().find_map(|effect| {
            if let Effect::Branch { target } = effect { Some(target) } else { None }
        });
        for effect in effects {
            match effect {
                Effect::Branch { .. } if tail && decoded.opcode == Opcode::B => branches += 1,
                Effect::PcUpdate { value }
                    if (!tail && *value == advance) || (tail && branch_target == Some(value)) => {}
                Effect::RegWrite { index: register @ 0..=30, value, .. }
                    if !tail
                        && !mentions_sp(value)
                        && (*register <= 17 || self.unwind.is_some()) =>
                {
                    post.apply_effect(effect)
                        .map_err(|e| format!("prefix register effect: {e:?}"))?;
                }
                Effect::FlagUpdate { n, z, c, v }
                    if !tail && ![n, z, c, v].into_iter().any(mentions_sp) =>
                {
                    post.apply_effect(effect).map_err(|e| format!("prefix flag effect: {e:?}"))?;
                }
                _ => return Err(format!("empty-frame prefix rejects {}", effect.variant_name())),
            }
        }
        if tail {
            if branches != 1 || decoded.opcode != Opcode::B {
                return Err("tail prefix has no actual Branch effect".into());
            }
            if !crate::compiled_object::all_padding(&self.window.code[index + 4..]) {
                return Err("tail has non-padding unvisited bytes".into());
            }
        } else if branches != 0 || decoded.opcode == Opcode::B {
            return Err("prefix contains an extra branch".into());
        }
        if let Some((_, _, prefixes)) = self.unwind.as_mut() {
            // Includes the transfer instruction PRE-state, not abstract rely state.
            prefixes.push((pc, pre.clone()));
        }
        self.expected = post;
        self.in_flight = Some((pc, tail));
        Ok(())
    }
    pub(super) fn after(&mut self, post: &MachineState) -> Result<(), String> {
        let (pc, tail) = self.in_flight.take().ok_or("prefix post-state has no actual pre-step")?;
        if !same_state(post, &self.expected) {
            return Err("prefix full actual post-state differs".into());
        }
        self.pcs.push(pc);
        self.next = pc.checked_add(4).ok_or("prefix PC overflow")?;
        self.terminal = tail;
        Ok(())
    }
    fn finish(self) -> Result<CompletePrefix, String> {
        if self.unwind.is_some()
            || !self.terminal
            || self.in_flight.is_some()
            || self.pcs.is_empty()
        {
            return Err("tail prefix has no complete actual transfer".into());
        }
        Ok(CompletePrefix { state: self.expected, pcs: self.pcs })
    }
}

#[cfg(test)]
mod tests;

#[path = "leaf_call_instance/transition.rs"]
mod transition;

pub(super) use transition::compose_memory_tails;

#[path = "leaf_call_instance/tail_unwind.rs"]
pub(super) mod tail_unwind;
