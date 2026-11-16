//! Complete original caller transition for a sealed same-object empty-frame Tail.
//! A specialized callee statement is checked against independently rebuilt
//! source/machine transitions before it can withdraw the ordinary M5 frontier.
use super::*;

struct ActualTransition {
    context: TailContext,
    expected: leaf_memory::ExpectedOriginal,
}

fn context(
    input: &CerInput<'_>,
    layout: &ObjectLayout,
    caller: &str,
) -> Result<TailContext, String> {
    let window = layout.windows.get(caller).ok_or("tail caller window missing")?;
    if window.sites.len() != 1 || window.sites[0].kind != MachineSiteKind::Tail {
        return Err("memory composition requires one actual named Tail".into());
    }
    let symbol = window.sites[0].callee.as_deref().ok_or("tail target unnamed")?;
    let model = LeafModel::actual(input, layout, symbol)?;
    let query = format!("CER_LEAF_QUERY@{}:{}", layout.object.sha256_hex(), caller);
    TailContext::derive(input, layout, window, &model, query)
}

/// Rebuild full actual source expansion and execute the actual callee bytes
/// from the sealed Tail boundary. The returned goal contains no abstract
/// CER_S/CER_R/call-post-memory rely variables and invokes no solver/prover.
fn reconstruct(
    input: &CerInput<'_>,
    layout: &ObjectLayout,
    context: TailContext,
    finite_coverage_witnesses: &[(Formula, Formula)],
) -> Result<ActualTransition, String> {
    let callee = &context.binding.callee_symbol;
    let body = input.bodies.get(callee).ok_or("actual tail source leaf body missing")?;
    let producer =
        input.producers.get(body.producer).ok_or("actual source leaf producer missing")?;
    let module = producer.module.as_ref();
    let function = module.function_by_id(body.func).ok_or("actual source leaf function missing")?;
    leaf_memory::replay_source_shape(function)?;
    let callee_place = input.placements.get(callee).ok_or("actual leaf P missing")?;
    let sig = signature_of(module, function.ty)?;
    check_placement(module, &sig, function.calling_conv, callee_place, true)
        .map_err(|e| format!("source leaf placement: {e:?}"))?;
    let spec = eval_spec(input, module, function, &sig, callee_place, &BTreeMap::new())?;
    let source = leaf_memory::Source::read(module, function, &spec, input.m_cg, callee)?
        .at_empty_tail(&context)?;
    let bound = crate::cer_memory_machine::BoundObject::bind(
        input.object,
        input.m_cg,
        input.relocation_model,
    )?;
    let actual_callee = bound.function(callee)?;
    let callee_window = layout.windows.get(callee).ok_or("actual machine leaf missing")?;
    let no_calls = BTreeMap::new();
    let mut exec = CerExec::new(callee_window, &no_calls, &callee_place.ret, true);
    exec.leaf_trace =
        Some(leaf_memory::Trace::begin(&actual_callee, callee_window, &context.tail)?);
    let outcome = exec.run(
        callee_window.start,
        context.tail.clone(),
        Vec::new(),
        0,
        false,
        Formula::Bool(true),
    )?;
    if let Some(error) = exec.leaf_refusal {
        return Err(error);
    }
    let execution =
        exec.leaf_trace.take().ok_or("complete actual leaf execution absent")?.finish()?;
    let actual_caller = bound.function(&context.binding.caller_symbol)?;
    let execution = execution.at_empty_tail(&context, &actual_caller)?;
    let inputs = leaf_memory::KernelInputs::derive_tail_original(
        source,
        execution,
        finite_coverage_witnesses,
    )?;
    let caller_body =
        input.bodies.get(&context.binding.caller_symbol).ok_or("actual caller source missing")?;
    let caller_producer =
        input.producers.get(caller_body.producer).ok_or("actual caller producer missing")?;
    let caller_function = caller_producer
        .module
        .function_by_id(caller_body.func)
        .ok_or("actual caller function missing")?;
    let caller_place =
        input.placements.get(&context.binding.caller_symbol).ok_or("actual caller P missing")?;
    let caller_sig = signature_of(&caller_producer.module, caller_function.ty)?;
    let caller_abi = abi_extensions::Plan::new(
        &caller_producer.module,
        caller_function.calling_conv,
        &caller_sig.0,
        &caller_sig.1,
        caller_place,
        true,
    )?;
    let expected = inputs.expected_tail(caller_place, &caller_abi, &outcome, &context.bindings)?;
    Ok(ActualTransition { context, expected })
}

/// Reuse the ACTUAL already checked callee proof; reconstruct the complete
/// caller goal first and require exact correspondence before ONE kernel check.
/// No call to proof production, SAT, original leaf replay or compiler occurs.
pub(super) fn produce(
    input: &CerInput<'_>,
    layout: &ObjectLayout,
    caller: &str,
    provider: &ActualLeafProof,
) -> Result<leaf_memory::Closed, String> {
    let context = context(input, layout, caller)?;
    if context.binding.callee != provider.binding
        || context.binding.callee_symbol != provider.symbol
    {
        return Err(
            "actual complete caller transition targets a different checked leaf subject".into()
        );
    }
    let substitution = context.substitution(&provider.checked)?;
    let mapped = map_original(provider.checked.original_equations(), &substitution)?;
    let actual = reconstruct(input, layout, context, &mapped)?;
    let checked =
        crate::original_conjunction_certificate::specialize_original_for_expected_transition(
            &provider.checked,
            &substitution,
            &actual.context.bindings,
            actual.expected.equations(),
        )?;
    actual.expected.finish(ProvenEvidence::KernelInstantiated {
        theorem: checked.label().into(),
        original: Some(Arc::new(checked)),
    })
}

fn replay(
    input: &CerInput<'_>,
    layout: &ObjectLayout,
    caller: &str,
    packet: &crate::original_conjunction_certificate::OriginalConjunctionCertificate,
) -> Result<leaf_memory::Closed, String> {
    let context = context(input, layout, caller)?;
    let finite = packet
        .original_equations()
        .get(context.bindings.len()..)
        .ok_or("retained original caller source-byte witnesses missing")?;
    let actual = reconstruct(input, layout, context, finite)?;
    let checked = packet.replay(actual.expected.equations())?;
    actual.expected.finish(ProvenEvidence::KernelInstantiated {
        theorem: checked.label().into(),
        original: Some(Arc::new(checked)),
    })
}

fn fresh_caller(
    input: &CerInput<'_>,
    layout: &ObjectLayout,
    caller: &str,
) -> Result<FunctionCertificate, String> {
    let window = layout.windows.get(caller).ok_or("caller extent missing")?;
    let context = context(input, layout, caller)?;
    let mut cert = fresh_certificate(input, layout, window)?;
    let callee = &context.binding.callee_symbol;
    cert.placement_sha256.insert(callee.clone(), input.placements[callee].digest());
    cert.call_sites.push(CallSiteRecord {
        offset: Some(context.binding.machine_pc),
        reloc: window.sites[0].reloc.map(|kind| kind.name()),
        symbol: callee.clone(),
        ir_site: site_name(context.binding.source_site),
        kind: CallSiteKind::Tail,
    });
    cert.assumptions.push(Assumption::CoEmitted(callee.clone()));
    Ok(cert)
}
fn metadata_matches(row: &OriginalReplayWireRow, cert: &FunctionCertificate) -> bool {
    row.symbol == cert.symbol
        && row.linkage == cert.linkage
        && row.section == cert.section
        && row.extent == cert.extent
        && row.text_sha256 == cert.text_sha256
        && row.producer_ir_sha256 == cert.producer_ir_sha256
        && row.placement_sha256 == cert.placement_sha256
}
fn admit(
    input: &CerInput<'_>,
    mut cert: FunctionCertificate,
    closed: leaf_memory::Closed,
) -> Result<FunctionCertificate, String> {
    let evidence = closed.into_evidence();
    let ProvenEvidence::KernelInstantiated { original: Some(checked), .. } = &evidence else {
        return Err("complete tail theorem has no retained original kernel proof".into());
    };
    cert.original_proof =
        Some(crate::original_conjunction_certificate::OriginalConjunctionCertificate::bind(
            checked, input, &cert,
        )?);
    cert.obligations.o0_abi = ObligationGrade::proven(
        "complete caller raw GPR/SP/Dreg/return-target and physical entry equations are in the retained original kernel theorem; actual prefix/leaf never writes X18",
    );
    cert.obligations.o1_binding = ObligationGrade::proven(
        "same-object nonpreemptible actual source/callee/P/target/relocation and canonical Tail operand rebound before full caller proof use",
    );
    cert.obligations.o2_pairing = ObligationGrade::proven(
        "one complete typed source Call/Return equals one authenticated actual empty-frame Tail followed by the exact call-free callee bytes",
    );
    cert.obligations.o3_events = ObligationGrade::proven(
        "every original actual argument binding and every reached machine read/write byte has source coverage in the complete checked caller transition",
    );
    cert.obligations.o4_return = ObligationGrade::proven(
        "actual caller physical return and entire source/machine exit arrays agree at a fresh unrestricted64 query in ONE retained original CIC theorem",
    );
    cert.obligations.o5_frame = ObligationGrade::proven(
        "M5 bounded Tail composition: exact common M0, complete zero-frame/no-SP prefix plus actual leaf effects, source call memory threading and full original caller theorem checked; no ordinary abstract rely premise used",
    );
    finish(&mut cert, Some(evidence));
    if !cert.is_kernel_proved() || cert.original_proof.is_none() {
        return Err("complete checked caller theorem did not retain favorable packet".into());
    }
    Ok(cert)
}

/// Called AFTER the ordinary M5 downgrade and BEFORE closure/report limits.
/// Only the bounded complete caller theorem may withdraw its specific frontier.
pub(in crate::call_event) fn compose_memory_tails(
    input: &CerInput<'_>,
    layout: &ObjectLayout,
    certificates: &mut [FunctionCertificate],
    providers: &BTreeMap<String, ActualLeafProof>,
    pending_memory_callers: &BTreeSet<String>,
    retained: Option<&BTreeMap<String, OriginalReplayWireRow>>,
    retain_scalar_original: bool,
) {
    let splits = SplitIndex::new(input);
    for cert in certificates {
        if matches!(cert.verdict, OutputVerdict::Refuted { .. }) {
            continue;
        }
        // Production withdraws its M5 frontier only with the complete caller
        // theorem. An already-Kernel zero-memory scalar tail may also RETAIN
        // that same stronger theorem; unsupported/Refuted production rows are
        // not promoted through this optional retention path. Replay starts
        // fresh and never relies on untrusted old wire grades.
        let scalar_retention =
            retain_scalar_original && cert.is_kernel_proved() && cert.original_proof.is_none();
        if retained.is_none() && !pending_memory_callers.contains(&cert.symbol) && !scalar_retention
        {
            continue;
        }
        let Ok(fresh) = fresh_caller(input, layout, &cert.symbol) else {
            continue;
        };
        let Some(provider) = fresh.call_sites.first().and_then(|site| providers.get(&site.symbol))
        else {
            continue;
        };
        let mut blocked = Obligations {
            o0_abi: ObligationGrade::not_reached(),
            o1_binding: ObligationGrade::not_reached(),
            o2_pairing: ObligationGrade::not_reached(),
            o3_events: ObligationGrade::not_reached(),
            o4_return: ObligationGrade::not_reached(),
            o5_frame: ObligationGrade::not_reached(),
        };
        if block_unknown_variadic_split(input, &splits, &cert.symbol, &mut blocked) {
            continue;
        }
        let result = match retained {
            None => produce(input, layout, &cert.symbol, provider),
            Some(rows) => {
                let Some(row) = rows.get(&cert.symbol) else {
                    continue;
                };
                let Some(packet) = row.original_proof.as_ref() else {
                    continue;
                };
                if !metadata_matches(row, &fresh) || packet.require_subject(input, &fresh).is_err()
                {
                    continue;
                }
                replay(input, layout, &cert.symbol, packet)
            }
        };
        match result.and_then(|closed| admit(input, fresh, closed)) {
            Ok(proved) => *cert = proved,
            Err(error) if retained.is_some() => {
                // The leaf-only first phase may have a generic metadata/shape
                // refusal. This phase reached the independently bound complete
                // caller theorem, so report its actual decline instead.
                cert.obligations.o4_return = ObligationGrade::unknown(format!(
                    "complete bounded caller transition replay declined: {error}"
                ));
                finish(cert, None);
            }
            Err(_) => {} // Unsupported/mismatched theorem is never Refuted.
        }
    }
}
