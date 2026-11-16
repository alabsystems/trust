//! A distinct actual-machine prefix capability for ZERO_FRAME Tail records.
//! It grants metadata recovery authority only, never ordinary leaf/caller proof
//! authority. Mathematical TailExecution cannot be converted into this type.
use super::*;
use crate::cer_memory_machine::{BoundFunction, FunctionBinding};

pub(crate) struct ActualTailUnwindPrefixes {
    binding: FunctionBinding,
    entry: MachineState,
    prefixes: Vec<(u64, MachineState)>,
}
impl ActualTailUnwindPrefixes {
    pub(crate) fn prefixes(
        &self,
    ) -> Result<(&FunctionBinding, &MachineState, &[(u64, MachineState)]), String> {
        if self.prefixes.is_empty() || self.prefixes.len() > 11 {
            return Err("tail unwind prefix population exceeds retained bound".into());
        }
        Ok((&self.binding, &self.entry, &self.prefixes))
    }
    pub(in crate::call_event) fn derive(
        input: &CerInput<'_>,
        layout: &ObjectLayout,
        symbol: &str,
    ) -> Result<Self, String> {
        // Rebind original bytes internally. No mutable FunctionWindow or wire
        // census is accepted as machine execution authority.
        let bound = BoundFunction::bind(input.object, input.m_cg, symbol, input.relocation_model)?;
        let window = bound.window();
        if layout.object.format != ObjectFormat::MachO
            || layout.windows.get(symbol) != Some(window)
            || window.sites.len() != 1
            || window.sites[0].kind != MachineSiteKind::Tail
            || window.sites[0].in_trap_tail
            || window
                .relocations
                .iter()
                .any(|r| r.role != "tail" || r.offset != window.sites[0].offset)
        {
            return Err("unwind requires the exact one-site canonical named B Tail".into());
        }
        let site = &window.sites[0];
        let target = site.callee.as_ref().ok_or("unwind Tail has no actual named target")?;
        let callee = layout.windows.get(target).ok_or("unwind Tail target is not co-emitted")?;
        if !callee.expected.non_preemptible
            || !callee.unknown.is_empty()
            || !callee.sites.is_empty()
            || !callee.relocations.is_empty()
        {
            return Err("unwind Tail target is not an actual nonpreemptible call-free body".into());
        }
        // Retain the actual entry ABI/domain and full source/P identities. The
        // recovery equations below do not assume favorable function semantics.
        let body = input.bodies.get(symbol).ok_or("unwind caller source absent")?;
        let producer = input.producers.get(body.producer).ok_or("unwind source producer absent")?;
        let module = producer.module.as_ref();
        let function = module.function_by_id(body.func).ok_or("unwind function absent")?;
        let codegen = input
            .m_cg
            .functions
            .iter()
            .find(|f| f.name == symbol)
            .ok_or("unwind M_cg body absent")?;
        let signature = signature_of(module, function.ty)?;
        let place = input.placements.get(symbol).ok_or("unwind caller P absent")?;
        let callee_place = input.placements.get(target).ok_or("unwind Tail P absent")?;
        if !matches!(function.calling_conv, CallingConv::C | CallingConv::Rust)
            || !scalar64(place)
            || !scalar64(callee_place)
            || codegen.calling_conv != function.calling_conv
            || signature_of(input.m_cg, codegen.ty)? != signature
            || !abi_extensions::qualified_target(module)
            || !abi_extensions::qualified_target(input.m_cg)
        {
            return Err("unwind Tail entry is outside the qualified scalar64 ABI/domain".into());
        }
        plain_signature(module, function)?;
        plain_signature(input.m_cg, codegen)?;
        check_placement(module, &signature, function.calling_conv, place, true)
            .map_err(|e| format!("unwind actual entry P: {e:?}"))?;
        let mut entry = MachineState::symbolic();
        abi_extensions::Plan::new(
            module,
            function.calling_conv,
            &signature.0,
            &signature.1,
            place,
            true,
        )?
        .apply_entry(&mut entry);
        let places = BTreeMap::from([(site.offset, callee_place.clone())]);
        let mut exec = CerExec::new(window, &places, &place.ret, true);
        let mut trace = PrefixTrace::begin(window, &entry)?;
        trace.unwind = Some((bound.binding().clone(), entry.clone(), Vec::new()));
        exec.tail_instance_trace = Some(trace);
        // Only sealed completion BEFORE abstract Tail rely is consumed. A
        // later rely/return result is neither recovery nor function authority.
        let _ = exec.run(window.start, entry, Vec::new(), 0, false, Formula::Bool(true));
        exec.tail_instance_trace.take().ok_or("unwind actual trace missing")?.finish_unwind()
    }
}
impl PrefixTrace {
    fn finish_unwind(self) -> Result<ActualTailUnwindPrefixes, String> {
        if !self.terminal || self.in_flight.is_some() || self.pcs.is_empty() {
            return Err("unwind Tail traversal did not cover the actual transfer".into());
        }
        let (binding, entry, prefixes) =
            self.unwind.ok_or("ordinary instance trace has no unwind capability")?;
        if prefixes.len() != self.pcs.len()
            || prefixes.iter().zip(&self.pcs).any(|((pc, _), observed)| pc != observed)
        {
            return Err("unwind Tail PRE-state population differs from actual steps".into());
        }
        let witness = ActualTailUnwindPrefixes { binding, entry, prefixes };
        witness.prefixes()?;
        Ok(witness)
    }
}

pub(in crate::call_event) fn check_records(
    input: &CerInput<'_>,
    layout: &ObjectLayout,
    inventory: &Result<compact_unwind::Inventory, String>,
    certificates: &mut [FunctionCertificate],
    checked: &mut Vec<compact_unwind::CheckedRecord>,
    replay: Option<&BTreeMap<String, OriginalReplayWireRow>>,
) {
    let Ok(inventory) = inventory else { return };
    for certificate in certificates {
        if certificate.compact_unwind.is_some() || !inventory.supports(&certificate.symbol) {
            continue;
        }
        let result = (|| {
            let trace = ActualTailUnwindPrefixes::derive(input, layout, &certificate.symbol)?;
            // Construct expected subject from ACTUAL input, never an untrusted
            // report's extent/source/P/section fields. This is not a grade.
            let window = layout.windows.get(&certificate.symbol).ok_or("unwind window absent")?;
            let fresh = fresh_certificate(input, layout, window)?;
            let retained = match replay {
                Some(rows) => {
                    Some(rows.get(&certificate.symbol).and_then(|row| row.compact_unwind.as_ref()))
                }
                None => None,
            };
            inventory.check_tail(input, &fresh, &trace, retained)
        })();
        if let Ok(record) = result {
            certificate.compact_unwind = Some(record.certificate().clone());
            checked.push(record);
        }
    }
}
