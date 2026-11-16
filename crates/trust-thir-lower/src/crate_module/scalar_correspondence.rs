//! Additive, zero-authority observer of the actual assembled producer result.
//! No name join, output rewriting, verdict promotion, or census exclusion.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::io::{self, BufWriter, Write};

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefId, DefIndex, LOCAL_CRATE};
use trust_certify::scalar_mir::ScalarMirSuccessorFamily;
use trust_certify::scalar_mir::capture::{ScalarCaptureRegistry, ScalarPassObservation};
use trust_ir::{FuncId, Module, ProofDigest};

use super::{BodyRecord, json_escape};

pub(super) fn observe(
    tcx: TyCtxt<'_>,
    module: &Module,
    assigned: &[(u32, FuncId)],
    records: &[BodyRecord],
    expected: &[u32],
) {
    let Some(directory) = std::env::var_os("TRUST_SCALAR_CAPTURE_DIR") else {
        return;
    };
    let registry = tcx.sess.with_trust_compiler_state::<ScalarCaptureRegistry, _>(std::mem::take);
    let path = std::path::PathBuf::from(directory).join("actual-scalar-correspondence.json");
    let result =
        std::fs::OpenOptions::new().write(true).create_new(true).open(&path).and_then(|file| {
            let mut out = BufWriter::new(file);
            write_observation(tcx, module, assigned, records, expected, &registry, &mut out)?;
            out.flush()
        });
    if let Err(error) = result {
        eprintln!(
            "TRUST_SCALAR_CAPTURE_DIAGNOSTIC: output unavailable or incomplete at {}: {error}; no complete correspondence evidence published",
            path.display()
        );
    }
}

fn write_observation(
    tcx: TyCtxt<'_>,
    module: &Module,
    assigned: &[(u32, FuncId)],
    records: &[BodyRecord],
    expected: &[u32],
    registry: &ScalarCaptureRegistry,
    out: &mut impl Write,
) -> io::Result<()> {
    let mut indices: BTreeSet<u32> = expected.iter().copied().collect();
    indices.extend(records.iter().map(|record| record.def_index));
    indices.extend(registry.records.keys().copied());
    indices.extend(assigned.iter().map(|(index, _)| *index));
    let module_digest = module.stable_digest();
    write!(
        out,
        "{{\"schema\":\"trust.actual-scalar-model-correspondence.v1\",\"source_fidelity\":false,\"proof_authority\":false,\"verdict_changed\":false,\"module_digest\":\"{module_digest}\",\"expected_count\":{},\"producer_count\":{},\"assigned_count\":{},\"capture_count\":{},\"retained_source_bytes\":{},\"retained_body_bytes\":{},\"source_files\":[",
        expected.len(),
        records.len(),
        assigned.len(),
        registry.records.values().map(Vec::len).sum::<usize>(),
        registry.retained_source_bytes,
        registry.retained_body_bytes,
    )?;
    for (index, (identity, bytes)) in registry.sources.iter().enumerate() {
        if index != 0 {
            out.write_all(b",")?;
        }
        // At most 8 MiB of retained source payload, emitted once per exact
        // identity. JSON escaping expands it by at most six, not per body.
        write!(
            out,
            "{{\"identity\":\"{}\",\"normalized_source\":\"{}\"}}",
            json_escape(&format!("{identity:?}")),
            json_escape(bytes)
        )?;
    }
    out.write_all(b"],\"rows\":[")?;
    let function_counts = function_assignment_counts(assigned);
    let mut remaining_payload = 16 * 1024 * 1024_usize;
    let mut first = true;
    for index in indices {
        if !first {
            out.write_all(b",")?;
        }
        first = false;
        let captures = registry.records.get(&index).map(Vec::as_slice).unwrap_or(&[]);
        let producers: Vec<_> = records.iter().filter(|record| record.def_index == index).collect();
        let mappings: Vec<_> = assigned.iter().filter(|(def, _)| *def == index).collect();
        let expected_count = expected.iter().filter(|&&def| def == index).count();
        let capture_payload = bounded_capture_payload(captures, &mut remaining_payload);
        let selected = (|| {
            capture_payload.as_ref().map_err(Clone::clone)?;
            if !unique_population([expected_count, producers.len(), mappings.len(), captures.len()])
            {
                return Err(
                    "missing or duplicate expected/producer/mapping/capture identity".to_string()
                );
            }
            if function_counts.get(&mappings[0].1) != Some(&1) {
                return Err(
                    "assembled FuncId is assigned to more than one source occurrence".into()
                );
            }
            // Only independently enumerated actual compiler indices reach this query.
            let did = DefId { krate: LOCAL_CRATE, index: DefIndex::from_u32(index) };
            if producers[0].definition != crate::lineage::DefinitionIdentity::from_def_id(tcx, did)
            {
                return Err("producer definition identity changed".into());
            }
            let row = &captures[0];
            let family = select_pair(row, &format!("{:?}", tcx.def_path_hash(did)))?;
            Ok((row, mappings[0].1, family))
        })();
        let checked = selected.and_then(|(row, function, family)| {
            let after = row.after.as_ref().ok_or("missing actual post-pass body")?;
            let before = row.before.model.as_ref().map_err(Clone::clone)?;
            let after = after.model.as_ref().map_err(Clone::clone)?;
            let mir = trust_certify::scalar_mir::prove_successor_bridge_for_family(family, before, after)?;
            mir.replay()?;
            let ir = trust_certify::scalar_mir::actual_ir::prove_actual_successor_ir(module, function)?;
            ir.replay(module, function)?;
            Ok(format!("kernel-checked-model-correspondence-only; MIR family {:?}; MIR closure {} declarations; actual IR exhaustive UInt8 observation checked and replayed", mir.family(), mir.local_declarations()))
        });
        let (status, detail) = match checked {
            Ok(detail) => ("kernel-checked-model-only", detail),
            Err(detail) => ("refused", detail),
        };
        let (capture_text, capture_digest) = match capture_payload {
            Ok((text, digest)) => (text, digest.to_string()),
            Err(_) => (String::new(), String::new()),
        };
        let function_ids =
            mappings.iter().map(|(_, id)| id.index().to_string()).collect::<Vec<_>>().join(",");
        write!(
            out,
            "{{\"def_index\":{index},\"function_ids\":[{function_ids}],\"capture_count\":{},\"status\":\"{status}\",\"detail\":\"{}\",\"capture_digest\":\"{capture_digest}\",\"capture\":\"{}\"}}",
            captures.len(),
            json_escape(&detail),
            capture_text
        )?;
    }
    // Payload budgets never truncate the identity census. Compact refused
    // rows are still streamed for every index; their count scales with the
    // actual compiler population rather than being mislabeled a fixed cap.
    out.write_all(b"]}\n")
}

fn bounded_capture_payload<T: std::fmt::Debug + ?Sized>(
    value: &T,
    remaining: &mut usize,
) -> Result<(String, ProofDigest), String> {
    struct Bounded(String);
    impl std::fmt::Write for Bounded {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            if text.len() > (2 * 1024 * 1024_usize).saturating_sub(self.0.len()) {
                return Err(std::fmt::Error);
            }
            self.0.push_str(text);
            Ok(())
        }
    }
    let mut text = Bounded(String::new());
    write!(&mut text, "{value:#?}")
        .map_err(|_| "per-identity capture output payload exceeds bound")?;
    let encoded = json_escape(&text.0);
    if encoded.len() > *remaining {
        return Err("aggregate capture output payload exhausted; identity row retained".into());
    }
    *remaining -= encoded.len();
    Ok((encoded, ProofDigest::sha256_domain("trust.actual-scalar-capture.v1", text.0.as_bytes())))
}

fn function_assignment_counts(assigned: &[(u32, FuncId)]) -> BTreeMap<FuncId, usize> {
    let mut counts = BTreeMap::new();
    for (_, function) in assigned {
        *counts.entry(*function).or_insert(0) += 1;
    }
    counts
}

fn unique_population(counts: [usize; 4]) -> bool {
    counts == [1; 4]
}

fn select_pair(
    row: &ScalarPassObservation,
    expected_hash: &str,
) -> Result<ScalarMirSuccessorFamily, String> {
    if row.def_path_hash != expected_hash || row.pair_error.is_some() {
        return Err("captured definition or private pass pairing refused".into());
    }
    let after = row.after.as_ref().ok_or("missing actual post-pass body")?;
    if row.before.identity != after.identity
        || row.before.field_accounting != after.field_accounting
    {
        return Err("before/after source/phase/field-accounting identity changed".into());
    }
    let source_before = row.before.source.as_ref().map_err(Clone::clone)?;
    let source_after = after.source.as_ref().map_err(Clone::clone)?;
    if source_before != source_after {
        return Err("actual SourceFile contents/hash/span changed across the pass".into());
    }
    let before = row.before.model.as_ref().map_err(Clone::clone)?;
    let after = after.model.as_ref().map_err(Clone::clone)?;
    for family in [ScalarMirSuccessorFamily::CopyFixture, ScalarMirSuccessorFamily::CompilerMove] {
        if *before == family.before() && *after == family.after() {
            return Ok(family);
        }
    }
    Err("actual paired bodies are outside fixed scalar successor model".into())
}

#[cfg(test)]
mod tests {
    use trust_certify::scalar_mir::capture::{
        ScalarBodyObservation, ScalarSourceIdentity, ScalarSourceObservation,
    };

    use super::*;

    // Public model data are intentionally NOT a source authority. These tests
    // only exercise the diagnostic join's refusal, not rustc Body capture.
    fn pair() -> ScalarPassObservation {
        let before = ScalarBodyObservation {
            identity: "fixed same-Session test identity".into(),
            full_debug_body: "test model".into(),
            field_accounting: vec![("source", "retained")],
            source: Ok(ScalarSourceObservation {
                identity: ScalarSourceIdentity {
                    file_name: "fixture.rs".into(),
                    stable_source_id: "test".into(),
                    original_source_hash: "test-original".into(),
                    normalized_source_hash: "test-normalized".into(),
                },
                normalized_source: "fn successor(value:u8)->u16{(value as u16)+1}".into(),
                body_span: "test-span".into(),
            }),
            model: Ok(trust_certify::scalar_mir::successor_before()),
        };
        let mut after = before.clone();
        after.model = Ok(trust_certify::scalar_mir::successor_after());
        ScalarPassObservation {
            sequence: 0,
            def_path_hash: "test-def".into(),
            before,
            after: Some(after),
            pair_error: None,
        }
    }

    #[test]
    fn scalar_capture_join_preserves_exact_move_family_and_rejects_mixed_pair() {
        let mut row = pair();
        assert_eq!(select_pair(&row, "test-def").unwrap(), ScalarMirSuccessorFamily::CopyFixture);
        row.before.model = Ok(ScalarMirSuccessorFamily::CompilerMove.before());
        assert!(select_pair(&row, "test-def").is_err());
        row.after.as_mut().unwrap().model = Ok(ScalarMirSuccessorFamily::CompilerMove.after());
        assert_eq!(select_pair(&row, "test-def").unwrap(), ScalarMirSuccessorFamily::CompilerMove);
        row.before.model = Ok(ScalarMirSuccessorFamily::CopyFixture.before());
        assert!(select_pair(&row, "test-def").is_err());
    }

    #[test]
    fn scalar_capture_join_checks_definition_pair_source_and_full_models() {
        let original = pair();
        assert!(select_pair(&original, "test-def").is_ok());
        assert!(select_pair(&original, "different-def").is_err());
        let mut changes = Vec::new();
        let mut row = original.clone();
        row.after = None;
        changes.push(row);
        let mut row = original.clone();
        row.pair_error = Some("stale".into());
        changes.push(row);
        let mut row = original.clone();
        row.after.as_mut().unwrap().identity.push('x');
        changes.push(row);
        let mut row = original.clone();
        row.after.as_mut().unwrap().field_accounting.clear();
        changes.push(row);
        let mut row = original.clone();
        row.before.source = Err("source unavailable".into());
        changes.push(row);
        let mut row = original.clone();
        row.after.as_mut().unwrap().source.as_mut().unwrap().normalized_source =
            "changed source".into();
        changes.push(row);
        let mut row = original.clone();
        row.after
            .as_mut()
            .unwrap()
            .source
            .as_mut()
            .unwrap()
            .identity
            .original_source_hash
            .push('x');
        changes.push(row);
        let mut row = original.clone();
        row.before.model = Err("required constants unknown".into());
        changes.push(row);
        let mut row = original.clone();
        row.after.as_mut().unwrap().model = original.before.model.clone();
        changes.push(row);
        let mut row = original.clone();
        row.before.model.as_mut().unwrap().blocks[0].statements.clear();
        changes.push(row);
        for (i, row) in changes.iter().enumerate() {
            assert!(select_pair(row, "test-def").is_err(), "mutation {i}");
        }
    }

    #[test]
    fn scalar_capture_join_refuses_each_missing_or_duplicate_population() {
        assert!(unique_population([1; 4]));
        for index in 0..4 {
            for count in [0, 2, usize::MAX] {
                let mut counts = [1; 4];
                counts[index] = count;
                assert!(!unique_population(counts), "population {index} count {count}");
            }
        }
    }

    #[test]
    fn scalar_capture_join_refuses_duplicate_function_ids_even_across_distinct_definitions() {
        let first = FuncId::new(0);
        let second = FuncId::new(1);
        let distinct = function_assignment_counts(&[(7, first), (8, second)]);
        assert_eq!(distinct.get(&first), Some(&1));
        assert_eq!(distinct.get(&second), Some(&1));
        let aliased = function_assignment_counts(&[(7, first), (8, first)]);
        assert_eq!(aliased.get(&first), Some(&2));
        let repeated = function_assignment_counts(&[(7, first), (7, first)]);
        assert_eq!(repeated.get(&first), Some(&2));
        assert_eq!(function_assignment_counts(&[]).get(&first), None);
    }

    #[test]
    fn scalar_capture_output_budget_is_checked_before_consumption_and_never_partially_admits() {
        let mut remaining = 1024;
        assert!(bounded_capture_payload(&pair(), &mut remaining).is_err());
        assert_eq!(remaining, 1024);
        let (text, _) = bounded_capture_payload(&"small", &mut remaining).unwrap();
        assert_eq!(remaining, 1024 - text.len());
        let previous = remaining;
        assert!(bounded_capture_payload(&"\n".repeat(2 * 1024 * 1024), &mut remaining).is_err());
        assert_eq!(remaining, previous);
        remaining = 0;
        assert!(bounded_capture_payload(&[] as &[u8], &mut remaining).is_err());
        assert_eq!(remaining, 0);
    }
}
