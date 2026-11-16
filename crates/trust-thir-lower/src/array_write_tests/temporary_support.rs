//! A cast-created array is a writable temporary, not the original local's place.

use trust_ir::{Inst, Module};

use super::{A, Arg, B, Observation, Outcome, after_store, run};

const TEMPORARIES: [&str; 3] =
    ["cast_temporary_write", "cast_temporary_index_reseats", "cast_temporary_rhs_reseats"];

fn after_temporary_write(array: [u8; 4], index: u64, read: u64) -> Outcome {
    if index >= 4 || read >= 4 { Outcome::Panic } else { Outcome::Returned(array[read as usize]) }
}

/// Exactly the independently compiled native Rust360 population. The promoted
/// destination is separately counted as unsupported, never silently interpreted.
pub fn observe(module: &Module) -> Vec<Observation> {
    let mut cases = Vec::new();
    let mut add = |function, args: &[Arg], expected| {
        cases.push(Observation {
            function,
            args: args.to_vec(),
            expected,
            actual: run(module, function, args),
        });
    };
    for index in [0, 1, 2, 3, 4, u64::MAX] {
        for read in [0, 1, 2, 3, 4] {
            for value in [5, 77, 129] {
                let args = [Arg::Array(A), Arg::Index(index), Arg::Byte(value), Arg::Index(read)];
                add("cast_temporary_write", &args, after_temporary_write(A, index, read));
                add("ordinary_array_write", &args, after_store(A, index, value, read));
                let args = [
                    Arg::Array(A),
                    Arg::Array(B),
                    Arg::Index(index),
                    Arg::Byte(value),
                    Arg::Index(read),
                ];
                add("cast_temporary_index_reseats", &args, after_temporary_write(B, index, read));
                add("cast_temporary_rhs_reseats", &args, after_temporary_write(B, index, read));
            }
        }
    }
    assert_eq!(cases.len(), 360);
    cases
}

fn module() -> Module {
    let path = std::env::var_os("TRUST_ARRAY_TEMPORARY_WRITE_IR")
        .expect("fresh compiler-bound array temporary-write IR required");
    let bytes = std::fs::read(path).unwrap();
    assert!(bytes.len() < 4 * 1024 * 1024);
    let module = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn check_subject(module: &Module) {
    // Run the actual values first so stale producers fail with a source case,
    // independently of these additional instruction-shape assertions.
    for row in observe(module) {
        assert_eq!(row.actual, row.expected, "{row:?}");
    }
    for name in TEMPORARIES.into_iter().chain(["ordinary_array_write"]) {
        let found: Vec<_> = module.functions.iter().filter(|f| f.name == name).collect();
        assert_eq!(found.len(), 1);
        let f = found[0];
        let entry = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
        let nodes: Vec<_> = f.blocks.iter().flat_map(|b| &b.body).collect();
        assert_eq!(nodes.iter().filter(|n| matches!(n.inst, Inst::Assert { .. })).count(), 2);
        let writes: Vec<_> =
            nodes.iter().filter(|n| matches!(n.inst, Inst::InsertElement { .. })).collect();
        let reads: Vec<_> =
            nodes.iter().filter(|n| matches!(n.inst, Inst::ExtractElement { .. })).collect();
        assert_eq!(writes.len(), 1, "do not erase the temporary write");
        assert_eq!(reads.len(), 1);
        let Inst::InsertElement { array: written, .. } = writes[0].inst else { unreachable!() };
        let Inst::ExtractElement { array: returned, .. } = reads[0].inst else { unreachable!() };
        let captured = usize::from(name == "cast_temporary_rhs_reseats");
        assert_eq!(written, entry.params[captured].0, "wrong capture point for {name}");
        if name == "ordinary_array_write" {
            assert_eq!(returned, writes[0].results[0]);
        } else {
            let current = usize::from(name != "cast_temporary_write");
            assert_eq!(returned, entry.params[current].0, "temporary rebound original local");
            assert_ne!(returned, writes[0].results[0]);
        }
        let obligations: Vec<_> =
            module.proof_obligations.iter().filter(|r| r.function == Some(f.id)).collect();
        assert_eq!(obligations.len(), 2);
        assert!(obligations.iter().all(|r| r.status == trust_ir::ProofStatus::Pending));
    }
}

#[test]
#[ignore = "requires freshly emitted compiler-bound array temporary assignment module"]
fn actual_array_temporary_writes_preserve_original_places() {
    check_subject(&module());
}

#[test]
#[ignore = "requires fixed subject; changed IR is diagnostic only"]
fn actual_array_temporary_controls_detect_wrong_writeback_and_bounds() {
    let module = module();
    check_subject(&module);
    for name in TEMPORARIES {
        let mut wrong = module.clone();
        let f = wrong.functions.iter_mut().find(|f| f.name == name).unwrap();
        let writes: Vec<_> = f
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|n| matches!(n.inst, Inst::InsertElement { .. }))
            .map(|n| n.results[0])
            .collect();
        assert_eq!(writes.len(), 1);
        let mut edits = 0;
        for n in f.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let Inst::ExtractElement { array, .. } = &mut n.inst {
                assert_ne!(*array, writes[0]);
                *array = writes[0];
                edits += 1;
            }
        }
        assert_eq!(edits, 1);
        let mut args = vec![Arg::Array(A)];
        if name != "cast_temporary_write" {
            args.push(Arg::Array(B));
        }
        args.extend([Arg::Index(1), Arg::Byte(129), Arg::Index(1)]);
        assert_eq!(run(&wrong, name, &args), Outcome::Returned(129));
    }
    let mut dropped = module.clone();
    let f = dropped.functions.iter_mut().find(|f| f.name == "ordinary_array_write").unwrap();
    let original = f.blocks.iter().find(|b| b.id == f.entry).unwrap().params[0].0;
    let mut edits = 0;
    for n in f.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::ExtractElement { array, .. } = &mut n.inst {
            assert_ne!(*array, original);
            *array = original;
            edits += 1;
        }
    }
    assert_eq!(edits, 1);
    let args = [Arg::Array(A), Arg::Index(1), Arg::Byte(129), Arg::Index(1)];
    assert_eq!(run(&dropped, "ordinary_array_write", &args), Outcome::Returned(22));

    let mut reversed = module.clone();
    let f = reversed.functions.iter_mut().find(|f| f.name == "cast_temporary_write").unwrap();
    let n = f
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.body)
        .find(|n| matches!(n.inst, Inst::ICmp { .. }))
        .unwrap();
    let Inst::ICmp { op, .. } = &mut n.inst else { unreachable!() };
    assert_eq!(*op, trust_ir::ICmpOp::Ult);
    *op = trust_ir::ICmpOp::Uge;
    assert_eq!(run(&reversed, "cast_temporary_write", &args), Outcome::Panic);
}
