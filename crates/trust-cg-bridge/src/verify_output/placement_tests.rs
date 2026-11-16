//! Pure decoder/executor observations; these words are data, never native code.

use super::*;

fn words(code: &[u32]) -> Vec<u8> {
    code.iter().flat_map(|word| word.to_le_bytes()).collect()
}

#[test]
fn constant_register_branch_requires_runtime_placement() {
    for base in [0u64, 0x1000] {
        // The literal equals an in-object instruction coordinate. That numeric
        // coincidence grants no mapping from a runtime address to this object.
        let mov_x9 = 0xd280_0009 | (((base + 8) as u32) << 5);
        let code = words(&[mov_x9, 0xd61f_0120, 0xd280_0000, 0xd65f_03c0]);
        let error = symbolic_machine_output(&code, base, 64, false).unwrap_err();
        assert!(error.contains("runtime placement witness is absent"), "{error}");
        let error = symbolic_machine_outcome_traps(&code, base, 64, false)
            .err()
            .expect("trap execution must refuse the unplaced register target");
        assert!(error.contains("runtime placement witness is absent"), "{error}");
        let error = symbolic_machine_segment(
            &code,
            base,
            64,
            base,
            MachineState::symbolic(),
            &HashSet::from([base + 8]),
        )
        .err()
        .expect("a claimed cut point must not authorize an unplaced register target");
        assert!(error.contains("runtime placement witness is absent"), "{error}");
    }
}

#[test]
fn register_call_cannot_use_a_branch_relocation_to_bypass_placement() {
    let code = words(&[0xd280_0109, 0xd63f_0120, 0xd280_0000, 0xd65f_03c0]);
    let error = symbolic_machine_output(&code, 0, 64, false).unwrap_err();
    assert!(error.contains("runtime placement witness is absent"), "{error}");
    let env = CalleeEnv::empty();
    let relocations = HashMap::from([(4, BranchReloc::Call("callee".into()))]);
    let executor = PathMergingExecutor::new_env(&code, 0, 64, false, &env, &relocations);
    let error = executor.decode_at(4).unwrap_err();
    assert!(error.contains("not the canonical zero-displacement B/BL placeholder"), "{error}");
}

#[test]
fn relative_branch_and_return_keep_their_object_coordinate_semantics() {
    for base in [0, 0x1000] {
        let code = words(&[0x1400_0002, 0xd280_0020, 0xd280_0000, 0xd65f_03c0]);
        let value = symbolic_machine_output(&code, base, 64, false).unwrap();
        assert_eq!(value, Formula::BitVec { value: 0, width: 64 });
        let outcome = symbolic_machine_outcome_traps(&code, base, 64, false).unwrap();
        assert_eq!(outcome.value, value);
        assert_eq!(outcome.reach, Formula::Bool(true));
    }
}
