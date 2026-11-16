//! The legacy byte reader must validate the actual operand as well as its symbol.
use super::*;
#[path = "../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{Linkage as IrLinkage, Ty as IrTy};

#[test]
fn actual_macho_relocated_operand_is_checked_before_legacy_vot_effects() {
    let fixture = compiler_fixture();
    let report = fixture.report();
    assert!(
        report.certificate("constant_leaf").unwrap().is_kernel_proved(),
        "{}",
        explain(&report)
    );
    let parsed = crate::compiled_object::CompiledObject::parse(&fixture.object).unwrap();
    let expectations = crate::compiled_object::ObjectExpectations::from_module(
        &fixture.m_cg,
        parsed.format,
        fixture.model,
    )
    .unwrap();
    let layout = crate::compiled_object::ObjectLayout::bind(parsed, &expectations).unwrap();
    let window = &layout.windows["constant_caller"];
    let original_relocations = parse_text_branch26_relocs(&fixture.object).unwrap();
    let relocation = original_relocations.get(&window.start).unwrap();
    assert!(matches!(relocation,BranchReloc::Call(name) if name=="constant_leaf"));
    // The model environment is backed by the independently Kernel-checked actual
    // constant callee above, never an external declaration or favorable wire label.
    let mut environment = CalleeEnv::empty();
    environment.callees.insert(
        "constant_leaf".into(),
        CalleePure {
            output: Formula::BitVec { value: 7, width: 64 },
            arg_count: 1,
            arg_reg_widths: vec![64],
            ret_reg_width: 64,
        },
    );
    let relocations = HashMap::from([(0, relocation.clone())]);
    let canonical = symbolic_machine_outcome_env(
        &window.code,
        window.start,
        64,
        false,
        &environment,
        &relocations,
    )
    .unwrap();
    assert_eq!(canonical.value, Formula::BitVec { value: 7, width: 64 });
    let baseline = std::env::var_os("TRUST_BR26_BASELINE_OBSERVE").is_some();
    for immediate in [1u32, 0x03ffffff] {
        let mut code = window.code.clone();
        let old = u32::from_le_bytes(code[..4].try_into().unwrap());
        let word = (old & 0xfc000000) | immediate;
        code[..4].copy_from_slice(&word.to_le_bytes());
        let result = symbolic_machine_outcome_env(
            &code,
            window.start,
            64,
            false,
            &environment,
            &relocations,
        );
        if baseline {
            assert_eq!(result.as_ref().unwrap().value, Formula::BitVec { value: 7, width: 64 });
        } else {
            let error = result
                .err()
                .expect("unsupported operand must not produce a legacy byte derivation");
            assert!(error.contains("BRANCH26") && error.contains("operand"), "{error}");
        }
    }
    if let Some(output) = std::env::var_os("TRUST_BR26_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join("legacy-vot");
        std::fs::create_dir_all(&output).unwrap();
        std::fs::write(output.join("subject.o"), &fixture.object).unwrap();
        std::fs::write(output.join("actual-callee-certificates.json"), report.to_json()).unwrap();
        std::fs::write(output.join("observation.json"),serde_json::to_vec_pretty(&serde_json::json!({"baseline_observation":baseline,"caller_start":window.start,"original_word":u32::from_le_bytes(window.code[..4].try_into().unwrap()),"mutations":[1u32,0x03ffffff],"callee_source_constant":7,"callee_kernel_checked":true})).unwrap()).unwrap();
    }
}

fn compiler_fixture() -> Fixture {
    let mut builder = ModBuilder::new("vot_branch26_operand");
    let signature = builder.sig(&[IrTy::U64], Some(IrTy::U64));
    let callee = builder.define("constant_leaf", signature, IrLinkage::External, |f| {
        let value = f.konst(IrTy::U64, 7);
        f.ret(value);
    });
    builder.define("constant_caller", signature, IrLinkage::External, |f| {
        let result = f.call(callee, &[f.p(0)]);
        f.ret(result);
    });
    let module = targeted(&builder.finish(), DARWIN);
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            parallel: false,
            emit_proofs: false,
            never_inline: ["constant_leaf".to_string()].into_iter().collect(),
            ..Default::default()
        },
        TargetSpec::parse(DARWIN).unwrap(),
    )
    .with_codegen_license(fixture_license())
    .compile(&module)
    .unwrap()
    .object_code;
    Fixture::with_object(module, object, DARWIN)
}

#[test]
fn paired_addend_cannot_be_overwritten_by_a_later_branch26_symbol() {
    let fixture = compiler_fixture();
    let mut bytes = fixture.object.clone();
    let rd = |data: &[u8], at: usize| u32::from_le_bytes(data[at..at + 4].try_into().unwrap());
    let mut command = 32usize;
    let mut text_header = None;
    for _ in 0..rd(&bytes, 16) {
        if rd(&bytes, command) == 0x19 {
            for index in 0..rd(&bytes, command + 64) as usize {
                let header = command + 72 + index * 80;
                if bytes[header..header + 16].split(|byte| *byte == 0).next()
                    == Some(b"__text".as_slice())
                {
                    text_header = Some(header);
                }
            }
        }
        command += rd(&bytes, command + 4) as usize;
    }
    let header = text_header.unwrap();
    let record = rd(&bytes, header + 56) as usize;
    assert_eq!(rd(&bytes, header + 60), 1);
    let address = rd(&bytes, record);
    let flags = rd(&bytes, record + 4);
    assert_eq!(flags >> 28, 2);
    let call = bytes[record..record + 8].to_vec();
    let offset = bytes.len() as u32;
    bytes.extend_from_slice(&address.to_le_bytes());
    bytes.extend_from_slice(&(4u32 | (2 << 25) | (10 << 28)).to_le_bytes());
    bytes.extend_from_slice(&call);
    bytes[header + 56..header + 60].copy_from_slice(&offset.to_le_bytes());
    bytes[header + 60..header + 64].copy_from_slice(&2u32.to_le_bytes());
    let targets = parse_text_branch26_relocs(&bytes).unwrap();
    assert!(matches!(targets.get(&(address as u64)), Some(BranchReloc::Unmodeled)));
    let parsed = crate::compiled_object::CompiledObject::parse(&bytes).unwrap();
    let expected = crate::compiled_object::ObjectExpectations::from_module(
        &fixture.m_cg,
        parsed.format,
        fixture.model,
    )
    .unwrap();
    let layout = crate::compiled_object::ObjectLayout::bind(parsed, &expected).unwrap();
    let window = &layout.windows["constant_caller"];
    assert!(window.unknown.iter().any(|reason| reason.contains("non-zero addend")));
    let environment = CalleeEnv::empty();
    let normalized = HashMap::from([(0, BranchReloc::Unmodeled)]);
    let result = symbolic_machine_outcome_env(
        &window.code,
        window.start,
        64,
        false,
        &environment,
        &normalized,
    );
    let error = result.err().unwrap();
    assert!(error.contains("relocation") && error.contains("does not model"), "{error}");
    if let Some(output) = std::env::var_os("TRUST_BR26_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join("legacy-vot-addend4");
        std::fs::create_dir_all(&output).unwrap();
        std::fs::write(output.join("subject.o"), bytes).unwrap();
        std::fs::write(output.join("refusal.txt"), error).unwrap();
    }
}
