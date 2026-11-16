// End-to-end contract for the first assembled Trust-IR global emission rung.
//
// The admitted shape is intentionally narrow: immutable initialized local u64
// storage, addressed by GlobalAddr and read directly. These tests pin both sides
// of the seam — Module -> LIR provenance and canonical ObjectGlobal -> Mach-O —
// plus every close fail-closed boundary claimed by this increment.

use std::fs;
use std::process::Command;

use tempfile::TempDir;
use trust_cg_bridge::codegen_backend::{
    TrustCgCodegenBackend, TrustCgTargetArch, assembled_internal_object_globals,
};
use trust_cg_bridge::{ModuleLirError, lower_module_to_lir};
use trust_cg_codegen::macho::linker::{MachOParser, ParsedObject, ParsedSymbol};
use trust_cg_codegen::macho::reloc::AArch64RelocKind;
use trust_cg_lower::instructions::Opcode;
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage,
    Module, TlsModel, Ty, ValueId,
};

const ANSWER: u64 = 0x1122_3344_5566_7788;
const OTHER: u64 = 0x8877_6655_4433_2211;
const GLOBAL: &str = "assembled_promoted_u64";

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
}

fn local_u64(name: &str, value: u64) -> Global {
    Global {
        name: name.to_string(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(value as i128)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        // v41: a fixture that states no section, visibility or retention.
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}

fn add_reader(module: &mut Module, id: u32, name: &str, global: GlobalId, reads: usize) {
    assert!(reads == 1 || reads == 2);
    let ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut body = vec![
        InstrNode::new(Inst::GlobalAddr { global }).with_result(ValueId::new(0)),
        InstrNode::new(Inst::Load {
            ty: Ty::U64,
            ptr: ValueId::new(0),
            volatile: false,
            align: Some(8),
        })
        .with_result(ValueId::new(1)),
    ];
    let returned = if reads == 1 {
        ValueId::new(1)
    } else {
        body.extend([
            InstrNode::new(Inst::GlobalAddr { global }).with_result(ValueId::new(2)),
            InstrNode::new(Inst::Load {
                ty: Ty::U64,
                ptr: ValueId::new(2),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: ValueId::new(1),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
        ]);
        ValueId::new(4)
    };
    body.push(InstrNode::new(Inst::Return { values: vec![returned] }));

    let mut function = Function::new(FuncId::new(id), name, ty, BlockId::new(0));
    function.blocks.push(Block { id: BlockId::new(0), params: vec![], body });
    module.try_add_function(function).expect("Module::try_add_function: test fixture");
}

fn single_reader(value: u64, reads: usize) -> Module {
    let mut module = Module::new("assembled_global_fixture");
    module.globals.push(local_u64(GLOBAL, value));
    add_reader(&mut module, 0, "read_assembled_global", GlobalId::new(0), reads);
    module
}

fn emitted(module: &Module, func_id: FuncId) -> Vec<u8> {
    let lir = lower_module_to_lir(module, func_id).expect("global reader must lower");
    backend()
        .emit_object_with_trust_ir_globals(&[lir], module)
        .expect("globals-aware object emission must succeed")
}

fn macho_symbol<'a>(object: &'a ParsedObject, logical_name: &str) -> (usize, &'a ParsedSymbol) {
    let macho_name = format!("_{logical_name}");
    let matches = object
        .symbols
        .iter()
        .enumerate()
        .filter(|(_, symbol)| symbol.name == logical_name || symbol.name == macho_name)
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected exactly one symbol for {logical_name}");
    (matches[0].0, matches[0].1)
}

fn global_bytes_and_relocations(
    object_bytes: &[u8],
    logical_name: &str,
) -> (Vec<u8>, Vec<AArch64RelocKind>) {
    let object =
        MachOParser::parse(object_bytes).expect("bridge must emit parseable AArch64 Mach-O");
    let (symbol_index, symbol) = macho_symbol(&object, logical_name);
    assert!(symbol.is_defined(), "global must be defined, not left undefined");
    assert!(!symbol.is_external(), "Internal/Private global must remain local");
    assert!(
        !object
            .symbols
            .iter()
            .any(|candidate| { candidate.name == symbol.name && candidate.is_undefined() }),
        "the local definition must not have an undefined twin"
    );

    let section = &object.sections[usize::from(symbol.section) - 1];
    assert_eq!(section.name, "__const");
    assert_eq!(section.segment, "__TEXT");
    assert!(section.align >= 3, "u64 storage must be at least 8-byte aligned");
    let offset = usize::try_from(symbol.value - section.addr).expect("global offset");
    let data = section.data[offset..offset + 8].to_vec();

    let text =
        object.sections.iter().find(|section| section.name == "__text").expect("text section");
    let kinds = text
        .relocations
        .iter()
        .filter(|relocation| {
            relocation.is_extern && relocation.symbol_index as usize == symbol_index
        })
        .map(|relocation| relocation.kind)
        .collect();
    (data, kinds)
}

fn link_and_run(object: &[u8], expected: u64) {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!("SKIP native execution: requires an aarch64-apple-darwin host");
        return;
    }
    let directory = TempDir::new().expect("temporary link directory");
    let object_path = directory.path().join("assembled.o");
    let driver_path = directory.path().join("driver.c");
    let executable_path = directory.path().join("assembled");
    fs::write(&object_path, object).expect("write object");
    fs::write(
        &driver_path,
        format!(
            "#include <stdint.h>\n\
             extern uint64_t read_assembled_global(void);\n\
             int main(void) {{ return read_assembled_global() == UINT64_C({expected}) ? 0 : 1; }}\n"
        ),
    )
    .expect("write C driver");
    let linked = Command::new("cc")
        .arg(&driver_path)
        .arg(&object_path)
        .arg("-o")
        .arg(&executable_path)
        .output()
        .expect("invoke cc");
    assert!(
        linked.status.success(),
        "native link failed: {}",
        String::from_utf8_lossy(&linked.stderr)
    );
    let ran = Command::new(&executable_path).output().expect("run linked fixture");
    assert!(ran.status.success(), "linked fixture returned the wrong global value");
}

#[test]
fn globaladdr_load_has_one_exact_local_definition_and_relocation_pair() {
    let module = single_reader(ANSWER, 1);
    let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("lower");
    let instructions = &lir.blocks[&lir.entry_block].instructions;
    assert!(matches!(
        &instructions[0].opcode,
        Opcode::GlobalRef { name } if name == GLOBAL
    ));
    assert!(matches!(&instructions[1].opcode, Opcode::Load { .. }));

    let globals = assembled_internal_object_globals(&module).expect("canonical globals");
    assert_eq!(globals.len(), 1);
    assert_eq!(globals[0].name, GLOBAL);
    assert_eq!(globals[0].data, ANSWER.to_le_bytes());
    assert!(!globals[0].is_external);
    assert!(globals[0].symbol_refs.is_empty());

    let object = backend().emit_object_with_trust_ir_globals(&[lir], &module).expect("emit");
    let (data, kinds) = global_bytes_and_relocations(&object, GLOBAL);
    assert_eq!(data, ANSWER.to_le_bytes());
    assert_eq!(kinds.iter().filter(|kind| **kind == AArch64RelocKind::Page21).count(), 1);
    assert_eq!(kinds.iter().filter(|kind| **kind == AArch64RelocKind::Pageoff12).count(), 1);
    assert_eq!(kinds.len(), 2, "only the exact address-materialization pair targets data");
    link_and_run(&object, ANSWER);
}

#[test]
fn two_reads_share_one_definition_and_initializer_or_target_mutation_changes_execution() {
    let twice = single_reader(ANSWER, 2);
    let twice_object = emitted(&twice, FuncId::new(0));
    let (data, kinds) = global_bytes_and_relocations(&twice_object, GLOBAL);
    assert_eq!(data, ANSWER.to_le_bytes());
    assert_eq!(kinds.iter().filter(|kind| **kind == AArch64RelocKind::Page21).count(), 2);
    assert_eq!(kinds.iter().filter(|kind| **kind == AArch64RelocKind::Pageoff12).count(), 2);
    link_and_run(&twice_object, ANSWER.wrapping_add(ANSWER));

    let changed_initializer = single_reader(OTHER, 1);
    let changed_object = emitted(&changed_initializer, FuncId::new(0));
    assert_eq!(global_bytes_and_relocations(&changed_object, GLOBAL).0, OTHER.to_le_bytes());
    assert_ne!(twice_object, changed_object);
    link_and_run(&changed_object, OTHER);

    let mut retargeted = Module::new("retargeted_global_fixture");
    retargeted.globals.push(local_u64(GLOBAL, ANSWER));
    retargeted.globals.push(local_u64("other_promoted_u64", OTHER));
    add_reader(&mut retargeted, 0, "read_assembled_global", GlobalId::new(1), 1);
    let retargeted_object = emitted(&retargeted, FuncId::new(0));
    let (_, retarget_kinds) =
        global_bytes_and_relocations(&retargeted_object, "other_promoted_u64");
    assert_eq!(retarget_kinds.len(), 2, "relocation must follow the changed GlobalId");
    link_and_run(&retargeted_object, OTHER);
}

#[test]
fn missing_id_and_wrong_width_load_fail_before_object_emission() {
    let mut missing = single_reader(ANSWER, 1);
    missing.functions[0].blocks[0].body[0].inst = Inst::GlobalAddr { global: GlobalId::new(9) };
    assert!(matches!(
        lower_module_to_lir(&missing, FuncId::new(0)),
        Err(ModuleLirError::MissingGlobal { global: 9, .. })
    ));

    let mut width = single_reader(ANSWER, 1);
    width.functions[0].blocks[0].body[1].inst =
        Inst::Load { ty: Ty::U32, ptr: ValueId::new(0), volatile: false, align: Some(4) };
    assert!(matches!(
        lower_module_to_lir(&width, FuncId::new(0)),
        Err(ModuleLirError::UnsupportedMemory { .. })
    ));
}

#[test]
fn unsupported_global_shapes_and_symbol_collisions_fail_closed() {
    let base = single_reader(ANSWER, 1);
    let mut cases = Vec::new();

    let mut external = base.clone();
    external.globals[0].linkage = Linkage::External;
    cases.push(("external", external));
    let mut weak = base.clone();
    weak.globals[0].linkage = Linkage::Weak;
    cases.push(("weak", weak));
    let mut bss = base.clone();
    bss.globals[0].initializer = None;
    cases.push(("initializer", bss));
    let mut tls = base.clone();
    tls.globals[0].tls = Some(TlsModel::LocalExec);
    cases.push(("thread-local", tls));
    let mut mutable = base.clone();
    mutable.globals[0].mutable = true;
    cases.push(("mutable", mutable));
    let mut wrong_type = base.clone();
    wrong_type.globals[0].ty = Ty::I64;
    cases.push(("only u64", wrong_type));
    let mut invalid_align = base.clone();
    invalid_align.globals[0].align = Some(4);
    cases.push(("alignment", invalid_align));
    let mut embedded_relocation = base.clone();
    embedded_relocation.globals[0].initializer =
        Some(Constant::SymbolAddr { symbol: "read_assembled_global".to_string(), addend: 0 });
    cases.push(("SymbolAddr", embedded_relocation));

    for (expected, module) in cases {
        let error = assembled_internal_object_globals(&module)
            .expect_err("unsupported global form must not be dropped or emitted");
        assert!(error.to_string().contains(expected), "expected {expected:?} in {error}");
    }

    let mut duplicate = base.clone();
    duplicate.globals.push(local_u64(GLOBAL, OTHER));
    assert!(
        assembled_internal_object_globals(&duplicate)
            .expect_err("duplicate data symbol")
            .to_string()
            .contains("duplicate global symbol")
    );

    let mut collision = base.clone();
    collision.globals[0].name = "read_assembled_global".to_string();
    let lir = lower_module_to_lir(&collision, FuncId::new(0)).expect("shape still lowers");
    assert!(
        backend()
            .emit_object_with_trust_ir_globals(&[lir], &collision)
            .expect_err("function/data collision")
            .to_string()
            .contains("collides with a function")
    );
}

#[test]
fn function_symbol_proxy_remains_separate_from_object_data() {
    let mut module = single_reader(ANSWER, 1);
    module.globals.push(Global {
        name: "read_assembled_global".to_string(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
        // v41: a fixture that states no section, visibility or retention.
        section: None,
        visibility: Default::default(),
        retained: false,
    });

    let globals = assembled_internal_object_globals(&module)
        .expect("a matching function-address proxy is not BSS or imported data");
    assert_eq!(globals.len(), 1);
    assert_eq!(globals[0].name, GLOBAL);

    let object = emitted(&module, FuncId::new(0));
    let parsed = MachOParser::parse(&object).expect("parse emitted object");
    let proxy_symbols = parsed
        .symbols
        .iter()
        .filter(|symbol| {
            symbol.name == "read_assembled_global" || symbol.name == "_read_assembled_global"
        })
        .collect::<Vec<_>>();
    assert_eq!(proxy_symbols.len(), 1, "the function proxy must not create a data-symbol twin");
    assert!(proxy_symbols[0].is_defined());
}

#[cfg(feature = "ay-proofs")]
#[test]
fn clone_disagreement_is_refused_and_allow_unknown_keeps_the_same_global() {
    use trust_cg_bridge::codegen_backend::{CompiledModule, FunctionLinkage};
    use trust_cg_bridge::verify_output::{EmitPolicy, VerifyError};
    use trust_cg_bridge::verify_output_trust_ir::{
        TrustIrGateSource, emit_trust_ir_module_object_unverified,
        emit_trust_ir_module_object_verified,
    };

    let module = single_reader(ANSWER, 1);
    let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("lower");
    let source = TrustIrGateSource {
        abi_cross_check: None,
        symbol: "read_assembled_global".to_string(),
        module: std::sync::Arc::new(module.clone()),
        func_id: FuncId::new(0),
    };
    let compiled = CompiledModule {
        name: "assembled.codegen-unit".to_string(),
        lir_functions: vec![lir],
        object_path: None,
        function_count: 1,
        source_functions: None,
        linkage: vec![FunctionLinkage::External],
        statics: Vec::new(),
    };

    let ungated = emit_trust_ir_module_object_unverified(
        std::slice::from_ref(&source),
        &compiled,
        &backend(),
    )
    .expect("explicit gate-off path must retain globals");
    let strict = emit_trust_ir_module_object_verified(
        std::slice::from_ref(&source),
        &compiled.linkage,
        &[],
        EmitPolicy::StrictProvenOnly,
        &backend(),
    );
    assert!(matches!(strict, Err(VerifyError::Unknown { .. })));
    let (allowed, report) = emit_trust_ir_module_object_verified(
        std::slice::from_ref(&source),
        &compiled.linkage,
        &[],
        EmitPolicy::AllowUnknown,
        &backend(),
    )
    .expect("AllowUnknown may ship the explicitly uncertified global-load slice");
    assert_eq!(report.unknown, 1);
    assert_eq!(report.proved, 0);
    assert_eq!(report.validated, 0);
    assert_eq!(
        global_bytes_and_relocations(&ungated.bytes, GLOBAL).0,
        global_bytes_and_relocations(&allowed.bytes, GLOBAL).0
    );

    let mut two_function_module = Module::new("clone_disagreement");
    two_function_module.globals.push(local_u64(GLOBAL, ANSWER));
    add_reader(&mut two_function_module, 0, "read_assembled_global", GlobalId::new(0), 1);
    add_reader(&mut two_function_module, 1, "read_assembled_global_again", GlobalId::new(0), 1);
    let lir0 = lower_module_to_lir(&two_function_module, FuncId::new(0)).expect("lower 0");
    let lir1 = lower_module_to_lir(&two_function_module, FuncId::new(1)).expect("lower 1");
    let source0 = TrustIrGateSource {
        abi_cross_check: None,
        symbol: lir0.name.clone(),
        module: std::sync::Arc::new(two_function_module.clone()),
        func_id: FuncId::new(0),
    };
    let mut divergent = two_function_module.clone();
    divergent.globals[0].initializer = Some(Constant::Int(OTHER as i128));
    let source1 = TrustIrGateSource {
        abi_cross_check: None,
        symbol: lir1.name.clone(),
        module: std::sync::Arc::new(divergent),
        func_id: FuncId::new(1),
    };
    let compiled = CompiledModule {
        name: "clone-disagreement.codegen-unit".to_string(),
        lir_functions: vec![lir0, lir1],
        object_path: None,
        function_count: 2,
        source_functions: None,
        linkage: vec![FunctionLinkage::External, FunctionLinkage::External],
        statics: Vec::new(),
    };
    let error = emit_trust_ir_module_object_unverified(&[source0, source1], &compiled, &backend())
        .expect_err("different global tables must not be merged");
    assert!(error.to_string().contains("different global table"));
}
