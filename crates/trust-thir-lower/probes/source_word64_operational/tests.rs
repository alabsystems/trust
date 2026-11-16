use clean_kernel::env::{EnvError, TrustedEnvExt};
use clean_kernel::{Declaration, Environment, Expr, KernelTypeError, Level, Name, ReferenceKernel, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{load_module_with_deps, parse_module, reference_base_closed, DefinitionSafety};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::io::Read as _;
use std::path::PathBuf;

const MAX_PACKET_BYTES: usize = 256 * 1024 * 1024;

const THEOREMS: &[&str] = &[
    "original_decodes", "start_exact", "addition_step", "return_step", "run_exact", "original_returns", "no_body_violation",
    "SourceWord64RecordOriginal.original_decodes",
    "SourceWord64RecordOriginal.trailing_refused",
    "SourceWord64RecordOriginal.missing_generic_refused",
    "SourceWord64Evaluation.ordinary_call_unresolved",
    "SourceWord64Evaluation.retained_evaluates",
    "SourceWord64Evaluation.retained_agrees",
    "SourceWord64Call.caller_decodes",
    "SourceWord64Call.wrong_owner_refused",
    "SourceWord64Call.caller_evaluates",
    "SourceWord64Call.call_claim_agrees_with_callee",
    "PairCallerOperational.original_decodes",
    "PairCallerOperational.caller_unchanged",
    "PairCallerOperational.callee_blocks_unchanged",
    "PairCallerOperational.linked_returns",
    "PairCallerOperational.zero_depth_refused",
    "PairCallerOperational.missing_body_refused",
    "PairCallerOperational.call_claim_matches_linked",
    "SourceWord64MiniRust.reference_add",
    "SourceWord64MiniRust.linked_reference_agreement",
];

#[derive(Serialize, Deserialize)]
struct Proof {
    theorem: String,
    closure: [u8; 32],
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Packet {
    schema: u32,
    module_bytes: Vec<u8>,
    source_bytes: Vec<u8>,
    caller_source_bytes: Vec<u8>,
    caller_module_bytes: Vec<u8>,
    // Lossless, bounded CLENEDG2 data only. Decoding does not construct the
    // independent ReferenceKernel below or restore any authority from a stamp.
    proof_environment: Vec<u8>,
    proofs: Vec<Proof>,
}

fn directory() -> PathBuf {
    std::env::var_os("TRUST_WORD64_OPERATIONAL_DIR").expect("owned compiled artifact directory").into()
}

fn name(short: &str) -> Name {
    if short.contains('.') { Name::from_string(short) }
    else { Name::from_string(&format!("SemRWord64Pair.{short}")) }
}

fn original() -> Vec<u8> {
    let capture = PathBuf::from(std::env::var_os("TRUST_SOURCE_PAIR_CAPTURES").unwrap());
    let bytes = std::fs::read(capture.join("core-callee.module")).unwrap();
    assert_eq!(bytes, include_bytes!("core-callee.module"));
    let module = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), bytes);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    assert_eq!(module.functions.len(), 1);
    assert!(!module.functions[0].is_declaration());
    bytes
}

fn checked() -> ReferenceKernel {
    let directory = directory();
    let mut parsed_modules = Vec::new();
    for module in ["SemRWord64Pair", "SourceWord64Record", "SourceWord64RecordOriginal", "SourceWord64Evaluation", "SourceWord64Call", "PairCallerOperational", "SourceWord64MiniRust"] {
        let bytes = std::fs::read(directory.join(format!("{module}.olean"))).unwrap();
        for part in ["olean.private", "olean.server"] {
            assert!(!directory.join(format!("{module}.{part}")).exists());
        }
        let parsed = parse_module(&bytes).unwrap();
        let listed: BTreeSet<_> = parsed.const_names.iter().map(String::as_str).collect();
        assert_eq!(listed, parsed.constants.iter().map(|c| c.name.as_str()).collect());
        assert!(!listed.is_empty());
        parsed_modules.push(parsed);
    }
    let targets: BTreeSet<_> = THEOREMS.iter().copied().chain([
        "WrongDecode", "WrongResult", "WrongFuel", "MissingInputValidity",
    ]).map(name).collect();
    let mut imported = Environment::for_lean_replay();
    load_module_with_deps(&mut imported, "SourceWord64MiniRust", &[
        directory, clean_olean::require_pinned_lean_lib_path().unwrap(),
    ]).unwrap();
    let closure: BTreeSet<_> = targets.iter().flat_map(|target|
        imported.dependency_closure(target).unwrap()).collect();
    for parsed in &parsed_modules {
        for declaration in &parsed.constants {
            if closure.contains(&Name::from_string(&declaration.name)) {
                assert!(!matches!(declaration.definition_safety,
                    Some(DefinitionSafety::Unsafe | DefinitionSafety::Partial)),
                    "non-kernel proof dependency: {}", declaration.name);
            }
        }
    }
    // Import is untrusted. Every dependency of every new kernel declaration is
    // admitted from EMPTY through the fixed Lean-reference entry, not a normal
    // Clean checker with native reducers or a structural environment stamp.
    let checked = reference_base_closed(&imported, &targets, &ClosedRecheckOptions::default()).unwrap();
    eprintln!("{}", checked.report.verdict_sentence());
    assert!(checked.report.passed(), "{:#?}", checked.report.refusals);
    assert!(checked.entry_refusals.is_empty(), "{:#?}", checked.entry_refusals);
    assert!(targets.iter().all(|target| checked.admitted.contains(target)));
    assert!(checked.report.axioms_admitted.iter().all(|n|
        ["propext", "Classical.choice", "Quot.sound"].contains(&n.as_str())));
    checked.into_kernel().unwrap()
}

fn bind_original_bytes(kernel: &mut ReferenceKernel, bytes: &[u8], subject: &str, theorem: &str) {
    let nat = Expr::const_str("Nat");
    let list_nat = Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), nat.clone());
    let literal = bytes.iter().rev().fold(
        Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), nat.clone()),
        |tail, byte| Expr::apps(Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [nat.clone(), Expr::nat_lit(u64::from(*byte)), tail]),
    );
    let source = Expr::const_(name(subject), vec![]);
    kernel.add_checked(Declaration::Theorem {
        name: name(theorem), level_params: vec![],
        type_: Expr::apps(Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [list_nat.clone(), source.clone(), literal]),
        value: Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [list_nat, source]),
    }).unwrap();
}

// The carrier contains only original declaration DATA, not the checked context.
// Structural insertion never checks or claims the statements. Only replay in
// the independently reconstructed ReferenceKernel below can accept a proof.
fn proof_data(environment: &Environment, names: &[Name]) -> Vec<u8> {
    let mut data = Environment::default();
    let refused = data.extend_constants_structural(names.iter().map(|name|
        environment.get_const(name).unwrap().clone()));
    assert!(refused.is_empty(), "{refused:?}");
    assert!(data.get_const(&Name::from_string("Nat")).is_none());
    data.to_dag_bincode().unwrap()
}

fn replay(kernel: &mut ReferenceKernel, packet: &Packet) {
    assert_eq!(packet.schema, 3);
    assert_eq!(packet.module_bytes, original());
    let data = Environment::from_dag_bincode(&packet.proof_environment).unwrap();
    assert_eq!(packet.proofs.len(), THEOREMS.len());
    assert_eq!(packet.source_bytes, include_bytes!("core-callee.source"));
    bind_original_bytes(kernel, &packet.module_bytes, "originalBytes", "ExactRetainedBytes");
    bind_original_bytes(kernel, &packet.source_bytes,
        "SourceWord64RecordOriginal.originalBytes", "ExactRetainedSourceBytes");
    assert_eq!(packet.caller_source_bytes, include_bytes!("pair-caller.source"));
    assert_eq!(packet.caller_module_bytes, include_bytes!("pair-caller.module"));
    bind_original_bytes(kernel, &packet.caller_source_bytes,
        "SourceWord64Call.callerBytes", "ExactRetainedCallerSourceBytes");
    bind_original_bytes(kernel, &packet.caller_module_bytes,
        "PairCallerOperational.originalBytes", "ExactRetainedCallerModuleBytes");
    for (proof, expected) in packet.proofs.iter().zip(THEOREMS) {
        assert_eq!(&proof.theorem, expected);
        let actual = kernel.environment().get_const(&name(expected)).unwrap();
        let retained = data.get_const(&name(expected)).unwrap();
        assert_eq!(retained.type_, actual.type_);
        assert_eq!(retained.value, actual.value);
        assert_eq!(proof.closure, kernel.environment().closure_digest(&name(expected)).unwrap());
        kernel.add_checked(Declaration::Theorem {
            name: name(&format!("Replay_{expected}")), level_params: vec![],
            type_: retained.type_.clone(), value: retained.value.clone().unwrap(),
        }).unwrap();
    }
    for (negative, positive) in [
        ("WrongDecode", "original_decodes"),
        ("WrongResult", "original_returns"),
        ("WrongFuel", "original_returns"),
        ("MissingInputValidity", "original_returns"),
    ] {
        let retained = data.get_const(&name(positive)).unwrap();
        let result = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("Refuse_{negative}")), level_params: vec![],
            type_: Expr::const_(name(negative), vec![]), value: retained.value.clone().unwrap(),
        });
        assert!(matches!(result, Err(ReferenceRefusal::Kernel(EnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. }, ..
        }))), "{negative}: {result:?}");
    }
    for positive in &THEOREMS[7..] {
        let retained = data.get_const(&name(positive)).unwrap();
        let result = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("RefuseFalse_{positive}")), level_params: vec![],
            type_: Expr::const_str("False"), value: retained.value.clone().unwrap(),
        });
        assert!(matches!(result, Err(ReferenceRefusal::Kernel(EnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. }, ..
        }))), "{positive}: {result:?}");
    }
}

#[test]
fn deep_proof_transport_roundtrips_without_recursive_json() {
    let mut environment = Environment::default();
    environment.init_nat().unwrap();
    let mut type_ = Expr::const_str("Nat");
    let mut value = Expr::nat_lit(0);
    for _ in 0..512 {
        type_ = Expr::arrow(Expr::const_str("Nat"), type_);
        value = Expr::lam(clean_kernel::BinderInfo::Default, Expr::const_str("Nat"), value);
    }
    let declaration = Name::from_string("deepTransportFixture");
    environment.add_decl(Declaration::Definition {
        name: declaration.clone(), level_params: vec![], type_: type_.clone(),
        value: value.clone(), is_reducible: true,
    }).unwrap();
    let packet = Packet { schema: 3, module_bytes: vec![], source_bytes: vec![],
        caller_source_bytes: vec![], caller_module_bytes: vec![], proofs: vec![],
        proof_environment: proof_data(&environment, &[declaration.clone()]) };
    let bytes = serde_json::to_vec(&packet).unwrap();
    assert!(bytes.len() <= MAX_PACKET_BYTES);
    let decoded: Packet = serde_json::from_slice(&bytes).unwrap();
    let data = Environment::from_dag_bincode(&decoded.proof_environment).unwrap();
    let retained = data.get_const(&declaration).unwrap();
    assert_eq!(retained.type_, type_);
    assert_eq!(retained.value.as_ref(), Some(&value));
    assert!(Environment::from_dag_bincode(
        &decoded.proof_environment[..decoded.proof_environment.len() - 1]
    ).is_err());
}

#[test]
fn operational_reference_kernel_produces_packet() {
    assert!(std::env::var_os("TRUST_WORD64_OPERATIONAL_FORBID_PRODUCER").is_none());
    let mut kernel = checked();
    let proofs = THEOREMS.iter().map(|short| {
        Proof { theorem: (*short).into(),
            closure: kernel.environment().closure_digest(&name(short)).unwrap() }
    }).collect();
    let packet = Packet { schema: 3, module_bytes: original(),
        source_bytes: include_bytes!("core-callee.source").to_vec(),
        caller_source_bytes: include_bytes!("pair-caller.source").to_vec(),
        caller_module_bytes: include_bytes!("pair-caller.module").to_vec(),
        proof_environment: proof_data(kernel.environment(), &THEOREMS.iter().map(|s| name(s)).collect::<Vec<_>>()), proofs };
    replay(&mut kernel, &packet);
    let bytes = serde_json::to_vec(&packet).unwrap();
    assert!(bytes.len() <= MAX_PACKET_BYTES);
    std::fs::write(directory().join("packet.json"), bytes).unwrap();
}

#[test]
fn operational_fresh_process_replays_unchanged_proofs() {
    assert_eq!(std::env::var("TRUST_WORD64_OPERATIONAL_FORBID_PRODUCER").unwrap(), "1");
    let mut bytes = Vec::new();
    std::fs::File::open(directory().join("packet.json")).unwrap()
        .take(MAX_PACKET_BYTES as u64 + 1).read_to_end(&mut bytes).unwrap();
    assert!(bytes.len() <= MAX_PACKET_BYTES);
    let packet = serde_json::from_slice(&bytes).unwrap();
    replay(&mut checked(), &packet);
    assert_eq!(std::fs::read(directory().join("packet.json")).unwrap(), bytes);
    std::fs::write(directory().join("fresh-replay.json"),
        b"{\"producer_forbidden\":true,\"unchanged_proofs\":true,\"false_subjects_refused\":23,\"compiler_admission\":false}\n").unwrap();
}
