use clean_kernel::env::{EnvError, TrustedEnvExt};
use clean_kernel::{Declaration, Environment, Expr, KernelTypeError, Name, ReferenceKernel, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{load_module_with_deps, parse_module, reference_base_closed, DefinitionSafety};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::io::Read as _;
use std::path::PathBuf;

const MAX_PACKET_BYTES: usize = 256 * 1024 * 1024;

const THEOREMS: &[&str] = &[
    "construct_trait_pointer", "undef_data_refused", "undef_metadata_refused",
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
    // Lossless, bounded CLENEDG2 data only. Decoding does not construct the
    // independent ReferenceKernel below or restore any authority from a stamp.
    proof_environment: Vec<u8>,
    proofs: Vec<Proof>,
}

fn directory() -> PathBuf {
    std::env::var_os("TRUST_POINTER_OPERATIONAL_DIR").expect("owned compiled artifact directory").into()
}

fn name(short: &str) -> Name {
    Name::from_string(&format!("PointerPartsOperational.{short}"))
}

fn original() -> Vec<u8> {
    std::fs::read(directory().join("PointerPartsOperational.olean")).unwrap()
}

fn checked() -> ReferenceKernel {
    let directory = directory();
    let bytes = std::fs::read(directory.join("PointerPartsOperational.olean")).unwrap();
    for part in ["olean.private", "olean.server"] {
        assert!(!directory.join(format!("PointerPartsOperational.{part}")).exists());
    }
    let parsed = parse_module(&bytes).unwrap();
    let listed: BTreeSet<_> = parsed.const_names.iter().map(String::as_str).collect();
    assert_eq!(listed, parsed.constants.iter().map(|c| c.name.as_str()).collect());
    assert!(!listed.is_empty());
    let targets: BTreeSet<_> = THEOREMS.iter().map(|short| name(short)).collect();
    assert!(targets.iter().all(|target| listed.contains(target.to_string().as_str())));
    let mut imported = Environment::for_lean_replay();
    load_module_with_deps(&mut imported, "PointerPartsOperational", &[
        directory,
        PathBuf::from(std::env::var_os("TRUST_POINTER_SEMANTICS_DIR").unwrap()),
        clean_olean::installed_lean_lib_path("leanprover/lean4:v4.8.0").expect("exact canonical semantics toolchain"),
    ]).unwrap();
    // Lean 4.8 also stores generated unsafe executable helpers in an olean.
    // They are not theorem targets. Check safety over the full dependency
    // closures of every advertised proof, rather than granting those helpers
    // authority or requesting a proof of executable compiler output.
    let closure: BTreeSet<_> = targets.iter().flat_map(|target|
        imported.dependency_closure(target).unwrap()).collect();
    for declaration in &parsed.constants {
        if closure.contains(&Name::from_string(&declaration.name)) {
            assert!(!matches!(declaration.definition_safety,
                Some(DefinitionSafety::Unsafe | DefinitionSafety::Partial)),
                "non-kernel proof dependency: {} {:?}", declaration.name,
                declaration.definition_safety);
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
    assert_eq!(packet.schema, 1);
    assert_eq!(packet.module_bytes, original());
    let data = Environment::from_dag_bincode(&packet.proof_environment).unwrap();
    assert_eq!(packet.proofs.len(), THEOREMS.len());
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
    for positive in THEOREMS {
        let retained = data.get_const(&name(positive)).unwrap();
        let result = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("Refuse_false_{positive}")), level_params: vec![],
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
    let packet = Packet { schema: 1, module_bytes: vec![], proofs: vec![],
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
    assert!(std::env::var_os("TRUST_POINTER_OPERATIONAL_FORBID_PRODUCER").is_none());
    let mut kernel = checked();
    let proofs = THEOREMS.iter().map(|short| {
        Proof { theorem: (*short).into(),
            closure: kernel.environment().closure_digest(&name(short)).unwrap() }
    }).collect();
    let packet = Packet { schema: 1, module_bytes: original(),
        proof_environment: proof_data(kernel.environment(), &THEOREMS.iter().map(|s| name(s)).collect::<Vec<_>>()), proofs };
    replay(&mut kernel, &packet);
    let bytes = serde_json::to_vec(&packet).unwrap();
    assert!(bytes.len() <= MAX_PACKET_BYTES);
    std::fs::write(directory().join("packet.json"), bytes).unwrap();
}

#[test]
fn operational_fresh_process_replays_unchanged_proofs() {
    assert_eq!(std::env::var("TRUST_POINTER_OPERATIONAL_FORBID_PRODUCER").unwrap(), "1");
    let mut bytes = Vec::new();
    std::fs::File::open(directory().join("packet.json")).unwrap()
        .take(MAX_PACKET_BYTES as u64 + 1).read_to_end(&mut bytes).unwrap();
    assert!(bytes.len() <= MAX_PACKET_BYTES);
    let packet = serde_json::from_slice(&bytes).unwrap();
    replay(&mut checked(), &packet);
    assert_eq!(std::fs::read(directory().join("packet.json")).unwrap(), bytes);
    std::fs::write(directory().join("fresh-replay.json"),
        b"{\"producer_forbidden\":true,\"unchanged_proofs\":true,\"false_subjects_refused\":3,\"compiler_admission\":false}\n").unwrap();
}
