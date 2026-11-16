// Trust: 2026-10-08 — a Rust reference carries no permission instruction.
//
// trust-ir docs/SPEC_RATIFICATIONS.md, "A Rust reference carries no permission
// instruction": a Rust producer spells every reference it creates as the place's
// address value, that value itself or a `Copy` of it at its own type, and never
// emits `Borrow`, `BorrowMut` or `EndBorrow`. Those drive trust-ir's
// allocation-keyed permission machine, which is not Rust's reference semantics:
// this bridge has no source for `EndBorrow` (its input carries no NLL loans), so
// every borrow it used to emit stayed live and made each later free of its
// allocation undefined behaviour, and Lean faulted on the ordinary shapes outright.
//
// THE CENSUS. Every committed `VerifiableFunction` fixture of this crate
// (`tests/data/*.json` and `fixtures/*.json`, real MIR captures and synthetic
// bodies alike) is lowered through the production entry point. On every fixture
// that lowers, no node of the module is a permission instruction, and every node
// carrying a reference claim (`SharedBorrow` / `UniqueBorrow`) is a `Copy` at a
// pointer type. The per-fixture NUMBER of references is not pinned: a reference
// the lowering folds away leaves no node, so the census pins the spelling of the
// references that reach the module, not the lowering's coverage. It REPORTS how
// many fixtures lower and how many `Rvalue::Ref` statements their inputs hold
// (measured 2026-10-08: 142 in 90 of the 175 fixtures, 71 of them `&mut`), and it
// refuses to pass vacuously.
//
// A local `matches!` stands in for trust-ir's proved `InstShape::uses_borrow_permissions`
// until Trust's trust-ir gitlink holds that predicate. Mutation: restore the thin
// `Inst::Borrow` / `Inst::BorrowMut` arm in `lower_rvalue` and this test fails on
// the first fixture with a thin reference.
//
// This is the bridge's guard for the rule (no runtime exit check is added to the
// MIR lane: ruling R-2 / AI-1). trust-ir's validator keys the rule on the
// `Producer::TRust` stamp and its bundle check on a `RustMir` input; MIR-bridge
// output outside a bundle (the codegen instance route, the differential's oracle,
// crate dumps) is guarded here only, by this sample.
use std::path::Path;

use trust_ir::inst::Inst;
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty as IrTy;
use trust_types::{Rvalue, Statement, VerifiableFunction};

fn fixtures() -> Vec<(String, VerifiableFunction)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut paths = Vec::new();
    for dir in ["tests/data", "fixtures"] {
        for entry in std::fs::read_dir(root.join(dir)).unwrap_or_else(|e| panic!("{dir}: {e}")) {
            let path = entry.expect("a directory entry").path();
            if path.extension().is_some_and(|ext| ext == "json") {
                paths.push(path);
            }
        }
    }
    paths.sort();
    paths
        .into_iter()
        .map(|path| {
            let json = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
            let func: VerifiableFunction = serde_json::from_str(&json)
                .unwrap_or_else(|e| panic!("{}: not a VerifiableFunction: {e}", path.display()));
            (path.display().to_string(), func)
        })
        .collect()
}

/// `(shared, mutable)` counts of the `Rvalue::Ref` statements of the input body.
fn references_in(func: &VerifiableFunction) -> (usize, usize) {
    let mut counts = (0, 0);
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::Ref { mutable, .. }, .. } = stmt {
                if *mutable {
                    counts.1 += 1;
                } else {
                    counts.0 += 1;
                }
            }
        }
    }
    counts
}

fn is_permission_instruction(inst: &Inst) -> bool {
    matches!(inst, Inst::Borrow { .. } | Inst::BorrowMut { .. } | Inst::EndBorrow { .. })
}

fn is_reference_claim(proof: &ProofAnnotation) -> bool {
    matches!(proof, ProofAnnotation::SharedBorrow | ProofAnnotation::UniqueBorrow)
}

fn lower(func: &VerifiableFunction) -> Option<trust_ir::Module> {
    let func = func.clone();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || trust_ir_bridge::lower_to_trust_ir(&func).ok())
        .expect("spawn")
        .join()
        .expect("lowering a committed fixture must not panic")
}

#[test]
fn rust_references_spell_as_pointer_values() {
    let fixtures = fixtures();
    let mut lowered = 0usize;
    let mut with_reference = 0usize;
    let (mut shared, mut mutable) = (0usize, 0usize);
    let mut copies = 0usize;
    let mut failures = Vec::new();
    for (name, func) in &fixtures {
        let (s, m) = references_in(func);
        shared += s;
        mutable += m;
        if s + m > 0 {
            with_reference += 1;
        }
        let Some(module) = lower(func) else { continue };
        lowered += 1;
        let nodes = module
            .functions
            .iter()
            .flat_map(|function| function.blocks.iter())
            .flat_map(|block| block.body.iter());
        let mut module_references = 0usize;
        for node in nodes {
            if is_permission_instruction(&node.inst) {
                failures.push(format!("{name}: a permission instruction, {:?}", node.inst));
            }
            if node.proofs.iter().any(is_reference_claim) {
                if !matches!(&node.inst, Inst::Copy { ty: IrTy::Ptr | IrTy::FatPtr(_), .. }) {
                    failures.push(format!(
                        "{name}: a reference claim on a node that is not a pointer Copy, {:?}",
                        node.inst
                    ));
                }
                module_references += 1;
            }
        }
        if s + m > 0 && module_references == 0 {
            eprintln!("{name}: {} reference(s) in the input, none in the module", s + m);
        }
        copies += module_references;
    }
    eprintln!(
        "rust_references_spell_as_pointer_values: {} fixtures, {lowered} lower; {with_reference} \
         carry {} `Rvalue::Ref` ({shared} shared, {mutable} mutable); {copies} claim-carrying \
         reference node(s) in the lowered modules",
        fixtures.len(),
        shared + mutable
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // The census is not vacuous: the committed inputs carry references, and some
    // of them reach a lowered module as claim-carrying `Copy`s.
    assert!(shared + mutable > 0, "the fixture set carries no `Rvalue::Ref`");
    assert!(copies > 0, "no reference reached a lowered module: the census proved nothing");
}
