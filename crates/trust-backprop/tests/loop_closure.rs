//! Pillar-2 closed-loop demonstration: prove → strengthen → BACKPROP.
//!
//! Last turn showed the STRENGTHEN half (trust-strengthen proposes a spec for a
//! proof failure). This closes the loop: feed that `Proposal` through
//! `trust-backprop`, which rewrites the SOURCE to insert a first-class
//! `requires` clause into the function signature — the form trustc lowers into
//! `body.contract`, so the NEXT compile re-verifies the strengthened function.
//! The subject is the real `range.rs::unsigned_max` shift-overflow the flywheel
//! surfaced.
use trust_backprop::{GovernancePolicy, apply_plan, apply_plan_to_source};
use trust_strengthen::{Proposal, ProposalKind};

#[test]
fn prove_strengthen_backprop_loop_closes_on_unsigned_max() {
    // A real source file (proposal_to_rewrites locates the fn by reading it).
    let dir = std::env::temp_dir().join(format!("tbp_loop_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("range_demo.rs");
    // Private fn (governance intentionally refuses to auto-edit a `pub` API).
    let source = "fn unsigned_max(width: u32) -> u128 {\n    (1u128 << width) - 1\n}\n";
    std::fs::write(&file, source).unwrap();

    // The proposal trust-strengthen emits for the shift-overflow (context-aware:
    // real shift var `width` + real operand bit width 128).
    let proposal = Proposal {
        function_path: file.display().to_string(),
        function_name: "unsigned_max".into(),
        kind: ProposalKind::AddPrecondition { spec_body: "width < 128".into() },
        confidence: 0.9,
        rationale: "shift amount must be below the operand's bit width".into(),
    };

    // BACKPROP: proposal → governance-checked RewritePlan → rewritten source.
    let plan = apply_plan(&[proposal], &GovernancePolicy::default()).expect("plan builds");
    assert!(!plan.rewrites.is_empty(), "a private-fn precondition proposal must yield a rewrite");

    let rewritten = apply_plan_to_source(source, &plan).expect("rewrite applies");

    // The loop only closes if the clause lands in the SIGNATURE — between the
    // return type and the body brace. That position is what the parser lowers
    // into `body.contract`; the same text one line lower would be a statement
    // the re-prove step never sees as a precondition.
    let clause = rewritten
        .find("requires width < 128")
        .unwrap_or_else(|| panic!("backprop must insert a native requires clause; got:\n{rewritten}"));
    let body_brace = rewritten.find('{').expect("the rewritten fn must keep a body");
    assert!(
        clause < body_brace,
        "the requires clause must precede the body brace to be a signature clause:\n{rewritten}"
    );
    assert!(rewritten.contains("fn unsigned_max"), "the function must survive:\n{rewritten}");
    // Spec syntax is the two ratified languages only: no attribute form survives.
    assert!(
        !rewritten.contains("#["),
        "spec text must be a native clause, not an attribute:\n{rewritten}"
    );

    std::fs::remove_dir_all(&dir).ok();
}
