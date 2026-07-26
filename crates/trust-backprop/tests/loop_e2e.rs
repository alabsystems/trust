//! End-to-end pass over one rewrite-loop iteration on the real div-zero
//! fixture: prove verdict → strengthen → plan → approval → checkpoint → apply
//! → undo.
//!
//! The compiler verdict is the one thing this test supplies rather than
//! measures: every stage after it is the production code path, driven by the
//! same fixture the program-index benchmark uses. So this file is evidence
//! about the LOOP — that a real div-zero failure yields a native `requires`
//! clause, that the clause is never silently written into the user's file, and
//! that whatever *is* written can be taken back byte for byte. It is not
//! evidence about the verifier, and a passing run here says nothing about
//! whether trustc can prove anything. The real-compiler frontier evidence lives
//! in `program_index_real_verifier_repair_e2e.rs`.

use std::path::{Path, PathBuf};

use trust_backprop::{
    ApprovalPolicy, ContractClauseKind, GovernancePolicy, RewriteKind, RewritePlan, SourceRewrite,
    apply_plan, apply_plan_to_source, classify_rewrite, create_checkpoint, default_rules, rollback,
};
use trust_backprop::file_io::apply_plan_to_files;
use trust_strengthen::{
    FailureAnalysis, Proposal, ProposalKind, analyze_failure, read_function, strengthen_with_context,
};
use trust_types::{
    Formula, SourceSpan, VcKind, VerificationCondition, VerificationResult as SolverVerdict,
};

const FIXTURE: &str = "examples/bench/program_index/cases/proof_div_zero_flawed.rs";
const FUNCTION: &str = "divide_unchecked";

#[test]
fn div_zero_iteration_proposes_a_native_requires_clause_and_never_auto_writes_it() {
    let workspace = Workspace::from_fixture();
    let proposals = workspace.strengthen_div_zero_failure();

    let precondition = proposals
        .iter()
        .find_map(|proposal| match &proposal.kind {
            ProposalKind::AddPrecondition { spec_body } => Some(spec_body.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("a div-zero failure must propose a precondition: {proposals:#?}"));
    assert_eq!(
        precondition, "y != 0",
        "the precondition must name the fixture's real divisor parameter"
    );

    let plan = apply_plan(&proposals, &GovernancePolicy::default()).expect("plan builds");
    let (auto, review) = split_by_approval(&plan);

    // The clause is a semantic claim about the contract that nothing has
    // checked yet, so it belongs in front of a reviewer, not in the file.
    let queued = review
        .iter()
        .find(|rewrite| {
            matches!(
                &rewrite.kind,
                RewriteKind::InsertContractClause { clause: ContractClauseKind::Requires, .. }
            )
        })
        .expect("the requires clause must be queued for review");
    assert!(
        !auto.iter().any(|rewrite| matches!(
            rewrite.kind,
            RewriteKind::InsertContractClause { .. }
        )),
        "no contract clause may be written to source without review: {auto:#?}"
    );

    // What the reviewer is being offered has to be a native signature clause:
    // the same position trustc lowers into `body.contract`. A clause rendered
    // anywhere else would re-verify as nothing at all.
    let mut clause_plan = RewritePlan::new("review: requires clause".to_string());
    clause_plan.rewrites.push(queued.clone());
    let rendered = apply_plan_to_source(&workspace.original, &clause_plan)
        .expect("the queued clause renders into the fixture");
    let clause = rendered
        .find("requires y != 0")
        .unwrap_or_else(|| panic!("the queued rewrite must render a native clause:\n{rendered}"));
    let body_brace = rendered
        .find(&format!("fn {FUNCTION}"))
        .and_then(|start| rendered[start..].find('{').map(|offset| start + offset))
        .expect("the rewritten fn must keep a body");
    assert!(
        clause < body_brace,
        "the clause must sit in the signature, not the body:\n{rendered}"
    );
    assert!(!rendered.contains("#["), "spec text must be a native clause:\n{rendered}");
}

#[test]
fn applied_rewrites_reach_the_file_and_the_checkpoint_takes_them_back() {
    let workspace = Workspace::from_fixture();
    let proposals = workspace.strengthen_div_zero_failure();
    let plan = apply_plan(&proposals, &GovernancePolicy::default()).expect("plan builds");
    let (auto, _) = split_by_approval(&plan);
    assert!(
        !auto.is_empty(),
        "the div-zero iteration must have something to apply, or this test proves nothing"
    );

    // Exactly the order the loop uses: capture first, write second.
    let checkpoint =
        create_checkpoint(&[workspace.file.clone()]).expect("checkpoint the fixture copy");
    let mut auto_plan = RewritePlan::new("auto".to_string());
    auto_plan.rewrites = auto;
    auto_plan.sort_for_application();
    apply_plan_to_files(&auto_plan).expect("the approved plan applies");

    let applied = std::fs::read_to_string(&workspace.file).expect("read the rewritten fixture");
    assert_ne!(applied, workspace.original, "the loop must actually have edited the file");
    assert!(
        applied.contains("assert!(y != 0"),
        "the approved rewrite is the runtime non-zero check:\n{applied}"
    );

    rollback(&checkpoint).expect("rollback restores the fixture");
    let restored = std::fs::read_to_string(&workspace.file).expect("read the restored fixture");
    assert_eq!(
        restored, workspace.original,
        "a rejected generation must leave the file byte-identical to what the user wrote"
    );
}

#[test]
fn a_regressed_generation_is_undone_even_after_several_applies() {
    let workspace = Workspace::from_fixture();
    let proposals = workspace.strengthen_div_zero_failure();
    let plan = apply_plan(&proposals, &GovernancePolicy::default()).expect("plan builds");
    let (auto, _) = split_by_approval(&plan);

    // The loop holds one checkpoint per generation, so an undo has to survive
    // the file having been rewritten more than once since it was taken.
    let first = create_checkpoint(&[workspace.file.clone()]).expect("first checkpoint");
    let mut auto_plan = RewritePlan::new("auto".to_string());
    auto_plan.rewrites = auto;
    auto_plan.sort_for_application();
    apply_plan_to_files(&auto_plan).expect("first apply");

    let after_first = std::fs::read_to_string(&workspace.file).expect("read after first apply");
    let hand_edit = format!("{after_first}\n// a later generation\n");
    std::fs::write(&workspace.file, &hand_edit).expect("second write");

    rollback(&first).expect("rollback to the first checkpoint");
    let restored = std::fs::read_to_string(&workspace.file).expect("read after rollback");
    assert_eq!(restored, workspace.original, "the undo must reach past every later write");
}

/// A private copy of the shipped fixture, so a test that rewrites source can
/// never rewrite the repository's own fixture.
struct Workspace {
    _dir: tempfile::TempDir,
    file: PathBuf,
    original: String,
}

impl Workspace {
    fn from_fixture() -> Self {
        let fixture = repo_root().join(FIXTURE);
        let original = std::fs::read_to_string(&fixture)
            .unwrap_or_else(|error| panic!("read {}: {error}", fixture.display()));
        let dir = tempfile::tempdir().expect("create loop e2e tempdir");
        let file = dir.path().join("proof_div_zero_flawed.rs");
        std::fs::write(&file, &original).expect("copy the fixture");
        // The rewrite plan carries file paths; canonicalize once so the
        // checkpoint and the plan agree on the file's identity.
        let file = file.canonicalize().expect("canonicalize the fixture copy");
        Self { _dir: dir, file, original }
    }

    /// The strengthen half of one loop iteration for a div-by-zero failure
    /// reported against this fixture's division.
    fn strengthen_div_zero_failure(&self) -> Vec<Proposal> {
        let path = self.file.display().to_string();
        let context = read_function(&path, FUNCTION)
            .unwrap_or_else(|| panic!("the fixture must expose `{FUNCTION}` to the source reader"));
        let analysis = div_zero_analysis(&path);
        let proposals = strengthen_with_context(&path, FUNCTION, &[analysis], &context);
        assert!(!proposals.is_empty(), "a classified div-zero failure must propose something");
        proposals
    }
}

/// The failure a verifier reports for `x / y` when it cannot rule out `y == 0`.
fn div_zero_analysis(file: &str) -> FailureAnalysis {
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: FUNCTION.into(),
        location: SourceSpan {
            file: file.to_string(),
            line_start: 7,
            col_start: 5,
            line_end: 7,
            col_end: 10,
        },
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let verdict = SolverVerdict::Failed {
        solver: "ay-smtlib".into(),
        time_ms: 5,
        counterexample: None,
    };
    analyze_failure(&vc, &verdict)
}

/// Partition a plan the way the loop does: `Auto` is written to disk, anything
/// else waits for a human.
fn split_by_approval(plan: &RewritePlan) -> (Vec<SourceRewrite>, Vec<SourceRewrite>) {
    let rules = default_rules();
    let mut auto = Vec::new();
    let mut review = Vec::new();
    for rewrite in &plan.rewrites {
        match classify_rewrite(rewrite, &rules) {
            ApprovalPolicy::Auto => auto.push(rewrite.clone()),
            _ => review.push(rewrite.clone()),
        }
    }
    (auto, review)
}

fn repo_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .unwrap_or_else(|| manifest.clone())
}
