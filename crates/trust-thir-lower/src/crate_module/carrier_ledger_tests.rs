//! Trust (plan step 3.4, docs/design/2026-10-02-step3-lean-through-trust-ir.md §4, §5.2, §5.3;
//! D36/D37): the authenticated tier-`gate` carrier, the session ledger, the codegen
//! license's per-function leg 4 and the Clean conservation leg.
//!
//! These replace `assembled_codegen_handoff_refuses_clean_origin_rows`, which pinned that the F1
//! handoff never indexes a Clean-origin row. Since 3.4 it indexes exactly the rows of this
//! Session's carrier ledger — a `gate` row stamped `clean-carrier-gate` whose gate token
//! authenticates the exact Function — and still refuses every other one. The tokens here are
//! REAL: minted by the frozen carrier gate from a Clean-kernel verdict over an actual emitted
//! Function, then published through `authenticate_published`, exactly as the join does it.
//!
//! What each test pins, and what it read before its code: `gated_clean_row_is_indexed` (the
//! handoff refused the row outright); `structural_clean_row_is_not_indexed` (unchanged:
//! refused); `forged_stamp_without_ledger_entry_is_refused` (no stamp existed, so nothing
//! checked one); `clean_row_edited_after_the_gate_is_refused` (no ledger, so nothing
//! re-authenticated the Function after the join); `subgate_clean_row_does_not_withdraw_the_rust_license`
//! (leg 4 withdrew the whole module); `ledger_of_another_session_is_refused` (no ledger
//! identity); `clean_conservation_counts_rust_callee_calls` (a Clean row had no verdict and was
//! withdrawn as "no verdict").
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use std::collections::BTreeSet;
use std::sync::Arc;

use trust_certify::clean_island::CleanIslandSession;
use trust_clean_ir_gate::{PublishedTrustIrFaithful, clean_carrier_gate_stamp};
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId};
use trust_ir::{BinOp, Block, BodyGate, Function, Inst, InstrNode, Module, Producer, Ty};

use super::*;
use crate::effect_conservation::{
    Effect, Lane, TagKind, declared_clean_callees, judge_clean_census, judge_clean_row,
};
use crate::lineage::DefinitionIdentity;
use crate::{AssembledCrateModuleForCodegen, AuthenticatedCleanRow, CleanLedgerSession};

/// The Clean def's source `DefIndex` and Rust path in every fixture (t1's `m::cleanWsum`).
const CLEAN_INDEX: u32 = 4;
const CLEAN_PATH: &str = "m::cleanWsum";
/// WS5.2: the link-time symbol the collector binds the Clean row to (a fixture v0 spelling of
/// `m::cleanWsum`; this test has no `tcx` to compute it).
const CLEAN_SYMBOL: &str = "_RNvNtCs0_2t11m9cleanWsum";
/// The Rust body's source `DefIndex`.
const RUST_INDEX: u32 = 2;

fn rust_identity() -> DefinitionIdentity {
    DefinitionIdentity::test_only(0x0003_4ca1, u64::from(RUST_INDEX))
}

fn clean_identity() -> DefinitionIdentity {
    DefinitionIdentity::test_only(0x0003_4ca1, u64::from(CLEAN_INDEX))
}

/// A direct-lane Rust body: `fn rust_only()`, one block, `ret`.
fn rust_body(id: u32, ty: FuncTyId) -> Function {
    let mut function = Function::new(FuncId::new(id), "rust_only", ty, BlockId::new(0))
        .with_producer(Producer::TRust);
    let mut block = Block::new(BlockId::new(0));
    block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(block);
    function
}

/// t1's crate as the join publishes it: `rust_only` at FuncId 0 (the direct set), and
/// `cleanWsum := a + b` at FuncId 1, relocated, `Producer::Clean`, stamped
/// `clean-carrier-gate` — with the published token `authenticate_published` returned for it.
fn gated_fixture() -> (Module, PublishedTrustIrFaithful) {
    let mut session = CleanIslandSession::new();
    let outcome = session.check("def cleanWsum (a b : UInt64) : UInt64 := a + b");
    assert!(!outcome.is_rejected(), "fixture must kernel-check: {outcome:?}");
    let env = session.environment().expect("untainted fixture");
    let plan = trust_clean_origin::plan_clean_origin_body(env, "cleanWsum").expect("plans");
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).expect("signature");
    let mut function =
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .expect("emits");
    // WS5.2: the collector names the subject by the Rust item's link-time symbol (the Lean
    // spelling moves to `display_path`) before the carrier gate mints its token.
    crate::link_symbol::bind_clean_origin_link_symbol(&mut function, CLEAN_SYMBOL)
        .expect("WS5.2: the fixture binds its link-time symbol");
    let token = trust_clean_ir_gate::admit_wrapping_binop(
        env,
        &plan,
        CLEAN_INDEX,
        CLEAN_PATH,
        &signature,
        &function,
    )
    .expect("the carrier gate admits the actual emitted Function");

    let mut module = Module::new("t1");
    let unit = module
        .add_func_type(FuncTy { params: vec![], returns: vec![], is_vararg: false, abi: None })
        .expect("Module::add_func_type: test fixture");
    module.try_add_function(rust_body(0, unit)).expect("Module::try_add_function: test fixture");
    let clean_ty =
        module.add_func_type(signature.clone()).expect("Module::add_func_type: test fixture");
    let mut published = function.clone();
    published.id = FuncId::new(1);
    published.ty = clean_ty;
    published.producer = Some(Producer::Clean);
    published.body_gate = Some(clean_carrier_gate_stamp());
    let entry = token
        .authenticate_published(
            "cleanWsum",
            CLEAN_INDEX,
            CLEAN_PATH,
            &signature,
            &function,
            &published,
        )
        .expect("the join's publication authenticates");
    module.try_add_function(published).expect("Module::try_add_function: test fixture");
    assert_eq!(module.functions[1].id, FuncId::new(1));
    (module, entry)
}

fn ledger_row(entry: PublishedTrustIrFaithful) -> AuthenticatedCleanRow {
    AuthenticatedCleanRow::new(FuncId::new(1), CLEAN_INDEX, clean_identity(), entry)
}

fn rust_bodies() -> Vec<(u32, DefinitionIdentity, FuncId)> {
    vec![(RUST_INDEX, rust_identity(), FuncId::new(0))]
}

fn assigned() -> Vec<(u32, FuncId)> {
    vec![(RUST_INDEX, FuncId::new(0))]
}

fn edit_add_to_sub(function: &mut Function) {
    for node in &mut function.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            assert_eq!(*op, BinOp::Add, "fixture is `a + b`");
            *op = BinOp::Sub;
            return;
        }
    }
    panic!("fixture has no BinOp");
}

fn direct_stamp() -> Option<BodyGate> {
    Some(BodyGate::Gated { authority: TRUST_DIRECT_LANE_AUTHORITY.to_string(), evidence: None })
}

#[test]
fn gated_clean_row_is_indexed() {
    let (mut module, entry) = gated_fixture();
    let session = CleanLedgerSession::fresh();
    let ledger = vec![ledger_row(entry)];

    // Leg 4: the authenticated row keeps its `clean-carrier-gate` stamp, the direct body keeps
    // the structural license, and the license is granted.
    let mut errors = Vec::new();
    let carrier = crate::clean_carrier_authenticated(&module, &ledger, &mut errors);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(carrier, BTreeSet::from([FuncId::new(1)]));
    assert_eq!(stamp_codegen_license(&mut module, &assigned(), &carrier), None);
    assert_eq!(module.functions[0].body_gate, direct_stamp());
    assert_eq!(module.functions[1].body_gate, Some(clean_carrier_gate_stamp()));
    // The `clean-carrier-gate` row is licensed for its own consumer only: never in this
    // producer's inventory (the crate-module lane emits no Clean body).
    assert_eq!(inventory_from_stamps(&module), vec![FuncId::new(0)]);

    // The handoff indexes it beside the Rust body, from this Session's ledger.
    let handoff = AssembledCrateModuleForCodegen::checked_with_ledger(
        Arc::new(module),
        rust_bodies(),
        ledger,
        Some(session),
    )
    .expect("an authenticated gate row is handed off");
    assert_eq!(handoff.lookup_exact(CLEAN_INDEX, clean_identity()), Some(FuncId::new(1)));
    assert_eq!(handoff.lookup_exact(RUST_INDEX, rust_identity()), Some(FuncId::new(0)));
    assert_eq!(handoff.indexed_def_index(FuncId::new(1)), Some(CLEAN_INDEX));
    let rows = handoff.clean_ledger(session).expect("this Session's ledger");
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].published().rust_def_path(), CLEAN_PATH);
    assert!(matches!(handoff.clean_row_check(session, FuncId::new(1)), Some(Ok(_))));
    assert!(handoff.clean_row_check(session, FuncId::new(0)).is_none(), "a Rust body");

    // And the Clean conservation leg judges it conserved: its declaration fixes no call.
    let module = handoff.assembled_module().expect("module");
    assert!(judge_clean_row(&module, &rows[0]).is_empty());
}

#[test]
fn structural_clean_row_is_not_indexed() {
    // `cleanMin` below tier `gate`: a Clean body with no token, so no ledger entry and no stamp.
    let (mut module, entry) = gated_fixture();
    module.functions[1].body_gate = None;
    module.functions[1].name = "cleanMin".to_string();

    // Passed as a Rust body: refused, as before 3.4.
    let mut bodies = rust_bodies();
    bodies.push((CLEAN_INDEX, clean_identity(), FuncId::new(1)));
    let err = AssembledCrateModuleForCodegen::checked(Arc::new(module.clone()), bodies)
        .err()
        .expect("a Clean row is never handed off as a Rust body");
    assert!(err.contains("Clean-origin FuncId(1)") && err.contains("as a Rust body"), "{err}");

    // With no ledger it is not indexed at all; the Rust body is.
    let handoff = AssembledCrateModuleForCodegen::checked(Arc::new(module.clone()), rust_bodies())
        .expect("the Rust body alone is handed off");
    assert_eq!(handoff.lookup_exact(CLEAN_INDEX, clean_identity()), None);

    // A ledger entry cannot be pointed at it: the token authenticates only its own stamped
    // Function, and this one carries no stamp.
    let err = AssembledCrateModuleForCodegen::checked_with_ledger(
        Arc::new(module.clone()),
        rust_bodies(),
        vec![ledger_row(entry)],
        Some(CleanLedgerSession::fresh()),
    )
    .err()
    .expect("an unstamped row does not authenticate");
    assert!(err.contains("ledger-stamp"), "{err}");

    // Leg 4 stamps it `Ungated` (no authenticated entry), and keeps the direct license.
    assert_eq!(stamp_codegen_license(&mut module, &assigned(), &BTreeSet::new()), None);
    assert_eq!(module.functions[1].body_gate, Some(BodyGate::Ungated));
    assert_eq!(module.functions[0].body_gate, direct_stamp());
}

#[test]
fn forged_stamp_without_ledger_entry_is_refused() {
    // The stamp is a free-form string anyone can write. Without its ledger entry the handoff
    // refuses the WHOLE module (a finalization error), whichever producer the body claims.
    let (module, _entry) = gated_fixture();
    let err = AssembledCrateModuleForCodegen::checked_with_ledger(
        Arc::new(module.clone()),
        rust_bodies(),
        Vec::new(),
        Some(CleanLedgerSession::fresh()),
    )
    .err()
    .expect("a stamp with no ledger entry is refused");
    assert!(err.contains("no entry in this Session's carrier ledger"), "{err}");
    // WS5.2: the refusal names the row by its `Function.name`, the bound link-time symbol.
    assert!(err.contains(&format!("FuncId(1) `{CLEAN_SYMBOL}`")), "{err}");

    let mut rust_forgery = module.clone();
    rust_forgery.functions[0].body_gate = Some(clean_carrier_gate_stamp());
    rust_forgery.functions[1].body_gate = None;
    let err = AssembledCrateModuleForCodegen::checked(Arc::new(rust_forgery), rust_bodies())
        .err()
        .expect("a stamp on a Rust body is refused");
    assert!(err.contains("FuncId(0) `rust_only`"), "{err}");

    // Leg 4 never honors a stamp it did not authenticate: with no authenticated entry the forged
    // stamp is overwritten `Ungated`, and the read-back agrees.
    let mut stamped = module;
    assert_eq!(stamp_codegen_license(&mut stamped, &assigned(), &BTreeSet::new()), None);
    assert_eq!(stamped.functions[1].body_gate, Some(BodyGate::Ungated));
    assert!(clean_carrier_stamps(&stamped).is_empty());
}

#[test]
fn clean_row_edited_after_the_gate_is_refused() {
    // `a + b` became `a - b` after the join authenticated and stamped the row; the stamp is
    // still there, the shape and carrier still read `wrapping-binop` at UInt64.
    let (mut module, entry) = gated_fixture();
    edit_add_to_sub(&mut module.functions[1]);
    let ledger = vec![ledger_row(entry)];

    // At the codegen license: a fatal self-disagreement, no license.
    let mut errors = Vec::new();
    let carrier = crate::clean_carrier_authenticated(&module, &ledger, &mut errors);
    assert!(carrier.is_empty());
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("ledger-digest"), "{errors:?}");
    let mut stamped = module.clone();
    assert_eq!(stamp_codegen_license(&mut stamped, &assigned(), &carrier), None);
    assert_eq!(stamped.functions[1].body_gate, Some(BodyGate::Ungated));

    // At the handoff: refused.
    let err = AssembledCrateModuleForCodegen::checked_with_ledger(
        Arc::new(module.clone()),
        rust_bodies(),
        ledger,
        Some(CleanLedgerSession::fresh()),
    )
    .err()
    .expect("an edited row is never handed off");
    assert!(err.contains("does not authenticate") && err.contains("ledger-digest"), "{err}");

    // And edited AFTER the handoff was installed (the handoff's own module changed under it):
    // the lookup re-authenticates and refuses, and the conservation leg refuses it too.
    let (good, entry) = gated_fixture();
    let session = CleanLedgerSession::fresh();
    let mut handoff = AssembledCrateModuleForCodegen::checked_with_ledger(
        Arc::new(good),
        rust_bodies(),
        vec![ledger_row(entry)],
        Some(session),
    )
    .expect("the unedited row is handed off");
    let mut edited = (*handoff.assembled_module().unwrap()).clone();
    edit_add_to_sub(&mut edited.functions[1]);
    handoff.module = Some(Arc::new(edited.clone()));
    assert!(matches!(handoff.clean_row_check(session, FuncId::new(1)), Some(Err(_))));
    let rows = handoff.clean_ledger(session).expect("same Session");
    let tags = judge_clean_row(&edited, &rows[0]);
    assert_eq!(tags.len(), 1, "{tags:?}");
    assert_eq!(tags[0].kind, TagKind::NotConserved(Effect::Census));
}

#[test]
fn subgate_clean_row_does_not_withdraw_the_rust_license() {
    // t3's shape: a Rust body beside a Clean row below tier `gate` (no ledger entry).
    let (mut module, _entry) = gated_fixture();
    module.functions[1].body_gate = None;
    assert_eq!(compute_codegen_license(&module, &assigned()), Ok(vec![FuncId::new(0)]));
    let refusal = stamp_codegen_license(&mut module, &assigned(), &BTreeSet::new());
    assert_eq!(refusal, None, "the direct license is not withdrawn");
    assert_eq!(module.functions[0].body_gate, direct_stamp());
    assert_eq!(module.functions[1].body_gate, Some(BodyGate::Ungated));
    let published = decide_publication("t3", module.clone(), &assigned(), &[], refusal)
        .unwrap_or_else(|reason| panic!("publishes: {reason}"));
    assert_eq!(published.codegen_inventory(), &[FuncId::new(0)]);
    assert!(!published.is_codegen_licensed(FuncId::new(1)));

    // Control: an appended body of any OTHER producer still withdraws the whole module (leg 4
    // was relaxed for Clean-origin bodies only, D37 / STEP3.4-LEG4-SCOPE).
    let mut foreign = module;
    foreign.functions[1].producer = Some(Producer::TRust);
    let refusal = stamp_codegen_license(&mut foreign, &assigned(), &BTreeSet::new())
        .expect("a non-Clean appended body withdraws the license");
    assert!(refusal.contains("other than Clean"), "{refusal}");
    assert_eq!(foreign.functions[0].body_gate, Some(BodyGate::Ungated));
    // And an authenticated set cannot license a non-Clean body.
    assert!(
        clean_carrier_licensed(&foreign, &assigned(), &BTreeSet::from([FuncId::new(1)])).is_empty()
    );
}

/// A REAL compiler `Session`, built as `rustc_interface` builds one (`rustc_session::build_session`
/// from default options for the host target, inside its own session globals), handed to `f`. The
/// ledger identity under test lives in `Session` state, so only a real `Session` exercises
/// [`CleanLedgerSession::of`]; a synthetic identity would pin the comparison and not the binding.
#[allow(rustc::bad_opt_access)]
fn with_real_session<R>(f: impl FnOnce(&rustc_session::Session) -> R) -> R {
    use rustc_session::config::{ErrorOutputType, Input, Options, build_target_config};
    use rustc_session::{
        CodegenBackendInit, CompilerIO, EarlyDiagCtxt, build_early_session, build_session,
    };
    use rustc_span::source_map::{RealFileLoader, SourceMapInputs};

    static USING_INTERNAL_FEATURES: std::sync::atomic::AtomicBool =
        std::sync::atomic::AtomicBool::new(false);
    let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
    let options = Options::default();
    let target = build_target_config(
        &early_dcx,
        &options.target_triple,
        options.sysroot.path(),
        options.unstable_opts.unstable_options,
    );
    let source_map = SourceMapInputs {
        file_loader: Box::new(RealFileLoader) as _,
        path_mapping: options.file_path_mapping(),
        hash_kind: options.unstable_opts.src_hash_algorithm(&target),
        checksum_hash_kind: options.unstable_opts.checksum_hash_algorithm(),
    };
    rustc_span::create_session_globals_then(
        rustc_span::edition::DEFAULT_EDITION,
        &[],
        Some(source_map),
        || {
            let io = CompilerIO {
                input: Input::Str {
                    name: rustc_span::FileName::Custom(String::new()),
                    input: String::new(),
                },
                output_dir: None,
                output_file: None,
                temps_dir: None,
            };
            // Upstream 1.101: `build_session` takes a built `EarlySession`
            // (which needs the session globals this closure runs under) and
            // the codegen-backend init info separately.
            let early = build_early_session(options, target, None);
            let sess = build_session(
                early,
                CodegenBackendInit::default(),
                io,
                Default::default(),
                "",
                &USING_INTERNAL_FEATURES,
            );
            f(&sess)
        },
    )
}

#[test]
fn ledger_of_another_session_is_refused() {
    // Two REAL compiler Sessions in one process, both alive at once: the second is built on its
    // own thread with its own session globals, as a second compiler in the same process is.
    // Each takes its ledger identity from its own Session state (`CleanLedgerSession::of`):
    // one identity for the whole of a Session, never the identity of another Session.
    let (first_session, second_session) = with_real_session(|first| {
        let identity = CleanLedgerSession::of(first);
        assert_eq!(CleanLedgerSession::of(first), identity, "one identity for the whole Session");
        let other = std::thread::scope(|scope| {
            scope
                .spawn(|| with_real_session(|second| CleanLedgerSession::of(second)))
                .join()
                .expect("the second Session is built")
        });
        assert_eq!(CleanLedgerSession::of(first), identity, "another Session changes nothing here");
        (identity, other)
    });
    assert_ne!(first_session, second_session, "two Sessions never share a ledger identity");
    let (module, entry) = gated_fixture();
    let handoff = AssembledCrateModuleForCodegen::checked_with_ledger(
        Arc::new(module),
        rust_bodies(),
        vec![ledger_row(entry)],
        Some(first_session),
    )
    .expect("installed by the first Session");
    assert!(handoff.clean_ledger(first_session).is_ok());
    let err = handoff
        .clean_ledger(second_session)
        .err()
        .expect("the second Session never reads the first Session's ledger");
    assert!(err.contains("honored only in the Session that minted it"), "{err}");
    assert!(matches!(handoff.clean_row_check(second_session, FuncId::new(1)), Some(Err(_))));
    assert!(matches!(handoff.clean_row_check(first_session, FuncId::new(1)), Some(Ok(_))));

    // A ledger with no installing Session is not installed at all.
    let (module, entry) = gated_fixture();
    let err = AssembledCrateModuleForCodegen::checked_with_ledger(
        Arc::new(module),
        rust_bodies(),
        vec![ledger_row(entry)],
        None,
    )
    .err()
    .expect("a ledger needs its Session");
    assert!(err.contains("no installing Session"), "{err}");
}

#[test]
fn clean_conservation_counts_rust_callee_calls() {
    // A Lean -> Rust chain (`twice_inc := inc (inc x)` with a second callee): the census is the
    // declaration's Rust-callee node list — callees, ORDER and MULTIPLICITY.
    let (inc, dec) = (FuncId::new(5), FuncId::new(6));
    let chain = |calls: &[FuncId], extra: Option<Inst>| {
        let mut function =
            Function::new(FuncId::new(9), "twice_inc", FuncTyId::new(0), BlockId::new(0))
                .with_producer(Producer::Clean);
        let mut block = Block::new(BlockId::new(0));
        for callee in calls {
            block.body.push(InstrNode::new(Inst::Call { callee: *callee, args: vec![] }));
        }
        if let Some(inst) = extra {
            block.body.push(InstrNode::new(inst));
        }
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        function
    };
    let body = chain(&[inc, inc, dec], None);
    assert!(judge_clean_census(&body, &[inc, inc, dec]).is_empty(), "exactly the declared list");
    for declared in [vec![inc, dec], vec![inc, dec, inc], vec![inc, inc, dec, dec], vec![]] {
        let tags = judge_clean_census(&body, &declared);
        assert_eq!(tags.len(), 1, "{declared:?}: {tags:?}");
        assert_eq!(tags[0].kind, TagKind::NotConserved(Effect::Call), "{declared:?}");
    }
    // An unlisted call is not conserved even when every declared call is present.
    let tags = judge_clean_census(&chain(&[inc, inc, dec, FuncId::new(7)], None), &[inc, inc, dec]);
    assert_eq!(tags.len(), 1, "{tags:?}");
    // Any other effect, whatever the calls: a store, an `undef`.
    let store = Inst::Store {
        ty: Ty::U64,
        ptr: trust_ir::ValueId::new(0),
        value: trust_ir::ValueId::new(1),
        volatile: false,
        align: None,
    };
    let tags = judge_clean_census(&chain(&[inc, inc, dec], Some(store)), &[inc, inc, dec]);
    assert!(tags.iter().any(|tag| tag.kind == TagKind::NotConserved(Effect::Store)), "{tags:?}");
    let undef = Inst::Undef { ty: Ty::U64 };
    let tags = judge_clean_census(&chain(&[inc, inc, dec], Some(undef)), &[inc, inc, dec]);
    assert!(tags.iter().any(|tag| tag.kind == TagKind::Abstracted(Lane::Undef)), "{tags:?}");

    // Every shape the carrier gate reflects today fixes NO call, so a gated row that calls is
    // not conserved.
    let (module, entry) = gated_fixture();
    assert!(declared_clean_callees(entry.shape()).is_empty());
    let mut calling = module.functions[1].clone();
    calling.blocks[0]
        .body
        .insert(0, InstrNode::new(Inst::Call { callee: FuncId::new(0), args: vec![] }));
    let tags = judge_clean_census(&calling, &declared_clean_callees(entry.shape()));
    assert_eq!(tags.len(), 1, "{tags:?}");
    assert_eq!(tags[0].kind, TagKind::NotConserved(Effect::Call));
    assert!(
        judge_clean_census(&module.functions[1], &declared_clean_callees(entry.shape())).is_empty()
    );
}
