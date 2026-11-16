// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **THE UNFOLDED WEIGHT OF A `let`-BOUND RUST-CALL CHAIN IS BOUNDED ON THE
//! PLAN (2026-09-16).**
//!
//! The explicit value temporary (`emit::walk_let_spine`, W5 increment 7) made
//! the Rust-call chain a DAG: one node per `let`, read by several later nodes.
//! Until then every chain was a TREE, and that invariant silently bounded the
//! size of the term side B reflects — a tree of at most `COMPOSED_MAX_OPS`
//! nodes reflects to at most that many applications. A DAG has no such bound:
//! `let a0 := add2 x x; let a1 := add2 a0 a0; …; add2 a30 a30` is 32 nodes,
//! passes every node-count and depth rail, and unfolds to `2^32 - 1`
//! applications. Reflected as a tree, that is an out-of-memory death inside
//! the compiler where a refusal is due.
//!
//! Two independent fixes, pinned here together:
//!
//! 1. **The bound, on the PLAN.** `emit::check_rust_call_chain`'s unfold rail
//!    computes the unfolded size by dynamic programming over the sealed plan
//!    (saturating) and refuses past the kernel envelope this lane is measured
//!    at (`named_calls::MAX_NODES`, mirrored here as [`UNFOLD_CAP`] because it
//!    is `pub(crate)`), with a refusal that names the boundary and the fix
//!    (v7/D3). This is the one that makes the failure a refusal, and it is
//!    measured in bounded time. `control_27` half_13 measures the kernel at
//!    the same cap from the other side.
//! 2. **The memo, in the reflector.** `reflect_rust_call::render_node` renders
//!    each node once and clones the (shallow, `Arc`-childed) `Expr` at every
//!    later read, so the reflected term is a DAG in memory — the SAME term,
//!    minted in linear time. Defence in depth: it is not the bound.
//!
//! The control: a LINEAR chain of the same node count — every node read once,
//! weight = node count — still plans, emits, reflects and passes the kernel
//! gate, so the bound refuses the unfolding and not the length.

use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use clean_kernel::Environment;
use trust_clean_origin::{
    COMPOSED_MAX_OPS, CleanOriginPlan, CleanOriginShape, RustCallArg, RustCallLiteral,
    RustCallNode, RustCalleeRef,
};

/// `named_calls::MAX_NODES`, the kernel envelope `emit::check_rust_call_chain`
/// rails the unfolded chain at. It is `pub(crate)`, so it is MIRRORED here —
/// and a mirror that can drift is worth less than no mirror, so which test
/// catches the drift matters and is stated exactly.
///
/// The pin is [`a_doubling_chain_at_the_node_cap_refuses_with_options_in_bounded_time`],
/// which asserts the refusal NOTE contains this number: the note is formatted
/// from the crate's own `MAX_NODES`, so a crate that moves the cap prints a
/// different number and that assertion fails.
///
/// It is NOT [`the_cap_admits_the_last_doubling_within_it_and_refuses_the_next`],
/// which the comment here used to credit. That test computes its subject FROM
/// this mirror (`last_admitted_doubling` walks `1 << n` against `UNFOLD_CAP`),
/// so a divergence moves both sides of its own comparison and it stays green:
/// at a real cap of 6_000 with the mirror still 4_096 it would still find 12,
/// still admit `2^12 - 1` and still refuse `2^13 - 1`. It pins the SHAPE of the
/// boundary, not its VALUE. The two together pin both; only one pins the value.
const UNFOLD_CAP: usize = 4_096;
use trust_types::admissible_body::recognize_rust_call_chain;
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
    UnwindEdge, VerifiableBody, VerifiableFunction,
};

fn rust_call_environment(source: &str) -> (Environment, Vec<RustCalleeRef>) {
    use trust_certify::clean_island::{CleanIslandSession, RustCallee};
    let declarations = vec![
        RustCallee { clean_name: "tick".into(), params: vec![Ty::u64()], result: Ty::u64() },
        RustCallee {
            clean_name: "add2".into(),
            params: vec![Ty::u64(), Ty::u64()],
            result: Ty::u64(),
        },
    ];
    let mut session = CleanIslandSession::new();
    session.declare_rust_callees(&declarations).unwrap();
    let report = session.check_all(&[source]);
    assert!(!report.is_rejected(), "{report:?}");
    let table = declarations
        .into_iter()
        .map(|row| RustCalleeRef {
            def_path: format!("test::{}", row.clean_name),
            clean_name: row.clean_name,
            params: row.params,
            result: row.result,
        })
        .collect();
    (session.environment().unwrap().clone(), table)
}

/// `n` nodes, each reading the previous one TWICE: unfolded weight `2^n - 1`.
fn doubling_source(name: &str, n: usize) -> String {
    assert!(n >= 2);
    let mut source = format!("def {name} (x : UInt64) : UInt64 :=\n  let a0 := add2 x x;\n");
    for k in 1..n - 1 {
        source.push_str(&format!("  let a{k} := add2 a{} a{};\n", k - 1, k - 1));
    }
    source.push_str(&format!("  add2 a{} a{}\n", n - 2, n - 2));
    source
}

/// `n` nodes, each reading the previous one ONCE: unfolded weight `n`.
fn linear_source(name: &str, n: usize) -> String {
    assert!(n >= 2);
    let mut source = format!("def {name} (x : UInt64) : UInt64 :=\n  let a0 := tick x;\n");
    for k in 1..n - 1 {
        source.push_str(&format!("  let a{k} := tick a{};\n", k - 1));
    }
    source.push_str(&format!("  tick a{}\n", n - 2));
    source
}

/// The MIR the materializer emits for a Rust-call chain over ONE `u64`
/// parameter: `_0` the result, `_1` the parameter, one temporary per non-root
/// node, one `Call` per node, a `Copy` at every read.
fn emitted_chain(
    name: &str,
    plan: &CleanOriginPlan,
    table: &[RustCalleeRef],
) -> VerifiableFunction {
    let CleanOriginShape::RustCallChain { nodes } = plan.shape() else {
        panic!("`{name}` planned {:?}, not a Rust-call chain", plan.shape());
    };
    emitted_chain_of_nodes(name, nodes, table)
}

fn emitted_chain_of_nodes(
    name: &str,
    nodes: &[RustCallNode],
    table: &[RustCalleeRef],
) -> VerifiableFunction {
    let root = nodes.len() - 1;
    let temp_of = |k: usize| 2 + k;
    let locals: Vec<LocalDecl> =
        (0..2 + root).map(|index| LocalDecl { index, ty: Ty::u64(), name: None }).collect();
    let mut blocks: Vec<BasicBlock> = nodes
        .iter()
        .enumerate()
        .map(|(k, node)| BasicBlock {
            id: BlockId(k),
            stmts: Vec::new(),
            terminator: Terminator::Call {
                func: table[node.callee].def_path.clone().into(),
                args: node
                    .args
                    .iter()
                    .map(|arg| match arg {
                        RustCallArg::Param(i) => Operand::Copy(Place::local(1 + i)),
                        RustCallArg::Node(j) => Operand::Copy(Place::local(temp_of(*j))),
                        RustCallArg::Literal(RustCallLiteral::UInt(v)) => {
                            Operand::Constant(ConstValue::Uint(*v, 64))
                        }
                        RustCallArg::Literal(RustCallLiteral::Bool(b)) => {
                            Operand::Constant(ConstValue::Bool(*b))
                        }
                    })
                    .collect(),
                dest: Place::local(if k == root { 0 } else { temp_of(k) }),
                target: Some(BlockId(k + 1)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: None,
                unwind: UnwindEdge::Continue,
            },
        })
        .collect();
    blocks.push(BasicBlock {
        id: BlockId(nodes.len()),
        stmts: Vec::new(),
        terminator: Terminator::Return,
    });
    VerifiableFunction {
        name: name.into(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Plan and, if it plans, run the emitted MIR through the whole of side B
/// (`admit_lowering`: recognize, reflect, kernel gate). Returns the elapsed
/// wall clock and the outcome.
fn plan_and_admit(source: &str, name: &str) -> (Duration, Result<(), String>) {
    let (env, table) = rust_call_environment(source);
    let started = Instant::now();
    let outcome = trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, name, &table)
        .map_err(|refusal| refusal.note())
        .and_then(|plan| {
            let emitted = emitted_chain(name, &plan, &table);
            trust_clean_origin::admit_lowering(&env, &plan, &emitted)
                .map(|_| ())
                .map_err(|refusal| refusal.note())
        });
    (started.elapsed(), outcome)
}

/// A doubling chain of `n` nodes as a HAND-BUILT plan shape (callee index 1 is
/// `add2` in [`rust_call_environment`]'s table), for reaching side B with a
/// weight the planner now refuses.
fn doubling_nodes(n: usize) -> Vec<RustCallNode> {
    let add2 = 1;
    // `let_binding` mirrors what `walk_let_spine` would mark: every node but
    // the root is a `let` value temporary, in binding order. Nothing here
    // runs the seal — `emitted_chain_of_nodes` builds the MIR directly — so
    // these markers are for faithfulness to the shape, not for a check.
    let mut nodes = vec![RustCallNode {
        callee: add2,
        args: vec![RustCallArg::Param(0), RustCallArg::Param(0)],
        let_binding: Some(0),
    }];
    for k in 1..n {
        nodes.push(RustCallNode {
            callee: add2,
            args: vec![RustCallArg::Node(k - 1), RustCallArg::Node(k - 1)],
            let_binding: (k + 1 < n).then_some(k),
        });
    }
    nodes
}

/// Recognize and REFLECT ONLY (no kernel gate) a hand-built doubling chain of
/// `n` nodes: the cost of `reflect_rust_call_chain`, which includes the
/// kernel's type check of the minted definition in a scratch clone.
fn recognize_and_reflect_doubling(n: usize) -> (Duration, Result<(), String>) {
    let (env, table) = rust_call_environment("def probe (x : UInt64) : UInt64 := x");
    let extracted = emitted_chain_of_nodes("boom", &doubling_nodes(n), &table);
    let allowed: BTreeSet<String> = table.iter().map(|row| row.def_path.clone()).collect();
    let names: BTreeMap<String, String> =
        table.iter().map(|row| (row.def_path.clone(), row.clean_name.clone())).collect();
    let started = Instant::now();
    let outcome = recognize_rust_call_chain(&extracted, &allowed)
        .ok_or_else(|| "the emitted chain did not recognize".to_owned())
        .and_then(|body| {
            trust_clean_origin::reflect_rust_call_chain(&env, "boom", &body, &extracted, &names)
                .map(|_| ())
        });
    (started.elapsed(), outcome)
}

/// The largest `n` whose doubling weight `2^n - 1` is within the cap.
fn last_admitted_doubling() -> usize {
    (1..usize::BITS as usize)
        .take_while(|n| (1usize << n) - 1 <= UNFOLD_CAP)
        .last()
        .expect("the cap admits at least a two-node chain")
}

/// A generous wall-clock bound: the refusal is a plan-time DP over at most
/// `COMPOSED_MAX_OPS` nodes and takes microseconds; the admitted controls
/// take tens of milliseconds in a debug build. Anything approaching this is
/// the exponential coming back.
const GENEROUS: Duration = Duration::from_secs(10);

// ═══════════════════════════════ the pins ═══════════════════════════════

/// **THE REVIEWER'S FILE** (`rcboom32.rs`): 32 `let`-bound `add2` calls, each
/// reading the previous one twice. Node count 32 = `COMPOSED_MAX_OPS`, depth
/// 32, every pre-existing rail passed; unfolded weight `2^32 - 1`. It must
/// REFUSE — at plan time, with the boundary and the options — and it must do
/// so in bounded time, because before the bound existed it did neither.
#[test]
fn a_doubling_chain_at_the_node_cap_refuses_with_options_in_bounded_time() {
    let n = COMPOSED_MAX_OPS;
    let (env, table) = rust_call_environment(&doubling_source("boom", n));
    let started = Instant::now();
    let refusal =
        trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, "boom", &table)
            .expect_err("a chain of unfolded weight 2^32 - 1 must not plan");
    let elapsed = started.elapsed();
    let note = refusal.note();
    assert!(note.contains("unfolds every shared"), "{note}");
    assert!(note.contains(&(1u128 << 32).saturating_sub(1).to_string()), "{note}");
    assert!(note.contains(&UNFOLD_CAP.to_string()), "{note}");
    assert!(note.contains("options:"), "{note}");
    assert!(note.contains("split the chain across sibling `def`s"), "{note}");
    assert!(elapsed < GENEROUS, "the refusal took {elapsed:?}; the exponential is back");
}

/// The BOUNDARY is pinned: the last doubling within the cap admits through the
/// whole of side B (recognize, reflect, kernel gate), and the next doubling
/// refuses at plan time.
///
/// What this test can and cannot see, stated because the difference is easy to
/// misread. Its subject comes from [`UNFOLD_CAP`], the MIRROR, so it compares
/// the implementation against a doubling chosen by the mirror rather than
/// against the crate's own constant. A cap that moves DOWN past the last
/// admitted doubling fails it (that chain stops admitting). A cap that moves UP
/// without crossing the next doubling does NOT: at a real cap of 6_000 with the
/// mirror still 4_096 this test finds the same 12, `2^12 - 1` still admits and
/// `2^13 - 1` still refuses, all green. The VALUE is pinned one test up, by
/// [`a_doubling_chain_at_the_node_cap_refuses_with_options_in_bounded_time`],
/// which reads the number out of the refusal note the crate itself formatted.
#[test]
fn the_cap_admits_the_last_doubling_within_it_and_refuses_the_next() {
    let n = last_admitted_doubling();
    assert_eq!(
        n, 12,
        "the pinned cap is 4,096 (`named_calls::MAX_NODES`); re-measure before moving it"
    );

    let (elapsed, outcome) = plan_and_admit(&doubling_source("edge", n), "edge");
    outcome
        .unwrap_or_else(|note| panic!("weight 2^{n} - 1 is within the cap and must admit: {note}"));
    assert!(elapsed < GENEROUS, "admitting weight 2^{n} - 1 took {elapsed:?}");

    let (elapsed, outcome) = plan_and_admit(&doubling_source("past", n + 1), "past");
    let note = outcome.expect_err("the next doubling is past the cap and must refuse");
    assert!(note.contains("unfolds every shared") && note.contains("options:"), "{note}");
    assert!(elapsed < GENEROUS, "refusing weight 2^{} - 1 took {elapsed:?}", n + 1);
}

/// THE CONTROL: a LINEAR chain of the same node count — every node read once,
/// weight = node count = `COMPOSED_MAX_OPS` — plans as 32 nodes, emits,
/// reflects and passes the kernel gate. The bound refuses the UNFOLDING, not
/// the length.
#[test]
fn a_linear_chain_of_the_same_node_count_still_compiles_through_the_reader() {
    let n = COMPOSED_MAX_OPS;
    let (env, table) = rust_call_environment(&linear_source("line", n));
    let plan = trust_clean_origin::plan_clean_origin_body_with_rust_callees(&env, "line", &table)
        .unwrap_or_else(|refusal| {
            panic!("a linear chain of {n} nodes must plan: {}", refusal.note())
        });
    let CleanOriginShape::RustCallChain { nodes } = plan.shape() else {
        panic!("planned {:?}", plan.shape());
    };
    assert_eq!(nodes.len(), n);
    let started = Instant::now();
    trust_clean_origin::admit_lowering(&env, &plan, &emitted_chain("line", &plan, &table))
        .unwrap_or_else(|refusal| panic!("the linear chain must admit: {}", refusal.note()));
    assert!(started.elapsed() < GENEROUS);
}

/// The memo, pinned STRUCTURALLY: the reflector renders a shared node ONCE and
/// every later read is a shallow clone, so the two reads of node `k` in
/// `add2 a_k a_k` share their children by POINTER. Without the memo each read
/// is a fresh rendering and the `Arc`s differ.
///
/// Pinned by pointer rather than by time on purpose. Measured 2026-09-16
/// (`measure_doubling_chain_cost`, reflect-only, memo in place): 2^20 in
/// 451 ms, 2^22 in 1.8 s, 2^24 in 7.3 s — LINEAR IN THE UNFOLDED WEIGHT even
/// with the memo, because `reflect_rust_call_chain` full-kernel-checks the
/// minted definition and the kernel's type inference walks the DAG as a tree.
/// So a timing assertion here could not tell memo from no memo: the memo
/// removes the `2^n` allocations (the out-of-memory), not the `2^n` time. That
/// is exactly why the plan-time bound is the one that matters, and this pin
/// only holds the memo in place as defence in depth.
#[test]
fn the_reflector_renders_a_shared_node_once() {
    use std::sync::Arc;

    use clean_kernel::ExprKind;

    let n = 12;
    let (env, table) = rust_call_environment("def probe (x : UInt64) : UInt64 := x");
    let extracted = emitted_chain_of_nodes("boom", &doubling_nodes(n), &table);
    let allowed: BTreeSet<String> = table.iter().map(|row| row.def_path.clone()).collect();
    let names: BTreeMap<String, String> =
        table.iter().map(|row| (row.def_path.clone(), row.clean_name.clone())).collect();
    let body = recognize_rust_call_chain(&extracted, &allowed).expect("the chain recognizes");
    let value =
        trust_clean_origin::reflect_rust_call_chain(&env, "boom", &body, &extracted, &names)
            .unwrap_or_else(|reason| panic!("the hand-built chain must reflect: {reason}"));

    // `fun (x : UInt64) => add2 R R` where `R` renders node n-2.
    let ExprKind::Lam(_, _, root) = value.kind() else { panic!("not a lambda: {value:?}") };
    let reads = root.get_app_args();
    assert_eq!(reads.len(), 2, "the root reads node {} twice", n - 2);
    let (ExprKind::App(f0, a0), ExprKind::App(f1, a1)) = (reads[0].kind(), reads[1].kind()) else {
        panic!("the shared node is an application");
    };
    assert!(
        Arc::ptr_eq(f0, f1) && Arc::ptr_eq(a0, a1),
        "the two reads of the shared node must be shallow clones of ONE rendering; a fresh \
         rendering per read is the tree unfolding the memo exists to prevent"
    );
    // And it is still the SAME term: a different `Expr` with the same structure
    // is not what the memo produces, but what it produces is structurally equal
    // to it, so the gate decides the same proposition either way.
    assert_eq!(reads[0], reads[1]);
}

/// The memo's time bound is NOT the point (see above), but a hand-built chain
/// past the plan cap must still reflect without running out of memory, which
/// is the failure mode the reviewer reproduced at 32 nodes. 2^20 applications
/// in ~0.5 s debug is well inside the generous limit; the tree unfolding was
/// 2^20 allocations on top of it.
#[test]
fn a_hand_built_chain_past_the_plan_cap_still_reflects_in_bounded_time() {
    let (elapsed, outcome) = recognize_and_reflect_doubling(20);
    outcome.unwrap_or_else(|reason| panic!("the hand-built chain must reflect: {reason}"));
    assert!(elapsed < GENEROUS, "reflecting 20 shared nodes took {elapsed:?}");
}

/// The measurement behind the cap. Run by hand:
/// `targo --unverified test -p trust-clean-origin --test let_chain_unfolded_weight -- --ignored --nocapture measure_doubling_chain_cost`
#[test]
#[ignore = "measurement, prints timings; the cap is chosen from its output"]
fn measure_doubling_chain_cost() {
    let show = |outcome: &Result<(), String>| match outcome {
        Ok(()) => "admitted".to_owned(),
        Err(note) => format!("refused: {note}"),
    };
    for n in [2usize, 4, 6, 8, 10, 12, 14, 16, 18, 20] {
        let (elapsed, outcome) = plan_and_admit(&doubling_source("boom", n), "boom");
        eprintln!(
            "plan+admit doubling n={n:2} weight=2^{n}-1={:>12} elapsed={elapsed:?} {}",
            (1u128 << n) - 1,
            show(&outcome)
        );
    }
    for n in [8usize, 16, 32] {
        let (elapsed, outcome) = plan_and_admit(&linear_source("line", n), "line");
        eprintln!(
            "plan+admit linear   n={n:2} weight={n:>12} elapsed={elapsed:?} {}",
            show(&outcome)
        );
    }
    for n in [8usize, 16, 20, 22, 24] {
        let (elapsed, outcome) = recognize_and_reflect_doubling(n);
        eprintln!(
            "reflect-only doubling n={n:2} weight=2^{n}-1={:>12} elapsed={elapsed:?} {}",
            (1u128 << n) - 1,
            show(&outcome)
        );
    }
}
