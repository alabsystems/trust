// Execution-level regressions for the bridge's block lowering order and for an
// entry block that is a loop target.
//
// `lower_body` lowers blocks in reverse postorder and hands a single-predecessor
// block its predecessor's exit values; a join reads block parameters that every
// predecessor fills. The function entry is an implicit extra predecessor of bb0
// that cannot fill block parameters, so an entry block re-entered by a backedge
// (rustc codegen calls it a "reentrant start block") read the function-entry
// values of its loop-carried locals on every iteration — with one backedge a
// silent wrong loop (it never advances), with two or more an ISel failure.
//
// Each fixture here is emitted ONCE through the host backend (bridge -> trust-cg ISel
// -> object), linked with a tiny C harness and run on the real CPU, and the printed
// results are compared with the Rust-computed expectation. Every tricky body has a
// twin with the same semantics in the shape that was always handled, so a harness
// failure cannot pass for a fix. See
// docs/issues/2026-09-29-trust-cg-mir-isel-value-not-defined-before-use-inlined-chain.md.
//
// Anti-vacuity: a lowering, emission, link or run failure PANICS (never skips).

use std::fs;
use std::process::Command;

use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn host_triple() -> &'static str {
    if cfg!(target_vendor = "apple") {
        if cfg!(target_arch = "aarch64") { "aarch64-apple-darwin" } else { "x86_64-apple-darwin" }
    } else {
        TrustCgTargetArch::host().triple()
    }
}

fn emit_obj(func: &VerifiableFunction) -> Vec<u8> {
    let backend = TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), host_triple());
    let lir = backend
        .lower_function(func)
        .unwrap_or_else(|e| panic!("lower_function failed for {}: {e:?}", func.name));
    backend
        .emit_object(&[lir])
        .unwrap_or_else(|e| panic!("emit_object failed for {}: {e:?}", func.name))
}

/// Run `int f(int)` on the real CPU for every input; PANIC on any cc/link/run failure.
/// A wrong loop lowering can spin forever, so the harness arms a 10 s `alarm` and a
/// hang fails as a run failure.
fn run_int_fn(func: &VerifiableFunction, inputs: &[i32]) -> Vec<i32> {
    let obj = emit_obj(func);
    let dir = tempfile::tempdir().expect("tempdir");
    let obj_path = dir.path().join("fn.o");
    let c_path = dir.path().join("harness.c");
    let bin_path = dir.path().join("h");
    fs::write(&obj_path, &obj).expect("write obj");
    let calls: String =
        inputs.iter().map(|v| format!("    printf(\"%d\\n\", {}({v}));\n", func.name)).collect();
    let harness = format!(
        "#include <stdio.h>\n#include <unistd.h>\nextern int {name}(int);\nint main(void) {{\n    alarm(10);\n{calls}    return 0;\n}}\n",
        name = func.name,
    );
    fs::write(&c_path, harness).expect("write harness");
    let link = Command::new("cc")
        .arg(&c_path)
        .arg(&obj_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .expect("spawn cc");
    assert!(
        link.status.success(),
        "cc link FAILED for {}: {}",
        func.name,
        String::from_utf8_lossy(&link.stderr)
    );
    let out = Command::new(&bin_path).output().expect("spawn harness binary");
    assert!(
        out.status.success(),
        "run FAILED for {}: {:?} (stdout so far: {:?})",
        func.name,
        out.status,
        String::from_utf8_lossy(&out.stdout)
    );
    let res: Vec<i32> = String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .map(|t| t.parse().expect("i32 output"))
        .collect();
    assert_eq!(res.len(), inputs.len(), "result count mismatch for {}", func.name);
    res
}

const INPUTS: &[i32] = &[0, 1, 2, 3, 7, 20, 41, 100, -5];

fn sp() -> SourceSpan {
    SourceSpan::default()
}

fn local(index: usize, ty: Ty) -> LocalDecl {
    LocalDecl { index, ty, name: None }
}

fn assign(dest: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(dest), rvalue, span: sp() }
}

fn copy(index: usize) -> Operand {
    Operand::Copy(Place::local(index))
}

fn int(v: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(v, 32))
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn goto(id: usize) -> Terminator {
    Terminator::Goto(BlockId(id))
}

fn switch(discr: usize, targets: Vec<(u128, usize)>, otherwise: usize) -> Terminator {
    Terminator::SwitchInt {
        discr: copy(discr),
        targets: targets.into_iter().map(|(v, bb)| (v, BlockId(bb))).collect(),
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: sp(),
    }
}

fn func(name: &str, locals: Vec<LocalDecl>, mut blocks: Vec<BasicBlock>) -> VerifiableFunction {
    blocks.sort_by_key(|bb| bb.id.0);
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: sp(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn expect(f: impl Fn(i32) -> i32) -> Vec<i32> {
    INPUTS.iter().map(|&x| f(x)).collect()
}

/// `do { x += 3 } while x < 100; x` with the ENTRY block as the loop header, entered
/// again from bb1. `pre_header` instead starts with a bb0 that only jumps to the loop.
fn entry_loop(pre_header: bool) -> VerifiableFunction {
    let h = usize::from(pre_header);
    let mut blocks = vec![
        block(
            h,
            vec![
                assign(1, Rvalue::BinaryOp(BinOp::Add, copy(1), int(3))),
                assign(2, Rvalue::BinaryOp(BinOp::Lt, copy(1), int(100))),
            ],
            switch(2, vec![(0, h + 2)], h + 1),
        ),
        block(h + 1, vec![], goto(h)),
        block(h + 2, vec![assign(0, Rvalue::Use(copy(1)))], Terminator::Return),
    ];
    if pre_header {
        blocks.push(block(0, vec![], goto(1)));
    }
    let name = if pre_header { "entry_loop_pre_header" } else { "entry_loop_reentrant" };
    func(name, vec![local(0, Ty::i32()), local(1, Ty::i32()), local(2, Ty::Bool)], blocks)
}

fn add3_until_100(mut x: i32) -> i32 {
    loop {
        x += 3;
        if x >= 100 {
            return x;
        }
    }
}

#[test]
fn loop_back_to_the_entry_block_executes_like_its_pre_header_twin() {
    let want = expect(add3_until_100);
    assert_eq!(run_int_fn(&entry_loop(true), INPUTS), want, "pre-header twin (control)");
    assert_eq!(run_int_fn(&entry_loop(false), INPUTS), want, "bb0 is the loop header");
}

/// `entry_loop`, but the result is read back through `&x` after the loop, so the argument
/// `x` lives in memory (its address is taken) and its slot must be stored ONCE, with the
/// function-entry value. Stored at the top of a looping bb0 instead, the back edge would
/// reset `x` to its entry value every iteration: the loop never advances (the alarm fires).
fn entry_loop_address_taken(pre_header: bool) -> VerifiableFunction {
    let h = usize::from(pre_header);
    let mut blocks = vec![
        block(
            h,
            vec![
                assign(1, Rvalue::BinaryOp(BinOp::Add, copy(1), int(3))),
                assign(2, Rvalue::BinaryOp(BinOp::Lt, copy(1), int(100))),
            ],
            switch(2, vec![(0, h + 2)], h + 1),
        ),
        block(h + 1, vec![], goto(h)),
        block(
            h + 2,
            vec![
                assign(3, Rvalue::Ref { mutable: false, place: Place::local(1) }),
                assign(
                    0,
                    Rvalue::Use(Operand::Copy(Place {
                        local: 3,
                        projections: vec![Projection::Deref],
                    })),
                ),
            ],
            Terminator::Return,
        ),
    ];
    if pre_header {
        blocks.push(block(0, vec![], goto(1)));
    }
    let name = if pre_header { "entry_loop_addr_pre_header" } else { "entry_loop_addr_reentrant" };
    let ref_i32 = Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) };
    func(
        name,
        vec![local(0, Ty::i32()), local(1, Ty::i32()), local(2, Ty::Bool), local(3, ref_i32)],
        blocks,
    )
}

#[test]
fn looping_entry_block_stores_a_memory_backed_argument_once() {
    let want = expect(add3_until_100);
    assert_eq!(
        run_int_fn(&entry_loop_address_taken(true), INPUTS),
        want,
        "pre-header twin (control)"
    );
    assert_eq!(
        run_int_fn(&entry_loop_address_taken(false), INPUTS),
        want,
        "bb0 is the loop header and the argument lives in memory"
    );
}

/// The same loop with TWO backedges into the entry block: even `x` steps by 3
/// through bb1, odd `x` by 3 through bb2 (so both latches run).
fn entry_loop_two_latches(pre_header: bool) -> VerifiableFunction {
    let h = usize::from(pre_header);
    let mut blocks = vec![
        block(
            h,
            vec![
                assign(1, Rvalue::BinaryOp(BinOp::Add, copy(1), int(3))),
                assign(2, Rvalue::BinaryOp(BinOp::Lt, copy(1), int(100))),
            ],
            switch(2, vec![(0, h + 3)], h + 4),
        ),
        block(h + 1, vec![], goto(h)),
        block(h + 2, vec![], goto(h)),
        block(h + 3, vec![assign(0, Rvalue::Use(copy(1)))], Terminator::Return),
        block(
            h + 4,
            vec![assign(3, Rvalue::BinaryOp(BinOp::BitAnd, copy(1), int(1)))],
            switch(3, vec![(0, h + 1)], h + 2),
        ),
    ];
    if pre_header {
        blocks.push(block(0, vec![], goto(1)));
    }
    let name = if pre_header { "entry_loop2_pre_header" } else { "entry_loop2_reentrant" };
    func(
        name,
        vec![local(0, Ty::i32()), local(1, Ty::i32()), local(2, Ty::Bool), local(3, Ty::i32())],
        blocks,
    )
}

#[test]
fn two_backedges_to_the_entry_block_execute_like_their_pre_header_twin() {
    let want = expect(add3_until_100);
    assert_eq!(
        run_int_fn(&entry_loop_two_latches(true), INPUTS),
        want,
        "pre-header twin (control)"
    );
    assert_eq!(
        run_int_fn(&entry_loop_two_latches(false), INPUTS),
        want,
        "bb0 is the header of a loop with two latches"
    );
}

/// `e2e_emit_metadata`'s `sum_loop` fixture: `while n != 0 { n -= 1 } n`, the loop
/// test in the entry block (bb0: switch n == 0 -> bb2 else bb1; bb1: n -= 1; goto bb0).
fn countdown(pre_header: bool) -> VerifiableFunction {
    let h = usize::from(pre_header);
    let mut blocks = vec![
        block(h, vec![], switch(1, vec![(0, h + 2)], h + 1)),
        block(
            h + 1,
            vec![assign(
                1,
                Rvalue::BinaryOp(BinOp::Sub, copy(1), Operand::Constant(ConstValue::Int(1))),
            )],
            goto(h),
        ),
        block(h + 2, vec![assign(0, Rvalue::Use(copy(1)))], Terminator::Return),
    ];
    if pre_header {
        blocks.push(block(0, vec![], goto(1)));
    }
    let name = if pre_header { "countdown_pre_header" } else { "countdown_reentrant" };
    func(name, vec![local(0, Ty::i32()), local(1, Ty::i32())], blocks)
}

#[test]
fn countdown_tested_in_the_entry_block_executes_like_its_pre_header_twin() {
    // Non-negative inputs only: a negative n counts down through i32::MIN.
    let inputs = &[0, 1, 2, 3, 7, 20, 41, 100];
    let want = vec![0; inputs.len()];
    assert_eq!(run_int_fn(&countdown(true), inputs), want, "pre-header twin (control)");
    assert_eq!(run_int_fn(&countdown(false), inputs), want, "bb0 tests the loop condition");
}

/// `s = 0; i = 0; while i < n { s += i; i += 1 } s`. `header_last` numbers the loop
/// header after the loop body and the exit (bb0 -> bb3 -> {bb1 body, bb2 exit});
/// otherwise the header is bb1, the body bb2 and the exit bb3.
fn sum_loop(header_last: bool) -> VerifiableFunction {
    let (header, body, exit) = if header_last { (3, 1, 2) } else { (1, 2, 3) };
    let blocks = vec![
        block(
            0,
            vec![assign(0, Rvalue::Use(int(0))), assign(2, Rvalue::Use(int(0)))],
            goto(header),
        ),
        block(
            header,
            vec![assign(3, Rvalue::BinaryOp(BinOp::Lt, copy(2), copy(1)))],
            switch(3, vec![(0, exit)], body),
        ),
        block(
            body,
            vec![
                assign(0, Rvalue::BinaryOp(BinOp::Add, copy(0), copy(2))),
                assign(2, Rvalue::BinaryOp(BinOp::Add, copy(2), int(1))),
            ],
            goto(header),
        ),
        block(exit, vec![], Terminator::Return),
    ];
    let name = if header_last { "sum_loop_header_last" } else { "sum_loop_in_flow" };
    func(
        name,
        vec![local(0, Ty::i32()), local(1, Ty::i32()), local(2, Ty::i32()), local(3, Ty::Bool)],
        blocks,
    )
}

#[test]
fn loop_with_header_numbered_after_its_body_executes_like_its_in_flow_twin() {
    let want = expect(|n| (0..n.max(0)).sum());
    assert_eq!(run_int_fn(&sum_loop(false), INPUTS), want, "in-flow twin (control)");
    assert_eq!(run_int_fn(&sum_loop(true), INPUTS), want, "header numbered after body and exit");
}
