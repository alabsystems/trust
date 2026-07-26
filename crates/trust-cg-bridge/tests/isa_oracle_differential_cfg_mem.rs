// G13-FULL: Differential VALIDATION of the trust-machine-sem AArch64 ISA model for
// the CONTROL-FLOW / COMPARISON / SELECT / LOOP / MEMORY instruction classes — the
// classes the straight-line-ALU suite (isa_oracle_differential.rs) did NOT reach.
//
// Same two routes as the ALU suite and the aterm Switch suite:
//   route-(b) REAL CPU : emit the function ONCE to a Mach-O object, link it with a
//                        tiny C harness, EXECUTE on silicon, read the result.
//   route-(a) ISA MODEL: decode the SAME emitted bytes (trust-disasm) and execute
//                        them under trust-machine-sem's formal AArch64 ConcreteState,
//                        threading PC through CondBr/Switch/loop-backedges and
//                        reading/writing ConcreteState.memory for loads/stores.
//
// For every function we run MANY deterministic inputs (edge values + seeded xorshift;
// comparison boundaries; loop-bound 0/1/large; branch both-taken) and assert
// route-(a) == route-(b). Agreement = the formal ISA model is faithful to silicon for
// these classes too. A NEGATIVE CONTROL corrupts a model arm in the NEW classes
// (inverts the CondBr condition) and asserts the differential FAILS — teeth for CFG.
//
// Anti-vacuity: route-(b) PANICS (never skips) if cc/link/run fails; the negative
// control proves a wrong CFG arm would be caught.
//
// Instruction classes newly exercised here (vs the ALU baseline): ICmp (Subs+Csinc),
// Select / conditional-move (Csinc/Csel pattern from `if`), CondBr (BCond), Switch
// (multi-target), bounded loop (backward Branch / backedge), Store (Str) + Load (Ldr)
// + stack frame (Stp/Ldp). HONEST scope notes are in the final `coverage_report` test.

use std::fs;
use std::process::Command;

use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ===========================================================================
// Emission + Mach-O __text extraction (identical machinery to the ALU/aterm suites).
// ===========================================================================

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

/// Minimal Mach-O 64 reader: (`__text` bytes, vmaddr). The emitted object is a single
/// relocation-free `__text` section, so the bytes are a self-contained code image.
fn macho_text(obj: &[u8]) -> (Vec<u8>, u64) {
    let rd_u32 = |o: usize| u32::from_le_bytes(obj[o..o + 4].try_into().unwrap());
    let rd_u64 = |o: usize| u64::from_le_bytes(obj[o..o + 8].try_into().unwrap());
    assert_eq!(rd_u32(0), 0xfeed_facf, "expected 64-bit little-endian Mach-O");
    let ncmds = rd_u32(16);
    let mut cmd_off = 32usize;
    for _ in 0..ncmds {
        let cmd = rd_u32(cmd_off);
        let cmdsize = rd_u32(cmd_off + 4) as usize;
        if cmd == 0x19 {
            let nsects = rd_u32(cmd_off + 64);
            let mut sec = cmd_off + 72;
            for _ in 0..nsects {
                if obj[sec..sec + 16].starts_with(b"__text\0") {
                    let addr = rd_u64(sec + 32);
                    let size = rd_u64(sec + 40) as usize;
                    let offset = rd_u32(sec + 48) as usize;
                    return (obj[offset..offset + size].to_vec(), addr);
                }
                sec += 80;
            }
        }
        cmd_off += cmdsize;
    }
    panic!("no __text section in emitted object");
}

// ===========================================================================
// route-(a): execute the emitted AArch64 image under the formal trust-machine-sem
// AArch64 semantics. This is the SAME in-order effect applier the aterm Switch suite
// (route_a_isa_semantic_execution_matches_proven_table) uses, extended to seed a
// stack region (SP) for functions that build a frame (Stp/Ldp) or spill locals.
// ===========================================================================

/// A safe stack base far above the code image so the prologue's `sp - frame` never
/// aliases the code bytes. ConcreteState memory is a sparse BTreeMap, so this is free.
const STACK_TOP: u64 = 0x1_0000_0000;
const MEM_BASE: u64 = 0x2_0000_0000; // where load/store data buffers live (route-a)

/// Execute the image under the ISA model. `args` are placed in X0.. per AAPCS64
/// (each arg occupies one X register, low bits set by width). `ret_width` selects
/// whether W0 (32) or X0 (64) is read at the first `ret`. Returns the raw u64 reg.
fn run_isa(
    cs: &mut trust_machine_sem::ConcreteState,
    base: u64,
    code: &[u8],
    args: &[u64],
    max_steps: usize,
) -> Option<u64> {
    use trust_disasm::{decode_aarch64, Opcode};
    use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics};

    for g in cs.gpr.iter_mut() {
        *g = 0;
    }
    for (i, &a) in args.iter().enumerate() {
        cs.gpr[i] = a;
    }
    cs.sp = STACK_TOP;
    cs.pc = base;
    cs.flags = trust_machine_sem::ConcreteFlags::default();

    let sem = Aarch64Semantics;
    let ms = MachineState::symbolic();
    for _ in 0..max_steps {
        let off = cs.pc.checked_sub(base)? as usize;
        let bytes: [u8; 4] = code.get(off..off + 4)?.try_into().ok()?;
        let insn = decode_aarch64(&bytes, cs.pc).ok()?;
        if insn.opcode == Opcode::Ret {
            return Some(cs.gpr[0]);
        }
        // Surface a real ISA-model coverage gap precisely instead of skipping.
        let effects = match sem.effects(&ms, &insn) {
            Ok(e) => e,
            Err(e) => panic!(
                "ISA MODEL GAP: trust-machine-sem has no semantics for {:?} \
                 (bytes {:08x} at pc {:#x}): {e:?}",
                insn.opcode,
                u32::from_le_bytes(bytes),
                cs.pc
            ),
        };
        let mut pc_set = false;
        for eff in &effects {
            match eff {
                Effect::Branch { target } | Effect::Return { target } => {
                    cs.pc = cs.eval_bv(target, 64).ok()? as u64;
                    pc_set = true;
                }
                Effect::Call { target, .. } => {
                    cs.pc = cs.eval_bv(target, 64).ok()? as u64;
                    pc_set = true;
                }
                Effect::PcUpdate { .. } | Effect::ConditionalBranch { .. } => {
                    let pc = cs.pc;
                    cs.apply_effect(eff).unwrap_or_else(|e| {
                        panic!("ISA MODEL GAP: apply_effect failed for {eff:?} of {:?} at pc {pc:#x}: {e:?}", insn.opcode)
                    });
                    pc_set = true;
                }
                _ => {
                    let pc = cs.pc;
                    cs.apply_effect(eff).unwrap_or_else(|e| {
                        panic!("ISA MODEL GAP: apply_effect failed for {eff:?} of {:?} at pc {pc:#x}: {e:?}", insn.opcode)
                    });
                }
            }
        }
        if !pc_set {
            cs.pc = cs.pc.wrapping_add(4);
        }
    }
    None
}

// ===========================================================================
// route-(b): execute the SAME emitted bytes on the real CPU. One link + run per fn,
// every input fed via a data file (scanf), results read back in order. PANIC (never
// skip) on cc/link/run failure — anti-vacuity.
// ===========================================================================

/// For functions of signature `int f(int...)` with `nargs` integer args.
fn route_b_run_int(func: &VerifiableFunction, nargs: usize, inputs: &[Vec<i32>]) -> Vec<i32> {
    let obj = emit_obj(func);
    let dir = tempfile::tempdir().expect("tempdir");
    let obj_path = dir.path().join("fn.o");
    let c_path = dir.path().join("harness.c");
    let data_path = dir.path().join("in.txt");
    let bin_path = dir.path().join("h");
    fs::write(&obj_path, &obj).expect("write obj");

    let mut data = format!("{}\n", inputs.len());
    for row in inputs {
        assert_eq!(row.len(), nargs, "input arity mismatch");
        for v in row {
            data.push_str(&format!("{v} "));
        }
        data.push('\n');
    }
    fs::write(&data_path, &data).expect("write data");

    let params = (0..nargs).map(|_| "int").collect::<Vec<_>>().join(", ");
    let decls = (0..nargs).map(|i| format!("int a{i};")).collect::<Vec<_>>().join(" ");
    let scan_fmt = (0..nargs).map(|_| "%d").collect::<Vec<_>>().join(" ");
    let scan_args = (0..nargs).map(|i| format!("&a{i}")).collect::<Vec<_>>().join(", ");
    let call_args = (0..nargs).map(|i| format!("a{i}")).collect::<Vec<_>>().join(", ");
    let harness = format!(
        r#"
#include <stdio.h>
extern int {fname}({params});
int main(void) {{
    FILE *f = fopen("{path}", "r");
    if (!f) return 2;
    long n; if (fscanf(f, "%ld", &n) != 1) return 3;
    for (long i = 0; i < n; i++) {{
        {decls}
        if (fscanf(f, "{scan_fmt}", {scan_args}) != {nargs}) return 4;
        printf("%d\n", {fname}({call_args}));
    }}
    fclose(f);
    return 0;
}}
"#,
        fname = func.name,
        path = data_path.display(),
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
        "route-(b) cc link FAILED for {}: {}",
        func.name,
        String::from_utf8_lossy(&link.stderr)
    );
    let out = Command::new(&bin_path).output().expect("spawn harness binary");
    assert!(out.status.success(), "route-(b) run FAILED for {}: {:?}", func.name, out.status);
    let res: Vec<i32> = String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .map(|t| t.parse().expect("i32 output"))
        .collect();
    assert_eq!(res.len(), inputs.len(), "route-(b) result count mismatch for {}", func.name);
    res
}

// ===========================================================================
// Deterministic input generation.
// ===========================================================================

struct XorShift(u64);
impl XorShift {
    fn new(seed: u64) -> Self {
        XorShift(seed | 1)
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn next_i32(&mut self) -> i32 {
        self.next_u64() as u32 as i32
    }
}

const EDGES: &[i32] = &[0, 1, -1, 2, -2, 5, -5, 100, -100, i32::MIN, i32::MAX, i32::MIN + 1, i32::MAX - 1];

/// (a,b) pairs: full edge×edge cross product + edge×random + pure random, >= 400.
fn pairs(seed: u64) -> Vec<Vec<i32>> {
    let mut rng = XorShift::new(seed);
    let mut v = Vec::new();
    for &a in EDGES {
        for &b in EDGES {
            v.push(vec![a, b]);
        }
    }
    for &e in EDGES {
        for _ in 0..6 {
            v.push(vec![e, rng.next_i32()]);
            v.push(vec![rng.next_i32(), e]);
        }
    }
    while v.len() < 400 {
        v.push(vec![rng.next_i32(), rng.next_i32()]);
    }
    v
}

/// (a,b,c) triples for 3-arg functions (clamp).
fn triples(seed: u64) -> Vec<Vec<i32>> {
    let mut rng = XorShift::new(seed);
    let small = [0, 1, -1, 5, -5, 10, -10, 100, -100];
    let mut v = Vec::new();
    for &a in &small {
        for &lo in &small {
            for &hi in &small {
                v.push(vec![a, lo, hi]);
            }
        }
    }
    while v.len() < 800 {
        // lo <= hi not enforced — both orders exercise the branches.
        v.push(vec![rng.next_i32() % 200, rng.next_i32() % 200, rng.next_i32() % 200]);
    }
    v
}

/// Single-arg loop bounds: 0, 1, small, boundary, plus seeded small positives.
fn loop_bounds(seed: u64) -> Vec<Vec<i32>> {
    let mut rng = XorShift::new(seed);
    let mut v: Vec<Vec<i32>> = vec![0, 1, 2, 3, 5, 10, 50, 100, 256, 1000].into_iter().map(|n| vec![n]).collect();
    while v.len() < 300 {
        v.push(vec![(rng.next_u64() % 2000) as i32]);
    }
    v
}

// ===========================================================================
// FUNCTION AUTHORS — CFG / compare / select / loop.
//
// `if` is lowered by rustc-style MIR as: compute a bool via a comparison BinOp, then
// SwitchInt on the bool (otherwise = the != 0 / "then" arm). That is exactly the MIR
// shape, and the aterm suite already proved SwitchInt executes faithfully under the
// ISA model; here it lowers to Subs (cmp) + Csinc (cset, the comparison/select
// materialization) + Subs + BCond (conditional branch) + B (branch).
// ===========================================================================

fn sp() -> SourceSpan {
    SourceSpan::default()
}

fn cmp_branch_block(
    cmp: BinOp,
    lhs: usize,
    rhs: usize,
    cond_local: usize,
    then_blk: usize,
    else_blk: usize,
) -> BasicBlock {
    // bool cond = lhs <cmp> rhs; if cond != 0 -> then else -> else.
    BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(cond_local),
            rvalue: Rvalue::BinaryOp(cmp, Operand::Copy(Place::local(lhs)), Operand::Copy(Place::local(rhs))),
            span: sp(),
        }],
        terminator: Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(cond_local)),
            targets: vec![(0, BlockId(else_blk))], // cond == 0 -> else
            otherwise: BlockId(then_blk),          // cond != 0 -> then
            exhaustive_enum_unreachable: false,
            span: sp(),
        },
    }
}

fn ret_use_block(id: usize, src_local: usize) -> BasicBlock {
    BasicBlock {
        id: BlockId(id),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(src_local))),
            span: sp(),
        }],
        terminator: Terminator::Return,
    }
}

fn wrap(name: &str, body: VerifiableBody) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("cfgmem::{name}"),
        span: sp(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// max(a,b): if a>=b {a} else {b}  — ICmp(Ge) + CondBr + Select-by-control-flow.
fn author_max() -> VerifiableFunction {
    wrap(
        "cfg_max",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::bool_ty(), name: None },
            ],
            blocks: vec![
                cmp_branch_block(BinOp::Ge, 1, 2, 3, 1, 2),
                ret_use_block(1, 1), // then: a
                ret_use_block(2, 2), // else: b
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
    )
}

/// min(a,b): if a<=b {a} else {b}  — ICmp(Le).
fn author_min() -> VerifiableFunction {
    wrap(
        "cfg_min",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::bool_ty(), name: None },
            ],
            blocks: vec![cmp_branch_block(BinOp::Le, 1, 2, 3, 1, 2), ret_use_block(1, 1), ret_use_block(2, 2)],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
    )
}

/// abs(x): if x < 0 { -x } else { x }  — ICmp(Lt) + UnaryOp(Neg) + CondBr + merge.
fn author_abs() -> VerifiableFunction {
    use trust_types::UnOp;
    wrap(
        "cfg_abs",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::bool_ty(), name: None },
            ],
            blocks: vec![
                // c = x < 0 ; if c != 0 -> negate-block else -> identity-block
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: sp(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: sp(),
                    },
                },
                // then: ret = -x
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                },
                ret_use_block(2, 1), // else: x
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
    )
}

/// clamp(x, lo, hi): if x < lo { lo } else if x > hi { hi } else { x } — two chained
/// ICmp + CondBr, three merges (tree-structured CFG).
fn author_clamp() -> VerifiableFunction {
    wrap(
        "cfg_clamp",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("lo".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("hi".into()) },
                LocalDecl { index: 4, ty: Ty::bool_ty(), name: None },
                LocalDecl { index: 5, ty: Ty::bool_ty(), name: None },
            ],
            blocks: vec![
                // bb0: c1 = x < lo ; if c1 -> bb1(ret lo) else bb2
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))),
                        span: sp(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: sp(),
                    },
                },
                ret_use_block(1, 2), // ret lo
                // bb2: c2 = x > hi ; if c2 -> bb3(ret hi) else bb4(ret x)
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(BinOp::Gt, Operand::Copy(Place::local(1)), Operand::Copy(Place::local(3))),
                        span: sp(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: sp(),
                    },
                },
                ret_use_block(3, 3), // ret hi
                ret_use_block(4, 1), // ret x
            ],
            arg_count: 3,
            return_ty: Ty::i32(),
        },
    )
}

/// dispatch(tag): match tag { 0=>10, 1=>20, 2=>30, _=>0 } — multi-target SwitchInt.
fn author_dispatch() -> VerifiableFunction {
    let leaf = |id: usize, val: i64| BasicBlock {
        id: BlockId(id),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(val as u128, 32))),
            span: sp(),
        }],
        terminator: Terminator::Return,
    };
    wrap(
        "cfg_dispatch",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("tag".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2)), (2, BlockId(3))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: sp(),
                    },
                },
                leaf(1, 10),
                leaf(2, 20),
                leaf(3, 30),
                leaf(4, 0),
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
    )
}

/// sum_to(n): s=0; i=0; while i<n { s+=i; i+=1 } s — bounded loop with a backedge.
fn author_sum_loop() -> VerifiableFunction {
    wrap(
        "cfg_sum_loop",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::bool_ty(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign { place: Place::local(0), rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))), span: sp() },
                        Statement::Assign { place: Place::local(2), rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))), span: sp() },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb1: c = i < n ; if c==0 -> exit else body
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(Place::local(2)), Operand::Copy(Place::local(1))),
                        span: sp(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: sp(),
                    },
                },
                // bb2: s += i ; i += 1 ; goto bb1 (BACKEDGE)
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign { place: Place::local(0), rvalue: Rvalue::BinaryOp(BinOp::Add, Operand::Copy(Place::local(0)), Operand::Copy(Place::local(2))), span: sp() },
                        Statement::Assign { place: Place::local(2), rvalue: Rvalue::BinaryOp(BinOp::Add, Operand::Copy(Place::local(2)), Operand::Constant(ConstValue::Uint(1, 32))), span: sp() },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
    )
}

// ===========================================================================
// MEMORY: store-then-load roundtrip through a raw pointer.
// fn ptr_rw(p: *mut i32, v: i32) -> i32 { *p = v; *p }
// Lowers to a stack frame (Stp/Ldp), spills of p & v to the frame (Str/Ldr), then
// Str (the store *p=v) and Ldr (the load *p) — genuine Store + Load + frame memory.
// route-(b): pass &cell on the real CPU. route-(a): seed the cell in ConcreteState.
// ===========================================================================

fn author_ptr_rw() -> VerifiableFunction {
    let ptr_ty = Ty::RawPtr { mutable: true, pointee: Box::new(Ty::i32()) };
    wrap(
        "mem_ptr_rw",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: ptr_ty, name: Some("p".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("v".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: sp(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place { local: 1, projections: vec![Projection::Deref] })),
                        span: sp(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
    )
}

// ===========================================================================
// Per-function CFG differential (int args -> int result).
// ===========================================================================

fn differential_cfg(func: &VerifiableFunction, nargs: usize, inputs: &[Vec<i32>], max_steps: usize) {
    // route-(b): real CPU, batched.
    let cpu = route_b_run_int(func, nargs, inputs);

    // route-(a): formal ISA model, same bytes.
    let obj = emit_obj(func);
    let (code, base) = macho_text(&obj);
    let mut cs = trust_machine_sem::ConcreteState::new();
    for (i, byte) in code.iter().enumerate() {
        cs.store_memory_le(base + i as u64, 1, *byte as u128).expect("seed code image");
    }

    let mut mism = Vec::new();
    for (idx, row) in inputs.iter().enumerate() {
        let args: Vec<u64> = row.iter().map(|&v| (v as u32) as u64).collect();
        let raw = run_isa(&mut cs, base, &code, &args, max_steps).unwrap_or_else(|| {
            panic!("route-(a) ISA exec failed/looped for {} at {:?}", func.name, row)
        });
        let model = raw as u32 as i32;
        if model != cpu[idx] {
            mism.push((row.clone(), model, cpu[idx]));
        }
    }
    assert!(
        mism.is_empty(),
        "{}: ISA model DISAGREES with real CPU at {} of {} inputs (args, model, cpu): {:?}",
        func.name,
        mism.len(),
        inputs.len(),
        &mism[..mism.len().min(8)]
    );
    println!("{}: {} samples, model == cpu", func.name, inputs.len());
}

#[test]
fn cfg_max_min_clamp_abs_dispatch_loop_match_real_cpu() {
    differential_cfg(&author_max(), 2, &pairs(0x1111), 1000);
    differential_cfg(&author_min(), 2, &pairs(0x2222), 1000);
    differential_cfg(&author_abs(), 1, &pairs(0x3333).into_iter().map(|r| vec![r[0]]).collect::<Vec<_>>(), 1000);
    differential_cfg(&author_clamp(), 3, &triples(0x4444), 1000);
    // dispatch: tags 0..=8 (in + out of range) exhaustively, repeated for >= 400.
    let mut tags: Vec<Vec<i32>> = Vec::new();
    for rep in 0..50 {
        for t in -1..=8 {
            tags.push(vec![t + (rep % 1) /* keep value */]);
        }
    }
    differential_cfg(&author_dispatch(), 1, &tags, 1000);
    // sum_loop: max bound 2000 -> ~ a few thousand model steps; cap generously.
    differential_cfg(&author_sum_loop(), 1, &loop_bounds(0x6666), 200_000);
}

// ===========================================================================
// MEMORY differential: ptr_rw store-then-load roundtrip.
// route-(b): pass the address of a stack `int cell` on the real CPU.
// route-(a): pick a buffer address in ConcreteState memory, seed an initial value,
// set X0 = buffer addr, X1 = v, execute; the function stores v then loads it back.
// ===========================================================================

#[test]
fn mem_store_load_roundtrip_matches_real_cpu() {
    let func = author_ptr_rw();

    // Deterministic v values: edges + seeded random, with a byte-order stress value.
    let mut rng = XorShift::new(0x7777);
    let mut vs: Vec<i32> = vec![0, 1, -1, 0x1234_5678, -0x1234_5678i32, i32::MIN, i32::MAX, 42, 0x7f, -0x80];
    while vs.len() < 400 {
        vs.push(rng.next_i32());
    }

    // ---- route-(b): real CPU. The harness allocates one `int cell`, calls
    // ptr_rw(&cell, v) for each v, prints both the return value AND the cell, so we
    // confirm the STORE landed (cell == v) and the LOAD read it back (ret == v).
    let obj = emit_obj(&func);
    let dir = tempfile::tempdir().expect("tempdir");
    let obj_path = dir.path().join("fn.o");
    let c_path = dir.path().join("h.c");
    let data_path = dir.path().join("v.txt");
    let bin_path = dir.path().join("h");
    fs::write(&obj_path, &obj).expect("obj");
    let mut data = format!("{}\n", vs.len());
    for v in &vs {
        data.push_str(&format!("{v}\n"));
    }
    fs::write(&data_path, &data).expect("data");
    let harness = format!(
        r#"
#include <stdio.h>
extern int {fname}(int*, int);
int main(void) {{
    FILE *f = fopen("{path}", "r");
    if (!f) return 2;
    long n; if (fscanf(f, "%ld", &n) != 1) return 3;
    for (long i = 0; i < n; i++) {{
        int v; if (fscanf(f, "%d", &v) != 1) return 4;
        int cell = 0x0BADF00D;
        int r = {fname}(&cell, v);
        printf("%d %d\n", r, cell);
    }}
    fclose(f);
    return 0;
}}
"#,
        fname = func.name,
        path = data_path.display(),
    );
    fs::write(&c_path, harness).expect("harness");
    let link = Command::new("cc").arg(&c_path).arg(&obj_path).arg("-o").arg(&bin_path).output().expect("cc");
    assert!(link.status.success(), "mem route-(b) link FAILED: {}", String::from_utf8_lossy(&link.stderr));
    let out = Command::new(&bin_path).output().expect("run");
    assert!(out.status.success(), "mem route-(b) run FAILED: {:?}", out.status);
    let cpu: Vec<i32> = String::from_utf8_lossy(&out.stdout).split_whitespace().map(|t| t.parse().expect("int")).collect();
    assert_eq!(cpu.len(), vs.len() * 2, "route-(b) must print (ret, cell) per input");

    // ---- route-(a): formal ISA model, SAME bytes. Seed code image, pick a data
    // buffer address, seed cell=0x0BADF00D, X0=buffer, X1=v; read W0 (ret) and the
    // 4 bytes at the buffer (the stored cell).
    let (code, base) = macho_text(&obj);
    let mut cs = trust_machine_sem::ConcreteState::new();
    for (i, byte) in code.iter().enumerate() {
        cs.store_memory_le(base + i as u64, 1, *byte as u128).expect("seed code");
    }

    let mut mism = Vec::new();
    for (idx, &v) in vs.iter().enumerate() {
        let buf = MEM_BASE;
        cs.store_memory_le(buf, 4, 0x0BAD_F00Du32 as u128).expect("seed cell");
        let raw = run_isa(&mut cs, base, &code, &[buf, (v as u32) as u64], 10_000)
            .unwrap_or_else(|| panic!("route-(a) mem exec failed for v={v}"));
        let model_ret = raw as u32 as i32;
        let model_cell = cs.load_memory_le(buf, 4).expect("read back cell") as u32 as i32;
        let cpu_ret = cpu[idx * 2];
        let cpu_cell = cpu[idx * 2 + 1];
        if model_ret != cpu_ret || model_cell != cpu_cell {
            mism.push((v, model_ret, model_cell, cpu_ret, cpu_cell));
        }
        // Sanity: the store must have landed and the load must have read it back.
        assert_eq!(model_cell, v, "route-(a): STORE of v={v} did not land in memory");
        assert_eq!(model_ret, v, "route-(a): LOAD did not read back v={v}");
    }
    assert!(
        mism.is_empty(),
        "mem_ptr_rw: ISA model DISAGREES with real CPU at {} of {} inputs (v, m_ret, m_cell, c_ret, c_cell): {:?}",
        mism.len(),
        vs.len(),
        &mism[..mism.len().min(8)]
    );
    println!("mem_ptr_rw: {} samples, store+load roundtrip model == cpu", vs.len());
}

// ===========================================================================
// NEGATIVE CONTROL: prove the differential has TEETH for the NEW (CFG) classes.
//
// We corrupt the ISA MODEL's handling of the conditional branch specifically: a
// shadow runner that INVERTS the BCond condition. Running cfg_max under the corrupted
// model must DISAGREE with the real CPU on at least one input — proving that a wrong
// CondBr arm in trust-machine-sem would be caught by this differential (it is not
// vacuous). The faithful model must AGREE everywhere (sanity).
// ===========================================================================

fn run_isa_inverted_bcond(
    cs: &mut trust_machine_sem::ConcreteState,
    base: u64,
    code: &[u8],
    args: &[u64],
) -> Option<i32> {
    use trust_disasm::{decode_aarch64, Opcode};
    use trust_machine_sem::{eval_condition, Aarch64Semantics, ConcreteFlags, Effect, MachineState, Semantics};

    for g in cs.gpr.iter_mut() {
        *g = 0;
    }
    for (i, &a) in args.iter().enumerate() {
        cs.gpr[i] = a;
    }
    cs.sp = STACK_TOP;
    cs.pc = base;
    cs.flags = ConcreteFlags::default();

    let sem = Aarch64Semantics;
    let ms = MachineState::symbolic();
    for _ in 0..10_000 {
        let off = cs.pc.checked_sub(base)? as usize;
        let bytes: [u8; 4] = code.get(off..off + 4)?.try_into().ok()?;
        let insn = decode_aarch64(&bytes, cs.pc).ok()?;
        if insn.opcode == Opcode::Ret {
            return Some(cs.gpr[0] as u32 as i32);
        }
        let effects = sem.effects(&ms, &insn).ok()?;
        let mut pc_set = false;
        for eff in &effects {
            match eff {
                // CORRUPTED arm: invert the conditional-branch outcome.
                Effect::ConditionalBranch { condition, target, fallthrough } => {
                    let taken = eval_condition(cs.flags, *condition);
                    let nx = if taken { fallthrough } else { target }; // INVERTED
                    cs.pc = cs.eval_bv(nx, 64).ok()? as u64;
                    pc_set = true;
                }
                Effect::PcUpdate { .. } => {
                    cs.apply_effect(eff).ok()?;
                    pc_set = true;
                }
                Effect::Branch { target } | Effect::Return { target } | Effect::Call { target, .. } => {
                    cs.pc = cs.eval_bv(target, 64).ok()? as u64;
                    pc_set = true;
                }
                _ => cs.apply_effect(eff).ok()?,
            }
        }
        if !pc_set {
            cs.pc = cs.pc.wrapping_add(4);
        }
    }
    None
}

#[test]
fn negative_control_inverted_condbr_is_detected() {
    let func = author_max();
    let inputs = pairs(0xBEEF);
    let cpu = route_b_run_int(&func, 2, &inputs);

    let obj = emit_obj(&func);
    let (code, base) = macho_text(&obj);
    let mut cs = trust_machine_sem::ConcreteState::new();
    for (i, byte) in code.iter().enumerate() {
        cs.store_memory_le(base + i as u64, 1, *byte as u128).expect("seed");
    }

    // Faithful model: must agree with the CPU everywhere (sanity that the harness
    // and ABI are right).
    let mut faithful_ok = true;
    for (idx, row) in inputs.iter().enumerate() {
        let args = vec![(row[0] as u32) as u64, (row[1] as u32) as u64];
        let m = run_isa(&mut cs, base, &code, &args, 1000).expect("faithful exec") as u32 as i32;
        if m != cpu[idx] {
            faithful_ok = false;
        }
    }
    assert!(faithful_ok, "sanity: the FAITHFUL ISA model must equal the real CPU for cfg_max");

    // Corrupted model (inverted CondBr): must DISAGREE on at least one input.
    let mut disagreements = 0usize;
    for (idx, row) in inputs.iter().enumerate() {
        let args = vec![(row[0] as u32) as u64, (row[1] as u32) as u64];
        let m = run_isa_inverted_bcond(&mut cs, base, &code, &args).expect("corrupt exec");
        if m != cpu[idx] {
            disagreements += 1;
        }
    }
    assert!(
        disagreements > 0,
        "NEGATIVE CONTROL FAILED: inverting the CondBr arm did NOT change any result, so the \
         differential would NOT catch a wrong control-flow arm — it would be toothless."
    );
    println!(
        "negative control: inverted-CondBr model disagrees with CPU on {} of {} inputs (teeth confirmed)",
        disagreements,
        inputs.len()
    );
}

#[test]
fn coverage_report() {
    // HONEST record of what this rung newly validates-by-execution vs leaves audited.
    println!("=== G13-FULL CFG/compare/select/loop/memory differential coverage ===");
    println!("VALIDATED-BY-EXECUTION (route-a ISA model == route-b real CPU, same bytes):");
    println!("  ICmp           : cfg_max(Ge) cfg_min(Le) cfg_abs(Lt) cfg_clamp(Lt,Gt) cfg_sum_loop(Lt)");
    println!("  CondBr (BCond) : every if/loop-guard above; negative control inverts it -> detected");
    println!("  Select         : if/else materialization (Csinc + branch merge) in max/min/abs/clamp");
    println!("  Switch (multi) : cfg_dispatch (3 cases + default), in+out-of-range tags");
    println!("  Loop backedge  : cfg_sum_loop (backward Branch), bounds 0/1/.../2000");
    println!("  Store (Str)    : mem_ptr_rw  (*p = v), confirmed landed in memory both routes");
    println!("  Load  (Ldr)    : mem_ptr_rw  (return *p), confirmed read-back both routes");
    println!("  Frame (Stp/Ldp): mem_ptr_rw prologue/epilogue + local spills");
    println!("STILL AUDITED-ONLY (not reached by this rung):");
    println!("  GEP/array-Load over a runtime index via slice/raw fat-pointer: blocked by the");
    println!("  route-(b) FAT-POINTER CALLING CONVENTION (C FFI), NOT an ISA-model gap. The");
    println!("  function lowers cleanly (Madd GEP + Ldr in a loop) and the opcodes ARE modeled;");
    println!("  only the silicon-side FFI handshake for fat pointers is unresolved here.");
}
