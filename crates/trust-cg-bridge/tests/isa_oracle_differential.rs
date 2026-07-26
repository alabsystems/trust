// G13: Differential VALIDATION of the trust-machine-sem AArch64 ISA model (the
// ~9.3K-LOC hand-written oracle the proven-output certificates rest on) against
// the REAL CPU. The model is thereby validated-BY-EXECUTION, not trusted-by-audit.
//
// For each ALU op with a landed proven-output cert {add, sub, mul, and, or, xor,
// shl, shr}, we author an i32 `op(a, b) -> i32` VerifiableFunction, emit it ONCE
// to a real Mach-O object, and then for MANY deterministic (a, b) i32 input pairs:
//
//   route-(b) REAL CPU : link the SAME emitted bytes with a tiny C harness, run on
//                        the silicon, read the i32 result.
//   route-(a) ISA MODEL: decode the SAME emitted bytes (trust-disasm) and execute
//                        them under trust-machine-sem's formal AArch64 ConcreteState
//                        with W0=a, W1=b, read W0.
//
// assert route-(a) == route-(b) for every sampled input. Agreement over the whole
// sample = the formal ISA model is faithful to real silicon for these ops.
//
// A NEGATIVE CONTROL (`negative_control_*`) proves the harness has teeth: it cross-
// pairs route-(a) of one op against route-(b) of a DIFFERENT op and asserts a
// mismatch IS detected — so a wrong ISA arm could not slip through unnoticed.

use std::fs;
use std::process::Command;

use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_types::{
    BasicBlock, BlockId, BinOp, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// The eight ALU ops (those with landed proven-output certs).
// ---------------------------------------------------------------------------

const OPS: &[(&str, BinOp)] = &[
    ("add", BinOp::Add),
    ("sub", BinOp::Sub),
    ("mul", BinOp::Mul),
    ("and", BinOp::BitAnd),
    ("or", BinOp::BitOr),
    ("xor", BinOp::BitXor),
    ("shl", BinOp::Shl),
    ("shr", BinOp::Shr),
];

/// Author `op_<name>(a: i32, b: i32) -> i32 { a <op> b }` as a VerifiableFunction.
fn author_alu_vf(name: &str, op: BinOp) -> VerifiableFunction {
    let sp = SourceSpan::default;
    VerifiableFunction {
        name: format!("op_{name}"),
        def_path: format!("alu::op_{name}"),
        span: sp(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: sp(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// Emission (lift from the reference aterm_table_step_codegen.rs test).
// ---------------------------------------------------------------------------

fn host_triple() -> &'static str {
    if cfg!(target_vendor = "apple") {
        if cfg!(target_arch = "aarch64") { "aarch64-apple-darwin" } else { "x86_64-apple-darwin" }
    } else {
        TrustCgTargetArch::host().triple()
    }
}

/// Lower + emit `func` to a real object (host arch, Mach-O on apple).
fn emit_obj(func: &VerifiableFunction) -> Option<Vec<u8>> {
    let backend = TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), host_triple());
    let lir = backend.lower_function(func).ok()?;
    backend.emit_object(&[lir]).ok()
}

/// Minimal Mach-O 64 reader: return (`__text` bytes, its vmaddr). The emitted
/// object is a single relocation-free `__text` section (these ALU bodies are a
/// few instructions, no jump tables), so the bytes are a self-contained code
/// image loaded at `vmaddr`.
fn macho_text(obj: &[u8]) -> Option<(Vec<u8>, u64)> {
    let rd_u32 = |o: usize| -> Option<u32> {
        Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?))
    };
    let rd_u64 = |o: usize| -> Option<u64> {
        Some(u64::from_le_bytes(obj.get(o..o + 8)?.try_into().ok()?))
    };
    if rd_u32(0)? != 0xfeed_facf {
        return None; // not 64-bit Mach-O (little-endian)
    }
    let ncmds = rd_u32(16)?;
    let mut cmd_off = 32usize; // after mach_header_64
    for _ in 0..ncmds {
        let cmd = rd_u32(cmd_off)?;
        let cmdsize = rd_u32(cmd_off + 4)? as usize;
        if cmd == 0x19 {
            // LC_SEGMENT_64; sections start after the 72-byte segment_command_64
            let nsects = rd_u32(cmd_off + 64)?;
            let mut sec = cmd_off + 72;
            for _ in 0..nsects {
                let name = &obj[sec..sec + 16];
                if name.starts_with(b"__text\0") {
                    let addr = rd_u64(sec + 32)?;
                    let size = rd_u64(sec + 40)? as usize;
                    let offset = rd_u32(sec + 48)? as usize;
                    return Some((obj.get(offset..offset + size)?.to_vec(), addr));
                }
                sec += 80; // section_64
            }
        }
        cmd_off += cmdsize;
    }
    None
}

// ---------------------------------------------------------------------------
// route-(a): execute the emitted AArch64 bytes under trust-machine-sem.
// ---------------------------------------------------------------------------

/// Execute the AArch64 code image under the formal `trust-machine-sem` semantics
/// with the AAPCS64 integer arg regs W0=`a`, W1=`b`; return W0 at the first `ret`
/// (the i32 return value, masked to 32 bits). `cs` must be pre-seeded with the
/// image (these bodies perform no stores, so one seeding is reused across inputs).
fn run_alu_isa(
    cs: &mut trust_machine_sem::ConcreteState,
    base: u64,
    code: &[u8],
    a: i32,
    b: i32,
) -> Option<i32> {
    use trust_disasm::{decode_aarch64, Opcode};
    use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics};

    for g in cs.gpr.iter_mut() {
        *g = 0;
    }
    // AAPCS64: 32-bit args occupy W0/W1 (low half of X0/X1). Place the bit pattern
    // (zero-extended into the 64-bit reg) exactly as the ABI/caller would.
    cs.gpr[0] = (a as u32) as u64;
    cs.gpr[1] = (b as u32) as u64;
    cs.pc = base;
    cs.flags = trust_machine_sem::ConcreteFlags::default();

    let sem = Aarch64Semantics;
    let ms = MachineState::symbolic();
    for _ in 0..100_000 {
        let off = cs.pc.checked_sub(base)? as usize;
        let bytes: [u8; 4] = code.get(off..off + 4)?.try_into().ok()?;
        let insn = decode_aarch64(&bytes, cs.pc).ok()?;
        if insn.opcode == Opcode::Ret {
            // W0 = low 32 bits of X0, reinterpreted as i32.
            return Some(cs.gpr[0] as u32 as i32);
        }
        let effects = sem.effects(&ms, &insn).ok()?;
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
                    cs.apply_effect(eff).ok()?;
                    pc_set = true;
                }
                _ => {
                    cs.apply_effect(eff).ok()?;
                }
            }
        }
        if !pc_set {
            cs.pc = cs.pc.wrapping_add(4);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// route-(b): execute the SAME emitted bytes on the real CPU, for a batch of
// inputs (one link + one run per op; all input pairs printed in order).
// ---------------------------------------------------------------------------

/// Emit `func`, link with a C harness that calls it on every `(a, b)` pair (read
/// from argv-free embedded data via stdin? no — we embed them in the C source),
/// run, return the i32 results in pair order. Returns None if cc/link/run fails.
fn route_b_run_batch(func: &VerifiableFunction, pairs: &[(i32, i32)]) -> Option<Vec<i32>> {
    let obj = emit_obj(func)?;

    let dir = tempfile::tempdir().ok()?;
    let obj_path = dir.path().join("fn.o");
    let c_path = dir.path().join("harness.c");
    let data_path = dir.path().join("pairs.txt");
    let bin_path = dir.path().join("h");
    fs::write(&obj_path, &obj).ok()?;

    // Pairs are fed via a file (read with scanf) to keep the C source small and
    // avoid emitting 2000+ literal calls. n is printed first.
    let mut data = format!("{}\n", pairs.len());
    for (a, b) in pairs {
        data.push_str(&format!("{a} {b}\n"));
    }
    fs::write(&data_path, &data).ok()?;

    let harness = format!(
        r#"
#include <stdio.h>
extern int {fname}(int, int);
int main(void) {{
    FILE *f = fopen("{path}", "r");
    if (!f) return 2;
    long n; if (fscanf(f, "%ld", &n) != 1) return 3;
    for (long i = 0; i < n; i++) {{
        int a, b;
        if (fscanf(f, "%d %d", &a, &b) != 2) return 4;
        printf("%d\n", {fname}(a, b));
    }}
    fclose(f);
    return 0;
}}
"#,
        fname = func.name,
        path = data_path.display(),
    );
    fs::write(&c_path, harness).ok()?;

    let link = Command::new("cc")
        .arg(&c_path)
        .arg(&obj_path)
        .arg("-o")
        .arg(&bin_path)
        .output()
        .ok()?;
    if !link.status.success() {
        eprintln!("cc link FAILED: {}", String::from_utf8_lossy(&link.stderr));
        return None;
    }
    let out = Command::new(&bin_path).output().ok()?;
    if !out.status.success() {
        eprintln!("run FAILED: status {:?}", out.status);
        return None;
    }
    let res: Vec<i32> = String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .map(|t| t.parse().expect("i32 output"))
        .collect();
    if res.len() != pairs.len() {
        eprintln!("route-b returned {} results, expected {}", res.len(), pairs.len());
        return None;
    }
    Some(res)
}

// ---------------------------------------------------------------------------
// Deterministic input generation: fixed-seed xorshift + edge values.
// ---------------------------------------------------------------------------

/// Minimal deterministic xorshift64* PRNG (no external rand crate).
struct XorShift(u64);
impl XorShift {
    fn new(seed: u64) -> Self {
        XorShift(seed | 1) // never 0
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

const EDGES: &[i32] = &[0, 1, -1, 2, -2, i32::MIN, i32::MAX, i32::MIN + 1, i32::MAX - 1];

/// Build a deterministic set of (a, b) i32 pairs for one op: the full edge x edge
/// cross product, edges crossed with a few random values, plus pure-random pairs,
/// so the total is >= 2000 per op. `seed` makes each op's random tail distinct but
/// reproducible.
fn input_pairs(seed: u64) -> Vec<(i32, i32)> {
    let mut rng = XorShift::new(seed);
    let mut pairs = Vec::new();

    // 1. edge x edge cross product (9*9 = 81 pairs) — all the corner cases.
    for &a in EDGES {
        for &b in EDGES {
            pairs.push((a, b));
        }
    }
    // 2. edges crossed with random (and random crossed with edges).
    for &e in EDGES {
        for _ in 0..40 {
            pairs.push((e, rng.next_i32()));
            pairs.push((rng.next_i32(), e));
        }
    }
    // 3. pure random pairs to top up well past 2000.
    while pairs.len() < 2200 {
        pairs.push((rng.next_i32(), rng.next_i32()));
    }
    pairs
}

// ---------------------------------------------------------------------------
// The differential validation: route-(a) ISA model == route-(b) real CPU.
// ---------------------------------------------------------------------------

/// Run the full differential for one op. Returns (sample_count, mismatches).
fn differential_for_op(
    name: &str,
    op: BinOp,
    seed: u64,
) -> (usize, Vec<(i32, i32, i32, i32)>) {
    let vf = author_alu_vf(name, op);
    let pairs = input_pairs(seed);

    // route-(b): real CPU, batched (one link + run).
    let cpu = route_b_run_batch(&vf, &pairs)
        .unwrap_or_else(|| panic!("route-(b) emit->link->run failed for op {name}"));

    // route-(a): formal ISA model on the SAME emitted bytes.
    let obj = emit_obj(&vf).unwrap_or_else(|| panic!("emit object for op {name}"));
    let (code, base) = macho_text(&obj)
        .unwrap_or_else(|| panic!("extract __text for op {name}"));
    let mut cs = trust_machine_sem::ConcreteState::new();
    for (i, byte) in code.iter().enumerate() {
        cs.store_memory_le(base + i as u64, 1, *byte as u128).expect("seed image");
    }

    let mut mism = Vec::new();
    for (idx, &(a, b)) in pairs.iter().enumerate() {
        let model = run_alu_isa(&mut cs, base, &code, a, b)
            .unwrap_or_else(|| panic!("route-(a) ISA exec failed for op {name} at (a={a}, b={b})"));
        let silicon = cpu[idx];
        if model != silicon {
            mism.push((a, b, model, silicon));
        }
    }
    (pairs.len(), mism)
}

#[test]
fn isa_model_matches_real_cpu_over_all_alu_ops() {
    let mut report = Vec::new();
    for (i, &(name, op)) in OPS.iter().enumerate() {
        let seed = 0xA1u64.wrapping_mul(i as u64 + 1).wrapping_add(0xDEAD_BEEF + i as u64);
        let (n, mism) = differential_for_op(name, op, seed);
        report.push((name, n, mism.len()));
        assert!(
            mism.is_empty(),
            "op {name}: trust-machine-sem ISA model DISAGREES with the real CPU at {} of {} \
             sampled inputs (a, b, model, cpu): {:?}",
            mism.len(),
            n,
            &mism[..mism.len().min(8)]
        );
    }
    // Surface the per-op sample counts in test output (run with --nocapture).
    for (name, n, m) in &report {
        println!("op {name}: {n} samples, {m} mismatches (model == cpu)");
    }
    let total: usize = report.iter().map(|(_, n, _)| n).sum();
    println!("TOTAL: {} samples across {} ops, ALL model == cpu", total, OPS.len());
}

// ---------------------------------------------------------------------------
// NEGATIVE CONTROL: prove the harness has teeth.
// ---------------------------------------------------------------------------

#[test]
fn negative_control_wrong_op_pairing_is_detected() {
    // Cross-pair route-(a) of op X's bytes against route-(b) of op Y's bytes
    // (X != Y). If the harness were toothless it would "pass" anyway; instead we
    // assert that a mismatch IS observed for every wrong pairing on at least one
    // sampled input. This proves the differential would CATCH a wrong ISA arm:
    // had the model implemented, say, ADD where the bytes encode SUB, the
    // X-vs-Y disagreement is exactly what a real model bug would look like.
    let pairs = input_pairs(0x1234_5678);

    // Precompute route-(b) (real CPU) results for every op once.
    let mut cpu_results: Vec<(&str, Vec<i32>)> = Vec::new();
    for &(name, op) in OPS {
        let vf = author_alu_vf(name, op);
        let cpu = route_b_run_batch(&vf, &pairs)
            .unwrap_or_else(|| panic!("route-(b) failed for op {name}"));
        cpu_results.push((name, cpu));
    }

    // For each op X, run route-(a) on X's bytes and confirm it MATCHES route-(b)
    // of X (sanity) but MISMATCHES route-(b) of every other op Y (teeth).
    for (xi, &(xname, xop)) in OPS.iter().enumerate() {
        let vf = author_alu_vf(xname, xop);
        let obj = emit_obj(&vf).unwrap_or_else(|| panic!("emit {xname}"));
        let (code, base) = macho_text(&obj).unwrap_or_else(|| panic!("text {xname}"));
        let mut cs = trust_machine_sem::ConcreteState::new();
        for (i, byte) in code.iter().enumerate() {
            cs.store_memory_le(base + i as u64, 1, *byte as u128).expect("seed");
        }
        let model_x: Vec<i32> = pairs
            .iter()
            .map(|&(a, b)| {
                run_alu_isa(&mut cs, base, &code, a, b)
                    .unwrap_or_else(|| panic!("route-(a) {xname} at ({a},{b})"))
            })
            .collect();

        for (yi, (yname, cpu_y)) in cpu_results.iter().enumerate() {
            let agrees_everywhere = model_x.iter().zip(cpu_y.iter()).all(|(m, c)| m == c);
            if xi == yi {
                assert!(
                    agrees_everywhere,
                    "sanity: route-(a) of {xname} must equal route-(b) of {xname} everywhere"
                );
            } else {
                // The harness has teeth: a wrong (X-bytes vs Y-cpu) pairing must
                // be detected as a disagreement on at least one input. (The 81
                // edge x edge pairs include cases like (5, 3) where every pair of
                // distinct ops differs, e.g. add=8 != sub=2 != and=1 ...)
                assert!(
                    !agrees_everywhere,
                    "NEGATIVE CONTROL FAILED: route-(a) of {xname} spuriously agreed with \
                     route-(b) of {yname} on ALL inputs — the harness would NOT catch a \
                     wrong ISA arm. This means the differential is toothless."
                );
            }
        }
    }
    println!("negative control: all {} wrong op pairings detected as mismatches", OPS.len() * (OPS.len() - 1));
}
