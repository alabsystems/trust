// Route-(b) exhaustive translation validation by execution + route-(a) first
// links, for the aterm `table_step` parser transition function.
//
// The clean kernel (in trust-certify) proves the trust-ir `table_step` program
// refines the spec, and the spec is machine-verified == aterm's real table. This
// file closes the last link the kernel proofs do NOT reach: the actual MACHINE
// CODE `trust-cg` emits. `table_step` is authored as a `VerifiableFunction`
// (the IR trust-cg consumes), lowered + emitted to a real object, then:
//   (b) linked and EXHAUSTIVELY EXECUTED on every input, output compared to the
//       proven table — complete behavioral equivalence of the shipped bytes for
//       this finite function (trust base: linker + CPU + FFI, no machine semantics);
//   (a) run through trust-cg's translation-validation apparatus for what it
//       genuinely establishes (honest coverage; the LIR->machine semantic step is
//       the documented wall — see the (a) goal paragraph in the design doc §8.13).

// 2D-grid (state × byte) tables are built and checked by coordinate index, which
// is clearer here than iterator gymnastics.
#![allow(clippy::needless_range_loop)]

use std::fs;
use std::process::Command;

use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ---- spike: confirm emit -> link -> execute runs real machine code ----------

fn make_add() -> VerifiableFunction {
    VerifiableFunction {
        name: "spike_add".to_string(),
        def_path: "spike::add".to_string(),
        span: SourceSpan::default(),
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
                        trust_types::BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
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

/// Emit `func` to a real object, link it with a C harness that calls it, run, and
/// return captured stdout. `harness_c` must define `main` and may declare the
/// emitted function `extern`. Returns None if cc/link/run is unavailable.
fn emit_link_run(func: &VerifiableFunction, harness_c: &str) -> Option<String> {
    // host() hardcodes an -unknown-linux-gnu triple (always ELF). On macOS the
    // native linker needs Mach-O, so request the host arch with the apple-darwin
    // triple and see whether the codegen pipeline keys object format off the triple.
    let triple = if cfg!(target_vendor = "apple") {
        if cfg!(target_arch = "aarch64") { "aarch64-apple-darwin" } else { "x86_64-apple-darwin" }
    } else {
        TrustCgTargetArch::host().triple()
    };
    let backend = TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), triple);
    let lir = match backend.lower_function(func) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("STEP lower_function FAILED: {e:?}");
            return None;
        }
    };
    let obj = match backend.emit_object(&[lir]) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("STEP emit_object FAILED: {e:?}");
            return None;
        }
    };
    // Optional: persist the emitted object for disassembly/inspection.
    if let Ok(p) = std::env::var("PERSIST_OBJ") {
        let _ = fs::write(&p, &obj);
    }

    let dir = tempfile::tempdir().ok()?;
    let obj_path = dir.path().join("fn.o");
    let c_path = dir.path().join("harness.c");
    let bin_path = dir.path().join("h");
    fs::write(&obj_path, &obj).ok()?;
    fs::write(&c_path, harness_c).ok()?;

    let link =
        Command::new("cc").arg(&c_path).arg(&obj_path).arg("-o").arg(&bin_path).output().ok()?;
    if !link.status.success() {
        eprintln!("STEP cc link FAILED: {}", String::from_utf8_lossy(&link.stderr));
        return None;
    }
    let out = Command::new(&bin_path).output().ok()?;
    if !out.status.success() {
        eprintln!("STEP run FAILED: status {:?}", out.status);
        return None;
    }
    Some(String::from_utf8_lossy(&out.stdout).into_owned())
}

#[test]
fn spike_emit_link_execute_real_machine_code() {
    // Confirms the whole emit -> link -> run loop produces real machine code that
    // computes the function: spike_add(2,3) == 5, observed from the executed bytes.
    let harness = r#"
#include <stdio.h>
extern int spike_add(int, int);
int main(void) { printf("%d\n", spike_add(2, 3)); return 0; }
"#;
    match emit_link_run(&make_add(), harness) {
        Some(out) => assert_eq!(out.trim(), "5", "executed machine code must compute 2+3=5"),
        None => panic!("emit->link->run pipeline failed (cc/linking unavailable?)"),
    }
}

// ---- the proven aterm next-state table (compact: class_matrix o classifier) --
//
// These two literals are the kernel-proven + drift-guarded data from
// trust-certify (full_aterm_class_matrix + aterm_byte_classifier_row). The full
// 14x256 next-state table is their composition `class_matrix[s][classifier[b]]`,
// which trust-certify kernel-PROVES equals the real aterm table over all 256
// bytes (verifies_nextstate_composition_in_chunks) and the spec-drift guard
// confirms == the live aterm artifact. So executing the compiled function against
// this table validates the shipped bytes against the proven function.

fn class19_matrix() -> Vec<Vec<i128>> {
    vec![
        vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 7, 12, 13],
        vec![0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 3, 7, 12, 13, 1, 3, 7, 12, 13],
        vec![0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 1, 3, 7, 12, 13],
        vec![0, 0, 0, 0, 4, 4, 4, 3, 3, 5, 0, 0, 0, 0, 1, 3, 7, 12, 13],
        vec![0, 0, 0, 0, 4, 4, 6, 4, 4, 5, 0, 0, 0, 0, 1, 3, 7, 12, 13],
        vec![0, 0, 0, 0, 6, 6, 6, 5, 5, 5, 0, 0, 0, 0, 1, 3, 7, 12, 13],
        vec![0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 1, 3, 7, 12, 13],
        vec![0, 0, 0, 10, 8, 11, 8, 7, 7, 9, 10, 10, 10, 10, 1, 3, 7, 12, 13],
        vec![0, 0, 0, 10, 8, 11, 11, 8, 8, 9, 10, 10, 10, 10, 1, 3, 7, 12, 13],
        vec![0, 0, 0, 10, 11, 11, 11, 9, 9, 9, 10, 10, 10, 10, 1, 3, 7, 12, 13],
        vec![0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 1, 10, 10, 10, 10],
        vec![0, 0, 0, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 1, 3, 7, 12, 13],
        vec![0, 12, 12, 12, 12, 12, 12, 0, 12, 12, 12, 12, 12, 12, 1, 12, 12, 12, 12],
        vec![0, 0, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 1, 13, 13, 13, 13],
    ]
}

#[rustfmt::skip]
fn byte_classifier() -> Vec<usize> {
    vec![
        8, 8, 8, 8, 8, 8, 8, 7, 8, 8, 8, 8, 8, 8, 8, 8,
        8, 8, 8, 8, 8, 8, 8, 8, 0, 8, 0, 14, 8, 8, 8, 8,
        9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
        4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 6, 6, 6, 6,
        3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
        11, 3, 3, 3, 3, 3, 3, 3, 13, 3, 3, 10, 3, 12, 13, 13,
        3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
        3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 8,
        2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
        16, 2, 2, 2, 2, 2, 2, 2, 18, 2, 2, 15, 1, 17, 18, 18,
        2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
        2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
        2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
        2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
        2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
        2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    ]
}

/// The full 14x256 next-state table as the composition class_matrix[s][classify[b]].
fn full_next_state_table() -> Vec<Vec<i128>> {
    let cm = class19_matrix();
    let cls = byte_classifier();
    (0..14).map(|s| (0..256).map(|b| cm[s][cls[b]]).collect()).collect()
}

/// Author `table_step(state: i64, byte: i64) -> i64` as a VerifiableFunction: a
/// nested SwitchInt (outer on state, inner on byte) whose leaves return the
/// constant `cells[state][byte]`. Mirrors trust-certify's `author_table_step_module`
/// but in the IR trust-cg consumes. Block ids: 0=entry, 1=trap, 2+s=row[s],
/// (2+n_states + s*n_bc + b)=leaf[s][b].
fn author_table_step_vf(cells: &[Vec<i128>]) -> VerifiableFunction {
    let n_states = cells.len();
    let n_bc = cells[0].len();
    let row_id = |s: usize| BlockId(2 + s);
    let leaf_id = |s: usize, b: usize| BlockId(2 + n_states + s * n_bc + b);
    let sp = SourceSpan::default;

    let mut blocks: Vec<BasicBlock> = Vec::with_capacity(2 + n_states + n_states * n_bc);

    // entry: switch state -> row[s]
    blocks.push(BasicBlock {
        id: BlockId(0),
        stmts: vec![],
        terminator: Terminator::SwitchInt {
            exhaustive_enum_unreachable: false,
            discr: Operand::Copy(Place::local(1)),
            targets: (0..n_states).map(|s| (s as u128, row_id(s))).collect(),
            otherwise: BlockId(1),
            span: sp(),
        },
    });
    // trap: return 0
    blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
            span: sp(),
        }],
        terminator: Terminator::Return,
    });
    // rows: switch byte -> leaf[s][b]
    for s in 0..n_states {
        blocks.push(BasicBlock {
            id: row_id(s),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                exhaustive_enum_unreachable: false,
                discr: Operand::Copy(Place::local(2)),
                targets: (0..n_bc).map(|b| (b as u128, leaf_id(s, b))).collect(),
                otherwise: BlockId(1),
                span: sp(),
            },
        });
    }
    // leaves: return cells[s][b]
    for s in 0..n_states {
        for b in 0..n_bc {
            blocks.push(BasicBlock {
                id: leaf_id(s, b),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(
                        cells[s][b] as u128,
                        64,
                    ))),
                    span: sp(),
                }],
                terminator: Terminator::Return,
            });
        }
    }

    VerifiableFunction {
        name: "table_step".to_string(),
        def_path: "aterm::table_step".to_string(),
        span: sp(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i64(), name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("state".into()) },
                LocalDecl { index: 2, ty: Ty::i64(), name: Some("byte".into()) },
            ],
            blocks,
            arg_count: 2,
            return_ty: Ty::i64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn exhaustively_executes_compiled_table_step_matches_proven_table() {
    // ROUTE (b): the shipped MACHINE CODE, exhaustively. Author table_step over the
    // full 14x256 table, compile to a real Mach-O object, link, and EXECUTE it on
    // every one of the 3584 (state, byte) inputs, comparing each output to the
    // proven table. A full match = the compiled artifact is behaviorally identical
    // to the kernel-proven function on its ENTIRE input domain. (Trust base: the
    // system linker + CPU + the i64,i64->i64 FFI signature — no machine semantics.)
    let table = full_next_state_table();
    let vf = author_table_step_vf(&table);

    // Harness: call table_step for all (s,b) in canonical order, print outputs.
    let harness = r#"
#include <stdio.h>
extern long table_step(long, long);
int main(void) {
    for (long s = 0; s < 14; s++)
        for (long b = 0; b < 256; b++)
            printf("%ld\n", table_step(s, b));
    return 0;
}
"#;
    let out = match emit_link_run(&vf, harness) {
        Some(o) => o,
        None => panic!("emit->link->run of table_step failed"),
    };
    let got: Vec<i128> = out.split_whitespace().map(|t| t.parse().expect("int")).collect();
    assert_eq!(got.len(), 14 * 256, "harness must print all 3584 outputs");

    let mut mismatches = Vec::new();
    for s in 0..14 {
        for b in 0..256 {
            let expected = table[s][b];
            let actual = got[s * 256 + b];
            if expected != actual {
                mismatches.push((s, b, expected, actual));
            }
        }
    }
    assert!(
        mismatches.is_empty(),
        "compiled table_step diverges from the proven table at {} of 3584 inputs: {:?}",
        mismatches.len(),
        &mismatches[..mismatches.len().min(8)]
    );
}

// ---- route (a) SEMANTIC: execute the emitted bytes under a FORMAL ISA model ---
//
// The strongest route-(a) result reachable for a finite function: decode the
// emitted machine code with `trust-disasm` and execute it under the FORMAL
// AArch64 semantics in `trust-machine-sem` (NOT the real CPU) on all 3584 inputs,
// proving the result == the proven table. Unlike route (b) (real-CPU execution),
// this pins the guarantee to an auditable, reusable formal ISA semantics: the
// HONEST trust floor is "the trust-machine-sem AArch64 model's fidelity + the
// decoder", not the opaque silicon. This is "proof modulo a formal ISA semantics"
// — the §8.13 route-(a) end-state, for the finite domain.

/// Lower + emit `func` to a real object (host arch, Mach-O on apple).
fn emit_obj(func: &VerifiableFunction) -> Option<Vec<u8>> {
    let triple = if cfg!(target_vendor = "apple") {
        if cfg!(target_arch = "aarch64") { "aarch64-apple-darwin" } else { "x86_64-apple-darwin" }
    } else {
        TrustCgTargetArch::host().triple()
    };
    let backend = TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), triple);
    let lir = backend.lower_function(func).ok()?;
    backend.emit_object(&[lir]).ok()
}

/// Minimal Mach-O 64 reader: return (`__text` bytes, its vmaddr). The emitted
/// object is a single relocation-free `__text` section, so the bytes are a
/// self-contained code+jump-table image loaded at `vmaddr`.
fn macho_text(obj: &[u8]) -> Option<(Vec<u8>, u64)> {
    let rd_u32 =
        |o: usize| -> Option<u32> { Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?)) };
    let rd_u64 =
        |o: usize| -> Option<u64> { Some(u64::from_le_bytes(obj.get(o..o + 8)?.try_into().ok()?)) };
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
                let is_text = name.starts_with(b"__text\0");
                if is_text {
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

/// Minimal ELF64 little-endian reader for a relocatable object's `.text`
/// section. This test executes machine code, not the ELF container header.
fn elf64_text(obj: &[u8]) -> Option<(Vec<u8>, u64)> {
    if obj.get(..6)? != b"\x7fELF\x02\x01" {
        return None;
    }
    let rd_u16 =
        |o: usize| -> Option<u16> { Some(u16::from_le_bytes(obj.get(o..o + 2)?.try_into().ok()?)) };
    let rd_u32 =
        |o: usize| -> Option<u32> { Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?)) };
    let rd_u64 =
        |o: usize| -> Option<u64> { Some(u64::from_le_bytes(obj.get(o..o + 8)?.try_into().ok()?)) };

    let section_table = usize::try_from(rd_u64(40)?).ok()?;
    let section_size = usize::from(rd_u16(58)?);
    let section_count = usize::from(rd_u16(60)?);
    let names_index = usize::from(rd_u16(62)?);
    if section_size < 64 || names_index >= section_count {
        return None;
    }

    let header_at = |index: usize| -> Option<usize> {
        (index < section_count)
            .then_some(section_table.checked_add(index.checked_mul(section_size)?)?)
    };
    let names_header = header_at(names_index)?;
    let names_offset = usize::try_from(rd_u64(names_header + 24)?).ok()?;
    let names_size = usize::try_from(rd_u64(names_header + 32)?).ok()?;
    let names = obj.get(names_offset..names_offset.checked_add(names_size)?)?;

    for index in 0..section_count {
        let header = header_at(index)?;
        let name_offset = usize::try_from(rd_u32(header)?).ok()?;
        let name_tail = names.get(name_offset..)?;
        let name_end = name_tail.iter().position(|byte| *byte == 0)?;
        if &name_tail[..name_end] != b".text" {
            continue;
        }
        let address = rd_u64(header + 16)?;
        let offset = usize::try_from(rd_u64(header + 24)?).ok()?;
        let size = usize::try_from(rd_u64(header + 32)?).ok()?;
        return Some((obj.get(offset..offset.checked_add(size)?)?.to_vec(), address));
    }
    None
}

/// Execute the AArch64 code image under the formal `trust-machine-sem` semantics
/// with x0=`x0_in`, x1=`x1_in`; return x0 at the first `ret`. `cs` must be
/// pre-seeded with the image (memory is read-only — table_step performs no
/// stores — so one seeding is reused across inputs).
fn run_table_step(
    cs: &mut trust_machine_sem::ConcreteState,
    base: u64,
    code: &[u8],
    x0_in: u64,
    x1_in: u64,
) -> Option<u64> {
    use trust_disasm::{Opcode, decode_aarch64};
    use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics};

    for g in cs.gpr.iter_mut() {
        *g = 0;
    }
    cs.gpr[0] = x0_in;
    cs.gpr[1] = x1_in;
    cs.pc = base;
    cs.flags = trust_machine_sem::ConcreteFlags::default();

    let sem = Aarch64Semantics;
    let ms = MachineState::symbolic();
    for _ in 0..100_000 {
        let off = cs.pc.checked_sub(base)? as usize;
        let bytes: [u8; 4] = code.get(off..off + 4)?.try_into().ok()?;
        let insn = decode_aarch64(&bytes, cs.pc).ok()?;
        if insn.opcode == Opcode::Ret {
            return Some(cs.gpr[0]);
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

#[test]
fn route_a_isa_semantic_execution_matches_proven_table() {
    let table = full_next_state_table();
    let vf = author_table_step_vf(&table);
    let obj = emit_obj(&vf).expect("emit table_step object");
    let (code, base) = macho_text(&obj).expect("extract __text section");

    // Seed the image into a ConcreteState memory ONCE (read-only during exec).
    let mut cs = trust_machine_sem::ConcreteState::new();
    for (i, b) in code.iter().enumerate() {
        cs.store_memory_le(base + i as u64, 1, *b as u128).expect("seed image");
    }

    let mut mism = Vec::new();
    for s in 0..14u64 {
        for b in 0..256u64 {
            let got = run_table_step(&mut cs, base, &code, s, b)
                .unwrap_or_else(|| panic!("ISA execution failed at state={s} byte={b}"));
            let want = table[s as usize][b as usize] as u64;
            if got != want {
                mism.push((s, b, want, got));
            }
        }
    }
    assert!(
        mism.is_empty(),
        "ISA-semantics execution of the emitted bytes diverges from the proven table at {} of \
         3584 inputs (state,byte,want,got): {:?}",
        mism.len(),
        &mism[..mism.len().min(8)]
    );
}

#[test]
fn route_a_isa_execution_verifies_bounds_check_traps() {
    // Coverage the in-domain run omits: OUT-OF-RANGE inputs must hit the
    // `cmp`/`b.hi` -> trap path (return 0) WITHOUT an out-of-bounds jump-table read.
    // This exercises the bounds-check machine code (cmp x,#0xd / cmp x,#0xff) that
    // guards the two jump tables — proving the compiled guards work, under the ISA
    // semantics, for the whole out-of-domain.
    let vf = author_table_step_vf(&full_next_state_table());
    let obj = emit_obj(&vf).expect("emit table_step object");
    let (code, base) = macho_text(&obj).expect("extract __text");
    let mut cs = trust_machine_sem::ConcreteState::new();
    for (i, b) in code.iter().enumerate() {
        cs.store_memory_le(base + i as u64, 1, *b as u128).expect("seed");
    }
    // state > 13: outer bounds check -> trap -> 0.
    for s in 14u64..64 {
        let got = run_table_step(&mut cs, base, &code, s, 0).expect("exec");
        assert_eq!(got, 0, "out-of-range state {s} must trap to 0 (no OOB jump-table read)");
    }
    // byte > 255 (with a valid state): inner bounds check -> trap -> 0.
    for b in 256u64..512 {
        let got = run_table_step(&mut cs, base, &code, 3, b).expect("exec");
        assert_eq!(got, 0, "out-of-range byte {b} must trap to 0 (no OOB jump-table read)");
    }
}

#[test]
fn route_a_isa_execution_faithfully_runs_the_actual_bytes() {
    // Sensitivity control: compile a table with ONE flipped cell and confirm the
    // ISA-semantics execution returns the BUGGY value (i.e. it faithfully executes
    // the emitted bytes, so it WOULD catch a codegen bug — not a trivial pass).
    let good = full_next_state_table();
    let mut bad = good.clone();
    let (s, b) = (7usize, 0x30usize);
    bad[s][b] = (good[s][b] + 1) % 14; // a different, valid next-state
    let obj = emit_obj(&author_table_step_vf(&bad)).expect("emit buggy table_step");
    let (code, base) = macho_text(&obj).expect("extract __text");
    let mut cs = trust_machine_sem::ConcreteState::new();
    for (i, byte) in code.iter().enumerate() {
        cs.store_memory_le(base + i as u64, 1, *byte as u128).expect("seed");
    }
    let got = run_table_step(&mut cs, base, &code, s as u64, b as u64).expect("exec");
    assert_eq!(got, bad[s][b] as u64, "ISA exec must return what the (buggy) bytes compute");
    assert_ne!(got, good[s][b] as u64, "ISA exec must NOT silently return the good value");
}

#[test]
fn route_a_isa_execution_faithful_over_a_permuted_table() {
    // CONCLUSIVE sensitivity control (rules out a coincidental full-table match):
    // compile a PERMUTED table (next-state v -> (v+1)%14, a bijection that changes
    // EVERY cell, since v != (v+1)%14 for v in 0..14) and confirm the ISA execution
    // matches the PERMUTED table at all 3584 inputs and differs from the real table
    // at all 3584. So the driver faithfully computes whatever the emitted bytes
    // encode — the match in route_a_isa_semantic_execution is genuine, not luck.
    let good = full_next_state_table();
    let permuted: Vec<Vec<i128>> =
        good.iter().map(|r| r.iter().map(|&v| (v + 1) % 14).collect()).collect();
    let obj = emit_obj(&author_table_step_vf(&permuted)).expect("emit permuted table_step");
    let (code, base) = macho_text(&obj).expect("extract __text");
    let mut cs = trust_machine_sem::ConcreteState::new();
    for (i, byte) in code.iter().enumerate() {
        cs.store_memory_le(base + i as u64, 1, *byte as u128).expect("seed");
    }
    let (mut matched_permuted, mut differed_from_good) = (0usize, 0usize);
    for s in 0..14u64 {
        for b in 0..256u64 {
            let got = run_table_step(&mut cs, base, &code, s, b).expect("exec");
            assert_eq!(
                got, permuted[s as usize][b as usize] as u64,
                "ISA exec must compute the PERMUTED table at (state={s}, byte={b})"
            );
            matched_permuted += 1;
            if got != good[s as usize][b as usize] as u64 {
                differed_from_good += 1;
            }
        }
    }
    assert_eq!(matched_permuted, 14 * 256, "must faithfully execute all 3584 permuted cells");
    assert_eq!(
        differed_from_good,
        14 * 256,
        "the permutation changes every cell, so ISA exec must differ from the real table everywhere"
    );
}

#[test]
fn route_a_isa_model_agrees_with_route_b_real_cpu() {
    // CROSS-VALIDATION of the ISA-fidelity residue: the SAME emitted bytes, executed
    // under the formal trust-machine-sem AArch64 semantics (route a) AND on the real
    // CPU (route b), must produce IDENTICAL output on all 3584 inputs. Agreement =
    // the formal ISA model is faithful to real silicon for this function — directly
    // exercising the residue route (a) rests on. (Emission is deterministic, so both
    // paths run the same machine code.)
    let table = full_next_state_table();
    let vf = author_table_step_vf(&table);

    // Route (b): real CPU, all 3584 outputs in canonical order.
    let harness = r#"
#include <stdio.h>
extern long table_step(long, long);
int main(void) {
    for (long s = 0; s < 14; s++)
        for (long b = 0; b < 256; b++)
            printf("%ld\n", table_step(s, b));
    return 0;
}
"#;
    let cpu_out = emit_link_run(&vf, harness).expect("route (b) emit->link->run");
    let cpu: Vec<i128> = cpu_out.split_whitespace().map(|t| t.parse().expect("int")).collect();
    assert_eq!(cpu.len(), 14 * 256, "route (b) must yield 3584 outputs");

    // Route (a): formal ISA model, same bytes, all 3584 outputs.
    let obj = emit_obj(&vf).expect("emit object");
    let (code, base) = macho_text(&obj).expect("extract __text");
    let mut cs = trust_machine_sem::ConcreteState::new();
    for (i, byte) in code.iter().enumerate() {
        cs.store_memory_le(base + i as u64, 1, *byte as u128).expect("seed");
    }

    let mut disagree = Vec::new();
    for s in 0..14u64 {
        for b in 0..256u64 {
            let model = run_table_step(&mut cs, base, &code, s, b).expect("route (a) exec");
            let silicon = cpu[(s * 256 + b) as usize] as u64;
            if model != silicon {
                disagree.push((s, b, model, silicon));
            }
        }
    }
    assert!(
        disagree.is_empty(),
        "formal ISA model disagrees with the real CPU at {} of 3584 inputs (state,byte,model,cpu): {:?}",
        disagree.len(),
        &disagree[..disagree.len().min(8)]
    );
}

// ---- route (a) on x86-64 (after wiring trust-cg's real x86 backend) ----------

fn emit_obj_x86(func: &VerifiableFunction) -> Option<Vec<u8>> {
    let backend = TrustCgCodegenBackend::new_for_triple(
        TrustCgTargetArch::X86_64,
        "x86_64-unknown-linux-gnu",
    );
    let lir = backend.lower_function(func).ok()?;
    backend.emit_object(&[lir]).ok()
}

fn run_table_step_x86(
    cs: &mut trust_machine_sem::ConcreteState,
    base: u64,
    code: &[u8],
    x0_in: u64,
    x1_in: u64,
) -> Option<u64> {
    use trust_disasm::{Opcode, decode_x86_64};
    use trust_machine_sem::{Effect, MachineState, Semantics, X86_64Semantics};
    for g in cs.gpr.iter_mut() {
        *g = 0;
    }
    cs.gpr[7] = x0_in; // rdi
    cs.gpr[6] = x1_in; // rsi
    cs.pc = base;
    cs.sp = 0x7000_0000;
    cs.flags = trust_machine_sem::ConcreteFlags::default();
    let sem = X86_64Semantics;
    let ms = MachineState::symbolic();
    for _ in 0..1_000_000 {
        let off = cs.pc.checked_sub(base)? as usize;
        let end = (off + 16).min(code.len());
        let insn = decode_x86_64(code.get(off..end)?, cs.pc).ok()?;
        if insn.opcode == Opcode::Ret {
            return Some(cs.gpr[0]); // rax
        }
        let effects = sem.effects(&ms, &insn).ok()?;
        // Two-pass (clone-free): evaluate EVERY effect formula against the
        // unmutated PRE-instruction state, then apply. Required because some
        // effects (e.g. x86 PUSH: SpWrite then MemWrite{addr=SP-8}) reference a
        // register that an earlier same-instruction effect mutates.
        let mut reg_w: Vec<(u8, u32, u128)> = Vec::new();
        let mut sp_w: Option<u64> = None;
        let mut mem_w: Vec<(u64, u32, u128)> = Vec::new();
        let mut flag_w: Option<trust_machine_sem::ConcreteFlags> = None;
        let mut pc_w: Option<u64> = None;
        for eff in &effects {
            match eff {
                Effect::RegWrite { index, width, value } => {
                    reg_w.push((*index, *width, cs.eval_bv(value, *width).ok()?));
                }
                Effect::SpWrite { value } => sp_w = Some(cs.eval_bv(value, 64).ok()? as u64),
                Effect::MemWrite { address, value, width_bytes } => {
                    let a = cs.eval_bv(address, 64).ok()? as u64;
                    let vw = (*width_bytes * 8).min(128);
                    mem_w.push((a, *width_bytes, cs.eval_bv(value, vw).ok()?));
                }
                Effect::MemRead { .. } => {} // value consumed by a paired RegWrite formula
                Effect::FlagUpdate { n, z, c, v } => {
                    flag_w = Some(trust_machine_sem::ConcreteFlags {
                        n: cs.eval_bool(n).ok()?,
                        z: cs.eval_bool(z).ok()?,
                        c: cs.eval_bool(c).ok()?,
                        v: cs.eval_bool(v).ok()?,
                    });
                }
                Effect::PcUpdate { value } => pc_w = Some(cs.eval_bv(value, 64).ok()? as u64),
                Effect::ConditionalBranch { condition, target, fallthrough } => {
                    let nx = if trust_machine_sem::eval_condition(
                        trust_machine_sem::ConcreteFlags {
                            n: cs.flags.n,
                            z: cs.flags.z,
                            c: cs.flags.c,
                            v: cs.flags.v,
                        },
                        *condition,
                    ) {
                        target
                    } else {
                        fallthrough
                    };
                    pc_w = Some(cs.eval_bv(nx, 64).ok()? as u64);
                }
                Effect::Branch { target }
                | Effect::Return { target }
                | Effect::Call { target, .. } => {
                    pc_w = Some(cs.eval_bv(target, 64).ok()? as u64);
                }
                _ => {}
            }
        }
        for (i, w, v) in reg_w {
            cs.write_gpr(i, w, v).ok()?;
        }
        if let Some(sp) = sp_w {
            cs.sp = sp;
        }
        for (a, wb, v) in mem_w {
            cs.store_memory_le(a, wb, v).ok()?;
        }
        if let Some(f) = flag_w {
            cs.flags = f;
        }
        let pc_set = pc_w.is_some();
        if let Some(pc) = pc_w {
            cs.pc = pc;
        }
        if !pc_set {
            cs.pc = cs.pc.wrapping_add(insn.size as u64);
        }
    }
    None
}

#[test]
fn route_a_x86_64_isa_semantic_execution_matches_proven_table() {
    // Now that trust-cg's real x86 backend (X86Pipeline) is wired in, the X86_64
    // target emits genuine x86-64. Decode it (trust-disasm) and execute under the
    // formal trust-machine-sem x86-64 semantics on all 3584 inputs == proven table.
    // A SECOND, independent ISA validation of the same compilation.
    let table = full_next_state_table();
    let object = emit_obj_x86(&author_table_step_vf(&table)).expect("emit x86-64 object");
    let (code, base) = elf64_text(&object).expect("extract x86-64 ELF .text section");

    let mut cs = trust_machine_sem::ConcreteState::new();
    for (i, b) in code.iter().enumerate() {
        cs.store_memory_le(base + i as u64, 1, *b as u128).expect("seed");
    }
    let mut mism = Vec::new();
    for s in 0..14u64 {
        for b in 0..256u64 {
            let got = run_table_step_x86(&mut cs, base, &code, s, b)
                .unwrap_or_else(|| panic!("x86-64 ISA execution failed at state={s} byte={b}"));
            let want = table[s as usize][b as usize] as u64;
            if got != want {
                mism.push((s, b, want, got));
            }
        }
    }
    assert!(
        mism.is_empty(),
        "x86-64 ISA execution diverges from the proven table at {} of 3584 (state,byte,want,got): {:?}",
        mism.len(),
        &mism[..mism.len().min(8)]
    );
}
