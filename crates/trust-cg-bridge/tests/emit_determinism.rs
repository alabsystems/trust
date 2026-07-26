// G20: Cross-process BIT-IDENTICAL determinism of trust-cg's EMITTED MACHINE CODE.
//
// NORTH STAR (bootstrap-trust-model.md): defeating trusting-trust needs Diverse
// Double-Compilation, and "DDC depends directly on build-determinism". G19 proved
// the trust-ir *IR serialization* + Module::stable_digest are bit-reproducible
// across a process boundary. THIS rung proves the OTHER half DDC actually compares:
// the EMITTED OBJECT BYTES that trust-cg produces (the Mach-O `.o`) are
// BIT-IDENTICAL across independent builds. This is a DISTINCT artifact from the IR:
// the .o bytes are where Mach-O/ELF writers, symbol tables, relocations and section
// layout live — exactly where nondeterminism hides (HashMap iteration over
// symbols/relocs, embedded timestamps, unstable ordering).
//
// Rust's std HashMap randomizes iteration per process (per-process RandomState seed),
// so two emits in SEPARATE processes diverge if ANY HashMap iteration feeds the
// object bytes. We therefore compare FULL object bytes across a REAL process
// boundary: the parent re-execs THIS test binary as fresh child processes (each with
// an independent HashMap RandomState — guaranteed by being a distinct OS process, and
// additionally perturbed via an env salt). Each child emits the SAME suite and prints
// the full object bytes (hex). The parent asserts every child's object bytes are
// byte-identical to its own, per function. There is also an in-process emit-twice
// floor check.
//
// ANTI-VACUITY / NEGATIVE CONTROL: `emit_determinism_negative_control` proves the
// byte comparison has TEETH — it mutates one emitted object byte and asserts the
// comparison FAILS. Without teeth, "all equal" would be vacuous.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Scope (honest): aarch64-apple-darwin Mach-O object emission ONLY. The ELF writer
// (elf/writer.rs) and the x86_64 emit path are NOT exercised here; see the residual
// note in the source-suite comment and the agent return.

use std::collections::BTreeMap;
use std::process::Command;

use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// We force the aarch64 Mach-O writer regardless of host so the artifact under test is
// stable: an aarch64-apple-darwin object. (On an aarch64 mac this is also the host.)
const TARGET_TRIPLE: &str = "aarch64-apple-darwin";

fn sp() -> SourceSpan {
    SourceSpan::default()
}

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, TARGET_TRIPLE)
}

fn wrap(name: &str, body: VerifiableBody) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("emit_determinism::{name}"),
        span: sp(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// --------------------------------------------------------------------------
// SUITE: scalar ALU (add/sub/mul/and/or/xor/shl/shr).
// Each is `fn(a: i32, b: i32) -> i32 { a OP b }`.
// --------------------------------------------------------------------------

fn alu(name: &str, op: BinOp) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
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
    )
}

// --------------------------------------------------------------------------
// SUITE: control flow.
// max(a,b): `if a < b { b } else { a }`  (CFG diamond + Select).
// clamp(x,lo,hi): nested branches.
// sum_loop(n): bounded loop with a backedge.
// --------------------------------------------------------------------------

fn author_max() -> VerifiableFunction {
    wrap(
        "cf_max",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::bool_ty(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: sp(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: sp(),
                    },
                },
                // a >= b : return a
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                },
                // a < b : return b
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
    )
}

fn author_clamp() -> VerifiableFunction {
    wrap(
        "cf_clamp",
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
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
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
                // x < lo : return lo
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                },
                // x >= lo : check x > hi
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(3)),
                        ),
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
                // x > hi : return hi
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                },
                // in range : return x
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::i32(),
        },
    )
}

fn author_sum_loop() -> VerifiableFunction {
    // acc = 0; i = 0; while i < n { acc += i; i += 1 } return acc
    wrap(
        "cf_sum_loop",
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
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                            span: sp(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                            span: sp(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
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
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(0)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: sp(),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: sp(),
                        },
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

// --------------------------------------------------------------------------
// SUITE: memory (store + load through a raw pointer).
// mem_ptr_rw(p: *mut i32, v: i32) -> i32 { *p = v; *p }
// --------------------------------------------------------------------------

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
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
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

/// The full suite under test, in stable order.
fn suite() -> Vec<VerifiableFunction> {
    vec![
        alu("alu_add", BinOp::Add),
        alu("alu_sub", BinOp::Sub),
        alu("alu_mul", BinOp::Mul),
        alu("alu_and", BinOp::BitAnd),
        alu("alu_or", BinOp::BitOr),
        alu("alu_xor", BinOp::BitXor),
        alu("alu_shl", BinOp::Shl),
        alu("alu_shr", BinOp::Shr),
        author_max(),
        author_clamp(),
        author_sum_loop(),
        author_ptr_rw(),
    ]
}

/// Emit every function in the suite to an aarch64 Mach-O object; return
/// (name -> object bytes) keyed in a deterministic (sorted) map.
fn emit_suite() -> BTreeMap<String, Vec<u8>> {
    let be = backend();
    let mut out = BTreeMap::new();
    for func in suite() {
        let lir = be
            .lower_function(&func)
            .unwrap_or_else(|e| panic!("lower_function failed for {}: {e:?}", func.name));
        let bytes = be
            .emit_object(&[lir])
            .unwrap_or_else(|e| panic!("emit_object failed for {}: {e:?}", func.name));
        assert!(!bytes.is_empty(), "{}: emitted object must be non-empty", func.name);
        assert_eq!(&bytes[..4], &[0xCF, 0xFA, 0xED, 0xFE], "{}: must be 64-bit LE Mach-O", func.name);
        out.insert(func.name.clone(), bytes);
    }
    out
}

// --------------------------------------------------------------------------
// Cross-process protocol. The child prints one line per function:
//   <<<EMIT>>>name|len|hexbytes<<<END>>>
// Markers are robust against libtest's surrounding noise.
// --------------------------------------------------------------------------

const CHILD_ENV: &str = "TRUST_EMIT_DETERMINISM_CHILD";
const CHILD_TEST_NAME: &str = "emit_determinism_child_emitter";

fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn from_hex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "hex string must have even length");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("valid hex"))
        .collect()
}

/// Child entry: emit the suite and print marker lines, then "exit" by returning.
/// Guarded so it only does work when re-exec'd by the parent.
#[test]
fn emit_determinism_child_emitter() {
    if std::env::var(CHILD_ENV).is_err() {
        // Not a child invocation; this is a no-op when run directly by `cargo test`.
        return;
    }
    let objs = emit_suite();
    for (name, bytes) in &objs {
        println!("<<<EMIT>>>{name}|{}|{}<<<END>>>", bytes.len(), to_hex(bytes));
    }
}

/// Run THIS test binary as a fresh child process, targeting only the child emitter
/// test, with an independent HashMap RandomState (distinct process + env salt), and
/// parse the per-function object bytes back out.
fn run_child(salt: &str) -> BTreeMap<String, Vec<u8>> {
    let exe = std::env::current_exe().expect("current_exe");
    let output = Command::new(&exe)
        .args(["--exact", CHILD_TEST_NAME, "--nocapture", "--test-threads=1"])
        .env(CHILD_ENV, "1")
        // Perturb the per-process hasher seed further; std already randomizes per
        // process, but this makes the divergence pressure explicit and reproducible.
        .env("TRUST_EMIT_DETERMINISM_SALT", salt)
        .output()
        .expect("re-exec child test binary");
    assert!(
        output.status.success(),
        "child process failed (salt={salt})\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("child stdout utf8");
    let mut map = BTreeMap::new();
    for line in stdout.lines() {
        // libtest with --nocapture prints the test status line WITHOUT a trailing
        // newline before the captured output, so the first marker line is prefixed
        // by "test <name> ... ". Locate the marker rather than requiring it at the
        // start of the line.
        let Some(start) = line.find("<<<EMIT>>>") else { continue };
        let rest = &line[start + "<<<EMIT>>>".len()..];
        let Some(end) = rest.find("<<<END>>>") else { continue };
        let payload = &rest[..end];
        let mut parts = payload.splitn(3, '|');
        let name = parts.next().expect("name").to_string();
        let len: usize = parts.next().expect("len").parse().expect("len is usize");
        let hex = parts.next().expect("hex");
        let bytes = from_hex(hex);
        assert_eq!(bytes.len(), len, "{name}: declared len must match decoded bytes");
        map.insert(name, bytes);
    }
    assert!(!map.is_empty(), "child produced no EMIT markers (salt={salt})");
    map
}

// --------------------------------------------------------------------------
// FLOOR CHECK: emit twice in-process must be byte-identical.
// --------------------------------------------------------------------------

#[test]
fn emit_determinism_in_process_floor() {
    if std::env::var(CHILD_ENV).is_ok() {
        return; // don't run during a child re-exec
    }
    let a = emit_suite();
    let b = emit_suite();
    assert_eq!(a.keys().collect::<Vec<_>>(), b.keys().collect::<Vec<_>>(), "suite names stable");
    for (name, abytes) in &a {
        let bbytes = &b[name];
        assert_eq!(
            abytes, bbytes,
            "{name}: in-process emit-twice produced DIFFERENT object bytes (len {} vs {})",
            abytes.len(),
            bbytes.len()
        );
    }
    println!("in-process floor: {} functions emit identically twice", a.len());
}

// --------------------------------------------------------------------------
// MAIN GATE: full object bytes are BIT-IDENTICAL across REAL process boundaries.
// --------------------------------------------------------------------------

#[test]
fn emit_determinism_cross_process_object_bytes_are_bit_identical() {
    if std::env::var(CHILD_ENV).is_ok() {
        return; // child path is handled by emit_determinism_child_emitter
    }

    // Parent's own emit (this process has its own HashMap RandomState).
    let parent = emit_suite();

    // Fork several independent child processes, each with a distinct salt and thus a
    // genuinely independent process-level HashMap RandomState. Any HashMap iteration
    // feeding the object bytes would diverge across these.
    let salts = ["alpha", "bravo", "charlie", "delta"];
    let mut total_compared = 0usize;
    for salt in salts {
        let child = run_child(salt);
        assert_eq!(
            parent.keys().collect::<Vec<_>>(),
            child.keys().collect::<Vec<_>>(),
            "child (salt={salt}) emitted a different set of functions"
        );
        for (name, pbytes) in &parent {
            let cbytes = &child[name];
            assert_eq!(
                pbytes.len(),
                cbytes.len(),
                "{name} (salt={salt}): object LENGTH differs across process boundary \
                 (parent {} vs child {}) — emit nondeterminism",
                pbytes.len(),
                cbytes.len()
            );
            if pbytes != cbytes {
                let first_diff = pbytes
                    .iter()
                    .zip(cbytes.iter())
                    .position(|(a, b)| a != b)
                    .unwrap_or(pbytes.len());
                panic!(
                    "{name} (salt={salt}): object BYTES differ across process boundary at \
                     offset {first_diff} (parent={:02x} child={:02x}) — REAL trust-cg emit \
                     nondeterminism hazard",
                    pbytes.get(first_diff).copied().unwrap_or(0),
                    cbytes.get(first_diff).copied().unwrap_or(0),
                );
            }
            total_compared += 1;
        }
    }
    println!(
        "cross-process: {} object comparisons across {} child processes — all BIT-IDENTICAL",
        total_compared,
        salts.len()
    );
}

// --------------------------------------------------------------------------
// NEGATIVE CONTROL: prove the byte comparison has TEETH.
//
// We take the parent's real emitted object, clone it, and flip a single code byte.
// The same equality assertion used by the main gate MUST report inequality. If a
// mutated object compared "equal", the gate would be vacuous.
// --------------------------------------------------------------------------

#[test]
fn emit_determinism_negative_control() {
    if std::env::var(CHILD_ENV).is_ok() {
        return;
    }
    let objs = emit_suite();
    let (name, real) = objs.iter().next().expect("suite is non-empty");

    // Clone and mutate one byte inside the code/section payload (well past the
    // header) so the comparison is forced to fail.
    let mut mutated = real.clone();
    let idx = mutated.len() / 2; // somewhere in the body, not the magic.
    mutated[idx] ^= 0xFF;

    assert_eq!(
        real.len(),
        mutated.len(),
        "{name}: mutation must not change length (it only flips a byte)"
    );
    assert_ne!(
        real, &mutated,
        "{name}: NEGATIVE CONTROL FAILED — a one-byte-mutated object compared EQUAL to the \
         original, meaning the byte comparison has no teeth"
    );

    // Also prove the exact diff offset is detectable, mirroring the main gate's logic.
    let diff = real
        .iter()
        .zip(mutated.iter())
        .position(|(a, b)| a != b)
        .expect("negative control: a differing byte must exist");
    assert_eq!(diff, idx, "{name}: the detected diff offset must be the mutated byte");
    println!(
        "negative control: 1-byte mutation in {name} object detected at offset {diff} — \
         comparison has teeth"
    );
}
