// module_object_internal_linkage.rs — ONE OBJECT PER CGU + the merge obligation.
//
// WHAT IS BEING ESTABLISHED
// -------------------------
// `Internal`-linkage mono-items (which every program calling `core` produces:
// `u64::from(u8)`, `wrapping_add`, `rotate_left`, ...) must be emitted as
// object-LOCAL symbols. A local symbol is unreachable from any other object, so
// the historical one-object-per-FUNCTION emission could not represent one at
// all. The fix merges each codegen unit into ONE object.
//
// The proven-output gate verifies each function in ISOLATION, over the exact
// bytes of a SINGLE-function object. Merging must therefore not be allowed to
// silently invalidate those proofs. This file pins the two properties that make
// the merge safe:
//
//   1. BYTE PRESERVATION — for every function, the merged object carries that
//      function's single-object machine code VERBATIM, at the offset the merged
//      object's OWN SYMBOL TABLE assigns it. (This is the obligation
//      `verify_output::emit_module_object_verified_reported_with_backend`
//      discharges as a refusal; here it is recomputed independently.)
//   2. LOCAL BINDING — a function marked `FunctionLinkage::Internal` is emitted
//      as a Mach-O local symbol (no `N_EXT`), while its `External` siblings keep
//      `N_EXT`, and the intra-object call to the local callee still resolves.
//
// ANTI-VACUITY (three layers, so "the bytes match" is never trivially true):
//   * `merged_object_is_genuinely_merged` asserts the merged object holds >1
//      defined text symbol at DISTINCT offsets, at least one of them non-zero,
//      and merged text strictly longer than any single function's text — so the
//      windows compared below are real, different, non-degenerate slices.
//   * `negative_control_corrupted_merge_is_detected` flips one instruction byte
//      inside the merged text and asserts the byte-preservation comparison then
//      FAILS. A check that cannot fail proves nothing.
//   * `negative_control_local_binding_is_observable` asserts the SAME module
//      emitted with `External` bindings has NO local text symbol — so the local
//      partition observed in the positive test is caused by the binding, not by
//      something the writer does anyway.
//
// Scope (honest): aarch64-apple-darwin Mach-O only. The ELF path carries the
// same binding channel but is not exercised here; the x86-64 emitters do not
// carry it at all and fail closed on a non-`Global` binding.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeMap;

use trust_cg_bridge::codegen_backend::{
    CompiledModule, FunctionLinkage, TrustCgCodegenBackend, TrustCgTargetArch,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

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
        def_path: format!("module_object_internal_linkage::{name}"),
        span: sp(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `name(y) -> i32 { y + y }` — a call-free leaf.
fn make_leaf(name: &str) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("y".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: sp(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
    )
}

/// `name(x) -> i32 { callee(x) + 1 }` — an intra-module direct call.
fn make_caller(name: &str, callee: &str) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("r".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                        func: callee.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: sp(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
    )
}

/// The module under test: an internalized leaf, a caller of it, and a second
/// exported leaf, so the object mixes local and global definitions.
fn module_functions() -> Vec<VerifiableFunction> {
    vec![
        make_leaf("cgu_helper"),
        make_caller("cgu_caller", "cgu_helper"),
        make_leaf("cgu_exported"),
    ]
}

fn compiled_module(linkage: Vec<FunctionLinkage>) -> CompiledModule {
    let backend = backend();
    let funcs = module_functions();
    let lir_functions = funcs
        .iter()
        .map(|func| backend.lower_function(func).expect("module function should lower"))
        .collect::<Vec<_>>();
    let function_count = lir_functions.len();
    CompiledModule {
        name: "internal_linkage.codegen_unit.0".to_string(),
        lir_functions,
        object_path: None,
        function_count,
        source_functions: Some(funcs),
        linkage,
    }
}

// ---------------------------------------------------------------------------
// Minimal, independent Mach-O readers. These deliberately do NOT call the
// writer's own encoders: the point is to read back what the SHIPPED bytes say.
// ---------------------------------------------------------------------------

fn rd_u32(obj: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(obj[off..off + 4].try_into().expect("4 bytes"))
}

fn rd_u64(obj: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(obj[off..off + 8].try_into().expect("8 bytes"))
}

/// `(text bytes, text vmaddr, __text section ordinal)`.
fn macho_text(obj: &[u8]) -> (Vec<u8>, u64, u8) {
    assert_eq!(rd_u32(obj, 0), 0xfeed_facf, "expected a 64-bit Mach-O object");
    let ncmds = rd_u32(obj, 16);
    let mut cmd_off = 32usize;
    let mut ordinal = 0u8;
    for _ in 0..ncmds {
        let cmd = rd_u32(obj, cmd_off);
        let cmdsize = rd_u32(obj, cmd_off + 4) as usize;
        if cmd == 0x19 {
            let nsects = rd_u32(obj, cmd_off + 64);
            let mut sec = cmd_off + 72;
            for _ in 0..nsects {
                ordinal += 1;
                if obj[sec..sec + 16].starts_with(b"__text\0") {
                    let addr = rd_u64(obj, sec + 32);
                    let size = rd_u64(obj, sec + 40) as usize;
                    let offset = rd_u32(obj, sec + 48) as usize;
                    return (obj[offset..offset + size].to_vec(), addr, ordinal);
                }
                sec += 80;
            }
        }
        cmd_off += cmdsize;
    }
    panic!("emitted object has no __text section");
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TextSymbol {
    offset: u64,
    is_global: bool,
}

/// Defined `__text` symbols, keyed by IR-level name (Mach-O `_` stripped).
fn macho_text_symbols(obj: &[u8]) -> BTreeMap<String, TextSymbol> {
    const N_EXT: u8 = 0x01;
    const N_TYPE: u8 = 0x0e;
    const N_SECT: u8 = 0x0e;

    let (_, text_base, text_ordinal) = macho_text(obj);
    let ncmds = rd_u32(obj, 16);
    let mut cmd_off = 32usize;
    let mut symtab = None;
    for _ in 0..ncmds {
        let cmd = rd_u32(obj, cmd_off);
        let cmdsize = rd_u32(obj, cmd_off + 4) as usize;
        if cmd == 0x02 {
            symtab = Some((
                rd_u32(obj, cmd_off + 8) as usize,
                rd_u32(obj, cmd_off + 12) as usize,
                rd_u32(obj, cmd_off + 16) as usize,
                rd_u32(obj, cmd_off + 20) as usize,
            ));
        }
        cmd_off += cmdsize;
    }
    let (symoff, nsyms, stroff, strsize) = symtab.expect("emitted object has no LC_SYMTAB");
    let strings = &obj[stroff..stroff + strsize];

    let mut found = BTreeMap::new();
    for index in 0..nsyms {
        let entry = symoff + index * 16;
        let n_strx = rd_u32(obj, entry) as usize;
        let n_type = obj[entry + 4];
        let n_sect = obj[entry + 5];
        let n_value = rd_u64(obj, entry + 8);
        if n_type & N_TYPE != N_SECT || n_sect != text_ordinal {
            continue;
        }
        let tail = &strings[n_strx..];
        let end = tail.iter().position(|b| *b == 0).expect("NUL-terminated symbol name");
        let name = std::str::from_utf8(&tail[..end]).expect("UTF-8 symbol name");
        let name = name.strip_prefix('_').unwrap_or(name).to_string();
        found.insert(
            name,
            TextSymbol { offset: n_value - text_base, is_global: n_type & N_EXT != 0 },
        );
    }
    found
}

/// Emit each function ALONE — the exact artifact shape the per-function gate
/// verifies. A single-function object's whole `__text` IS that function's code.
fn single_function_texts() -> BTreeMap<String, Vec<u8>> {
    let backend = backend();
    module_functions()
        .iter()
        .map(|func| {
            let lir = backend.lower_function(func).expect("function should lower");
            let obj = backend.emit_object(&[lir]).expect("single-function object should emit");
            (func.name.clone(), macho_text(&obj).0)
        })
        .collect()
}

fn emit_merged(linkage: Vec<FunctionLinkage>) -> Vec<u8> {
    backend()
        .emit_module_object(&compiled_module(linkage))
        .expect("whole-module object should emit")
        .bytes
}

/// The obligation itself, recomputed here from the shipped bytes alone.
fn merge_preserves_bytes(merged: &[u8], singles: &BTreeMap<String, Vec<u8>>) -> Result<(), String> {
    let (merged_text, _, _) = macho_text(merged);
    let symbols = macho_text_symbols(merged);
    for (name, verified) in singles {
        let symbol = symbols
            .get(name)
            .ok_or_else(|| format!("merged object defines no text symbol for `{name}`"))?;
        let start = symbol.offset as usize;
        let end = start + verified.len();
        let window = merged_text
            .get(start..end)
            .ok_or_else(|| format!("`{name}` symbol points past the merged text section"))?;
        if window != verified.as_slice() {
            return Err(format!(
                "`{name}` bytes at merged text offset {start} are not the verified bytes"
            ));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// ANTI-VACUITY 1: the merged object really merges.
// ---------------------------------------------------------------------------

#[test]
fn merged_object_is_genuinely_merged() {
    let merged = emit_merged(vec![FunctionLinkage::External; 3]);
    let (merged_text, _, _) = macho_text(&merged);
    let symbols = macho_text_symbols(&merged);

    for name in ["cgu_helper", "cgu_caller", "cgu_exported"] {
        assert!(
            symbols.contains_key(name),
            "merged object should define `{name}`; got {symbols:?}"
        );
    }

    let offsets: Vec<u64> = symbols.values().map(|symbol| symbol.offset).collect();
    let mut distinct = offsets.clone();
    distinct.sort_unstable();
    distinct.dedup();
    assert_eq!(distinct.len(), offsets.len(), "merged functions must occupy distinct offsets");
    assert!(
        offsets.iter().any(|offset| *offset > 0),
        "at least one function must NOT sit at offset 0, or the byte-preservation \
         windows are all the same slice"
    );

    let singles = single_function_texts();
    let longest = singles.values().map(|text| text.len()).max().expect("three functions");
    assert!(
        merged_text.len() > longest,
        "merged text ({} bytes) must exceed the longest single function ({longest} bytes)",
        merged_text.len()
    );
}

// ---------------------------------------------------------------------------
// PROPERTY 1: byte preservation across the merge.
// ---------------------------------------------------------------------------

#[test]
fn merge_preserves_every_verified_function_byte_for_byte() {
    let singles = single_function_texts();
    let merged = emit_merged(vec![FunctionLinkage::External; 3]);
    merge_preserves_bytes(&merged, &singles).expect("all-External merge must preserve bytes");
}

#[test]
fn merge_preserves_bytes_with_internal_linkage_too() {
    // Symbol binding is a symbol-table attribute; it must not perturb a single
    // instruction byte. This is what lets the per-function proofs — taken over
    // objects emitted WITHOUT bindings — transfer to the merged artifact.
    let singles = single_function_texts();
    let merged = emit_merged(vec![
        FunctionLinkage::Internal,
        FunctionLinkage::Internal,
        FunctionLinkage::External,
    ]);
    merge_preserves_bytes(&merged, &singles).expect("mixed-linkage merge must preserve bytes");
}

// ---------------------------------------------------------------------------
// ANTI-VACUITY 2: the byte-preservation check has teeth.
// ---------------------------------------------------------------------------

#[test]
fn negative_control_corrupted_merge_is_detected() {
    let singles = single_function_texts();
    let merged = emit_merged(vec![FunctionLinkage::External; 3]);
    merge_preserves_bytes(&merged, &singles).expect("baseline merge must preserve bytes");

    // Flip one byte inside the LAST function's body (offset > 0), so the
    // corruption is genuinely inside a merged window rather than in padding.
    let symbols = macho_text_symbols(&merged);
    let last_offset = symbols.values().map(|symbol| symbol.offset).max().expect("symbols");
    let (_, _, text_ordinal) = macho_text(&merged);
    assert!(text_ordinal >= 1);

    let ncmds = rd_u32(&merged, 16);
    let mut cmd_off = 32usize;
    let mut text_file_offset = None;
    for _ in 0..ncmds {
        let cmd = rd_u32(&merged, cmd_off);
        let cmdsize = rd_u32(&merged, cmd_off + 4) as usize;
        if cmd == 0x19 {
            let nsects = rd_u32(&merged, cmd_off + 64);
            let mut sec = cmd_off + 72;
            for _ in 0..nsects {
                if merged[sec..sec + 16].starts_with(b"__text\0") {
                    text_file_offset = Some(rd_u32(&merged, sec + 48) as usize);
                }
                sec += 80;
            }
        }
        cmd_off += cmdsize;
    }
    let text_file_offset = text_file_offset.expect("__text file offset");

    let mut corrupted = merged.clone();
    let victim = text_file_offset + last_offset as usize;
    corrupted[victim] ^= 0xff;

    let error = merge_preserves_bytes(&corrupted, &singles)
        .expect_err("a corrupted merged object MUST fail the byte-preservation check");
    assert!(
        error.contains("are not the verified bytes"),
        "expected a byte-divergence diagnosis, got: {error}"
    );
}

// ---------------------------------------------------------------------------
// PROPERTY 2: Internal linkage really produces a LOCAL symbol.
// ---------------------------------------------------------------------------

#[test]
fn internal_linkage_emits_a_local_text_symbol() {
    let merged = emit_merged(vec![
        FunctionLinkage::Internal,
        FunctionLinkage::Internal,
        FunctionLinkage::External,
    ]);
    let symbols = macho_text_symbols(&merged);

    assert!(
        !symbols["cgu_helper"].is_global,
        "an Internal-linkage function must be emitted WITHOUT N_EXT (a Mach-O local)"
    );
    assert!(!symbols["cgu_caller"].is_global, "the Internal caller must also be local");
    assert!(
        symbols["cgu_exported"].is_global,
        "an External-linkage sibling in the SAME object must keep N_EXT"
    );
}

// ---------------------------------------------------------------------------
// ANTI-VACUITY 3: the local partition is caused by the binding.
// ---------------------------------------------------------------------------

#[test]
fn negative_control_local_binding_is_observable() {
    let merged = emit_merged(vec![FunctionLinkage::External; 3]);
    let symbols = macho_text_symbols(&merged);
    for (name, symbol) in &symbols {
        assert!(
            symbol.is_global,
            "with every binding External, `{name}` must be a GLOBAL text symbol; \
             otherwise the local partition observed elsewhere is not caused by the binding"
        );
    }
}

// ---------------------------------------------------------------------------
// THE POINT OF THE WHOLE EXERCISE: a LOCAL callee is still callable, and the
// object the system linker consumes actually links and RUNS.
//
// This is the property a per-function object split cannot have: `cgu_helper` is
// emitted with no `N_EXT`, so nothing outside this object can resolve it — the
// intra-object `bl` must be satisfied from inside the same artifact. We link the
// merged object against a C driver that calls only the EXPORTED entry point and
// assert the program computes the right answer.
//
//   cgu_caller(x) = cgu_helper(x) + 1 = (x + x) + 1
//   cgu_caller(20) = 41
// ---------------------------------------------------------------------------

fn is_macos_aarch64() -> bool {
    std::env::consts::OS == "macos" && std::env::consts::ARCH == "aarch64"
}

#[test]
fn local_callee_links_and_runs_through_the_system_linker() {
    if !is_macos_aarch64() {
        eprintln!("skipping: needs aarch64-apple-darwin (host is macos/aarch64 only)");
        return;
    }

    // `cgu_helper` INTERNAL (local), `cgu_caller` EXTERNAL (the entry point),
    // `cgu_exported` EXTERNAL.
    let merged = emit_merged(vec![
        FunctionLinkage::Internal,
        FunctionLinkage::External,
        FunctionLinkage::External,
    ]);

    // Precondition for the test to mean anything: the callee really is local.
    let symbols = macho_text_symbols(&merged);
    assert!(
        !symbols["cgu_helper"].is_global,
        "the callee must be a LOCAL symbol, or this test does not exercise local resolution"
    );
    assert!(symbols["cgu_caller"].is_global, "the entry point must be exported");

    let dir = tempfile::tempdir().expect("tempdir");
    let obj = dir.path().join("cgu.o");
    std::fs::write(&obj, &merged).expect("write object");

    let driver = dir.path().join("driver.c");
    std::fs::write(
        &driver,
        "#include <stdio.h>\n\
         int cgu_caller(int);\n\
         int main(void) { printf(\"%d\\n\", cgu_caller(20)); return 0; }\n",
    )
    .expect("write driver");

    let exe = dir.path().join("probe");
    let build = std::process::Command::new("cc")
        .arg(&driver)
        .arg(&obj)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("cc should be runnable on macOS");
    assert!(
        build.status.success(),
        "linking the merged object with a LOCAL callee must succeed; cc said:\n{}",
        String::from_utf8_lossy(&build.stderr)
    );

    let run = std::process::Command::new(&exe).output().expect("run the linked program");
    assert!(run.status.success(), "the linked program must run");
    assert_eq!(
        String::from_utf8_lossy(&run.stdout).trim(),
        "41",
        "cgu_caller(20) must be cgu_helper(20) + 1 = 41, proving the LOCAL callee \
         was resolved inside the merged object"
    );
}

/// TEETH for the test above: the local symbol must NOT be resolvable from
/// another object. If it were, the local binding would be cosmetic and the
/// merge would not actually be load-bearing.
#[test]
fn local_callee_is_not_resolvable_from_outside_the_object() {
    if !is_macos_aarch64() {
        eprintln!("skipping: needs aarch64-apple-darwin");
        return;
    }

    let merged = emit_merged(vec![
        FunctionLinkage::Internal,
        FunctionLinkage::External,
        FunctionLinkage::External,
    ]);

    let dir = tempfile::tempdir().expect("tempdir");
    let obj = dir.path().join("cgu.o");
    std::fs::write(&obj, &merged).expect("write object");

    let driver = dir.path().join("driver.c");
    std::fs::write(&driver, "int cgu_helper(int);\nint main(void) { return cgu_helper(1); }\n")
        .expect("write driver");

    let exe = dir.path().join("probe");
    let build = std::process::Command::new("cc")
        .arg(&driver)
        .arg(&obj)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("cc should be runnable on macOS");
    assert!(
        !build.status.success(),
        "an Internal-linkage definition MUST be invisible outside its object; \
         the link unexpectedly succeeded"
    );
    let stderr = String::from_utf8_lossy(&build.stderr);
    assert!(
        stderr.contains("cgu_helper"),
        "the link failure must name the unresolved local symbol; got:\n{stderr}"
    );
}

// ---------------------------------------------------------------------------
// A mis-indexed binding vector must fail closed rather than mis-bind symbols.
// ---------------------------------------------------------------------------

#[test]
fn mismatched_linkage_vector_is_refused() {
    let module = compiled_module(vec![FunctionLinkage::Internal]);
    let error = backend()
        .emit_module_object(&module)
        .expect_err("a 1-entry linkage vector for a 3-function module must be refused");
    let rendered = format!("{error:?}");
    assert!(
        rendered.contains("linkage entries"),
        "expected a mis-indexed-linkage refusal, got: {rendered}"
    );
}
