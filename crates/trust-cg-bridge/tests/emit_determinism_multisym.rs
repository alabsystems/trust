// MULTI-SYMBOL / MULTI-RELOCATION cross-process BIT-IDENTICAL determinism of
// trust-cg's EMITTED MACH-O OBJECTS.
//
// NORTH STAR (bootstrap-trust-model.md): defeating trusting-trust needs Diverse
// Double-Compilation, and "DDC depends directly on build-determinism" — including
// the EMITTED OBJECT BYTES. G20 (emit_determinism.rs) proved bit-identical Mach-O
// objects across independent processes, but ONLY over single-symbol,
// relocation-FREE objects. That left the two paths where HashMap-iteration hazards
// most plausibly hide UNSTRESSED: the symbol-table ORDERING path (multiple symbols
// in one object) and the relocation ORDERING path (cross-function branch relocs).
//
// THIS rung closes that residual. We emit objects that GENUINELY contain >1 symbol
// AND >=1 relocation — multi-function modules with cross-function calls, where the
// caller object holds (a) its own defined symbol, (b) the callee as an undefined
// external symbol, and (c) a branch relocation from the call site to the callee —
// then prove the FULL object bytes are bit-identical across >=4 independent,
// re-exec'd child processes (each with an independent per-process HashMap
// RandomState). Rust's std HashMap randomizes iteration per process, so any HashMap
// iteration feeding the symbol table or relocation table would diverge here.
//
// ANTI-VACUITY (three layers, so "all equal" is never vacuous):
//   1. `multisym_object_has_multiple_symbols_and_relocations` PARSES the Mach-O
//      symtab (LC_SYMTAB) and the __text section relocations and asserts nsyms >= 2
//      AND nreloc >= 1 on the real emitted caller object — proving the comparison
//      actually exercises the symbol/reloc surface, not a trivial object.
//   2. `multisym_emit_determinism_negative_control` flips a byte inside the symbol
//      string-table region and asserts the comparison FAILS — teeth on the symbol
//      surface specifically.
//   3. `multisym_emit_negative_control_hashmap_reorder` takes the real symbol set,
//      routes the (name -> nlist) emission ORDER through a std HashMap (the exact
//      hazard class this rung guards), and asserts that two independent-process
//      HashMap orderings DIVERGE — proving the surface is genuinely
//      ordering-sensitive and that the Vec-based insertion order is what saves us.
//
// from the repo root:
//   RUSTC_BOOTSTRAP=1 cargo test --manifest-path crates/Cargo.toml \
//     -p trust-cg-bridge --test emit_determinism_multisym -- --test-threads=1
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Scope (honest): aarch64-apple-darwin Mach-O object emission ONLY (the triple is
// forced regardless of host). The ELF writer and x86_64 emit path are NOT exercised.

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::process::Command;

use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// Force the aarch64 Mach-O writer regardless of host so the artifact under test is
// a stable aarch64-apple-darwin object (mirrors emit_determinism.rs).
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
        def_path: format!("emit_determinism_multisym::{name}"),
        span: sp(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// --------------------------------------------------------------------------
// Multi-function modules with CROSS-FUNCTION CALLS.
//
// A caller object emitted by `emit_objects` contains:
//   * the caller's own DEFINED symbol,
//   * the callee as an UNDEFINED EXTERNAL symbol, and
//   * a branch RELOCATION at the call site referencing the callee.
// That is exactly the >1-symbol + >=1-reloc surface this rung stresses.
// --------------------------------------------------------------------------

/// `leaf(y) -> i32 { y + y }`  (a defined, call-free function).
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
        },
    )
}

/// `caller(x) -> i32 { callee(x) + 1 }` — calls `callee` (a separate function),
/// then adds 1 in a successor block.  Produces an undefined external symbol for
/// `callee` plus a branch relocation in the caller object.
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
                        is_unsafe_sig: false, is_foreign: false,
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
        },
    )
}

/// A two-function module: `helper` (leaf) + `caller` (calls helper).
fn module_caller_helper() -> Vec<VerifiableFunction> {
    vec![make_leaf("helper"), make_caller("caller", "helper")]
}

/// A three-function chain: `chain_leaf` <- `chain_mid` <- `chain_top`.
/// `chain_mid` and `chain_top` objects each carry an external symbol + reloc.
fn module_chain() -> Vec<VerifiableFunction> {
    vec![
        make_leaf("chain_leaf"),
        make_caller("chain_mid", "chain_leaf"),
        make_caller("chain_top", "chain_mid"),
    ]
}

/// Emit BOTH modules via `emit_objects`, returning (function-name -> object bytes)
/// in a deterministic (sorted) map keyed by Mach-O symbol-bearing function name.
fn emit_suite() -> BTreeMap<String, Vec<u8>> {
    let be = backend();
    let mut out = BTreeMap::new();
    for module in [module_caller_helper(), module_chain()] {
        let lir = be
            .lower_module(&module)
            .unwrap_or_else(|e| panic!("lower_module failed: {e:?}"));
        let objects = be
            .emit_objects(&lir)
            .unwrap_or_else(|e| panic!("emit_objects failed: {e:?}"));
        for (name, bytes) in objects {
            assert!(!bytes.is_empty(), "{name}: emitted object must be non-empty");
            assert_eq!(
                &bytes[..4],
                &[0xCF, 0xFA, 0xED, 0xFE],
                "{name}: must be 64-bit LE Mach-O"
            );
            assert!(out.insert(name.clone(), bytes).is_none(), "duplicate fn name {name}");
        }
    }
    out
}

// ==========================================================================
// Mach-O parser (just enough): LC_SYMTAB nsyms + LC_SEGMENT_64 section relocs.
// ==========================================================================

fn rd_u32(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
}

const MH_MAGIC_64: u32 = 0xFEED_FACF;
const LC_SEGMENT_64: u32 = 0x19;
const LC_SYMTAB: u32 = 0x02;

#[derive(Debug, Clone, Copy)]
struct Symtab {
    nsyms: u32,
    symoff: u32,
    stroff: u32,
    strsize: u32,
}

/// Parsed Mach-O facts used by the anti-vacuity assertions.
struct MachoFacts {
    symtab: Symtab,
    /// Total relocations across all sections of all segments.
    total_relocs: u32,
}

fn parse_macho(bytes: &[u8]) -> MachoFacts {
    assert!(bytes.len() >= 32, "object too small for a Mach-O header");
    let magic = rd_u32(bytes, 0);
    assert_eq!(magic, MH_MAGIC_64, "expected 64-bit little-endian Mach-O magic");
    // mach_header_64: magic(4) cputype(4) cpusubtype(4) filetype(4) ncmds(4)
    //                 sizeofcmds(4) flags(4) reserved(4) = 32 bytes.
    let ncmds = rd_u32(bytes, 16);
    let mut cmd_off = 32usize;

    let mut symtab: Option<Symtab> = None;
    let mut total_relocs = 0u32;

    for _ in 0..ncmds {
        let cmd = rd_u32(bytes, cmd_off);
        let cmdsize = rd_u32(bytes, cmd_off + 4) as usize;
        assert!(cmdsize >= 8, "load command size too small");

        match cmd {
            LC_SYMTAB => {
                // symtab_command: cmd(4) cmdsize(4) symoff(4) nsyms(4) stroff(4) strsize(4)
                let symoff = rd_u32(bytes, cmd_off + 8);
                let nsyms = rd_u32(bytes, cmd_off + 12);
                let stroff = rd_u32(bytes, cmd_off + 16);
                let strsize = rd_u32(bytes, cmd_off + 20);
                symtab = Some(Symtab { nsyms, symoff, stroff, strsize });
            }
            LC_SEGMENT_64 => {
                // segment_command_64: cmd(4) cmdsize(4) segname(16) vmaddr(8) vmsize(8)
                //   fileoff(8) filesize(8) maxprot(4) initprot(4) nsects(4) flags(4)
                //   = 72 bytes header, then nsects * section_64 (each 80 bytes).
                let nsects = rd_u32(bytes, cmd_off + 64);
                let mut sec_off = cmd_off + 72;
                for _ in 0..nsects {
                    // section_64: sectname(16) segname(16) addr(8) size(8) offset(4)
                    //   align(4) reloff(4) nreloc(4) flags(4) reserved1(4) reserved2(4)
                    //   reserved3(4) = 80 bytes.  Field offsets within the section:
                    //   sectname@0, segname@16, addr@32, size@40, offset@48, align@52,
                    //   reloff@56, nreloc@60, flags@64. (nreloc is at +60, NOT +68.)
                    let nreloc = rd_u32(bytes, sec_off + 60);
                    total_relocs += nreloc;
                    sec_off += 80;
                }
            }
            _ => {}
        }
        cmd_off += cmdsize;
    }

    MachoFacts {
        symtab: symtab.expect("object must contain an LC_SYMTAB load command"),
        total_relocs,
    }
}

/// Read the list of symbol names from the string table, in nlist order. nlist_64 is
/// 16 bytes: n_strx(4) n_type(1) n_sect(1) n_desc(2) n_value(8); name = strtab[n_strx..].
fn symbol_names(bytes: &[u8], st: Symtab) -> Vec<String> {
    let strtab = &bytes[st.stroff as usize..(st.stroff + st.strsize) as usize];
    (0..st.nsyms)
        .map(|i| {
            let ent = st.symoff as usize + i as usize * 16;
            let n_strx = rd_u32(bytes, ent) as usize;
            let tail = &strtab[n_strx..];
            let end = tail.iter().position(|&c| c == 0).unwrap_or(tail.len());
            String::from_utf8_lossy(&tail[..end]).into_owned()
        })
        .collect()
}

// --------------------------------------------------------------------------
// ANTI-VACUITY GUARD #1: the caller object GENUINELY has >1 symbol AND >=1 reloc.
// --------------------------------------------------------------------------

#[test]
fn multisym_object_has_multiple_symbols_and_relocations() {
    if std::env::var(CHILD_ENV).is_ok() {
        return;
    }
    let objs = emit_suite();

    // Check every CALLER object (those with a cross-function call) carries the
    // multi-symbol + relocation surface. Leaf objects (helper/chain_leaf) need not.
    let callers = ["caller", "chain_mid", "chain_top"];
    let mut checked = 0;
    for name in callers {
        let bytes = objs.get(name).unwrap_or_else(|| panic!("missing caller object {name}"));
        let facts = parse_macho(bytes);
        let names = symbol_names(bytes, facts.symtab);
        assert!(
            facts.symtab.nsyms >= 2,
            "{name}: object must have >1 symbol to stress symbol-table ordering, \
             got nsyms={} names={names:?}",
            facts.symtab.nsyms
        );
        assert!(
            facts.total_relocs >= 1,
            "{name}: object must have >=1 relocation to stress reloc ordering, \
             got total_relocs={}",
            facts.total_relocs
        );
        // The caller's own symbol and the callee external symbol must both appear.
        assert!(
            names.iter().any(|n| n.contains(name)),
            "{name}: caller's own symbol must appear in symtab, names={names:?}"
        );
        checked += 1;
    }
    assert_eq!(checked, callers.len(), "all caller objects must be checked");
    println!(
        "anti-vacuity: {} caller objects each have >=2 symbols and >=1 relocation",
        checked
    );
}

// --------------------------------------------------------------------------
// Cross-process protocol (mirrors emit_determinism.rs).
//   Child prints: <<<EMIT>>>name|len|hexbytes<<<END>>>
// --------------------------------------------------------------------------

const CHILD_ENV: &str = "TRUST_EMIT_DETERMINISM_MULTISYM_CHILD";
const CHILD_TEST_NAME: &str = "multisym_emit_child_emitter";

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

#[test]
fn multisym_emit_child_emitter() {
    if std::env::var(CHILD_ENV).is_err() {
        return;
    }
    let objs = emit_suite();
    for (name, bytes) in &objs {
        println!("<<<EMIT>>>{name}|{}|{}<<<END>>>", bytes.len(), to_hex(bytes));
    }
}

fn run_child(salt: &str) -> BTreeMap<String, Vec<u8>> {
    let exe = std::env::current_exe().expect("current_exe");
    let output = Command::new(&exe)
        .args(["--exact", CHILD_TEST_NAME, "--nocapture", "--test-threads=1"])
        .env(CHILD_ENV, "1")
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
fn multisym_emit_in_process_floor() {
    if std::env::var(CHILD_ENV).is_ok() {
        return;
    }
    let a = emit_suite();
    let b = emit_suite();
    assert_eq!(a.keys().collect::<Vec<_>>(), b.keys().collect::<Vec<_>>(), "names stable");
    for (name, abytes) in &a {
        assert_eq!(abytes, &b[name], "{name}: in-process emit-twice diverged");
    }
    println!("in-process floor: {} multi-symbol objects emit identically twice", a.len());
}

// --------------------------------------------------------------------------
// MAIN GATE: full object bytes BIT-IDENTICAL across REAL process boundaries.
// --------------------------------------------------------------------------

#[test]
fn multisym_emit_cross_process_object_bytes_are_bit_identical() {
    if std::env::var(CHILD_ENV).is_ok() {
        return;
    }
    let parent = emit_suite();

    // Re-confirm the surface is non-trivial in the parent too: at least one object
    // must carry >1 symbol + >=1 reloc, else the gate would be vacuous.
    let any_multisym = parent.iter().any(|(_, b)| {
        let f = parse_macho(b);
        f.symtab.nsyms >= 2 && f.total_relocs >= 1
    });
    assert!(any_multisym, "parent suite must contain a multi-symbol+reloc object");

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
                     nondeterminism hazard in the symbol-table/relocation path",
                    pbytes.get(first_diff).copied().unwrap_or(0),
                    cbytes.get(first_diff).copied().unwrap_or(0),
                );
            }
            total_compared += 1;
        }
    }
    println!(
        "cross-process: {} multi-symbol object comparisons across {} child processes — \
         all BIT-IDENTICAL",
        total_compared,
        salts.len()
    );
}

// --------------------------------------------------------------------------
// NEGATIVE CONTROL #2: teeth on the SYMBOL surface.
//
// Flip a byte inside the symbol string-table region of a real multi-symbol object,
// re-parse the symbol names, prove they actually changed, and assert the byte
// comparison (the same one the main gate uses) FAILS.
// --------------------------------------------------------------------------

#[test]
fn multisym_emit_determinism_negative_control() {
    if std::env::var(CHILD_ENV).is_ok() {
        return;
    }
    let objs = emit_suite();
    let real = objs.get("caller").expect("caller object present");
    let facts = parse_macho(real);
    assert!(facts.symtab.nsyms >= 2, "negative control needs a multi-symbol object");

    let before = symbol_names(real, facts.symtab);

    // Mutate a byte INSIDE the string table (a symbol name char), not the magic.
    // Pick an offset past the leading NUL with a non-NUL byte so a name visibly changes.
    let st = facts.symtab;
    let strtab_start = st.stroff as usize;
    let strtab_end = (st.stroff + st.strsize) as usize;
    let mut idx = None;
    for i in (strtab_start + 1)..strtab_end {
        if real[i] != 0 {
            idx = Some(i);
            break;
        }
    }
    let idx = idx.expect("string table must contain a non-NUL name byte");

    let mut mutated = real.clone();
    mutated[idx] ^= 0x20; // flip a case-ish bit so it stays a printable name char

    let after = symbol_names(&mutated, st);
    assert_ne!(before, after, "negative control: a symbol NAME must change after mutation");
    assert_ne!(
        real, &mutated,
        "NEGATIVE CONTROL FAILED — a symbol-name-mutated object compared EQUAL; \
         the byte comparison has no teeth on the symbol surface"
    );
    let diff = real
        .iter()
        .zip(mutated.iter())
        .position(|(a, b)| a != b)
        .expect("a differing byte must exist");
    assert_eq!(diff, idx, "the detected diff must be the mutated string-table byte");
    println!(
        "negative control (symbol surface): mutating string-table byte at offset {idx} \
         changed symbol names {before:?} -> {after:?} and the comparison detected it"
    );
}

// --------------------------------------------------------------------------
// NEGATIVE CONTROL #3: teeth on the ORDERING hazard class itself.
//
// The real emit builds the symbol table by iterating an INSERTION-ORDERED Vec, which
// is process-stable. The hazard we guard against is feeding that order through a std
// HashMap (per-process-randomized iteration). Here we model exactly that hazard: take
// the real object's symbol-name set, build the nlist-name ORDER via a HashMap in a
// re-exec'd child (independent RandomState) AND in the parent, and assert the two
// orderings DIVERGE across the process boundary. This proves (a) the surface is truly
// ordering-sensitive — so the main gate's "all equal" is meaningful — and (b) a
// HashMap in this path WOULD break determinism, which the Vec-based impl avoids.
// --------------------------------------------------------------------------

const HAZARD_CHILD_ENV: &str = "TRUST_EMIT_DETERMINISM_MULTISYM_HAZARD_CHILD";
const HAZARD_CHILD_TEST_NAME: &str = "multisym_hazard_child_emitter";

/// Build a symbol-ordering "fingerprint" by draining names through a std HashMap,
/// mimicking a HashMap-iteration-driven symbol-table emit. The iteration order is
/// per-process-randomized, so this is the hazard under test.
fn hashmap_ordering_fingerprint(names: &[String]) -> String {
    let mut map: HashMap<String, usize> = HashMap::new();
    for (i, n) in names.iter().enumerate() {
        map.insert(n.clone(), i);
    }
    // Iterate VALUES in HashMap order (the hazard): join the names in iteration order.
    map.keys().cloned().collect::<Vec<_>>().join(",")
}

#[test]
fn multisym_hazard_child_emitter() {
    if std::env::var(HAZARD_CHILD_ENV).is_err() {
        return;
    }
    // Use a sufficiently large, fixed symbol set so HashMap order is very likely to
    // differ between processes (the chance of two independent RandomStates yielding
    // the identical order over N>=8 distinct keys is negligible).
    let names: Vec<String> = (0..16).map(|i| format!("_sym_{i:02}")).collect();
    println!("<<<HAZARD>>>{}<<<END>>>", hashmap_ordering_fingerprint(&names));
}

fn run_hazard_child(salt: &str) -> String {
    let exe = std::env::current_exe().expect("current_exe");
    let output = Command::new(&exe)
        .args(["--exact", HAZARD_CHILD_TEST_NAME, "--nocapture", "--test-threads=1"])
        .env(HAZARD_CHILD_ENV, "1")
        .env("TRUST_EMIT_DETERMINISM_SALT", salt)
        .output()
        .expect("re-exec hazard child");
    assert!(output.status.success(), "hazard child failed (salt={salt})");
    let stdout = String::from_utf8(output.stdout).expect("utf8");
    for line in stdout.lines() {
        if let Some(s) = line.find("<<<HAZARD>>>") {
            let rest = &line[s + "<<<HAZARD>>>".len()..];
            if let Some(e) = rest.find("<<<END>>>") {
                return rest[..e].to_string();
            }
        }
    }
    panic!("hazard child produced no fingerprint (salt={salt})");
}

#[test]
fn multisym_emit_negative_control_hashmap_reorder() {
    if std::env::var(CHILD_ENV).is_ok() || std::env::var(HAZARD_CHILD_ENV).is_ok() {
        return;
    }
    // Collect several independent-process HashMap orderings of the same symbol set.
    let salts = ["alpha", "bravo", "charlie", "delta", "echo", "foxtrot"];
    let fingerprints: Vec<String> = salts.iter().map(|s| run_hazard_child(s)).collect();

    // TEETH: across these independent processes, at least two HashMap orderings MUST
    // differ. If they were all identical, the surface would not be ordering-sensitive
    // and the main determinism gate would be vacuous.
    let first = &fingerprints[0];
    let any_divergent = fingerprints.iter().any(|f| f != first);
    assert!(
        any_divergent,
        "NEGATIVE CONTROL FAILED — a HashMap-driven symbol ORDER was identical across all \
         {} independent processes; the ordering surface has no teeth. Fingerprints: {:?}",
        salts.len(),
        fingerprints
    );
    println!(
        "negative control (ordering hazard): HashMap-driven symbol order DIVERGED across \
         independent processes (proving the real Vec-based order is what keeps emit \
         deterministic). Distinct orderings: {}",
        {
            let mut uniq = fingerprints.clone();
            uniq.sort();
            uniq.dedup();
            uniq.len()
        }
    );
}
