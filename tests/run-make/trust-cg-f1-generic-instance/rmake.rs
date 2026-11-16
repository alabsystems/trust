//! Trust (step 2 increment 3, `docs/plans/2026-09-29-trust-ir-sole-compile-path.md`): code
//! generation from trust-ir for a crate that calls a GENERIC function, on the opt-in
//! `-Ztrust-cg-frontend=trust-ir` lane — the first generic Rust compiled with no MIR on its
//! codegen path.
//!
//! BEFORE (measured on stage1 `a99adf74c3` and again on `086c4da249`), SUBJECT A exited 1 and
//! wrote no rlib: `0/2 reachable function(s) completed`, `ident::<u64>` refused
//! `[generic-instance]` and `f` refused `[converter-refused]` (an unsupported `Call` to the
//! bodyless declaration `ident`). SUBJECT B gave `2/5`.
//!
//! AFTER: the instance lane lowers `ident::<u64>` at its arguments, SPLICES the body into the
//! codegen module, RELINKS `f`'s call edge to it, the leaf inliner removes the call and the
//! strict proven-output gate proves both functions. The objects are linked into a C program and
//! RUN: a gate verdict about bytes nobody executes proves only that the gate agrees with itself.
//!
//! Every CONTRAST below is a refusal the lane must keep making, and each one names why.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::macho::ARM64_RELOC_BRANCH26;
use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::{Object, ObjectSection, ObjectSymbol, RelocationFlags};
use run_make_support::{cc, rfs, run, rust_lib_name, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

const SUBJECT_A: &str = r#"#![crate_name = "inc3_subject"]
#[inline(never)]
fn ident<T>(x: T) -> T { x }
#[unsafe(no_mangle)]
pub extern "C" fn f(x: u64) -> u64 { ident::<u64>(x) ^ 7 }
"#;

const MAIN_A: &str = r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t f(uint64_t);
int main(void){ uint64_t xs[4]={0,1,0x10,UINT64_MAX}; for(int i=0;i<4;i++) printf("%llu%s",(unsigned long long)f(xs[i]), i==3?"\n":" "); return 0; }
"#;

/// Two instantiations of one generic body must stay TWO bodies: a collapsed instance key would
/// make `h` print `0` instead of `8 ^ 16 = 24`.
const SUBJECT_B: &str = r#"#![crate_name = "subj_b"]
pub trait Tag { fn tag() -> u64; }
impl Tag for u8 { #[inline(never)] fn tag() -> u64 { 8 } }
impl Tag for u16 { #[inline(never)] fn tag() -> u64 { 16 } }
#[inline(never)] fn pick<T: Tag>() -> u64 { T::tag() }
#[unsafe(no_mangle)] pub extern "C" fn h() -> u64 { pick::<u8>() ^ pick::<u16>() }
"#;

const MAIN_B: &str = r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t h(void);
int main(void){ printf("%llu\n",(unsigned long long)h()); return 0; }
"#;

const COMPLETED: &str =
    "reachable function(s) completed source -> trust_ir_of -> lower_module_to_lir";

/// The goal's recipe: an rlib through trust-cg and the trust-ir frontend, one codegen unit,
/// the DEFAULT strict proven-output gate (no `-Ztrust-cg-output-gate` flag).
fn frontend(input: &str, out: &str, extra: &[&str]) -> run_make_support::Rustc {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input(input)
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .args(extra)
        .out_dir(out)
        // A run-make recipe is a new policy boundary: bootstrap's inherited
        // deauthorization override must not decide this subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

/// The one object member of `rlib`.
fn object_member(rlib: &str) -> Vec<u8> {
    let data = rfs::read(rlib);
    let archive = ArchiveFile::parse(&*data).expect("rlib is an archive");
    let mut objects = Vec::new();
    for member in archive.members() {
        let member = member.expect("archive member");
        // `lib.rmeta` is itself wrapped in an object file on this target; the codegen unit's
        // member is the one `.o`.
        if !member.name().ends_with(b".o") {
            continue;
        }
        let bytes = member.data(&*data).expect("member data");
        assert!(run_make_support::object::File::parse(bytes).is_ok(), "the `.o` member parses");
        objects.push(bytes.to_vec());
    }
    assert_eq!(objects.len(), 1, "one codegen unit, one object");
    objects.pop().unwrap()
}

/// `_f` is defined and external, `ident::<u64>` is defined under its mangled symbol and is not
/// external, and `__text` carries no `ARM64_RELOC_BRANCH26`: the spliced callee was inlined, so
/// there is no real call.
fn inspect_subject_a(object: &[u8]) {
    let file = run_make_support::object::File::parse(object).expect("Mach-O object");
    let mut f_defined = false;
    let mut ident_defined = false;
    for symbol in file.symbols() {
        let Ok(name) = symbol.name() else { continue };
        if name == "_f" {
            assert!(symbol.is_definition() && symbol.is_global(), "`_f` must be defined, external");
            f_defined = true;
        }
        if name.contains("12inc3_subject5identyE") {
            assert!(symbol.is_definition(), "`{name}` must be defined");
            assert!(!symbol.is_global(), "`{name}` must not be external");
            ident_defined = true;
        }
    }
    assert!(f_defined, "the object must define `_f`");
    assert!(ident_defined, "the object must define `ident::<u64>` under its mangled symbol");
    for section in file.sections() {
        if section.name().ok() != Some("__text") {
            continue;
        }
        for (_, relocation) in section.relocations() {
            if let RelocationFlags::MachO { r_type, .. } = relocation.flags() {
                assert_ne!(
                    r_type, ARM64_RELOC_BRANCH26,
                    "no real call may survive: {relocation:?}"
                );
            }
        }
    }
}

fn link_and_run(object: &[u8], main_c: &str, tag: &str) -> String {
    let object_path = format!("{tag}.o");
    let main_path = format!("main_{tag}.c");
    let exe = format!("main_{tag}");
    rfs::write(&object_path, object);
    rfs::write(&main_path, main_c);
    cc().input(&main_path).input(&object_path).out_exe(&exe).run();
    run(&exe).stdout_utf8()
}

fn assert_no_ice(stderr: &str) {
    assert!(!stderr.contains("internal compiler error"), "{stderr}");
    assert!(!stderr.contains("the compiler unexpectedly panicked"), "{stderr}");
}

fn main() {
    rfs::write("inc3_subject.rs", SUBJECT_A);
    rfs::write("subj_b.rs", SUBJECT_B);
    seam_one_working_copy();
    instance_seam_test_oracle();

    // ── SUBJECT A — the goal's EXACT command line, then with the producer flag ─────────────
    for (tag, extra) in [
        ("goal", &["-Ztrust-verify=on"][..]),
        ("lower", &["-Ztrust-verify=on", "-Ztrust-ir-lower"][..]),
        ("off", &["-Ztrust-verify=off", "-Ztrust-ir-lower"][..]),
    ] {
        let out = format!("out_a_{tag}");
        let built = frontend("inc3_subject.rs", &out, extra).run();
        let stderr = built.stderr_utf8();
        assert_no_ice(&stderr);
        for needle in [
            &format!("trust-cg trust-ir frontend: 2/2 {COMPLETED}")[..],
            "2 [PROVED]",
            "0 refuted",
            // D17: the generic instance body is DISCLOSED per function, after the gate, with
            // the verdict it got.
            "instance-lane coverage: GENERIC instance body",
            "12inc3_subject5identyE",
            "emitted under its own symbol, inlined into `f`",
            "gate verdict [PROVED] (strict: only [PROVED] ships)",
            "NO per-instance MIR seam differential (owner ruling D17)",
        ] {
            assert!(stderr.contains(needle), "{tag}: missing `{needle}`:\n{stderr}");
        }
        // ... and persisted: the per-function coverage artifact.
        let coverage =
            rfs::read_to_string(format!("{out}/inc3_subject.trust-instance-coverage.json"));
        for needle in [
            "\"output_gate_policy\": \"strict\"",
            "\"kind\": \"generic-instance\"",
            "\"emitted_as_own_symbol\": true",
            "\"inlined_into\": [\"f\"]",
            "\"gate_verdict\": \"[PROVED] (strict: only [PROVED] ships)\"",
            "no MIR seam differential (owner ruling D17)",
        ] {
            assert!(coverage.contains(needle), "{tag}: coverage lacks `{needle}`:\n{coverage}");
        }
        assert!(coverage.contains("12inc3_subject5identyE"), "{coverage}");
        for forbidden in ["[generic-instance]", "[converter-refused]"] {
            assert!(!stderr.contains(forbidden), "{tag}: `{forbidden}` is back:\n{stderr}");
        }
        let rlib = format!("{out}/{}", rust_lib_name("inc3_subject"));
        let object = object_member(&rlib);
        // The artifact is BOUND to what it describes: the compiler that ran, and the object.
        let compiler = json_field(&coverage, "\"compiler\": \"");
        let version = rustc().arg("-vV").run().stdout_utf8();
        assert!(
            version.lines().next().is_some_and(|l| l.starts_with(&format!("rustc {compiler} "))),
            "{tag}: artifact compiler `{compiler}` is not the one that ran:\n{version}"
        );
        assert!(bound_to(&coverage, &rlib, &format!("a_{tag}")), "{tag}: not bound:\n{coverage}");
        inspect_subject_a(&object);
        assert_eq!(
            link_and_run(&object, MAIN_A, &format!("a_{tag}")),
            "7 6 23 18446744073709551608\n"
        );
    }

    // ── SUBJECT B — two instances of one body stay two ─────────────────────────────────────
    // `-Ztrust-verify=off`: strict verification fails `pick` on an unrelated runtime-checked
    // assert (measured); the proven-output gate is still the default strict one.
    let built = frontend("subj_b.rs", "out_b", &["-Ztrust-verify=off", "-Ztrust-ir-lower"]).run();
    let stderr = built.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains(&format!("trust-cg trust-ir frontend: 5/5 {COMPLETED}")), "{stderr}");
    assert!(stderr.contains("5 [PROVED]"), "{stderr}");
    assert!(stderr.contains("0 refuted"), "{stderr}");
    let object = object_member(&format!("out_b/{}", rust_lib_name("subj_b")));
    assert_eq!(link_and_run(&object, MAIN_B, "b"), "24\n", "a collapsed instance key prints 0");

    contrasts();
    unfaithful_panics();
    coverage_artifact_lifecycle();
    strictness_coercion();
    intrinsic_callee_is_not_an_item();
}

/// D17's strict condition under BATTERIES-ON verification: `-Ztrust-verify=on` coerces
/// `-Ztrust-cg-output-gate=allow-unknown` to the strict gate (one shared `strict_gate_from`), so
/// the generic body IS appended and the artifact says `strict`; and `=off` is a fatal error.
fn strictness_coercion() {
    let out = "out_von_au";
    let built = frontend(
        "inc3_subject.rs",
        out,
        &["-Ztrust-verify=on", "-Ztrust-cg-output-gate=allow-unknown"],
    )
    .run();
    let stderr = built.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains(&format!("frontend: 2/2 {COMPLETED}")), "{stderr}");
    assert!(stderr.contains("instance-lane coverage: GENERIC instance body"), "{stderr}");
    let coverage =
        rfs::read_to_string(format!("{out}/inc3_subject.trust-instance-coverage.json"));
    assert!(coverage.contains("\"output_gate_policy\": \"strict\""), "{coverage}");
    assert!(coverage.contains("\"kind\": \"generic-instance\""), "{coverage}");
    let refused =
        frontend("inc3_subject.rs", "out_von_off", &["-Ztrust-verify=on", "-Ztrust-cg-output-gate=off"])
            .run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("is incompatible with batteries-on strict"), "{stderr}");
}

/// A BEHAVIOURAL pin of the frozen call-site re-derivation: the producer's free-fn fast path
/// records a `DefKind::Fn` callee as a plain item without resolving it, so an intrinsic called
/// from a generic body is linked as an item; re-derived from its call site it resolves to an
/// `Intrinsic` instance, and the body is refused (`CalleeMisresolved`, its own text), never
/// spliced.
fn intrinsic_callee_is_not_an_item() {
    rfs::write(
        "in1.rs",
        r#"#![crate_name = "in1"]
#![feature(core_intrinsics)]
#![allow(internal_features)]
#[inline(never)] fn g<T>(x: u64, y: u64) -> u64 { unsafe { core::intrinsics::unchecked_add(x, y) } }
#[unsafe(no_mangle)] pub extern "C" fn f(x: u64) -> u64 { g::<u8>(x, 1) }
"#,
    );
    let refused =
        frontend("in1.rs", "out_in1", &["-Ztrust-verify=off", "-Ztrust-ir-lower"]).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    for needle in ["[instance-assembly]", "CalleeMisresolved", "which is not a plain item"] {
        assert!(stderr.contains(needle), "intrinsic: missing `{needle}`:\n{stderr}");
    }
    assert!(!std::path::Path::new("out_in1").join(rust_lib_name("in1")).exists());
}

/// The SHA-256 of `bytes`, as lowercase hex (`shasum -a 256` on a scratch copy).
fn sha256(bytes: &[u8], tag: &str) -> String {
    let path = format!("sha_{tag}.bin");
    rfs::write(&path, bytes);
    let out = run_make_support::cmd("shasum").arg("-a").arg("256").arg(&path).run().stdout_utf8();
    out.split_whitespace().next().expect("a digest").to_string()
}

/// The value after `key` in a coverage artifact, up to the next `"` or `,`.
fn json_field(coverage: &str, key: &str) -> String {
    let at = coverage.find(key).unwrap_or_else(|| panic!("no {key}:\n{coverage}")) + key.len();
    let rest = &coverage[at..];
    rest[..rest.find(|c| c == '"' || c == ',').expect("closed")].to_string()
}

/// The archive member of `rlib` named `file`, if there is one.
fn member_named(rlib: &str, file: &str) -> Option<Vec<u8>> {
    let data = rfs::read(rlib);
    let archive = ArchiveFile::parse(&*data).expect("rlib is an archive");
    archive.members().map(|m| m.expect("archive member")).find_map(|member| {
        (member.name() == file.as_bytes())
            .then(|| member.data(&*data).expect("member data").to_vec())
    })
}

/// THE CONSUMER RULE for the D17 coverage artifact's object binding (one object here): the rlib
/// has a member named `file`; its length exceeds `bytes` by 0..=7 bytes, all `\n` (Darwin `ar`
/// pads a member to 8 bytes with newlines); and SHA-256 of its first `bytes` bytes is `sha256`.
fn bound_to(coverage: &str, rlib: &str, tag: &str) -> bool {
    assert_eq!(coverage.matches("\"sha256\": ").count(), 1, "one object:\n{coverage}");
    let file = json_field(coverage, "\"file\": \"");
    let bytes: usize = json_field(coverage, "\"bytes\": ").parse().expect("a length");
    let digest = json_field(coverage, "\"sha256\": \"");
    let Some(member) = member_named(rlib, &file) else { return false };
    member.len() >= bytes
        && member.len() - bytes <= 7
        && member[bytes..].iter().all(|&b| b == b'\n')
        && sha256(&member[..bytes], tag) == digest
}

/// The D17 coverage artifact's lifecycle. A REFUSED trust-ir rebuild touches nothing: rustc keeps
/// the previous rlib, and the previous artifact stays beside it, still bound to its object. A
/// MONOMORPHIC-ONLY trust-ir rebuild removes it. An LLVM rebuild (which never runs trust-cg)
/// cannot remove it, and its binding then no longer matches the rlib, so a consumer rejects it.
fn coverage_artifact_lifecycle() {
    let off = &["-Ztrust-verify=off", "-Ztrust-ir-lower"][..];
    let out = "out_life";
    let json = format!("{out}/inc3_subject.trust-instance-coverage.json");
    let rlib = format!("{out}/{}", rust_lib_name("inc3_subject"));
    let goal = || {
        frontend("inc3_subject.rs", out, off).run();
        assert!(std::path::Path::new(&json).exists(), "the goal writes its artifact");
    };
    // (a) A REFUSED rebuild: `f` reaches a runtime check.
    goal();
    rfs::write(
        "life_refused.rs",
        r#"#![crate_name = "inc3_subject"]
#[inline(never)] fn ident<T>(x: T) -> T { x }
#[unsafe(no_mangle)] pub extern "C" fn f(x: u64) -> u64 { ident::<u64>(x) + 1 }
"#,
    );
    let refused = frontend("life_refused.rs", out, off).run_fail();
    assert!(refused.stderr_utf8().contains("[unfaithful-panic]"), "{}", refused.stderr_utf8());
    assert!(
        bound_to(&rfs::read_to_string(&json), &rlib, "life_refused"),
        "a refused rebuild keeps the previous artifact, bound to the previous rlib it leaves"
    );
    // (b) A MONOMORPHIC-ONLY rebuild.
    goal();
    rfs::write(
        "life_mono.rs",
        r#"#![crate_name = "inc3_subject"]
#[unsafe(no_mangle)] pub extern "C" fn f(x: u64) -> u64 { x ^ 7 }
"#,
    );
    frontend("life_mono.rs", out, off).run();
    assert!(!std::path::Path::new(&json).exists(), "a mono-only rebuild leaves no artifact");
    // (c) An LLVM rebuild cannot remove it, and its binding says it is stale.
    goal();
    assert!(bound_to(&rfs::read_to_string(&json), &rlib, "life_f1"), "bound to the F1 object");
    rustc()
        .input("inc3_subject.rs")
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .out_dir(out)
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    assert!(std::path::Path::new(&json).exists(), "LLVM never runs trust-cg");
    assert!(
        !bound_to(&rfs::read_to_string(&json), &rlib, "life_llvm"),
        "the stale artifact's binding must not match the LLVM-built object"
    );
}

/// Refusals the instance lane must keep making. Each compile FAILS (no rlib is written), so
/// nothing in it is ever emitted, and each names its reason.
fn contrasts() {
    let off = &["-Ztrust-verify=off", "-Ztrust-ir-lower"][..];

    // (1) A pending-const SENTINEL: `with_const::<u8>` reads a local `const`, which only the crate
    //     finalizer patches. Its own refusal is the producer's; its caller's is the assembler's.
    //     Both are `[instance-assembly]`: the census classifies a producer refusal by its
    //     variant, and `PendingConsts` is the instance seam's (not a declined lowering).
    rfs::write(
        "pc.rs",
        r#"#![crate_name = "pc"]
const K: u64 = 0x55;
#[inline(never)] fn with_const<T>(x: u64) -> u64 { x ^ K }
#[unsafe(no_mangle)] pub extern "C" fn g(x: u64) -> u64 { with_const::<u8>(x) }
"#,
    );
    let refused = frontend("pc.rs", "out_pc", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    for needle in ["PendingConsts", "2  (100.0%)  [instance-assembly]"] {
        assert!(stderr.contains(needle), "pending const: missing `{needle}`:\n{stderr}");
    }
    assert!(!stderr.contains("[producer-declined]"), "{stderr}");
    assert!(!std::path::Path::new("out_pc").join(rust_lib_name("pc")).exists());

    // (2) Crate-module mode keeps refusing: its published module is pre-monomorphization.
    let refused =
        frontend("inc3_subject.rs", "out_cm", &[off, &["-Ztrust-ir-crate-module"][..]].concat())
            .run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("[generic-instance]"), "{stderr}");

    // (3) MUTUAL RECURSION through an instance: a cycle needs real call edges (increment 5).
    rfs::write(
        "cycle.rs",
        r#"#![crate_name = "cycle"]
#[inline(never)] fn even<T>(n: u64) -> u64 { if n == 0 { 1 } else { odd::<T>(n - 1) } }
#[inline(never)] fn odd<T>(n: u64) -> u64 { if n == 0 { 0 } else { even::<T>(n - 1) } }
#[unsafe(no_mangle)] pub extern "C" fn parity(n: u64) -> u64 { even::<u8>(n) }
"#,
    );
    let refused = frontend("cycle.rs", "out_cycle", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("[instance-assembly]"), "{stderr}");
    assert!(stderr.contains("instance cycle"), "{stderr}");

    // (4) A LOCAL CLOSURE INSTANCE was `[generic-instance]` (its args are the closure's own);
    //     the instance lane splices only fn items, so it is `[instance-assembly]` now. Since
    //     2dc38fb191 (the exact typed FnOnce source handoff) a local closure is routed to that
    //     source route before the item-kind check, and this NON-capturing `Fn` closure is
    //     refused there: only a capturing by-value FnOnce has the typed environment convention.
    rfs::write(
        "closure.rs",
        r#"#![crate_name = "closure"]
#[unsafe(no_mangle)] pub extern "C" fn k(x: u64) -> u64 { let add = |y: u64| y ^ 1; add(x) }
"#,
    );
    let refused = frontend("closure.rs", "out_closure", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("[instance-assembly]"), "{stderr}");
    assert!(
        stderr.lines().any(|l| l.contains("e.g.")
            && l.contains("source closure `")
            && l.contains(
                "only a capturing FnOnce value has the typed source environment convention"
            )),
        "{stderr}"
    );
    assert!(!stderr.contains("[generic-instance]"), "{stderr}");

    // (5) A DROP-BEARING instance: `consume::<E>` drops an `E` whose variant holds a `Drop`
    //     payload. The producer elides implicit drops until increment 4, so it is refused.
    rfs::write(
        "drops.rs",
        r#"#![crate_name = "drops"]
pub struct D(pub u64);
impl Drop for D { #[inline(never)] fn drop(&mut self) {} }
pub enum E { A(u64), B(D) }
#[inline(never)] fn consume<T>(_x: T) {}
#[unsafe(no_mangle)] pub extern "C" fn use_e(x: u64) { consume::<E>(E::A(x)) }
"#,
    );
    let refused = frontend("drops.rs", "out_drops", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("LaneRefused(\"drop-bearing\")"), "{stderr}");
    assert!(!std::path::Path::new("out_drops").join(rust_lib_name("drops")).exists());

    // (6) A FINALIZE-VETOED monomorphic callee: `vetoed` holds inline assembly, so crate
    //     finalization never spliced it (`ExactAssembledBodyAbsent`). A generic caller must not
    //     re-lower it on the instance lane: the veto binds on callees, not only on work items.
    rfs::write(
        "veto.rs",
        r#"#![crate_name = "veto"]
#[inline(never)] fn vetoed(x: u64) -> u64 { unsafe { core::arch::asm!("nop") }; x }
#[inline(never)] fn wrap<T>(x: u64) -> u64 { vetoed(x) }
#[unsafe(no_mangle)] pub extern "C" fn r(x: u64) -> u64 { wrap::<u8>(x) }
"#,
    );
    let refused = frontend("veto.rs", "out_veto", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains(&format!("frontend: 0/3 {COMPLETED}")), "{stderr}");
    assert!(stderr.contains("[instance-assembly]"), "{stderr}");
    assert!(stderr.contains("has no assembled handoff body (ExactBodyAbsent"), "{stderr}");
    assert!(stderr.contains("is never re-lowered on the instance lane"), "{stderr}");
    assert!(!std::path::Path::new("out_veto").join(rust_lib_name("veto")).exists());

    // (7) D17's SECOND CONDITION: a generic body is appended only under the STRICT output gate.
    //     Under allow-unknown and under off the same goal subject is refused, and no coverage
    //     row is written.
    for policy in ["allow-unknown", "off"] {
        let out = format!("out_a_gate_{policy}");
        let gate = format!("-Ztrust-cg-output-gate={policy}");
        let refused =
            frontend("inc3_subject.rs", &out, &[off, &[gate.as_str()][..]].concat()).run_fail();
        let stderr = refused.stderr_utf8();
        assert_no_ice(&stderr);
        assert!(stderr.contains("[instance-assembly]"), "{policy}: {stderr}");
        assert!(stderr.contains("only under the STRICT proven-output gate"), "{policy}: {stderr}");
        assert!(
            !stderr.contains("instance-lane coverage"),
            "{policy}: nothing emitted, nothing disclosed:\n{stderr}"
        );
        assert!(!std::path::Path::new(&out).join("inc3_subject.trust-instance-coverage.json").exists());
        assert!(!std::path::Path::new(&out).join(rust_lib_name("inc3_subject")).exists());
    }

    // (8) A FOREIGN callee is named as one, not as a vetoed handoff body.
    rfs::write(
        "foreign.rs",
        r#"#![crate_name = "foreign"]
unsafe extern "C" { fn ext_fn(x: u64) -> u64; }
#[inline(never)] fn g<T>(x: u64) -> u64 { unsafe { ext_fn(x) } }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { g::<u8>(x) }
"#,
    );
    let refused = frontend("foreign.rs", "out_foreign", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("is a foreign declaration"), "{stderr}");

    // (9) A SELF-RECURSIVE monomorphic callee is a cycle, never linked as a leaf.
    rfs::write(
        "selfrec.rs",
        r#"#![crate_name = "selfrec"]
#[inline(never)] fn fr(n: u64) -> u64 { if n == 0 { 0 } else { fr(n ^ 1) } }
#[inline(never)] fn g<T>(x: u64) -> u64 { fr(x) ^ 1 }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { g::<u8>(x) }
"#,
    );
    let refused = frontend("selfrec.rs", "out_selfrec", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("calls itself: recursion needs real call edges"), "{stderr}");
    // Both instance-lane items (`g::<u8>` and `t0`) are refused by the assembler; the one
    // converter refusal is `fr`'s OWN handoff-lane row (its self-`Call` is outside the
    // converter's fragment), not a leaf link that reached the converter through `g`.
    assert!(stderr.contains("2  (66.6%)  [instance-assembly]"), "{stderr}");
    assert!(stderr.contains("1  (33.3%)  [converter-refused]"), "{stderr}");
    assert!(stderr.contains("7selfrec2fr` (outside the converter's mapped fragment)"), "{stderr}");

    // (10) A drop-bearing monomorphic LEAF callee is refused. Since main's effect-conservation
    //      gate (D28) the handoff withdrew such a leaf (its elided drop was an `Abstracted(drop)`
    //      tag, `NotConserved`). Since step 2 increment 4b the producer PLACES the leaf's drop,
    //      the gate finds it equal to rustc's elaboration and keeps the leaf in the handoff, so
    //      the refusal comes from the lane's own leaf drop check (`instance_drop_refusal`,
    //      `LaneRefused("drop-bearing")`) — D17's "drop-free" leg, which this lane keeps until
    //      increment 4c (D18 OD-2) — and the leaf itself is refused by the converter.
    rfs::write(
        "leafdrop.rs",
        r#"#![crate_name = "leafdrop"]
pub struct U;
impl Drop for U { #[inline(never)] fn drop(&mut self) {} }
#[inline(never)] fn leaf(x: u64) -> u64 { let _u = U; x ^ 2 }
#[inline(never)] fn g<T>(x: u64) -> u64 { leaf(x) ^ 1 }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { g::<u8>(x) }
"#,
    );
    let refused = frontend("leafdrop.rs", "out_leafdrop", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("monomorphic leaf callee `_R"), "{stderr}");
    assert!(stderr.contains("8leafdrop4leaf"), "{stderr}");
    assert!(stderr.contains("LaneRefused(\"drop-bearing\")"), "{stderr}");
    assert!(!stderr.contains("NotConserved"), "the leaf's drop is placed, not elided: {stderr}");
    assert!(!stderr.contains("Abstracted(drop"), "the leaf's drop is placed, not elided: {stderr}");

    // (11) A GENERIC `extern "C"` callee: its body is stamped with the C convention and the
    //      caller's declaration says C too (the per-edge check compares them). Output pinned.
    rfs::write(
        "cgen.rs",
        r#"#![crate_name = "cgen"]
#[inline(never)] extern "C" fn cg<T>(x: u64) -> u64 { x ^ 0x45 }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { cg::<u8>(x) }
"#,
    );
    let built = frontend("cgen.rs", "out_cgen", off).run();
    let stderr = built.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains(&format!("frontend: 2/2 {COMPLETED}")), "{stderr}");
    assert!(stderr.contains("2 [PROVED]"), "{stderr}");
    let object = object_member(&format!("out_cgen/{}", rust_lib_name("cgen")));
    let main = r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t t0(uint64_t);
int main(void){ printf("%llu %llu\n",(unsigned long long)t0(0),(unsigned long long)t0(0x45)); return 0; }
"#;
    assert_eq!(link_and_run(&object, main, "cgen"), "69 0\n");

    // (12) An OPAQUE COLLAPSE (docs/KNOWN_HAZARDS.md, OPEN 2026-10-01, abstraction lanes): the
    //      handoff splices `Holder::set_pair` storing only the `Option` discriminant `bool` where
    //      the program stores a 16-byte `Option<Pair>`. `Holder` needs no drop, so the instance
    //      lane must refuse the GENERIC setter; under D17 no seam differential would.
    //      Its static address also leaves a pending-const sentinel. The documented
    //      admission order refuses that sentinel before inspecting placeholder lanes.
    //      Keep this original input and separately exercise opaque collapse below.
    rfs::write(
        "opaque.rs",
        r#"#![crate_name = "opaque"]
pub static ANCHOR: u32 = 7;
pub struct Pair(pub u32, pub &'static u32);
pub struct Holder { pub p: Option<Pair>, pub n: u32 }
impl Holder {
    #[inline(never)] fn set_pair<T>(&mut self) { self.p = Some(Pair(1, &ANCHOR)); }
}
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u32) -> u32 {
    let mut h = Holder { p: None, n: x };
    h.set_pair::<u8>();
    h.n
}
"#,
    );
    let refused = frontend("opaque.rs", "out_opaque", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("[producer-declined]"), "{stderr}");
    assert!(
        stderr.lines().any(|l| l.contains("set_pair") && l.contains("PendingConsts")),
        "the original setter's unresolved static address must refuse first:\n{stderr}"
    );
    assert!(!stderr.contains("LaneRefused(\"drop-bearing\")"), "{stderr}");
    assert!(!std::path::Path::new("out_opaque").join(rust_lib_name("opaque")).exists());

    // (12b) The same non-drop Option<Pair> shape without a static-address
    // sentinel MUST reach the opaque-collapse gate. A pending-constant refusal
    // in (12) must never hide removal of the independent layout guard.
    rfs::write(
        "opaque_arg.rs",
        r#"#![crate_name = "opaque_arg"]
pub struct Pair(pub u32, pub &'static u32);
pub struct Holder { pub p: Option<Pair>, pub n: u32 }
impl Holder {
    #[inline(never)] fn set_pair<T>(&mut self, anchor: &'static u32) {
        self.p = Some(Pair(1, anchor));
    }
}
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u32, anchor: &'static u32) -> u32 {
    let mut h = Holder { p: None, n: x };
    h.set_pair::<u8>(anchor);
    h.n
}
"#,
    );
    let refused = frontend("opaque_arg.rs", "out_opaque_arg", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(
        stderr.lines().any(|l| l.contains("set_pair") && l.contains("LaneRefused(\"opaque collapse\")")),
        "the static-free generic setter must reach its opaque-collapse guard:\n{stderr}"
    );
    assert!(!stderr.contains("PendingConsts"), "the independent guard must be exercised: {stderr}");
    assert!(!stderr.contains("LaneRefused(\"drop-bearing\")"), "{stderr}");
    assert!(!std::path::Path::new("out_opaque_arg").join(rust_lib_name("opaque_arg")).exists());

    // (13) The same gate names a `&mut self` setter of a struct with a `Vec` sibling, which is
    //      ALSO drop-bearing (its `*self` place has the struct's type): the placeholder first.
    rfs::write(
        "opaque_vec.rs",
        r#"#![crate_name = "opaque_vec"]
pub struct S { pub rows: Vec<u32>, pub n: u32 }
impl S {
    #[inline(never)] fn set_n<T>(&mut self, v: u32) { self.n = v; }
}
#[unsafe(no_mangle)] pub extern "C" fn t0(s: &mut S, v: u32) { s.set_n::<u8>(v) }
"#,
    );
    let refused = frontend("opaque_vec.rs", "out_opaque_vec", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(
        stderr.lines().any(|l| l.contains("set_n") && l.contains("LaneRefused(\"opaque collapse\")")),
        "the generic setter itself is refused by the opaque-collapse gate:\n{stderr}"
    );
    assert!(!std::path::Path::new("out_opaque_vec").join(rust_lib_name("opaque_vec")).exists());

    // (14) A monomorphic LEAF callee is linked as its handoff body, never re-lowered. `leaf`'s
    //      `match` on an opaque-lane `Option` tests an `undef bool`. Since main's
    //      effect-conservation gate (D28) the handoff WITHDRAWS such a leaf (its `undef` and its
    //      opaque lane are `Abstracted` tags), so the refusal comes from the handoff lookup
    //      (`NotConserved`) before the assembler's own `undef` scan, which stays as a backstop.
    //      D28 also tags an opaque lane that leaves no `undef`, so the leaf gap this row used to
    //      document (inherited from the handoff lane) is closed for tagged lanes.
    rfs::write(
        "leafundef.rs",
        r#"#![crate_name = "leafundef"]
#[inline(never)] fn leaf(x: u32) -> u64 { let o = Some((x, x)); match o { Some(_) => 3, None => 4 } }
#[inline(never)] fn g<T>(x: u32) -> u64 { leaf(x) ^ 1 }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u32) -> u64 { g::<u8>(x) }
"#,
    );
    let refused = frontend("leafundef.rs", "out_leafundef", off).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("[instance-assembly]"), "{stderr}");
    assert!(stderr.contains("[effect-not-conserved]"), "{stderr}");
    assert!(
        stderr.contains("9leafundef4leaf")
            && stderr.contains("NotConserved")
            && stderr.contains("Abstracted(undef"),
        "{stderr}"
    );
    assert!(!std::path::Path::new("out_leafundef").join(rust_lib_name("leafundef")).exists());
}

/// R-8 ledger item 1 (plan §5): a function whose trust-ir can reach a runtime check lowers it to
/// a bare trap on F1, where MIR->LLVM panics. It is refused `[unfaithful-panic]` under EVERY
/// output-gate policy (strict, allow-unknown, off), on the handoff lane, the instance lane and
/// the crate-module lane, until the panic path is faithful (ledger item P). Before this,
/// `allow-unknown` EMITTED both subjects below. Under a non-strict policy the GENERIC subject is
/// refused first by D17's strict-only condition, which is what its row pins there.
fn unfaithful_panics() {
    let off = &["-Ztrust-verify=off", "-Ztrust-ir-lower"][..];
    rfs::write(
        "panics_mono.rs",
        r#"#![crate_name = "panics_mono"]
#[inline(never)] fn g(x: u64) -> u64 { x + 1 }
#[unsafe(no_mangle)] pub extern "C" fn mono_inc(x: u64) -> u64 { x + 1 }
#[unsafe(no_mangle)] pub extern "C" fn calls_g(x: u64) -> u64 { g(x) ^ 1 }
"#,
    );
    rfs::write(
        "panics_gen.rs",
        r#"#![crate_name = "panics_gen"]
#[inline(never)] fn inc<T>(x: u64) -> u64 { x + 1 }
#[unsafe(no_mangle)] pub extern "C" fn gen_inc(x: u64) -> u64 { inc::<u8>(x) }
"#,
    );
    for policy in ["strict", "allow-unknown", "off"] {
        let gate = format!("-Ztrust-cg-output-gate={policy}");
        // MONOMORPHIC (handoff lane): the item's own check, and a check in the callee it inlines.
        let out = format!("out_panics_mono_{policy}");
        let refused =
            frontend("panics_mono.rs", &out, &[off, &[gate.as_str()][..]].concat()).run_fail();
        let stderr = refused.stderr_utf8();
        assert_no_ice(&stderr);
        assert!(stderr.contains("[unfaithful-panic]"), "{policy}:\n{stderr}");
        assert!(stderr.contains("`mono_inc`"), "{policy}:\n{stderr}");
        assert!(stderr.contains("in `g`"), "the inlined callee's check is the caller's:\n{stderr}");
        assert!(!std::path::Path::new(&out).join(rust_lib_name("panics_mono")).exists());
        // GENERIC (instance lane).
        let out = format!("out_panics_gen_{policy}");
        let refused =
            frontend("panics_gen.rs", &out, &[off, &[gate.as_str()][..]].concat()).run_fail();
        let stderr = refused.stderr_utf8();
        assert_no_ice(&stderr);
        if policy == "strict" {
            assert!(stderr.contains("[unfaithful-panic]"), "{policy}:\n{stderr}");
            // Attributed to the GENERIC instance `inc::<u8>` (v0 `3inchEB2_`), not its caller.
            assert!(stderr.contains("3inchEB2_` (block"), "{policy}:\n{stderr}");
        } else {
            // Not strict: D17 refuses the generic append first.
            assert!(stderr.contains("only under the STRICT proven-output gate"), "{stderr}");
        }
        assert!(!std::path::Path::new(&out).join(rust_lib_name("panics_gen")).exists());
    }

    // Checks that SURVIVE `-Coverflow-checks=off`: division by zero and an out-of-bounds index.
    // Under the gate policy with NO gate behind the frontend (`off`), on the default lane and on
    // the crate-module lane (`lower_from_crate_module`, the refusal's second call site).
    rfs::write(
        "panics_div.rs",
        r#"#![crate_name = "panics_div"]
#[unsafe(no_mangle)] pub extern "C" fn d(a: u64, b: u64) -> u64 { a / b }
"#,
    );
    rfs::write(
        "panics_ix.rs",
        r#"#![crate_name = "panics_ix"]
#[inline(never)] pub fn ix(i: usize) -> u64 { [1u64, 2, 3][i] }
"#,
    );
    for (file, krate, kind) in
        [("panics_div.rs", "panics_div", "DivNonZero"), ("panics_ix.rs", "panics_ix", "InBounds")]
    {
        for crate_module in [false, true] {
            let out = format!("out_{krate}_{crate_module}");
            let mut flags = vec!["-Coverflow-checks=off", "-Ztrust-cg-output-gate=off"];
            flags.extend_from_slice(off);
            if crate_module {
                flags.push("-Ztrust-ir-crate-module");
            }
            let refused = frontend(file, &out, &flags).run_fail();
            let stderr = refused.stderr_utf8();
            assert_no_ice(&stderr);
            assert!(stderr.contains("[unfaithful-panic]"), "{krate} cm={crate_module}:\n{stderr}");
            assert!(stderr.contains(kind), "{krate} cm={crate_module}: no `{kind}`:\n{stderr}");
            assert!(!std::path::Path::new(&out).join(rust_lib_name(krate)).exists());
        }
    }
}

/// Trust (R8-SEAM, `docs/DECISION_QUEUE.md`, taken 2026-10-05): the crate-seam differential computes
/// from ONE working copy of the assembled module what it computed from whole-module copies. The
/// TEST-ONLY `-Ztrust-ir-seam-reference=<report>` option runs the pre-R8-SEAM seam over the
/// pre-R8-SEAM differential (`crates/trust-thir-lower/src/crate_module/seam_reference.rs` and
/// `.../differential/compare_entries_reference.rs`, verbatim) beside the live one at
/// crate finalization and fails finalization on any difference in the verdicts or the UC probe's
/// traced outcomes; `tests/run-make/trust-ir-seam-one-working-copy` pins that each lane is reached.
fn seam_cross_check(file: &str, edition: &str, tag: &str) {
    let report = format!("seam-reference-{tag}.txt");
    let out = rustc()
        .input(file)
        .crate_type("lib")
        .edition(edition)
        .arg("-Copt-level=0")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("--emit=metadata")
        .out_dir(format!("seam-out-{tag}"))
        .arg(format!("-Ztrust-ir-seam-reference={report}"))
        .run();
    let stderr = out.stderr_utf8();
    assert!(!stderr.contains("seam cross-check"), "{tag}: the seams differ:\n{stderr}");
    let text = rfs::read_to_string(&report);
    for line in ["differences 0", "restored true"] {
        assert!(text.lines().any(|l| l == line), "{tag}: the report lacks `{line}`:\n{text}");
    }
    assert!(!text.lines().any(|l| l == "verdicts 0"), "{tag}: no deferred body was compared:\n{text}");
}

fn seam_one_working_copy() {
    rfs::write("inc3_subject.rs", SUBJECT_A);
    rfs::write("subj_b.rs", SUBJECT_B);
    seam_cross_check("inc3_subject.rs", "2021", "subject-a");
    seam_cross_check("subj_b.rs", "2021", "subject-b");
}

/// The R8-SEAM cross-check on this fixture's subjects, under libtest as well as compiletest (the
/// frozen-file waiver cites it).
#[test]
fn the_seam_on_the_generic_instance_subjects_is_the_reference_seam() {
    seam_one_working_copy();
}


/// D17-SEAM-1 is an explicit TEST-ORACLE, not a new MIR production input. The ordinary
/// invocations above still pin their structural-only disclosure; only this invocation compares.
fn instance_seam_test_oracle() {
    let flags = ["-Ztrust-verify=off", "-Ztrust-ir-lower", "-Ztrust-ir-instance-seam-test"];
    for (tag, extra) in [("llvm", "-Zcodegen-backend=llvm"), ("metadata", "--emit=metadata"), ("no_codegen", "-Zno-codegen")] {
        let out = format!("out_seam_wrong_{tag}");
        let refused = frontend("inc3_subject.rs", &out, &[&flags[..], &[extra]].concat()).run_fail();
        let stderr = refused.stderr_utf8();
        assert_no_ice(&stderr);
        assert!(stderr.contains("requires explicit -Zcodegen-backend=trust-cg and object or link output"), "{tag}: {stderr}");
        assert!(!std::path::Path::new(&out).join("inc3_subject.trust-instance-coverage.json").exists());
    }
    let built = frontend("inc3_subject.rs", "out_instance_seam", &flags).run();
    let stderr = built.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("per-instance MIR seam TEST-ORACLE agreed"), "{stderr}");
    let coverage = rfs::read_to_string("out_instance_seam/inc3_subject.trust-instance-coverage.json");
    assert!(coverage.contains("per-instance MIR seam TEST-ORACLE agreed"), "{coverage}");
    assert!(!coverage.contains("no MIR seam differential"), "{coverage}");
    let rlib = format!("out_instance_seam/{}", rust_lib_name("inc3_subject"));
    assert!(bound_to(&coverage, &rlib, "instance_seam"), "{coverage}");
    let object = object_member(&rlib);
    assert_eq!(link_and_run(&object, MAIN_A, "instance_seam"), "7 6 23 18446744073709551608\n");

    // One source body, two concrete const instances: agreement must be re-minted at each
    // instance's arguments. A per-def green bit or collapsed instance key cannot cover both.
    rfs::write("seam_two.rs", r#"#![crate_name = "seam_two"]
#[inline(never)] fn mask<const N: u64>(x: u64) -> u64 { x ^ N }
#[unsafe(no_mangle)] pub extern "C" fn two_instances(x: u64) -> u64 {
    mask::<7>(x) ^ mask::<19>(x)
}
"#);
    let two = frontend("seam_two.rs", "out_seam_two", &flags).run();
    assert_no_ice(&two.stderr_utf8());
    let coverage = rfs::read_to_string("out_seam_two/seam_two.trust-instance-coverage.json");
    assert_eq!(coverage.matches("\"kind\": \"generic-instance\"").count(), 2, "{coverage}");
    let symbols: std::collections::BTreeSet<_> = coverage.lines()
        .filter(|line| line.contains("\"kind\": \"generic-instance\""))
        .map(|line| json_field(line, "\"symbol\": \""))
        .collect();
    assert_eq!(symbols.len(), 2, "distinct concrete instances must retain distinct symbols: {coverage}");
    assert_eq!(coverage.matches("per-instance MIR seam TEST-ORACLE agreed").count(), 2, "{coverage}");
    assert!(!coverage.contains("no MIR seam differential"), "{coverage}");
    let rlib = format!("out_seam_two/{}", rust_lib_name("seam_two"));
    assert!(bound_to(&coverage, &rlib, "seam_two"), "{coverage}");
    let object = object_member(&rlib);
    let main = r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t two_instances(uint64_t);
int main(void) { printf("%llu %llu\n", (unsigned long long)two_instances(1),
    (unsigned long long)two_instances(UINT64_MAX)); return 0; }
"#;
    assert_eq!(link_and_run(&object, main, "seam_two"), "20 20\n");

    // The inherited const owner and a type argument precede the method's own const argument.
    // Looking up a function-local position, or confusing the type argument with a const,
    // cannot supply both of the source values used by this actual instance.
    rfs::write("seam_owned_consts.rs", r#"#![crate_name = "seam_owned_consts"]
struct ConstOwner<const A: u64>;
impl<const A: u64> ConstOwner<A> {
    #[inline(never)] fn mix<T, const B: u64>(x: u64) -> u64 { x ^ A ^ B }
}
#[unsafe(no_mangle)] pub extern "C" fn owned_consts(x: u64) -> u64 {
    ConstOwner::<7>::mix::<u8, 19>(x)
}
"#);
    let owned = frontend("seam_owned_consts.rs", "out_seam_owned_consts", &flags).run();
    assert_no_ice(&owned.stderr_utf8());
    let coverage = rfs::read_to_string(
        "out_seam_owned_consts/seam_owned_consts.trust-instance-coverage.json");
    assert_eq!(coverage.matches("\"kind\": \"generic-instance\"").count(), 1, "{coverage}");
    assert_eq!(coverage.matches("per-instance MIR seam TEST-ORACLE agreed").count(), 1, "{coverage}");
    let rlib = format!("out_seam_owned_consts/{}", rust_lib_name("seam_owned_consts"));
    assert!(bound_to(&coverage, &rlib, "seam_owned_consts"), "{coverage}");
    let object = object_member(&rlib);
    let main = r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t owned_consts(uint64_t);
int main(void) { printf("%llu %llu\n", (unsigned long long)owned_consts(1),
    (unsigned long long)owned_consts(20)); return 0; }
"#;
    assert_eq!(link_and_run(&object, main, "seam_owned_consts"), "21 0\n");

    // An actual Drop-bearing instantiation is refused by the ordinary admission gate before
    // reaching the oracle. This protects that early refusal, not the oracle normalizer's
    // needs_drop=true branch. The original identity above deliberately has no `T: Copy` bound.
    rfs::write("seam_drop.rs", r#"#![crate_name = "seam_drop"]
struct WithDrop(u64);
impl Drop for WithDrop { fn drop(&mut self) {} }
#[inline(never)] fn consume<T>(_value: T) {}
#[unsafe(no_mangle)] pub extern "C" fn drop_subject(x: u64) { consume(WithDrop(x)); }
"#);
    let refused = frontend("seam_drop.rs", "out_seam_drop", &flags).run_fail();
    let stderr = refused.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(stderr.contains("LaneRefused(\"drop-bearing\")"), "{stderr}");
    assert!(!stderr.contains("per-instance MIR seam TEST-ORACLE agreed"), "{stderr}");
    assert!(!std::path::Path::new("out_seam_drop").join(rust_lib_name("seam_drop")).exists());

    // Both controls use a real source-produced module; a private clone changes its returned
    // Boolean constant, or replaces it by an out-of-fragment Undef. Neither may emit an object
    // or measured-success row. The original module remains the assembler's only input.
    rfs::write("seam_bool.rs", r#"#![crate_name = "seam_bool"]
#[inline(never)] fn choice<T>() -> bool { true }
#[unsafe(no_mangle)] pub extern "C" fn choice_subject() -> u64 {
    if choice::<u8>() { 1 } else { 2 }
}
"#);
    let positive = frontend("seam_bool.rs", "out_seam_bool", &flags).run();
    assert!(positive.stderr_utf8().contains("per-instance MIR seam TEST-ORACLE agreed"));
    for (mode, verdict) in [("bool-constant", "DerivedMismatch"), ("undef-constant", "DerivedUnsupported")] {
        let out = format!("out_seam_{mode}");
        let mutation = format!("-Ztrust-test-instance-seam-mutation={mode}");
        let refused = frontend("seam_bool.rs", &out, &[&flags[..], &[mutation.as_str()]].concat()).run_fail();
        let stderr = refused.stderr_utf8();
        assert_no_ice(&stderr);
        assert!(stderr.contains("per-instance MIR seam TEST-ORACLE"), "{stderr}");
        assert!(stderr.contains(verdict), "{mode}: {stderr}");
        assert!(!std::path::Path::new(&out).join(rust_lib_name("seam_bool")).exists());
        assert!(!std::path::Path::new(&out).join("seam_bool.trust-instance-coverage.json").exists());
    }
}

/// The actual diagnostic compiler comparison, original unbounded generic identity subject,
/// distinct concrete instances, strict real-drop refusal and private mutation controls.
#[test]
fn drop_free_generic_instances_keep_the_instance_test_oracle() {
    rfs::write("inc3_subject.rs", SUBJECT_A);
    instance_seam_test_oracle();
}
