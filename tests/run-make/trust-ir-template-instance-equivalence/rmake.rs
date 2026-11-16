//! Trust (PKG-C2d2 slice 1; design §5.5(a) and §6.6 of
//! `docs/design/2026-10-02-step2-inc6-trust-ir-in-metadata.md`; INC6.5-NO-AUTHORITY in
//! `docs/DECISION_QUEUE.md`): the template-instance equivalence TEST-ORACLE.
//!
//! In an F1 rlib session on the D17 seam-test lane, `-Ztrust-ir-template-instance-oracle` takes
//! each local generic instance D17 spliced and whose per-instance MIR seam TEST-ORACLE agreed,
//! constructs it from this crate's own authenticated level-S row, and compares its canonical text
//! exactly with the body D17 emits. Agreement and named refusals are notes; a mismatch is fatal.
//!
//! (A) both subjects agree, with overflow checks on and off; the object runs and is byte-identical
//!     to the seam-flags-only build. (B) out-of-fragment subjects refuse by name. (C) both negative
//!     controls fail the session with no rlib. (D) the driver fences the options. (E) runtime
//!     level-S admission stays closed: a downstream F1 consumer of a template is still refused.
//!
//! BEFORE this slice every leg failed: rustc rejected the unknown `-Ztrust-ir-template-instance-
//! oracle`.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::{cc, rfs, run, rust_lib_name, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

const SEAM: [&str; 3] = ["-Ztrust-verify=off", "-Ztrust-ir-lower", "-Ztrust-ir-instance-seam-test"];
const ORACLE: [&str; 5] = [
    "-Ztrust-verify=off",
    "-Ztrust-ir-lower",
    "-Ztrust-ir-lower-templates",
    "-Ztrust-ir-instance-seam-test",
    "-Ztrust-ir-template-instance-oracle",
];

/// The generics are `pub`, so each is reachable and gets an encoded level-S row. The identity is
/// bounded `T: Copy`: an unbounded `ident<T>` moves a parameter-typed value, so its template records
/// a drop fact and construction refuses it by name (leg B, `tie_moved`).
const SUBJECT: &str = r#"#![crate_name = "tie_subject"]
#[inline(never)] pub fn ident<T: Copy>(x: T) -> T { x }
#[inline(never)] pub fn mask<T>(x: u64) -> u64 { x ^ 0x55 }
#[unsafe(no_mangle)] pub extern "C" fn f(x: u64) -> u64 { ident::<u64>(x) ^ mask::<u8>(x) }
"#;

const MAIN: &str = r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t f(uint64_t);
int main(void){ uint64_t xs[4]={0,1,0x10,UINT64_MAX}; for(int i=0;i<4;i++) printf("%llu%s",(unsigned long long)f(xs[i]), i==3?"\n":" "); return 0; }
"#;

const MASK: &str = r#"#![crate_name = "tie_mask"]
#[inline(never)] pub fn mask<T>(x: u64) -> u64 { x ^ 0x55 }
#[unsafe(no_mangle)] pub extern "C" fn f(x: u64) -> u64 { mask::<u8>(x) }
"#;

/// (B) one crate per subject, so D17 admits each alone. The design's third subject,
/// `relay<T>(x: T) -> T { ident(x) }` at u64 (a callee hole), is not here: D17's own per-instance
/// MIR seam oracle refuses it (measured: `DerivedUnsupported: shim: Call(callee site args not
/// encodable / not concrete-mono)`), so the session fails before this oracle could see it.
const REFUSALS: [(&str, &str, &str, &str); 3] = [
    (
        "tie_moved",
        r#"#![crate_name = "tie_moved"]
#[inline(never)] pub fn ident<T>(x: T) -> T { x }
#[unsafe(no_mangle)] pub extern "C" fn f(x: u64) -> u64 { ident::<u64>(x) }
"#,
        "9tie_moved5ident",
        "construction: THIR source facts: original producer abstraction/drop facts require typed \
         semantic transport",
    ),
    (
        "tie_konst",
        r#"#![crate_name = "tie_konst"]
#[inline(never)] pub fn konst<const N: u64>() -> u64 { N }
#[unsafe(no_mangle)] pub extern "C" fn f() -> u64 { konst::<0x1234>() }
"#,
        "9tie_konst5konst",
        "construction: template source capture unavailable: THIR source facts: unsupported source \
         expression",
    ),
    (
        "tie_tagged",
        r#"#![crate_name = "tie_tagged"]
pub struct Marker;
#[inline(never)] pub fn tagged<T>(x: u64) -> u64 { x ^ 1 }
#[unsafe(no_mangle)] pub extern "C" fn f(x: u64) -> u64 { tagged::<Marker>(x) }
"#,
        "10tie_tagged6tagged",
        "outside the slice-1 comparator fragment: the construction carries a `structs` table",
    ),
];

/// (E) a downstream consumer of an upstream template instance.
const DOWNSTREAM: &str = r#"#![crate_name = "tie_down"]
#[inline(never)] pub fn g(x: u32) -> u32 { tie_subject::ident::<u32>(x) }
"#;

const AGREED: &str = "`: agreed (template ";
const NOTE: &str = "template-instance TEST-ORACLE: `";

/// The recipe of `trust-cg-f1-generic-instance`: an rlib through trust-cg and the trust-ir
/// frontend, one codegen unit, the DEFAULT strict proven-output gate.
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

/// The oracle's note lines for the symbol containing `mangled`.
fn notes<'a>(stderr: &'a str, mangled: &str) -> Vec<&'a str> {
    stderr.lines().filter(|l| l.contains(NOTE) && l.contains(mangled)).collect()
}

fn no_rlib(out: &str, name: &str) {
    assert!(!std::path::Path::new(out).join(rust_lib_name(name)).exists(), "{out}: an rlib");
}

fn main() {
    rfs::write("tie_subject.rs", SUBJECT);
    rfs::write("tie_mask.rs", MASK);
    positive();
    refusals();
    negative_controls();
    fences();
    admission_stays_closed();
}

/// (A) Both subjects agree; the session's output is unchanged by the oracle.
fn positive() {
    for checks in ["on", "off"] {
        let flag = format!("-Coverflow-checks={checks}");
        let out = format!("out_a_{checks}");
        let built = frontend("tie_subject.rs", &out, &[&ORACLE[..], &[flag.as_str()]].concat()).run();
        let stderr = built.stderr_utf8();
        assert_no_ice(&stderr);
        for mangled in ["11tie_subject5ident", "11tie_subject4mask"] {
            let rows = notes(&stderr, mangled);
            assert_eq!(rows.len(), 1, "{checks}: one note for `{mangled}`:\n{stderr}");
            assert!(rows[0].contains(AGREED), "{checks}: `{mangled}` did not agree:\n{stderr}");
            assert!(rows[0].contains("chained to the per-instance MIR seam TEST-ORACLE; no authority"));
        }
        assert_eq!(stderr.matches(NOTE).count(), 2, "{checks}: exactly two oracle notes:\n{stderr}");
        let coverage = rfs::read_to_string(format!("{out}/tie_subject.trust-instance-coverage.json"));
        assert_eq!(
            coverage.matches("per-instance MIR seam TEST-ORACLE agreed").count(),
            2,
            "{checks}: {coverage}"
        );
        let object = object_member(&format!("{out}/{}", rust_lib_name("tie_subject")));
        assert_eq!(link_and_run(&object, MAIN, &format!("a_{checks}")), "85 85 85 85\n");
        // The oracle changes no output: the same object as the seam flags alone.
        let seam_out = format!("out_seam_{checks}");
        let seam = frontend("tie_subject.rs", &seam_out, &[&SEAM[..], &[flag.as_str()]].concat()).run();
        assert!(!seam.stderr_utf8().contains(NOTE));
        let seam_object = object_member(&format!("{seam_out}/{}", rust_lib_name("tie_subject")));
        assert!(object == seam_object, "{checks}: the oracle changed the object");
    }
}

/// (B) Out-of-fragment subjects whose MIR seam oracle agreed are refused by name, never agreed.
fn refusals() {
    for (name, source, mangled, reason) in REFUSALS {
        let input = format!("{name}.rs");
        rfs::write(&input, source);
        let out = format!("out_b_{name}");
        let built = frontend(&input, &out, &ORACLE).run();
        let stderr = built.stderr_utf8();
        assert_no_ice(&stderr);
        let coverage = rfs::read_to_string(format!("{out}/{name}.trust-instance-coverage.json"));
        assert!(coverage.contains("per-instance MIR seam TEST-ORACLE agreed"), "{name}: {coverage}");
        let rows = notes(&stderr, mangled);
        assert_eq!(rows.len(), 1, "{name}: one note for `{mangled}`:\n{stderr}");
        assert!(rows[0].contains("`: refused("), "{name}: not a refusal:\n{stderr}");
        assert!(rows[0].contains(reason), "{name}: missing `{reason}`:\n{stderr}");
        assert_eq!(stderr.matches("`: refused(").count(), 1, "{name}: one refusal:\n{stderr}");
    }
}

/// (C) Each negative control fails the session, with no rlib and no ICE.
fn negative_controls() {
    for (mode, expected) in [
        ("int-constant", "negative control int-constant: disagreed"),
        ("envelope-byte", "negative control envelope-byte: refused"),
    ] {
        let out = format!("out_c_{mode}");
        let mutation = format!("-Ztrust-test-template-oracle-mutation={mode}");
        let failed = frontend("tie_mask.rs", &out, &[&ORACLE[..], &[mutation.as_str()]].concat())
            .run_fail();
        let stderr = failed.stderr_utf8();
        assert_no_ice(&stderr);
        assert!(stderr.contains("template-instance TEST-ORACLE disagreed for `"), "{mode}: {stderr}");
        assert!(stderr.contains(expected), "{mode}: missing `{expected}`:\n{stderr}");
        if mode == "envelope-byte" {
            assert!(stderr.contains("template content digest"), "{stderr}");
        }
        no_rlib(&out, "tie_mask");
    }
}

/// (D) The driver's fences.
fn fences() {
    let without = |flag: &str| ORACLE.iter().copied().filter(|f| *f != flag).collect::<Vec<_>>();
    let lane = "-Ztrust-ir-template-instance-oracle requires -Ztrust-ir-instance-seam-test and \
                -Ztrust-ir-lower-templates";
    let seam_off = without("-Ztrust-ir-instance-seam-test");
    let templates_off = without("-Ztrust-ir-lower-templates");
    let oracle_off: Vec<&str> =
        [&without("-Ztrust-ir-template-instance-oracle")[..], &["-Ztrust-test-template-oracle-mutation=int-constant"]].concat();
    let invalid: Vec<&str> = [&ORACLE[..], &["-Ztrust-test-template-oracle-mutation=bool-constant"]].concat();
    for (tag, flags, text) in [
        ("no_seam", seam_off, lane),
        ("no_templates", templates_off, lane),
        ("mutation_alone", oracle_off, "-Ztrust-test-template-oracle-mutation requires -Ztrust-ir-template-instance-oracle"),
        ("invalid_mutation", invalid, "invalid -Ztrust-test-template-oracle-mutation: expected int-constant or envelope-byte"),
    ] {
        let out = format!("out_d_{tag}");
        let failed = frontend("tie_mask.rs", &out, &flags).run_fail();
        let stderr = failed.stderr_utf8();
        assert_no_ice(&stderr);
        assert!(stderr.contains(text), "{tag}: missing `{text}`:\n{stderr}");
        no_rlib(&out, "tie_mask");
    }
}

/// (E) The leg-A rlib carries the level-S row, and an F1 consumer still refuses it: runtime S
/// admission stays closed in this slice.
fn admission_stays_closed() {
    rfs::write("tie_down.rs", DOWNSTREAM);
    let out = "out_e";
    rfs::create_dir_all(out);
    let failed = rustc()
        .input("tie_down.rs")
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Copt-level=0")
        .arg("-Coverflow-checks=on")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower=on")
        .arg("-Zshare-generics=no")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-f1-backend=compiler")
        .arg("-Ztrust-cg-output-gate=strict")
        .extern_("tie_subject", format!("out_a_on/{}", rust_lib_name("tie_subject")))
        .out_dir(out)
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run_fail();
    let stderr = failed.stderr_utf8();
    assert_no_ice(&stderr);
    assert!(
        stderr.contains("level-S instances require sealed template admission (6.6)"),
        "{stderr}"
    );
    no_rlib(out, "tie_down");
}
