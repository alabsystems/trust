//! D39/D40 level-R admission: an actual upstream leaf and a real two-edge upstream chain.
//! Build producer and consumer with this same compiler; compare the shipped F1 rlib against
//! LLVM on edge inputs and require upstream provenance after the strict output gate. These
//! are concrete non-generic bodies, not the still-open S/6.6 template admission milestone.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::{cmd, rfs, run, rust_lib_name, rustc, serde_json};

const UP: &str = r#"#![no_std]
#[inline] pub fn leaf(x: u64) -> u64 { x ^ 0x55 }
#[inline] pub fn middle(x: u64) -> u64 { leaf(x) ^ 7 }
#[inline] pub fn root(x: u64) -> u64 { middle(x) ^ 0x8000_0000_0000_0000 }
"#;
const DOWN: &str = r#"#![no_std]
#[inline(never)] pub fn entry_chain(x: u64) -> u64 { up::root(x) }
#[inline(never)] pub fn entry_leaf(x: u64) -> u64 { up::leaf(x) }
"#;
const RUNNER: &str = r#"fn main() {
    for x in [0, 1, 7, 127, 128, 255, 256, u32::MAX as u64, 1u64 << 63, u64::MAX] {
        println!("{x}:{}:{}", subject::entry_chain(x), subject::entry_leaf(x));
    }
}
"#;

fn command(input: &str, name: &str, out: &str, checks: &str) -> run_make_support::Rustc {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input(input)
        .crate_name(name)
        .crate_type("rlib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Copt-level=0")
        .arg(format!("-Coverflow-checks={checks}"))
        .arg("-Ztrust-verify=off")
        .out_dir(out)
        .env_remove("TRUST_NO_VERIFY");
    cmd
}

fn consumer(out: &str, checks: &str, producer: &str, f1: bool) -> run_make_support::Rustc {
    let mut cmd = command("down.rs", "subject", out, checks);
    cmd.extern_("up", producer).arg("-Ztrust-ir-lower=on");
    if f1 {
        cmd.arg("-Zcodegen-backend=trust-cg")
            .arg("-Ztrust-cg-frontend=trust-ir")
            .arg("-Ztrust-cg-f1-backend=compiler")
            .arg("-Ztrust-cg-output-gate=strict");
    }
    cmd
}

fn execute(out: &str, producer_dir: &str, tag: &str) -> String {
    rustc()
        .input("runner.rs")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .arg(format!("-Ldependency={producer_dir}"))
        .extern_("subject", format!("{out}/{}", rust_lib_name("subject")))
        .output(tag)
        .env_remove("TRUST_NO_VERIFY")
        .run();
    run(tag).stdout_utf8()
}

fn no_output(out: &str, stderr: &str, check: &str) {
    assert!(stderr.contains(check), "missing `{check}`:\n{stderr}");
    assert!(!stderr.contains("internal compiler error"), "{stderr}");
    assert!(!std::path::Path::new(out).join(rust_lib_name("subject")).exists());
}

fn compiler_call_evidence(out: &str, checks: &str, stderr: &str) {
    assert!(stderr.contains("completed source -> trust_ir_of -> codegen_module"), "{stderr}");
    assert!(!stderr.contains("lower_module_to_lir"), "{stderr}");
    assert!(stderr.contains(" 0 not closed, 0 refuted"), "{stderr}");
    let archive = rfs::read(format!("{out}/{}", rust_lib_name("subject")));
    let archive_file = ArchiveFile::parse(&*archive).expect("rlib archive");
    let mut objects = Vec::new();
    for member in archive_file.members() {
        let member = member.expect("archive member");
        if member.name().ends_with(b".o") {
            objects.push(member.data(&*archive).expect("object bytes").to_vec());
        }
    }
    assert_eq!(objects.len(), 1, "one codegen unit, one shipped object");
    let mut object = objects.pop().unwrap();
    // Darwin archive newline padding is outside the Mach-O string table.
    while object.last() == Some(&b'\n') { object.pop(); }
    let path = format!("shipped-{checks}.o");
    rfs::write(&path, &object);
    let digest = cmd("shasum").arg("-a").arg("256").arg(&path).run().stdout_utf8();
    let certificates = rfs::read_to_string(format!("{out}/subject.trust-cg-certificates.json"));
    let json: serde_json::Value = serde_json::from_str(&certificates).expect("certificate JSON");
    assert_eq!(json["schema"], "trust-cg-bridge.call-refinement.v1");
    assert_eq!(json["object_sha256"], digest.split_whitespace().next().unwrap());
    let certs = json["certificates"].as_array().expect("certificates");
    assert_eq!(json["closure"]["closed_kernel"].as_array().unwrap().len(), certs.len());
    assert!(json["closure"]["unclosed"].as_array().unwrap().is_empty());
    let disassembly = cmd("objdump").arg("-d").arg("-r").arg(&path).run().stdout_utf8();
    let mut functions: Vec<(String, Vec<String>)> = Vec::new();
    for line in disassembly.lines() {
        if let Some(rest) = line.strip_suffix(">:")
            && let Some((address, name)) = rest.split_once(" <")
            && address.chars().all(|c| c.is_ascii_hexdigit())
        {
            functions.push((name.into(), Vec::new()));
        } else if let Some((_, body)) = functions.last_mut() {
            body.push(line.into());
        }
    }
    for (caller, callee) in [("entry_chain", "root"), ("root", "middle"), ("middle", "leaf"), ("entry_leaf", "leaf")] {
        let named: Vec<_> = certs.iter().filter(|c| c["symbol"].as_str().unwrap().contains(caller)).collect();
        assert_eq!(named.len(), 1, "one certificate for {caller}: {certificates}");
        let cert = named[0];
        let sites = cert["call_sites"].as_array().expect("call sites");
        let site = sites.iter().find(|s| s["symbol"].as_str().is_some_and(|s| s.contains(callee)))
            .unwrap_or_else(|| panic!("{caller} has no actual call site to {callee}: {cert}"));
        let callee_symbol = site["symbol"].as_str().unwrap();
        assert!(certs.iter().any(|c| c["symbol"].as_str() == Some(callee_symbol)));
        assert!(cert["assumptions"].as_array().unwrap().iter().any(|a| a["kind"] == "CoEmitted" && a["symbol"] == callee_symbol));
        let bodies: Vec<_> = functions.iter().filter(|(name, _)| name.contains(caller)).collect();
        assert_eq!(bodies.len(), 1, "one emitted {caller}: {disassembly}");
        let body = &bodies[0].1;
        assert!(body.iter().enumerate().any(|(i, line)| {
            matches!(line.split('\t').nth(1).map(str::trim), Some("bl" | "b"))
                && (line.contains(callee) || body.get(i + 1).is_some_and(|line| line.contains("ARM64_RELOC_BRANCH26") && line.contains(callee)))
        }), "shipped {caller} has no machine call to {callee}: {disassembly}");
    }
}

fn main() {
    rfs::write("up.rs", UP);
    rfs::write("down.rs", DOWN);
    rfs::write("runner.rs", RUNNER);
    for checks in ["on", "off"] {
        let producer_dir = format!("producer-{checks}");
        command("up.rs", "up", &producer_dir, checks).arg("-Ztrust-ir-lower=on").run();
        let producer = format!("{producer_dir}/{}", rust_lib_name("up"));
        let f1 = format!("f1-{checks}");
        let stderr = consumer(&f1, checks, &producer, true).run().stderr_utf8();
        assert!(!stderr.contains("internal compiler error"), "{stderr}");
        compiler_call_evidence(&f1, checks, &stderr);
        let coverage = rfs::read_to_string(format!("{f1}/subject.trust-instance-coverage.json"));
        assert!(coverage.matches("\"kind\": \"upstream-entry\"").count() >= 3, "{coverage}");
        for needle in ["content SHA256", "rebound module SHA256", "conservation re-derived"] {
            assert!(coverage.contains(needle), "missing `{needle}`:\n{coverage}");
        }
        let oracle = format!("llvm-{checks}");
        consumer(&oracle, checks, &producer, false).run();
        assert_eq!(
            execute(&f1, &producer_dir, &format!("run-f1-{checks}")),
            execute(&oracle, &producer_dir, &format!("run-llvm-{checks}")),
        );
        let mismatch = format!("mismatch-{checks}");
        let other = if checks == "on" { "off" } else { "on" };
        let stderr = consumer(&mismatch, other, &producer, true).run_fail().stderr_utf8();
        no_output(&mismatch, &stderr, "mode: overflow-check-mode(");
    }
    command("up.rs", "up", "without-producer", "on").run();
    let producer = format!("without-producer/{}", rust_lib_name("up"));
    let stderr = consumer("missing", "on", &producer, true).run_fail().stderr_utf8();
    no_output("missing", &stderr, "compiled without the Trust-IR producer");
}
