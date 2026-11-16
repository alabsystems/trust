//! Trust (PKG-CP, R-8 item P): a failed check on F1's compiler lane panics as Rust does.
//!
//! Each subject is one `pub fn f(i64, i64) -> i64` holding one runtime check, compiled twice
//! as an rlib at `-Ztrust-verify=off -Ztrust-ir-lower -Coverflow-checks=on -Cpanic=abort`: by
//! LLVM (the oracle), and by F1's compiler lane (`-Ztrust-cg-f1-backend=compiler`). The same
//! LLVM-built driver links each and calls `f` once with inputs that pass the check and once
//! with inputs that fail it. On every input F1's stdout, stderr and exit status equal LLVM's
//! (the panic line names the same `file:line:col` and message; the thread id, which differs
//! between any two runs, is masked). One subject runs under a panic hook the driver installs,
//! which reads the `core::panic::Location` record and the message the failed check passed.
//!
//! The gate is `allow-unknown`: the strict gate grades a function with a sited check Unknown
//! until the call-event gate models the failure call (PKG-C5c), so strict refuses it.
//!
//! Two subjects hold only a check whose condition is constant true (`x % 7`, and `[x, 2, 3,
//! 4][3]`): their F1 objects name no panic entry, because the check is folded.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::{Object, ObjectSymbol};
use run_make_support::{rfs, rustc};

struct Subject {
    name: &'static str,
    body: &'static str,
    /// `(a, b)` that pass the check, then `(a, b)` that fail it.
    inputs: [(i64, i64); 2],
    /// The message the failing input prints.
    message: &'static str,
    hook: bool,
}

const MIN32: i64 = i32::MIN as i64;

const SUBJECTS: &[Subject] = &[
    Subject { name: "add", body: "(a as i32 + b as i32) as i64", inputs: [(1, 2), (i32::MAX as i64, 1)], message: "attempt to add with overflow", hook: false },
    Subject { name: "sub", body: "(a as u32 - b as u32) as i64", inputs: [(5, 3), (3, 5)], message: "attempt to subtract with overflow", hook: false },
    Subject { name: "mul", body: "(a as i32 * b as i32) as i64", inputs: [(6, 7), (65536, 65536)], message: "attempt to multiply with overflow", hook: false },
    Subject { name: "neg", body: "(-(a as i32)) as i64", inputs: [(5, 0), (MIN32, 0)], message: "attempt to negate with overflow", hook: false },
    Subject { name: "div", body: "(a as u32 / b as u32) as i64", inputs: [(7, 2), (7, 0)], message: "attempt to divide by zero", hook: false },
    Subject { name: "rem", body: "(a as u32 % b as u32) as i64", inputs: [(7, 2), (7, 0)], message: "attempt to calculate the remainder with a divisor of zero", hook: false },
    Subject { name: "div_min", body: "(a as i32 / b as i32) as i64", inputs: [(-7, 2), (MIN32, -1)], message: "attempt to divide with overflow", hook: false },
    Subject { name: "rem_min", body: "(a as i32 % b as i32) as i64", inputs: [(-7, 2), (MIN32, -1)], message: "attempt to calculate the remainder with overflow", hook: false },
    Subject { name: "shl", body: "((a as u32) << (b as u32)) as i64", inputs: [(1, 3), (1, 32)], message: "attempt to shift left with overflow", hook: false },
    Subject { name: "shr", body: "((a as i32) >> (b as u32)) as i64", inputs: [(-8, 1), (1, 40)], message: "attempt to shift right with overflow", hook: false },
    Subject { name: "bounds", body: "{ let t = [10i64, 20, 30, 40]; t[a as usize] }", inputs: [(2, 0), (4, 0)], message: "index out of bounds: the len is 4 but the index is 4", hook: false },
    Subject { name: "hooked", body: "(a as i32 + b as i32) as i64", inputs: [(1, 2), (i32::MAX as i64, 1)], message: "hook: subj.rs:1:", hook: true },
];

/// Subjects whose one check is constant true.
const FOLDED: &[(&str, &str)] =
    &[("rem7", "(a as u32 % 7) as i64"), ("index3", "{ let t = [a, 2, 3, 4]; let _ = b; t[3] }")];

const DRIVER: &str = r#"extern crate subj;
fn main() {
    let v: Vec<i64> = std::env::args().skip(1).map(|s| s.parse().unwrap()).collect();
    if std::env::var_os("SUBJ_HOOK").is_some() {
        std::panic::set_hook(Box::new(|info| {
            let loc = info.location().unwrap();
            eprintln!("hook: {}:{}:{}: {}", loc.file(), loc.line(), loc.column(), info.payload_as_str().unwrap_or("?"));
        }));
    }
    println!("{}", subj::f(v[0], v[1]));
}
"#;

fn subject_source(body: &str) -> String {
    format!("pub fn f(a: i64, b: i64) -> i64 {{ let _ = (a, b); {body} }}\n")
}

/// The subject's rlib in `out`, by LLVM or by F1's compiler lane.
fn compile(out: &str, f1: bool) -> run_make_support::Rustc {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input("subj.rs")
        .crate_name("subj")
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Coverflow-checks=on")
        .arg("-Zunstable-options")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .out_dir(out);
    if f1 {
        cmd.arg("-Zcodegen-backend=trust-cg")
            .arg("-Ztrust-cg-frontend=trust-ir")
            .arg("-Ztrust-cg-f1-backend=compiler")
            .arg("-Ztrust-cg-output-gate=allow-unknown");
    }
    cmd
}

fn driver(out: &str) -> String {
    rustc()
        .input("driver.rs")
        .crate_type("bin")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Ztrust-verify=off")
        .extern_("subj", format!("{out}/libsubj.rlib"))
        .output(format!("{out}/driver"))
        .run();
    format!("{out}/driver")
}

/// `thread 'main' (12345) panicked` -> `thread 'main' panicked`: the id differs between runs.
fn mask_thread_id(stderr: &str) -> String {
    stderr
        .lines()
        .map(|line| match (line.find("thread '"), line.find(") panicked")) {
            (Some(_), Some(end)) => match line[..end].rfind(" (") {
                Some(start) => format!("{}{}", &line[..start], &line[end + 1..]),
                None => line.to_string(),
            },
            _ => line.to_string(),
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn run(exe: &str, (a, b): (i64, i64), hook: bool) -> (String, String, Option<i32>, Option<i32>) {
    let mut cmd = run_make_support::cmd(exe);
    cmd.arg(a.to_string()).arg(b.to_string());
    if hook {
        cmd.env("SUBJ_HOOK", "1");
    }
    let done = cmd.run_unchecked();
    use std::os::unix::process::ExitStatusExt;
    let status = done.status();
    (done.stdout_utf8(), mask_thread_id(&done.stderr_utf8()), status.code(), status.signal())
}

/// The undefined symbols of the one object member of `rlib`.
fn undefined_symbols(rlib: &str) -> Vec<String> {
    let data = rfs::read(rlib);
    let archive = ArchiveFile::parse(&*data).expect("an archive");
    let mut names = Vec::new();
    for member in archive.members() {
        let member = member.expect("a member");
        if !member.name().ends_with(b".o") {
            continue;
        }
        let bytes = member.data(&*data).expect("member data");
        let object = run_make_support::object::File::parse(bytes).expect("an object");
        for symbol in object.symbols() {
            if symbol.is_undefined() {
                names.push(symbol.name().expect("a name").to_string());
            }
        }
    }
    names
}

fn main() {
    rfs::write("driver.rs", DRIVER);
    for s in SUBJECTS {
        rfs::write("subj.rs", subject_source(s.body));
        let llvm = format!("llvm_{}", s.name);
        let f1 = format!("f1_{}", s.name);
        compile(&llvm, false).run();
        let compiled = compile(&f1, true).run();
        compiled.assert_stderr_contains("sited at rustc's panic entry and location (PKG-CP)");
        compiled.assert_stderr_not_contains("[unfaithful-panic]");
        let (oracle, got) = (driver(&llvm), driver(&f1));
        for (i, input) in s.inputs.into_iter().enumerate() {
            let want = run(&oracle, input, s.hook);
            if i == 1 {
                assert!(want.1.contains(s.message), "{}: LLVM's stderr {:?}", s.name, want.1);
            }
            let have = run(&got, input, s.hook);
            assert_eq!(have, want, "{} on {input:?}: F1 (left) differs from LLVM (right)", s.name);
        }
    }
    for (name, body) in FOLDED {
        rfs::write("subj.rs", subject_source(body));
        let out = format!("f1_{name}");
        let compiled = compile(&out, true).run();
        compiled.assert_stderr_contains("1 runtime check(s) folded (constant true), 0 sited");
        let undefined = undefined_symbols(&format!("{out}/libsubj.rlib"));
        assert!(
            undefined.iter().all(|u| !u.contains("panic")),
            "{name}: the object names a panic entry: {undefined:?}"
        );
    }
}
