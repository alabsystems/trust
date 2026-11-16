//! A MIR `Not` on a `bool` must complement ONE bit, not the whole register.
//!
//! The builtin trust-cg MIR frontend used to map every `UnOp::Not` to the full-width bitwise
//! `Bnot` (`mvn` on AArch64). On a 0/1 `bool` that yields 0xFF..FF / 0xFF..FE, so under
//! `-Ztrust-cg-output-gate=allow-unknown` (the strict gate refuses the function: "unsupported
//! rvalue: UnaryOp(Not, …)") the program below printed `18446744073709551614
//! 18446744073709551615 18446744073709551615` where the default LLVM lane prints `0 1 1`.
//! `crates/trust-cg-bridge` now lowers a `bool` `Not` as `Bxor(x, 1)`.
//!
//! The fixture is deliberately an execution-level check: the wrong code was only observable in
//! the emitted binary, and the bridge unit tests only see the LIR opcode list. Each function
//! consumes the negated bool differently (a cast, an `if`, a `|`, a `^`), because a single
//! consumer can agree with the correct value by luck (`if !b` did on the unfixed compiler).
//!
//! Provenance: measured on Trust main `268b79222d`, `8483fb3b1d` and `d27fa6c198`, all wrong.
//! See docs/issues/2026-09-29-trust-cg-mir-bool-not-miscompiled-under-allow-unknown.md.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{bin_name, rfs, run, rustc};

const SUBJECT: &str = r#"#![crate_name = "bool_not_subject"]

#[unsafe(no_mangle)]
pub extern "C" fn not_cast(x: u64) -> u64 {
    let b = x == 0;
    let nb = !b;
    nb as u64
}

#[unsafe(no_mangle)]
pub extern "C" fn not_lt_cast(x: u64) -> u64 {
    let b = x < 5;
    (!b) as u64
}

#[unsafe(no_mangle)]
pub extern "C" fn not_or(x: u64) -> u64 {
    let a = x < 5;
    let b = x > 1;
    ((!a) | b) as u64
}

#[unsafe(no_mangle)]
pub extern "C" fn not_xor(x: u64) -> u64 {
    let a = x < 5;
    let b = x > 1;
    ((!a) ^ b) as u64
}

#[unsafe(no_mangle)]
pub extern "C" fn not_if(x: u64) -> u64 {
    let b = x < 5;
    if !b { 7 } else { 9 }
}
"#;

const DRIVER: &str = r#"extern crate bool_not_subject;

unsafe extern "C" {
    fn not_cast(x: u64) -> u64;
    fn not_lt_cast(x: u64) -> u64;
    fn not_or(x: u64) -> u64;
    fn not_xor(x: u64) -> u64;
    fn not_if(x: u64) -> u64;
}

fn main() {
    let inputs = [0_u64, 1, 2, 5, 6, 41, 200];
    for f in [not_cast, not_lt_cast, not_or, not_xor, not_if] {
        let row: Vec<String> = inputs.iter().map(|&x| unsafe { f(x) }.to_string()).collect();
        println!("{}", row.join(" "));
    }
}
"#;

/// The expected table, computed with the same expressions on the host.
fn expected() -> String {
    let inputs = [0_u64, 1, 2, 5, 6, 41, 200];
    let rows: [Box<dyn Fn(u64) -> u64>; 5] = [
        Box::new(|x| (!(x == 0)) as u64),
        Box::new(|x| (!(x < 5)) as u64),
        Box::new(|x| ((!(x < 5)) | (x > 1)) as u64),
        Box::new(|x| ((!(x < 5)) ^ (x > 1)) as u64),
        Box::new(|x| if !(x < 5) { 7 } else { 9 }),
    ];
    rows.iter()
        .map(|f| inputs.iter().map(|&x| f(x).to_string()).collect::<Vec<_>>().join(" "))
        .collect::<Vec<_>>()
        .join("\n")
}

fn main() {
    rfs::write("bool_not_subject.rs", SUBJECT);
    rfs::write("driver.rs", DRIVER);
    rfs::create_dir("out");

    // SUBJECT: the builtin MIR frontend with the gate explicitly weakened (the strict gate
    // refuses a bool `Not`, so `allow-unknown` is the only way this body reaches machine code).
    rustc()
        .input("bool_not_subject.rs")
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-cg-frontend=mir")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .out_dir("out")
        .run();

    // OBSERVER: the driver is built with the default backend, verify-off, like the sibling
    // trust-cg run-make observers.
    rustc()
        .input("driver.rs")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .extern_("bool_not_subject", "out/libbool_not_subject.rlib")
        .library_search_path("out")
        .output(bin_name("driver"))
        .run();

    let ran = run("driver");
    assert_eq!(
        ran.stdout_utf8().trim(),
        expected(),
        "a bool `Not` lowered by the trust-cg MIR frontend must equal the LLVM/host value on every input"
    );
}
