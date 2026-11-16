//! Trust (R-8 fail-open item 1, 2026-10-01; PKG-CP, 2026-11-12): F1 never lowers a failed
//! check to a bare trap.
//!
//! A failed trust-ir `Assert` (overflow, division, bounds) with no panic site could lower only
//! to a bare trap: no panic message, no location, no panic hook, SIGTRAP instead of abort
//! (R-8 "Fails OPEN" item 1). This fixture pins how each lane answers that:
//!
//! * The control: a function with no checks compiles on both lanes.
//! * The default (`lir`) consumer: an overflow-checked add, a division and an index each make
//!   F1 exit non-zero under the `unfaithful-panic` census class and write no rlib. That lane
//!   still has no panic path.
//! * The compiler consumer (`-Ztrust-cg-f1-backend=compiler`, PKG-CP): the same three checks are
//!   SITED (each names rustc's panic entry and a `core::panic::Location` record), and none is
//!   refused as unfaithful. The object then either is refused by the object reader (a record's
//!   relocated file pointer is not admitted yet: `[f1-output-gate:object]`) or ships, and a
//!   shipped object names rustc's entry for its check. Either way no bare trap ships. The bridge
//!   keeps its `ImplicitPanicUnfaithful` row for an unsited `Assert` and an `AssertInvoke`;
//!   `crates/trust-cg-bridge/tests/f1_compile.rs` pins that row.
//! * A check whose condition is constant true (`x % 7`) is folded on the compiler consumer:
//!   the crate compiles and its object names no panic entry.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::{Object, ObjectSymbol};
use run_make_support::{path, rfs, rustc};

fn f1(input: &str, out: &str, compiler_lane: bool) -> rustc::Rustc {
    let mut rustc = rustc();
    rustc
        .input(input)
        .crate_type("lib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Coverflow-checks=on")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .out_dir(out);
    if compiler_lane {
        rustc.arg("-Ztrust-cg-f1-backend=compiler").arg("-Ztrust-cg-output-gate=allow-unknown");
    }
    rustc
}

/// The undefined symbols of every object member of `rlib`.
fn undefined_symbols(rlib: &std::path::Path) -> Vec<String> {
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
    rfs::write("ok.rs", "#![crate_name = \"ok\"]\npub fn masked(x: u32) -> u8 { (x & 0xff) as u8 }\n");
    f1("ok.rs", "out_ok", false).run();
    f1("ok.rs", "out_ok_compiler", true).run();

    for (name, body, entry) in [
        ("add", "pub fn add(a: u32, b: u32) -> u32 { a + b }", "panic_const_add_overflow"),
        ("div", "pub fn div(a: u32, b: u32) -> u32 { a / b }", "panic_const_div_by_zero"),
        ("index", "pub fn index(a: &[u32; 4], i: usize) -> u32 { a[i] }", "panic_bounds_check"),
    ] {
        let input = format!("{name}.rs");
        rfs::write(&input, format!("#![crate_name = \"{name}\"]\n{body}\n"));

        let out = format!("out_{name}");
        let refused = f1(&input, &out, false).run_fail();
        refused.assert_stderr_contains("[unfaithful-panic]");
        refused.assert_stderr_contains("would lower to a bare trap");
        assert!(
            !path(&out).join(format!("lib{name}.rlib")).exists(),
            "{name}: an rlib was written despite the refusal"
        );

        let out = format!("out_{name}_compiler");
        let done = f1(&input, &out, true).run_unchecked();
        let stderr = done.stderr_utf8();
        assert!(
            stderr.contains("0 runtime check(s) folded (constant true), 1 sited at rustc's panic entry"),
            "{name}: the check was not sited: {stderr}"
        );
        assert!(!stderr.contains("[unfaithful-panic]"), "{name}: refused as unfaithful: {stderr}");
        let rlib = path(&out).join(format!("lib{name}.rlib"));
        if done.status().success() {
            let undefined = undefined_symbols(&rlib);
            assert!(
                undefined.iter().any(|u| u.contains(entry)),
                "{name}: the shipped object does not call `{entry}`: {undefined:?}"
            );
        } else {
            assert!(
                stderr.contains("[f1-output-gate:object]") && stderr.contains("carries relocations"),
                "{name}: refused for a reason other than the record's relocation: {stderr}"
            );
            assert!(!rlib.exists(), "{name}: an rlib was written despite the refusal");
        }
    }

    rfs::write("rem7.rs", "#![crate_name = \"rem7\"]\npub fn rem7(x: u32) -> u32 { x % 7 }\n");
    let folded = f1("rem7.rs", "out_rem7_compiler", true).run();
    folded.assert_stderr_contains("1 runtime check(s) folded (constant true), 0 sited");
    let undefined = undefined_symbols(&path("out_rem7_compiler").join("librem7.rlib"));
    assert!(
        undefined.iter().all(|u| !u.contains("panic")),
        "rem7: the folded check still names a panic entry: {undefined:?}"
    );
}
