//! The rustc Trust-IR frontend must carry an assembled promoted scalar all the
//! way through the shipped rlib instead of leaving GlobalRef dangling.
//!
//! This is deliberately the first, narrow object-global rung: immutable,
//! initialized, module-local `u64` storage. Strict still refuses because the
//! proof gate does not model GlobalAddr/Load yet; allow-unknown and an explicit
//! gate-off acknowledgement may emit, but both must retain identical storage.
//! Reachable source statics remain refused by the mono-item inventory.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::macho::{ARM64_RELOC_PAGE21, ARM64_RELOC_PAGEOFF12};
use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::{
    Object, ObjectSection, ObjectSymbol, RelocationFlags, RelocationTarget,
};
use run_make_support::{bin_name, rfs, run, rust_lib_name, rustc};

const ANSWER: u64 = 0x1122_3344_5566_7788;

fn main() {
    rfs::write(
        "promoted.rs",
        r#"#[inline(never)]
pub fn read_promoted() -> u64 {
    let value: &'static u64 = &0x1122_3344_5566_7788_u64;
    *value | *value
}
"#,
    );
    for directory in ["allow", "allow-ir", "off", "off-ir", "strict", "static-out"] {
        rfs::create_dir(directory);
    }

    let allowed = rustc()
        .input("promoted.rs")
        .crate_name("promoted_allow")
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .arg("-Ztrust-dump=ir:allow-ir")
        .out_dir("allow")
        .run();
    allowed
        .assert_stderr_contains("trust-cg trust-ir frontend: 1/1 reachable function(s) completed")
        .assert_stderr_contains("0 [PROVED]")
        .assert_stderr_contains("0 [VALIDATED]")
        .assert_stderr_contains("1 uncertified (emitted unproven under AllowUnknown)")
        .assert_stderr_contains("0 refuted");

    let allow_ir = rfs::read_to_string("allow-ir/promoted_allow.trust-ir.txt");
    let global = assert_promoted_ir(&allow_ir);
    let allow_rlib = format!("allow/{}", rust_lib_name("promoted_allow"));
    inspect_promoted_object(&allow_rlib, &global);
    link_and_run("promoted_allow", &allow_rlib, "allow-driver.rs", "allow-driver");

    let off = rustc()
        .input("promoted.rs")
        .crate_name("promoted_off")
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-output-gate=off")
        .arg("-Ztrust-dump=ir:off-ir")
        .out_dir("off")
        .run();
    off.assert_stderr_contains("proven-output gate explicitly DISABLED")
        .assert_stderr_contains("carry NO output-preservation proof");

    let off_ir = rfs::read_to_string("off-ir/promoted_off.trust-ir.txt");
    let off_global = assert_promoted_ir(&off_ir);
    assert_eq!(global, off_global, "gate policy must not rewrite semantic global identity");
    let off_rlib = format!("off/{}", rust_lib_name("promoted_off"));
    inspect_promoted_object(&off_rlib, &off_global);
    link_and_run("promoted_off", &off_rlib, "off-driver.rs", "off-driver");

    rustc()
        .input("promoted.rs")
        .crate_name("promoted_strict")
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-output-gate=strict")
        .out_dir("strict")
        .run_fail()
        .assert_stderr_contains("proven-output gate rejected it")
        .assert_stderr_contains("Unknown, fail-closed under StrictProvenOnly")
        .assert_stderr_contains("GlobalAddr");
    assert!(
        !std::path::Path::new(&format!("strict/{}", rust_lib_name("promoted_strict"))).exists(),
        "strict refusal must not leave a shippable rlib"
    );

    rfs::write(
        "source-static.rs",
        r#"pub static SOURCE_STATIC: u64 = 0x1122_3344_5566_7788;

pub fn read_source_static() -> u64 {
    SOURCE_STATIC
}
"#,
    );
    // Trust: reachable statics are WIRED into trust-cg object emission since
    // 408a792439 (relocation-free, non-thread-local, default-visibility statics
    // materialize as object data), so this lane no longer pins the retired
    // "reachable static … is not wired" refusal. Under `allow-unknown` the unit
    // now compiles with its one function emitted UNCERTIFIED — the GlobalAddr
    // read is an honest unknown, never a hidden unproven claim.
    rustc()
        .input("source-static.rs")
        .crate_name("source_static")
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .out_dir("static-out")
        .run()
        .assert_stderr_contains("1/1 reachable function(s) completed")
        .assert_stderr_contains("1 uncertified (emitted unproven under AllowUnknown)");
    // The soundness half: the SAME unit under the strict gate is still REFUSED —
    // an unproven GlobalAddr read never reaches an object.
    rustc()
        .input("source-static.rs")
        .crate_name("source_static")
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-output-gate=strict")
        .out_dir("static-strict")
        .run_fail()
        .assert_stderr_contains("proven-output gate rejected it");
    assert!(
        !std::path::Path::new(&format!("static-strict/{}", rust_lib_name("source_static")))
            .exists(),
        "strict refusal of a static-reading unit must not leave a shippable rlib"
    );
    // And the residual that IS still unwired keeps its refusal, by name: a static
    // whose initializer embeds a pointer needs relocated data the backend does not
    // emit.
    rfs::write(
        "pointer-static.rs",
        r#"pub static POINTER_STATIC: &u64 = &0x1122_3344_5566_7788;

pub fn read_pointer_static() -> u64 {
    *POINTER_STATIC
}
"#,
    );
    rustc()
        .input("pointer-static.rs")
        .crate_name("pointer_static")
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .out_dir("pointer-static-out")
        .run_fail()
        .assert_stderr_contains("reachable static `POINTER_STATIC` embeds 1 pointer(s)")
        .assert_stderr_contains("not wired into trust-cg object");
}

fn assert_promoted_ir(text: &str) -> String {
    let globals = text
        .lines()
        .filter_map(|line| line.trim().strip_prefix("global internal @"))
        .collect::<Vec<_>>();
    assert_eq!(globals.len(), 1, "expected one assembled internal global:\n{text}");
    let name = globals[0].split_whitespace().next().expect("global symbol").to_string();
    assert!(name.starts_with("__trust_promoted_"), "unexpected promotion name `{name}`");
    assert!(globals[0].contains("u64 = 1234605616436508552"));
    assert_eq!(text.matches("global_addr @global.0").count(), 1);
    assert_eq!(text.matches("load u64").count(), 2);
    name
}

fn inspect_promoted_object(rlib: &str, global: &str) {
    let archive_data = rfs::read(rlib);
    let archive = ArchiveFile::parse(&*archive_data).expect("rlib archive");
    let mut definitions = 0;
    let mut undefined_twins = 0;
    let mut relocation_types = Vec::new();

    for member in archive.members() {
        let member = member.expect("archive member");
        let data = member.data(&*archive_data).expect("archive member data");
        let Ok(object) = run_make_support::object::File::parse(data) else { continue };
        for symbol in object.symbols() {
            let Ok(name) = symbol.name() else { continue };
            if !symbol_matches(name, global) {
                continue;
            }
            if symbol.is_undefined() {
                undefined_twins += 1;
                continue;
            }
            definitions += 1;
            assert!(symbol.is_definition());
            assert!(symbol.is_local(), "Internal global escaped object-local visibility");
            assert!(!symbol.is_weak());
            let section = object
                .section_by_index(symbol.section_index().expect("defined global section"))
                .expect("global section");
            assert_eq!(section.segment_name().expect("segment name"), Some("__TEXT"));
            assert_eq!(section.name().expect("section name"), "__const");
            assert!(section.align() >= 8);
            let bytes = section
                .data_range(symbol.address(), 8)
                .expect("read global bytes")
                .expect("global bytes lie in section");
            assert_eq!(bytes, ANSWER.to_le_bytes());
        }

        for section in object.sections() {
            for (_, relocation) in section.relocations() {
                let RelocationTarget::Symbol(index) = relocation.target() else { continue };
                let symbol = object.symbol_by_index(index).expect("relocation target symbol");
                let Ok(name) = symbol.name() else { continue };
                if !symbol_matches(name, global) {
                    continue;
                }
                assert_eq!(section.name().expect("relocation section name"), "__text");
                let RelocationFlags::MachO { r_type, .. } = relocation.flags() else {
                    panic!("global relocation was not encoded as Mach-O: {relocation:?}");
                };
                relocation_types.push(r_type);
            }
        }
    }

    assert_eq!(definitions, 1, "promoted storage must have one exact definition");
    assert_eq!(undefined_twins, 0, "local storage must not have an undefined twin");
    relocation_types.sort_unstable();
    assert_eq!(
        relocation_types,
        [ARM64_RELOC_PAGE21, ARM64_RELOC_PAGEOFF12],
        "GlobalRef must carry exactly one PAGE21/PAGEOFF12 pair"
    );
}

fn symbol_matches(object_name: &str, logical_name: &str) -> bool {
    object_name == logical_name || object_name.strip_prefix('_') == Some(logical_name)
}

fn link_and_run(crate_name: &str, rlib: &str, source: &str, output: &str) {
    rfs::write(
        source,
        format!(
            "extern crate {crate_name};\n\
             fn main() {{ println!(\"{{}}\", {crate_name}::read_promoted()); }}\n"
        ),
    );
    rustc()
        .input(source)
        .edition("2024")
        .arg("-Cpanic=abort")
        // Trust: this driver is the end-to-end EXECUTION OBSERVER — the producer,
        // object and IR claims above are the subjects; it is built and run only to
        // check the linked runtime answer, so it must not itself be a verification
        // subject (same rule as the sibling observer binaries).
        .arg("-Ztrust-verify=off")
        .extern_(crate_name, rlib)
        .output(bin_name(output))
        .run();
    assert_eq!(run(output).stdout_utf8().trim(), ANSWER.to_string());
}
