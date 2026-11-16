//! Two attributes on a reachable source static that the builtin trust-cg backend used to
//! drop SILENTLY when it materialized the static as object data:
//!
//! * `#[used]` — the static must survive with no reference in its object. trust-ir v41
//!   carries this as `ObjectGlobal::retained`, which the Mach-O writer emits as
//!   `N_NO_DEAD_STRIP` in the symbol's `n_desc`. Before, every production static was
//!   emitted unretained, so a linker running `-dead_strip` could drop exactly the
//!   registration a `#[used]` static exists to keep. The control is an ordinary exported
//!   static in the same object, which must NOT carry the flag.
//! * `#[link_section]` — `ObjectGlobal` has no named-section channel for data, so the
//!   static's bytes would land in the default data section and the placement would vanish.
//!   It is now REFUSED by name, with the options, instead.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::{Object, ObjectSymbol, SymbolFlags};
use run_make_support::{rfs, rust_lib_name, rustc};

const N_NO_DEAD_STRIP: u16 = 0x0020;

fn trust_cg_lib(input: &str, crate_name: &str, out_dir: &str) -> run_make_support::Rustc {
    let mut cmd = rustc();
    cmd.input(input)
        .crate_name(crate_name)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .out_dir(out_dir);
    cmd
}

fn main() {
    rfs::write(
        "used.rs",
        r#"#[used]
static KEEP_REGISTRATION: u64 = 0x2a;

#[unsafe(no_mangle)]
pub static PLAIN_EXPORTED: u64 = 7;

pub fn read_plain() -> u64 {
    PLAIN_EXPORTED
}
"#,
    );
    rfs::create_dir("used-out");
    trust_cg_lib("used.rs", "used_static", "used-out").run();

    let rlib = rfs::read(format!("used-out/{}", rust_lib_name("used_static")));
    let archive = ArchiveFile::parse(&*rlib).expect("rlib is an archive");
    let mut keep = None;
    let mut plain = None;
    for member in archive.members() {
        let member = member.expect("archive member");
        let Ok(file) = run_make_support::object::File::parse(member.data(&*rlib).unwrap()) else {
            continue;
        };
        for symbol in file.symbols() {
            if !symbol.is_definition() {
                continue;
            }
            let name = symbol.name().unwrap_or("");
            let SymbolFlags::MachO { n_desc } = symbol.flags() else {
                continue;
            };
            if name.contains("KEEP_REGISTRATION") {
                keep = Some(n_desc);
            } else if name.contains("PLAIN_EXPORTED") {
                plain = Some(n_desc);
            }
        }
    }
    let keep = keep.expect("the #[used] static must be emitted as a defined data symbol");
    let plain = plain.expect("the control static must be emitted as a defined data symbol");
    assert_ne!(
        keep & N_NO_DEAD_STRIP,
        0,
        "#[used] static must carry N_NO_DEAD_STRIP (n_desc = {keep:#06x})"
    );
    assert_eq!(
        plain & N_NO_DEAD_STRIP,
        0,
        "an ordinary static must NOT be marked retained (n_desc = {plain:#06x})"
    );

    rfs::write(
        "section.rs",
        r#"#[unsafe(link_section = "__DATA,__trustsec")]
#[unsafe(no_mangle)]
pub static PLACED: u64 = 9;

pub fn read_placed() -> u64 {
    PLACED
}
"#,
    );
    rfs::create_dir("section-out");
    trust_cg_lib("section.rs", "section_static", "section-out")
        .run_fail()
        .assert_stderr_contains("reachable static `PLACED` has #[link_section = \"__DATA,__trustsec\"]")
        .assert_stderr_contains("no named-section channel for data");
    assert!(
        !std::path::Path::new(&format!("section-out/{}", rust_lib_name("section_static"))).exists(),
        "a refused #[link_section] static must not leave a shippable rlib"
    );
}
