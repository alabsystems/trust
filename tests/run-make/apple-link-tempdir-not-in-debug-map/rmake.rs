//! An Apple link must not write rustc's per-link temporary directory into the
//! output's debug map (the `N_OSO` stabs ld64 writes for every object that
//! carries debug information).
//!
//! Under LTO rustc links a copy of each upstream rlib with its Rust objects
//! removed, staged in a RANDOMLY named directory (`add_static_crate`); the
//! native objects left in that copy keep their DWARF, and ld64 recorded each
//! one's absolute path, random directory included. Two identical links then
//! wrote different bytes. Measured 2026-10-01 on two stage2 builds of one
//! Trust commit from one seed: `bin/ay` differed only by
//! `.../deps/rustcEhVYlf/liblibmimalloc_sys-*.rlib(*-static.o)` against
//! `.../deps/rustcUGczRC/...` and the code-signature hash of that page, and
//! because the compiler pins `ay`'s bytes, the compiler differed as well.
//!
//! The fixture is that shape in miniature: a native object built with `-g`,
//! bundled into an rlib, linked into a binary with fat LTO. The rlib lives in
//! `deps/`, not in rustc's working directory, as in a Cargo build: a
//! `libdep.rlib` beside rustc would let a `dsymutil` run in the wrong directory
//! read that copy instead and hide the fault the packed cases look for.
//!
//! - Unpacked: the binary is linked twice to the same output path and the two
//!   results must be byte-identical, and no debug-map entry may name a
//!   `rustc*` temporary directory, while the native object's entry must still
//!   be there (relative to that directory), so the check cannot pass by losing
//!   the debug map.
//! - Packed: rustc runs `dsymutil` while the directory still exists. The debug
//!   map names the staged object relative to it, so `dsymutil` must run inside
//!   it. Run anywhere else it cannot open the object, warns, still EXITS 0, and
//!   writes a dSYM without the object's DWARF, which rustc cannot see. So the
//!   dSYM must hold the native function's DWARF.
//! - A `-oso_prefix` of the user's own: it comes after rustc's and wins (ld64
//!   takes the last one), so the debug map is relative to the user's directory
//!   and `dsymutil` must run in rustc's working directory, as upstream ran it.
//!   Run inside the temporary directory, it loses the DWARF again.

//@ only-apple
//@ ignore-cross-compile (the fixture links a native object for the host)

use run_make_support::object::Endianness;
use run_make_support::object::macho::{MachHeader64, N_OSO};
use run_make_support::object::read::macho::{MachHeader as _, Nlist as _};
use run_make_support::{
    bin_name, cc, cwd, llvm_ar, llvm_dwarfdump, regex, rfs, rust_lib_name, rustc,
};

/// The debug-map (`N_OSO`) entries of `binary`, read from its symbol table:
/// printing every symbol of a binary that links std (`llvm-nm --debug-syms`)
/// would bury a failure's message in the test log.
fn debug_map(binary: &str) -> Vec<String> {
    let data = rfs::read(binary);
    let data = &*data;
    let header = MachHeader64::<Endianness>::parse(data, 0).unwrap();
    let endian = header.endian().unwrap();
    let mut commands = header.load_commands(endian, data, 0).unwrap();
    while let Some(command) = commands.next().unwrap() {
        if let Some(symtab) = command.symtab().unwrap() {
            let symbols = symtab.symbols::<MachHeader64<Endianness>, _>(endian, data).unwrap();
            return symbols
                .iter()
                .filter(|nlist| nlist.n_type() == N_OSO)
                .map(|nlist| {
                    let name = nlist.name(endian, symbols.strings()).unwrap();
                    String::from_utf8_lossy(name).into_owned()
                })
                .collect();
        }
    }
    panic!("`{binary}` has no symbol table");
}

/// `binary`'s dSYM must carry the DWARF of the native object's function.
#[track_caller]
fn assert_dsym_has_native_dwarf(binary: &str) {
    llvm_dwarfdump()
        .arg("--name=native_triple")
        .input(format!("{binary}.dSYM"))
        .run()
        .assert_stdout_contains("DW_TAG_subprogram")
        .assert_stdout_contains("(\"native_triple\")");
}

fn main() {
    rfs::write("native.c", "int native_triple(int x) { return 3 * x; }\n");
    cc().arg("-g").arg("-c").input("native.c").out_exe("native.o").run();
    llvm_ar().obj_to_ar().output_input("libnative.a", "native.o").run();

    rfs::write(
        "dep.rs",
        "#[link(name = \"native\", kind = \"static\")]\n\
         unsafe extern \"C\" {\n\
         \x20   fn native_triple(x: i32) -> i32;\n\
         }\n\
         pub fn triple(x: i32) -> i32 {\n\
         \x20   unsafe { native_triple(x) }\n\
         }\n",
    );
    rfs::create_dir("deps");
    let dep = format!("deps/{}", rust_lib_name("dep"));
    rustc().input("dep.rs").crate_type("rlib").output(&dep).run();

    rfs::write("main.rs", "fn main() {\n    std::process::exit(dep::triple(1) - 3);\n}\n");
    let link = |name: &str, args: &[&str]| {
        rustc()
            .input("main.rs")
            .extern_("dep", &dep)
            .arg("-Clto=fat")
            .args(args)
            .output(bin_name(name))
            .run();
        rfs::read(bin_name(name))
    };
    let temporary = regex::Regex::new(r"(^|/)rustc[0-9A-Za-z]{6}/").unwrap();

    // Unpacked: deterministic, and the temporary directory is not named.
    let first = link("main", &["-Csplit-debuginfo=unpacked"]);
    let second = link("main", &["-Csplit-debuginfo=unpacked"]);
    let osos = debug_map(&bin_name("main"));
    let leaked: Vec<&String> = osos.iter().filter(|path| temporary.is_match(path)).collect();
    assert!(leaked.is_empty(), "debug map names rustc's temporary link directory: {leaked:?}");
    assert!(
        osos.iter().any(|path| path == "libdep.rlib(native.o)"),
        "the native object's debug-map entry is missing (debug map: {osos:?})",
    );
    assert!(first == second, "two identical links wrote different bytes");

    // Packed: `dsymutil` reads the staged object from inside the directory.
    link("packed", &["-Cdebuginfo=1", "-Csplit-debuginfo=packed"]);
    let osos = debug_map(&bin_name("packed"));
    assert!(
        osos.iter().any(|path| path == "libdep.rlib(native.o)"),
        "the packed link's debug map does not name the native object relative to the \
         temporary directory (debug map: {osos:?})",
    );
    assert_dsym_has_native_dwarf(&bin_name("packed"));

    // The user's own `-oso_prefix` wins, and `dsymutil` runs where it applies.
    let user_prefix = format!("-Clink-arg=-Wl,-oso_prefix,{}/", cwd().display());
    link("user-prefix", &["-Cdebuginfo=1", "-Csplit-debuginfo=packed", &user_prefix]);
    let osos = debug_map(&bin_name("user-prefix"));
    let from_cwd = regex::Regex::new(r"^rustc[0-9A-Za-z]{6}/libdep\.rlib\(native\.o\)$").unwrap();
    assert!(
        osos.iter().any(|path| from_cwd.is_match(path)),
        "the user's -oso_prefix did not win (debug map: {osos:?})",
    );
    assert_dsym_has_native_dwarf(&bin_name("user-prefix"));
}
