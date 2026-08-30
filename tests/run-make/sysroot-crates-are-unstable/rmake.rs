// Check that crates in the sysroot are treated as unstable, unless they are
// on a list of known-stable sysroot crates.

use std::path::{Path, PathBuf};
use std::str;

use run_make_support::{rfs, rustc, target};

fn is_stable_crate(name: &str) -> bool {
    // Trust: `trust_bignum` is the I6 bignum carrier runtime — the runtime half
    // of Clean/Lean `Nat`. It ships in the sysroot and declares its surface
    // stable ON PURPOSE (crates/trust-bignum/src/lib.rs, "Plan step 8 as
    // amended by review defect 4"): the std build passes
    // `-Zforce-unstable-if-unmarked`, which would otherwise gate the crate
    // behind `rustc_private`, and the carrier is meant to be nameable. Twelve
    // in-tree `clean_origin_*` ui tests name it with no feature gate.
    matches!(name, "std" | "alloc" | "core" | "proc_macro" | "trust_bignum")
}

fn main() {
    for cr in get_unstable_sysroot_crates() {
        check_crate_is_unstable(&cr);
    }
    println!("Done");
}

#[derive(Debug)]
struct Crate {
    name: String,
    path: PathBuf,
}

fn check_crate_is_unstable(cr: &Crate) {
    let Crate { name, path } = cr;

    print!("- Verifying that sysroot crate '{name}' is an unstable crate ...");

    // Checking if rmeta path exists
    let rmeta_path = path.with_extension("rmeta");

    let mut cmd = rustc();
    cmd.crate_type("rlib").extern_(name, path); // Pass the rlib

    if rmeta_path.exists() {
        cmd.extern_(name, &rmeta_path);
    }

    let output = cmd.input("-").stdin_buf(format!("extern crate {name};")).run_fail();

    // Make sure it failed for the intended reason, not some other reason.
    // (The actual feature required varies between crates.)
    output.assert_stderr_contains("use of unstable library feature");

    println!(" OK");
}

fn get_unstable_sysroot_crates() -> Vec<Crate> {
    let sysroot_libs_dir =
        PathBuf::from(rustc().print("target-libdir").target(target()).run().stdout_utf8().trim());
    println!("Sysroot libs dir: {sysroot_libs_dir:?}");

    // Generate a list of all library crates in the sysroot.
    let sysroot_crates = get_all_crates_in_dir(&sysroot_libs_dir);
    println!(
        "Found {} sysroot crates: {:?}",
        sysroot_crates.len(),
        sysroot_crates.iter().map(|cr| &cr.name).collect::<Vec<_>>()
    );

    // Self-check: If we didn't find `core`, we probably checked the wrong directory.
    assert!(
        sysroot_crates.iter().any(|cr| cr.name == "core"),
        "Couldn't find `core` in {sysroot_libs_dir:?}"
    );

    let unstable_sysroot_crates =
        sysroot_crates.into_iter().filter(|cr| !is_stable_crate(&cr.name)).collect::<Vec<_>>();
    // Self-check: There should be at least one unstable crate in the directory.
    assert!(
        !unstable_sysroot_crates.is_empty(),
        "Couldn't find any unstable crates in {sysroot_libs_dir:?}"
    );
    unstable_sysroot_crates
}

fn get_all_crates_in_dir(libs_dir: &Path) -> Vec<Crate> {
    let mut libs = vec![];
    rfs::read_dir_entries(libs_dir, |path| {
        if !path.is_file() {
            return;
        }
        if let Some(name) = crate_name_from_path(path) {
            libs.push(Crate { name, path: path.to_owned() });
        }
    });
    libs.sort_by(|a, b| a.name.cmp(&b.name));
    libs
}

/// Treat a file as a crate if its name begins with `lib` and ends with `.rlib`.
/// The crate name is the part before the first hyphen (if any).
fn crate_name_from_path(path: &Path) -> Option<String> {
    let name = path
        .file_name()?
        .to_str()?
        .strip_prefix("lib")?
        .strip_suffix(".rlib")?
        .split('-')
        .next()
        .expect("split always yields at least one string");
    Some(name.to_owned())
}
