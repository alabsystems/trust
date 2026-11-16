// Trust: closure dump for the Lean↔Clean bridge audit lane
// (scripts/regen-trustir-oleans.sh). Loads the bridge root modules
// (BRIDGE_ROOT_MODULES — as of the semCast increment, both
// TrustIr.Semantics.Compare and TrustIr.Semantics.Cast, whose UNION closure
// is vendored since neither imports the other) with all transitive imports
// from freshly-built .olean trees and prints the visited module names, one
// per line — exactly the set the vendored artifacts (fixtures/trustir-oleans
// + vendor/lean-core-oleans) must contain, nothing more.
//
// Usage: bridge_closure --roots
//        bridge_closure --admit-lean-toolchain <snapshot-directory> <selected-bin> <new-report>
//        bridge_closure --snapshot-lean <repo> <full-commit> <new-directory>
//        bridge_closure <trustir-olean-lib-dir> <lean-core-lib-dir>

mod toolchain;

use std::ffi::OsStr;
use std::path::PathBuf;
use std::process::ExitCode;

use trust_bridge_closure::BRIDGE_ROOT_MODULES;

fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let first = args.next();
    if first.as_deref() == Some(OsStr::new("--admit-lean-toolchain")) {
        let (Some(source), Some(bin), Some(report)) = (args.next(), args.next(), args.next())
        else {
            eprintln!(
                "usage: bridge_closure --admit-lean-toolchain <snapshot-directory> <selected-bin> <new-report>"
            );
            return ExitCode::from(2);
        };
        if args.next().is_some() {
            eprintln!(
                "usage: bridge_closure --admit-lean-toolchain <snapshot-directory> <selected-bin> <new-report>"
            );
            return ExitCode::from(2);
        }
        return match toolchain::admit(
            PathBuf::from(source).as_path(),
            PathBuf::from(bin).as_path(),
            PathBuf::from(report).as_path(),
        ) {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("bridge_closure: toolchain admission failed: {error}");
                ExitCode::from(1)
            }
        };
    }
    if first.as_deref() == Some(OsStr::new("--roots")) {
        if args.next().is_some() {
            eprintln!("usage: bridge_closure --roots");
            return ExitCode::from(2);
        }
        for root in BRIDGE_ROOT_MODULES {
            println!("{root}");
        }
        return ExitCode::SUCCESS;
    }
    if first.as_deref() == Some(OsStr::new("--snapshot-lean")) {
        let (Some(repo), Some(commit), Some(destination)) = (args.next(), args.next(), args.next())
        else {
            eprintln!("usage: bridge_closure --snapshot-lean <repo> <full-commit> <new-directory>");
            return ExitCode::from(2);
        };
        if args.next().is_some() {
            eprintln!("usage: bridge_closure --snapshot-lean <repo> <full-commit> <new-directory>");
            return ExitCode::from(2);
        }
        let Some(commit) = commit.to_str() else {
            eprintln!("bridge_closure: snapshot requires a full Git commit ID");
            return ExitCode::from(2);
        };
        return match trust_bridge_closure::export_snapshot(
            PathBuf::from(repo).as_path(),
            commit,
            PathBuf::from(destination).as_path(),
        ) {
            Ok(count) => {
                println!("snapshot: {count} producer files from {commit}");
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("bridge_closure: snapshot failed: {error}");
                ExitCode::from(1)
            }
        };
    }
    let (Some(ship), Some(core)) = (first, args.next()) else {
        eprintln!(
            "usage: bridge_closure --roots | --admit-lean-toolchain <snapshot-directory> <selected-bin> <new-report> | --snapshot-lean <repo> <full-commit> <new-directory> | <trustir-olean-lib-dir> <lean-core-lib-dir>"
        );
        return ExitCode::from(2);
    };
    if args.next().is_some() {
        eprintln!("usage: bridge_closure <trustir-olean-lib-dir> <lean-core-lib-dir>");
        return ExitCode::from(2);
    }
    let search_paths = vec![PathBuf::from(ship), PathBuf::from(core)];
    let mut env = clean_kernel::Environment::default();
    env.ensure_native_reducers();
    let roots: Vec<String> = BRIDGE_ROOT_MODULES.iter().map(|s| (*s).to_string()).collect();
    let summaries = match clean_olean::load_modules_with_deps(&mut env, &roots, &search_paths) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("bridge_closure: import failed: {e:?}");
            return ExitCode::from(1);
        }
    };
    for s in &summaries {
        if let Some(m) = s.module_name.as_deref() {
            println!("{m}");
        }
    }
    ExitCode::SUCCESS
}
