// Trust: closure dump for the Lean↔Clean bridge audit lane
// (scripts/regen-trustir-oleans.sh). Loads the bridge root modules
// (BRIDGE_ROOT_MODULES — as of the semCast increment, both
// TrustIr.Semantics.Compare and TrustIr.Semantics.Cast, whose UNION closure
// is vendored since neither imports the other) with all transitive imports
// from freshly-built .olean trees and prints the visited module names, one
// per line — exactly the set the vendored artifacts (fixtures/trustir-oleans
// + vendor/lean-core-oleans) must contain, nothing more.
//
// Usage: bridge_closure <trustir-olean-lib-dir> <lean-core-lib-dir>

use std::path::PathBuf;
use std::process::ExitCode;

use trust_clean::trustir_bridge::BRIDGE_ROOT_MODULES;

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let (Some(ship), Some(core)) = (args.next(), args.next()) else {
        eprintln!("usage: bridge_closure <trustir-olean-lib-dir> <lean-core-lib-dir>");
        return ExitCode::from(2);
    };
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
