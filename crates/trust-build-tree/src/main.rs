//! A minimal source-buildable front door to the shared native manager.

fn main() {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        let mut args = std::env::args_os().skip(1).collect::<Vec<_>>();
        // Match Bootstrap's early administrative entry as well as direct use.
        if args.first().is_some_and(|arg| arg == "--trust-build-tree-lock") {
            args.remove(0);
        }
        std::process::exit(trust_build_tree::trust_repo_lock::management::cli::run(&args).into());
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        eprintln!("native build-tree management is unavailable on this platform");
        std::process::exit(2);
    }
}
