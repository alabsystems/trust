fn main() {
    // Trust: native entry captures before ordinary compiletest initialization.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    // SAFETY: first operation at genuine native entry, before CLI setup.
    if let Err(error) = unsafe { compiletest::capture_query_scheduler_at_entry() } {
        eprintln!("compiletest: inherited query transport refused: {error}");
        std::process::exit(75);
    }
    compiletest::cli::main();
}
