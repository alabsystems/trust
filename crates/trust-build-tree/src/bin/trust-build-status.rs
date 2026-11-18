//! Small consumer of the existing native status owner; no compiler or prover dependency.

fn main() {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let result = trust_build_tree::admission::status::command(
        &std::env::args_os().skip(1).collect::<Vec<_>>(),
        &mut std::io::stdout().lock(),
    );
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    let result: std::io::Result<()> = Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "native build status is unavailable on this platform",
    ));
    if let Err(error) = result {
        eprintln!("trust-build-status: {error}");
        std::process::exit(2);
    }
}
