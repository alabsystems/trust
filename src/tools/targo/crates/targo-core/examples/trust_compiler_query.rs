//! Bounded native regression observer for the actual pre-build-pool Rustc path.
//! A retained compiler and caller-supplied argv are explicit diagnostic inputs.
use cargo_util::ProcessBuilder;
use std::path::{Path, PathBuf};
use targo_core::util::{GlobalContext, Rustc};

fn main() -> anyhow::Result<()> {
    // SAFETY: FIRST operation, before arguments, files or context construction.
    unsafe { targo_core::context::initialize_jobserver() }?;
    let mut args = std::env::args_os().skip(1);
    let mode = args
        .next()
        .ok_or_else(|| anyhow::anyhow!("expected raw, query or unit"))?;
    let compiler = PathBuf::from(
        args.next()
            .ok_or_else(|| anyhow::anyhow!("expected compiler"))?,
    );
    let cache = PathBuf::from(
        args.next()
            .ok_or_else(|| anyhow::anyhow!("expected private cache path"))?,
    );
    let argv: Vec<_> = args.collect();
    let output = if mode == "raw" {
        let mut command = ProcessBuilder::new(&compiler);
        command.args(&argv);
        command.output_owned()?
    } else if mode == "query" || mode == "unit" {
        let gctx = GlobalContext::default()?;
        let rustc = Rustc::new(
            compiler.clone(),
            None,
            None,
            Path::new("/__not_a_rustup_proxy"),
            Some(cache),
            &gctx,
        )?;
        let mut command = rustc.process();
        command.args(&argv);
        if mode == "query" {
            let (stdout, stderr) = rustc.cached_output(&command, 0)?;
            std::io::stdout().write_all(stdout.as_bytes())?;
            std::io::stderr().write_all(stderr.as_bytes())?;
            return Ok(());
        }
        // Deliberately exercise ordinary Rustc::process, never the query owner.
        command.output_owned()?
    } else {
        anyhow::bail!("unknown query observer mode");
    };
    use std::io::Write as _;
    std::io::stdout().write_all(&output.stdout)?;
    std::io::stderr().write_all(&output.stderr)?;
    std::process::exit(output.status.code().unwrap_or(1));
}
