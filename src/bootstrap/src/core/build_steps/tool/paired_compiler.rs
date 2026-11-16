//! Bind final Targo to the completed compiler selected by this SDK constructor.
//! The profile records compatibility, never completed SDK or resource authority.

use std::io::{self, Read as _};
use std::time::{Duration, Instant};

use sha2::{Digest as _, Sha256};
use trust_resource_provenance::paired_compiler as profile;
use trust_resource_provenance::program::HeldProgram;

use super::*;

pub(super) fn bind(
    builder: &Builder<'_>,
    cargo: &mut CargoCommand,
    compiler: Compiler,
) -> io::Result<()> {
    if builder.config.dry_run() {
        return Ok(());
    }
    if compiler.is_forced_compiler() || builder.download_rustc() {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "native pairing requires this constructor's completed source-built compiler",
        ));
    }
    // `output_compiler` comes from the existing ensured Compiler/Assemble step.
    // Never substitute an ambient RUSTC, shim, PATH program or saved receipt.
    let root = builder.sysroot(compiler).canonicalize()?;
    let program = builder.rustc(compiler).canonicalize()?;
    let deadline = Instant::now() + Duration::from_secs(30);
    let mut file = fs::File::open(&program)?;
    let mut hash = Sha256::new();
    let mut total = 0u64;
    let mut buffer = [0; 65536];
    loop {
        if Instant::now() >= deadline {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "paired compiler capture deadline",
            ));
        }
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        total += count as u64;
        if total > 1024 * 1024 * 1024 {
            return Err(io::Error::other("paired compiler exceeds image bound"));
        }
        hash.update(&buffer[..count]);
    }
    let digest: [u8; 32] = hash.finalize().into();
    let held = HeldProgram::open(&root, &program, &digest, deadline)?;
    let mut query = crate::utils::exec::tool_metadata_command(&program);
    query.env_clear();
    for (key, value) in held.runtime_environment()? {
        query.env(key, value);
    }
    query.arg("--resource-capabilities");
    query.metadata_scheduler();
    // This known first-party sole-argument branch runs before backend/options,
    // using the SAME existing paid metadata implicit borrower. It is not a
    // preadmission probe of a user-selected executable.
    let output = query.bounded_metadata_output(deadline, 1024)?;
    if !output.status.success() {
        return Err(io::Error::other("completed compiler refused protocol discovery"));
    }
    let encoded = profile::capture(&held, &output.stdout, deadline)?;
    cargo.env(profile::PRODUCER_INPUT, encoded);
    Ok(())
}
