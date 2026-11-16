//! A diagnostic probe for the fixed scalar-model family, not a compiler certificate.
//!
//! Run through Trust, for example:
//! `targo --unverified run --manifest-path targo-trust/Cargo.toml --locked
//! -p trust-certify --example scalar_return_family_bundle -- prove NEW_PATH`
//! Then run the same command with `replay PATH` in a separate process.

use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::path::Path;
use std::process::ExitCode;

use trust_certify::scalar_return_family::{
    MAX_SCALAR_FAMILY_BUNDLE_BYTES, prove_u8_widen_add_one_family, replay_u8_widen_add_one_family,
};

const USAGE: &str = "scalar_return_family_bundle prove NEW_PATH | replay PATH
Construct or independently replay the versioned scalar-model proof bundle.
Output is create-only. Replay reconstructs the fixed Clean/model basis.
This is not a self-contained kernel distribution or Rust/MIR/compiler certificate.";

fn run(command: &str, path: &Path) -> Result<(), String> {
    match command {
        "prove" => {
            if path.try_exists().map_err(|e| format!("output: {e}"))? {
                return Err("output already exists; choose a new path".into());
            }
            let bytes = prove_u8_widen_add_one_family()?;
            replay_u8_widen_add_one_family(&bytes)?;
            // No truncation and no clobber race after the early usability check.
            // On an I/O failure a partial file may remain; replay always refuses
            // incomplete bytes, and no output path is ever proof authority.
            let mut output = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(path)
                .map_err(|e| format!("create output: {e}"))?;
            output
                .write_all(&bytes)
                .and_then(|()| output.sync_all())
                .map_err(|e| format!("output write failed (incomplete file may remain): {e}"))?;
            println!("wrote {} model-only proof-bundle bytes", bytes.len());
        }
        "replay" => {
            let input = File::open(path).map_err(|e| format!("open input: {e}"))?;
            let mut bytes = Vec::new();
            input
                .take((MAX_SCALAR_FAMILY_BUNDLE_BYTES + 1) as u64)
                .read_to_end(&mut bytes)
                .map_err(|e| format!("read input: {e}"))?;
            replay_u8_widen_add_one_family(&bytes)?;
            println!("replayed the complete scalar-model family; no compiler authority granted");
        }
        _ => return Err("unknown probe command".into()),
    }
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() == 1 && (args[0] == "--help" || args[0] == "-h") {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    if args.len() != 2 || (args[0] != "prove" && args[0] != "replay") {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    }
    match run(args[0].to_str().expect("validated ASCII command"), Path::new(&args[1])) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("scalar-model proof refused: {error}");
            ExitCode::FAILURE
        }
    }
}
