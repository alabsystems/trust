//! The row-parity probe that `scripts/vc_row_parity.py` builds at a parent and at
//! a candidate tree and diffs (T3 C01; plan S16). Measurement aid, not a gate.
//!
//! For every `*.json` file under the given roots, in sorted path order, it parses
//! a `VerifiableFunction`, runs `generate_vcs`, and prints one line per row:
//!
//! ```text
//! <fixture path relative to its root> <row index> <sha256 of the row's canonical JSON>
//! ```
//!
//! The canonical JSON is the exact-VC payload's encoding
//! (`canonical_exact_vc_payload` in `rustc_mir_transform/src/trust_verify.rs`):
//! `canonical_digest_json_value` (out-of-range 128-bit integers tagged as decimal
//! strings), every object's keys in byte order, serde_json's spelling of strings
//! and numbers. A fixture that does not parse prints `<fixture> - unparsed`, one
//! whose generation panics prints `<fixture> - panicked`, and one with no row
//! prints `<fixture> - rows=0`, so a fixture that changes class is a diff line
//! too. It reads no environment variable.
//!
//! Usage: `vc_row_parity_probe <fixture root>...`
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

use trust_types::digest::stable_sha256_hex;
use trust_types::{VerifiableFunction, canonical_digest_json_value, canonicalize_json_in_place};
use trust_vcgen::generate_vcs;

fn json_files(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(root) else { return };
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if path.is_dir() {
            json_files(&path, out);
        } else if path.extension().is_some_and(|x| x == "json") {
            out.push(path);
        }
    }
}

/// The row's digest, or `None` when it has no canonical encoding (it is then
/// printed as such, never as some other spelling's digest).
fn row_digest(vc: &trust_types::VerificationCondition) -> Option<String> {
    let mut value = canonical_digest_json_value(vc).ok()?;
    canonicalize_json_in_place(&mut value);
    let bytes = serde_json::to_vec(&value).ok()?;
    Some(stable_sha256_hex(&bytes))
}

fn main() {
    let roots: Vec<PathBuf> = std::env::args_os().skip(1).map(PathBuf::from).collect();
    if roots.is_empty() {
        eprintln!("usage: vc_row_parity_probe <fixture root>...");
        std::process::exit(2);
    }
    // A generator panic is a row of the output, not the end of the walk.
    std::panic::set_hook(Box::new(|_| {}));
    let (mut fixtures, mut rows) = (0usize, 0usize);
    for root in &roots {
        let mut files = Vec::new();
        json_files(root, &mut files);
        files.sort();
        for path in files {
            let rel = path.strip_prefix(root).unwrap_or(&path).display().to_string();
            fixtures += 1;
            let parsed = std::fs::read_to_string(&path)
                .ok()
                .and_then(|text| serde_json::from_str::<VerifiableFunction>(&text).ok());
            let Some(func) = parsed else {
                println!("{rel} - unparsed");
                continue;
            };
            let Ok(vcs) = catch_unwind(AssertUnwindSafe(|| generate_vcs(&func))) else {
                println!("{rel} - panicked");
                continue;
            };
            if vcs.is_empty() {
                println!("{rel} - rows=0");
            }
            for (index, vc) in vcs.iter().enumerate() {
                match row_digest(vc) {
                    Some(digest) => println!("{rel} {index} {digest}"),
                    None => println!("{rel} {index} no-canonical-encoding"),
                }
                rows += 1;
            }
        }
    }
    eprintln!("vc_row_parity_probe: {fixtures} fixture file(s), {rows} row(s)");
}
