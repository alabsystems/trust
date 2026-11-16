// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::io::{self, Write};
use std::path::PathBuf;

use trust_oracle_freeze_facts::{Error, PROTOCOL, committed_facts, read_requests};

fn run() -> Result<(), Error> {
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    if args.len() != 4 || args[0] != "--repo" || args[2] != "--commit" {
        return Err(Error::Unavailable(
            "usage: trust-oracle-freeze-facts --repo PATH --commit FULL_OID".into(),
        ));
    }
    let repo = PathBuf::from(&args[1]);
    let commit = args[3].to_str().ok_or_else(|| Error::Unavailable("non-ASCII commit".into()))?;
    let requests = read_requests(io::stdin().lock())?;
    let observed = committed_facts(&repo, commit, &requests)?;
    let mut output = io::BufWriter::new(io::stdout().lock());
    writeln!(output, "{PROTOCOL} {}", observed.facts.len())?;
    for fact in observed.facts {
        writeln!(output, "{}", fact.as_str())?;
    }
    output.flush()?;
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("oracle citation facts unavailable: {error}");
        std::process::exit(if matches!(error, Error::Unsupported(_)) { 3 } else { 2 });
    }
}
