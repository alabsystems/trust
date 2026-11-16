// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `targo trust store verify --facts`: STORE-1's explicit re-check, for the
//! local kernel fact store (TG6, `COMPILE-TIME-FACTS-1`).
//!
//! It rescans the store's integrity (every object re-hashed against its
//! content address), then re-checks every fact from scratch: a fresh Clean
//! session replays the fact's own log with real elaboration, performs the
//! fact's elaboration, and compares the environment delta, the outcome and
//! the dependencies with what the fact says. Each fact that does not
//! reproduce is quarantined, and the run exits 1. The re-check uses this
//! Targo's own Clean kernel.

use std::process::ExitCode;

const USAGE: &str = "\
Usage:
  targo trust store verify --facts    Re-check every local kernel fact

The local kernel fact store is {cargo home}/trust/results/v1/clean-kernel-facts-v1.
Every object is re-hashed against its content address, then every fact is
elaborated again from its own log and compared with what it says. A fact that
does not reproduce is quarantined (moved to the store's `quarantine/`).

Exit status: 0 every fact reproduced; 1 some fact was quarantined; 2 usage;
3 could not run (no cargo home, or no private store under it).
";

pub(crate) fn run_store_subcommand(args: &[String]) -> ExitCode {
    match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        ["verify", "--facts"] => verify_facts(),
        ["help"] | ["--help"] | ["-h"] => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        _ => {
            eprint!("targo trust store: expected `verify --facts`\n\n{USAGE}");
            ExitCode::from(2)
        }
    }
}

fn verify_facts() -> ExitCode {
    let Some(home) = crate::config::cargo_home() else {
        eprintln!("targo trust store: COULD NOT RUN: no cargo home");
        return ExitCode::from(3);
    };
    let store = match trust_certify::clean_fact::FactStore::open(&home) {
        Ok(store) => store,
        Err(error) => {
            eprintln!(
                "targo trust store: COULD NOT RUN: the local kernel fact store under {} is \
                 unavailable: {error}",
                home.display()
            );
            return ExitCode::from(3);
        }
    };
    let report = trust_certify::clean_island::verify_fact_store(&store);
    println!("local kernel facts: {}", store.root().display());
    println!(
        "integrity: {} sound, {} quarantined, {} dangling index entries removed, {} superseded \
         objects collected",
        report.rescan.sound,
        report.rescan.quarantined,
        report.rescan.dangling,
        report.rescan.collected
    );
    println!(
        "re-checked: {} reproduced, {} quarantined",
        report.reproduced,
        report.quarantined.len()
    );
    for (key, why) in &report.quarantined {
        println!("  quarantined {key}: {why}");
    }
    if report.quarantined.is_empty() && report.rescan.quarantined == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_bare_store_command_is_a_usage_error() {
        assert_eq!(run_store_subcommand(&[]), ExitCode::from(2));
        assert_eq!(run_store_subcommand(&["verify".to_string()]), ExitCode::from(2));
    }
}
