// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or MIT

//! R4 §2 CLI bridge: probe an untyped quantifier binder against the E3
//! closed type set and print the outcome vector as one JSON object per
//! line. The port tool shells to this instead of re-implementing inference —
//! the one-engine discipline means only trust-spec-elab may judge a typing.
//!
//! Usage:
//!   cargo run --example binder_probe -- <forall|exists> <binder> <body> [name:ty ...]
//!
//! Output: {"binder":"i","outcomes":{"nat":false,...},"unique":"u64"|null}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 3 {
        eprintln!("usage: binder_probe <forall|exists> <binder> <body> [name:ty ...]");
        std::process::exit(2);
    }
    let (quantifier, binder, body) = (&args[0], &args[1], &args[2]);
    let var_types: Vec<(&str, &str)> = args[3..]
        .iter()
        .map(|pair| {
            pair.split_once(':').unwrap_or_else(|| {
                eprintln!("malformed var:ty pair {pair:?}");
                std::process::exit(2);
            })
        })
        .collect();
    let outcomes =
        trust_spec_elab::probe_untyped_binder_typings(quantifier, binder, body, &var_types);
    let successes: Vec<&str> =
        outcomes.iter().filter(|(_, ok)| *ok).map(|(ty, _)| *ty).collect();
    let unique = if successes.len() == 1 {
        format!("\"{}\"", successes[0])
    } else {
        "null".to_string()
    };
    let pairs: Vec<String> =
        outcomes.iter().map(|(ty, ok)| format!("\"{ty}\":{ok}")).collect();
    println!(
        "{{\"binder\":\"{binder}\",\"outcomes\":{{{}}},\"unique\":{unique}}}",
        pairs.join(",")
    );
}
