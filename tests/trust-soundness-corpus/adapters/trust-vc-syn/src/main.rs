// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// trust-soundness-corpus adapter for trust-vc's syn lane: verify ONE function of
// ONE file with `trust_vc_core::verify_function_from_file` and print one JSON
// line. The runner builds this crate against a trust-vc checkout
// (`Cargo.toml.in`, `@TRUST_VC_CORE@` replaced by its path); the adapter makes
// no claim of its own, it only reports the verifier's.
fn esc(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => out.push(' '),
            c => out.push(c),
        }
    }
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: trust-vc-syn-adapter <file.rs> <function>");
        std::process::exit(2);
    }
    let _cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let result = trust_vc_core::verify_function_from_file(&args[1], &args[2]);
    let (verdict, raw) = match &result {
        Ok(trust_vc_core::VerifyResult::Verified) => ("proved", String::new()),
        Ok(trust_vc_core::VerifyResult::Counterexample { .. }) => {
            ("refuted", format!("{result:?}"))
        }
        Ok(other) => ("not-proved", format!("{other:?}")),
        Err(e) => ("error", e.to_string()),
    };
    let raw: String = raw.chars().take(400).collect();
    println!("{{\"verdict\":\"{verdict}\",\"raw\":\"{}\"}}", esc(&raw));
}
