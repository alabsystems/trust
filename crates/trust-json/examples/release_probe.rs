// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Probes whose behaviour CHANGES between debug and release, so they cannot be
// settled by `cargo test` alone.
//
//   release_probe nan            -- Formatter::write_f64/f32 on non-finite input
//   release_probe unbounded <d>  -- disable_recursion_limit stack threshold

use incumbent_serde_json as inc;
use std::panic::{catch_unwind, AssertUnwindSafe};
use trust_json as tj;
use trust_json::Formatter as _;

fn quiet<F: FnOnce() -> R, R>(f: F) -> Result<R, String> {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = catch_unwind(AssertUnwindSafe(f));
    std::panic::set_hook(prev);
    r.map_err(|e| {
        e.downcast_ref::<String>()
            .cloned()
            .or_else(|| e.downcast_ref::<&str>().map(|s| (*s).to_owned()))
            .unwrap_or_else(|| "<non-string panic>".into())
    })
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args[1].as_str() {
        "nan" => {
            println!("debug_assertions = {}", cfg!(debug_assertions));
            for (name, v) in [
                ("NaN", f64::NAN),
                ("inf", f64::INFINITY),
                ("-inf", f64::NEG_INFINITY),
            ] {
                let mine = quiet(|| {
                    let mut buf = Vec::new();
                    let mut f = tj::CompactFormatter;
                    f.write_f64(&mut buf, v).unwrap();
                    String::from_utf8_lossy(&buf).into_owned()
                });
                println!("  trust-json write_f64({name:>4}) -> {mine:?}");
            }
            for (name, v) in [
                ("NaN", f32::NAN),
                ("inf", f32::INFINITY),
                ("-inf", f32::NEG_INFINITY),
            ] {
                let mine = quiet(|| {
                    let mut buf = Vec::new();
                    let mut f = tj::CompactFormatter;
                    f.write_f32(&mut buf, v).unwrap();
                    String::from_utf8_lossy(&buf).into_owned()
                });
                println!("  trust-json write_f32({name:>4}) -> {mine:?}");
            }
            // The incumbent's Formatter, same contract, for comparison.
            for (name, v) in [
                ("NaN", f64::NAN),
                ("inf", f64::INFINITY),
                ("-inf", f64::NEG_INFINITY),
            ] {
                let theirs = quiet(|| {
                    use inc::ser::Formatter as _;
                    let mut buf = Vec::new();
                    let mut f = inc::ser::CompactFormatter;
                    f.write_f64(&mut buf, v).unwrap();
                    String::from_utf8_lossy(&buf).into_owned()
                });
                println!("  serde_json write_f64({name:>4}) -> {theirs:?}");
            }
        }
        "unbounded" => {
            let d: usize = args[2].parse().unwrap();
            let src = "[".repeat(d) + &"]".repeat(d);
            let h = std::thread::Builder::new()
                .stack_size(8 * 1024 * 1024)
                .spawn(move || {
                    let mut de = tj::Deserializer::from_str(&src).disable_recursion_limit();
                    de.parse_value().is_ok()
                })
                .unwrap();
            let ok = h.join().unwrap();
            std::process::exit(if ok { 0 } else { 1 });
        }
        other => panic!("unknown probe {other}"),
    }
}
