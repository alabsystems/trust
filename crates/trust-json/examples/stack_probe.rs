// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Per-frame stack cost probe. A stack overflow ABORTS the process, so this
// cannot live in a #[test]; the caller runs it once per (impl, depth, stack)
// triple and reads the exit status.
//
//   stack_probe <tj|inc> <depth> <stack_kib>
//
// exit 0 = parsed inside the given stack; SIGABRT = overflowed.

use incumbent_serde_json as inc;
use trust_json as tj;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let which = args[1].clone();
    let depth: usize = args[2].parse().unwrap();
    let stack_kib: usize = args[3].parse().unwrap();

    let src = "[".repeat(depth) + &"]".repeat(depth);

    let h = std::thread::Builder::new()
        .stack_size(stack_kib * 1024)
        .spawn(move || match which.as_str() {
            // Default recursion limit; only depths < 128 are reachable.
            "tj" => tj::from_str(&src).is_ok(),
            "inc" => inc::from_str::<inc::Value>(&src).is_ok(),
            // Unbounded lane, trust-json only (the incumbent's needs `serde`).
            "tj-unbounded" => {
                let mut de = tj::Deserializer::from_str(&src).disable_recursion_limit();
                de.parse_value().is_ok()
            }
            other => panic!("unknown impl {other}"),
        })
        .unwrap();

    let ok = h.join().unwrap();
    std::process::exit(if ok { 0 } else { 1 });
}
