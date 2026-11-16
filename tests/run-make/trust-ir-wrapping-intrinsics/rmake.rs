//! Trust: compiler wrapping intrinsics lower to modular integer IR, including
//! with overflow checks enabled. Same-spelled ordinary functions remain calls.
use run_make_support::{rfs, rustc, serde_json};

fn body<'a>(text: &'a str, name: &str) -> &'a str {
    let marker = format!("; #display-path: {name:?}\n");
    let start = text.find(&marker).expect("function must be recorded");
    let tail = &text[start..];
    &tail[..tail.find("\n}\n").expect("function end")]
}

fn main() {
    let mut source = String::from("#![feature(core_intrinsics)]\n#![allow(internal_features)]\n");
    let types = ["u8", "u16", "u32", "u64", "u128", "usize",
                 "i8", "i16", "i32", "i64", "i128", "isize"];
    for ty in types {
        for op in ["add", "sub", "mul"] {
            source.push_str(&format!(
                "pub fn {op}_{ty}(a: {ty}, b: {ty}) -> {ty} {{ core::intrinsics::wrapping_{op}(a, b) }}\n"
            ));
        }
    }
    source.push_str("#[inline(never)] fn wrapping_add(a: u64, b: u64) -> u64 { a ^ b }\n");
    source.push_str("pub fn ordinary(a: u64, b: u64) -> u64 { wrapping_add(a, b) }\n");
    rfs::write("subject.rs", source);
    rfs::create_dir("ir");
    rustc().input("subject.rs").crate_type("lib").emit("trust-ir")
        .out_dir("ir").arg("-Coverflow-checks=on").arg("-Ztrust-verify=on")
        .env_remove("TRUST_NO_VERIFY").run();
    let text = rfs::read_to_string("ir/subject.trust-ir.txt");
    let conservation: serde_json::Value = serde_json::from_str(
        &rfs::read_to_string("ir/subject.trust-ir.effect-conservation.json"),
    ).expect("effect conservation sidecar");
    let rows = conservation["functions"].as_array().expect("function roster");
    for ty in types {
        for op in ["add", "sub", "mul"] {
            let name = format!("{op}_{ty}");
            let function = body(&text, &name);
            assert!(function.contains(&format!("= {op} {ty} ")), "{name}: {function}");
            assert!(!function.contains("call "), "intrinsic is not a call: {function}");
            assert!(!function.contains("overflow"), "wrapping must not trap: {function}");
            assert!(!function.contains("assert "), "wrapping must not assert: {function}");
            let matches: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
            assert_eq!(matches.len(), 1, "complete conservation row for {name}");
            let row = matches[0];
            assert_eq!(row["verdict"], "conserved", "{name}: {row}");
            assert_eq!(row["tags"], serde_json::json!([]), "{name}: {row}");
            assert_eq!(row["equivalences"], serde_json::json!({"pure-intrinsic": 1}),
                "only the existing intrinsic equivalence applies: {name}: {row}");
        }
    }
    assert!(body(&text, "ordinary").contains("call "), "ordinary item stays a call");
}
