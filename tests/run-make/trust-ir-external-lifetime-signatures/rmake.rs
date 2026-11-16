//! Preserve external signatures and the actual formatting argument across recovery.
//@ ignore-cross-compile

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, run, rust_lib_name, rustc_path, serde_json};

fn functions(text: &str) -> Vec<&str> {
    let mut offset = 0;
    let mut result = Vec::new();
    for line in text.split_inclusive('\n') {
        if line.contains("fn @") {
            let tail = &text[offset..];
            let end = tail.find("\n}\n").expect("closed function") + 3;
            result.push(&tail[..end]);
        }
        offset += line.len();
    }
    result
}

/// WS5.2: `Function.name` is the link-time symbol; the def path a test knows a
/// function by is its `; #display-path: "..."` directive.
fn display_path(function: &str) -> Option<&str> {
    function
        .lines()
        .find_map(|line| line.trim_start().strip_prefix("; #display-path: \""))
        .and_then(|rest| rest.strip_suffix('"'))
}

fn named<'a>(functions: &[&'a str], leaf: &str) -> (usize, &'a str) {
    let matches: Vec<_> = functions
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, function)| {
            display_path(function).is_some_and(|path| path.rsplit("::").next() == Some(leaf))
        })
        .collect();
    assert_eq!(matches.len(), 1, "unique {leaf}: {matches:?}");
    matches[0]
}

fn signature<'a>(text: &'a str, function: &str) -> &'a str {
    let id = function
        .lines()
        .next()
        .unwrap()
        .split_once("(functy.")
        .unwrap()
        .1
        .split_once(')')
        .unwrap()
        .0;
    let prefix = format!("functy.{id} = ");
    text.lines().find_map(|line| line.strip_prefix(&prefix)).expect("signature")
}

fn assert_rust_declaration(function: &str) {
    assert!(function.lines().next().unwrap().starts_with("rustcc fn @"), "{function}");
    assert!(!function.lines().any(|line| line.trim_start().starts_with("bb")), "{function}");
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    cmd(&trustc)
        .args([
            "dep.rs",
            "--crate-name=external",
            "--crate-type=rlib",
            "--edition=2021",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=off",
        ])
        .run();
    cmd(&trustc)
        .args([
            "callers.rs",
            "--crate-name=callers",
            "--crate-type=lib",
            "--edition=2021",
            "--emit=trust-ir",
            "-Ztrust-policy=strict",
            "-Ztrust-verify=off",
        ])
        .arg(format!("--extern=external={}", rust_lib_name("external")))
        .run();

    let text = rfs::read_to_string("callers.trust-ir.txt");
    let fs = functions(&text);
    let (_, consume) = named(&fs, "consume");
    let (_, make) = named(&fs, "make");
    let (_, read) = named(&fs, "read");
    for declaration in [consume, make, read] {
        assert_rust_declaration(declaration);
    }
    let consumed_ty =
        signature(&text, consume).strip_prefix('(').unwrap().strip_suffix(") -> (u64)").unwrap();
    assert!(consumed_ty.starts_with("struct."), "{consumed_ty}");
    assert_eq!(signature(&text, make), format!("(ptr) -> ({consumed_ty})"));
    assert_eq!(signature(&text, read), "(ptr) -> (u64)");
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("callers.trust-ir.coverage.json")).unwrap();
    let bodies = coverage["bodies"].as_array().unwrap();
    assert_eq!(bodies.len(), 3, "no missing or extra caller rows: {coverage}");
    for name in ["constructed_then_consumed", "returned_then_consumed", "borrowed_scalar"] {
        let rows: Vec<_> = bodies.iter().filter(|body| body["def_path"] == name).collect();
        assert_eq!(rows.len(), 1, "{name}: {coverage}");
        assert_eq!(rows[0]["lowered"], true, "{name}: {}", rows[0]);
        assert_eq!(rows[0]["spliced"], true, "{name}: {}", rows[0]);
        assert_eq!(rows[0]["symbolic"], false, "{name}: {}", rows[0]);
        assert!(rows[0]["unsupported"].as_array().unwrap().is_empty());
    }

    // Trust: retain the original native13 witness, including println and all 21 assertions.
    // Native execution is a compatibility check; the IR assertions below independently
    // prevent an omitted print call or a discarded formatting value from passing it.
    for lane in ["off", "on"] {
        let binary = format!("pure-identity-{lane}");
        let mut compiler = cmd(&trustc);
        compiler.args([
            "pure_identity.rs",
            "--crate-name=inline_identity_fixture",
            "--crate-type=bin",
            "--edition=2021",
            "-Copt-level=0",
            "-Cdebuginfo=0",
            "-Ztrust-policy=strict",
            "-Ztrust-verify=off",
        ]);
        compiler.arg(format!("-Ztrust-ir-lower={lane}")).arg("-o").arg(bin_name(&binary));
        if lane == "on" {
            compiler.arg("-Ztrust-dump=ir:printing-ir");
        }
        compiler.run();
        assert_eq!(run(&binary).stdout_utf8(), "pure_rust_identity_assertions=21\n");
    }
    let text = rfs::read_to_string("printing-ir/inline_identity_fixture.trust-ir.txt");
    let fs = functions(&text);
    let (print_id, print) = named(&fs, "_print");
    let (constructor_id, constructor) = named(&fs, "from_str");
    assert_rust_declaration(print);
    assert_rust_declaration(constructor);
    let argument_ty =
        signature(&text, print).strip_prefix('(').unwrap().strip_suffix(") -> ()").unwrap();
    assert!(argument_ty.starts_with("struct."), "{argument_ty}");
    assert_eq!(signature(&text, constructor), format!("(fatptr<str>) -> ({argument_ty})"));
    // `report`, not `main`: `main` holds the fixture's `for` loop, which the
    // producer declines since `368e6bf306`; the print moved to a loop-free fn.
    let (_, main) = named(&fs, "report");
    let constructor_call = format!("call @func.{constructor_id}(");
    let constructions: Vec<_> =
        main.lines().filter(|line| line.contains(&constructor_call)).collect();
    assert_eq!(constructions.len(), 1, "{main}");
    let value = constructions[0].trim().split_once(" = ").unwrap().0;
    assert!(value.starts_with('%'), "{value}");
    let print_call = format!("call @func.{print_id}({value})");
    assert_eq!(
        main.matches(&print_call).count(),
        1,
        "print must consume the constructed value: {main}"
    );
    let bytes = b"pure_rust_identity_assertions=21\n"
        .iter()
        .map(u8::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    assert!(text.contains(&format!("array[ {bytes} ]")), "literal bytes must survive");
}
