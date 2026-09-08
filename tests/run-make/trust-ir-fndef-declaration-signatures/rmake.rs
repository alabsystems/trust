//! Exact bodyless declaration signatures and concrete-instance identity, end to end.
//!
//! Successful `--emit=trust-ir` includes the unconditional final validator. These controls also
//! inspect canonical text so a permissive vararg declaration, DefId-only alias, or signature-only
//! alias cannot pass merely because compilation happened to finish.

use std::collections::BTreeSet;
use std::path::PathBuf;

use run_make_support::{bin_name, rfs, run, rustc, serde_json, source_root};

struct Artifacts {
    source: PathBuf,
    text: String,
    coverage: serde_json::Value,
}

fn compile_ir(crate_name: &str, source_name: &str) -> Artifacts {
    let source = source_root().join("tests/ui/trust").join(source_name);
    let out = PathBuf::from(format!("{crate_name}-ir"));
    rfs::create_dir(&out);
    let stderr = rustc()
        .input(&source)
        .crate_name(crate_name)
        .crate_type("lib")
        .edition("2024")
        .emit("trust-ir")
        .out_dir(&out)
        .arg("-Ztrust-verify=off")
        .run()
        .stderr_utf8();
    for banned in ["final Trust-IR module validation failed", "CallEdgeSignatureMismatch"] {
        assert!(!stderr.contains(banned), "unexpected `{banned}`:\n{stderr}");
    }
    let text = rfs::read_to_string(out.join(format!("{crate_name}.trust-ir.txt")));
    let coverage = serde_json::from_str(&rfs::read_to_string(
        out.join(format!("{crate_name}.trust-ir.coverage.json")),
    ))
    .expect("coverage sidecar must be valid JSON");
    Artifacts { source, text, coverage }
}

fn functions(text: &str) -> Vec<&str> {
    let mut starts = Vec::new();
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        if line.contains("fn @") {
            starts.push(offset);
        }
        offset += line.len();
    }
    starts
        .into_iter()
        .map(|start| {
            let tail = &text[start..];
            let end =
                tail.find("\n}\n").unwrap_or_else(|| panic!("unterminated function:\n{tail}")) + 3;
            &tail[..end]
        })
        .collect()
}

fn named_function<'a>(functions: &'a [&'a str], name: &str) -> &'a str {
    let found: Vec<_> = functions
        .iter()
        .copied()
        .filter(|function| {
            let Some(header_name) = function
                .lines()
                .next()
                .and_then(|line| line.split_once("fn @"))
                .and_then(|(_, tail)| tail.split_once("(functy."))
                .map(|(name, _)| name)
            else {
                return false;
            };
            header_name.rsplit("::").next() == Some(name)
        })
        .collect();
    assert_eq!(found.len(), 1, "wanted one `{name}` function, got {found:?}");
    found[0]
}

fn referenced_id(function: &str, marker: &str) -> usize {
    let mut ids = BTreeSet::new();
    let mut rest = function;
    while let Some(at) = rest.find(marker) {
        rest = &rest[at + marker.len()..];
        let digits = rest.bytes().take_while(|byte| byte.is_ascii_digit()).count();
        assert!(digits > 0, "malformed `{marker}` in:\n{function}");
        ids.insert(rest[..digits].parse::<usize>().expect("numeric FuncId"));
        rest = &rest[digits..];
    }
    assert_eq!(ids.len(), 1, "wanted one `{marker}` target in:\n{function}");
    *ids.first().expect("one target")
}

fn signature<'a>(text: &'a str, function: &str) -> &'a str {
    let header = function.lines().next().expect("function header");
    let rest = header.split_once("(functy.").expect("function type in header").1;
    let digits = rest.bytes().take_while(|byte| byte.is_ascii_digit()).count();
    assert!(digits > 0, "malformed function type in `{header}`");
    let prefix = format!("functy.{} = ", &rest[..digits]);
    text.lines()
        .find_map(|line| line.strip_prefix(&prefix))
        .unwrap_or_else(|| panic!("missing `{prefix}` in:\n{text}"))
}

fn body_row<'a>(coverage: &'a serde_json::Value, leaf: &str) -> &'a serde_json::Value {
    let rows = coverage["bodies"].as_array().expect("body inventory");
    let found: Vec<_> = rows
        .iter()
        .filter(|row| {
            row["def_path"].as_str().is_some_and(|path| path.rsplit("::").next() == Some(leaf))
        })
        .collect();
    assert_eq!(found.len(), 1, "wanted one coverage row for `{leaf}`: {rows:?}");
    found[0]
}

fn assert_clean(coverage: &serde_json::Value, names: &[&str]) {
    for name in names {
        let row = body_row(coverage, name);
        assert_eq!(row["lowered"], true, "`{name}` not lowered: {row}");
        assert_eq!(row["spliced"], true, "`{name}` not spliced: {row}");
        assert_eq!(
            row["unsupported"].as_array().map(Vec::len),
            Some(0),
            "`{name}` unsupported: {row}"
        );
    }
}

fn declaration<'a>(functions: &'a [&'a str], id: usize) -> &'a str {
    let function = functions
        .get(id)
        .unwrap_or_else(|| panic!("FuncId {id} has no function; functions={functions:?}"));
    assert!(
        !function.lines().any(|line| line.trim_start().starts_with("bb")),
        "FuncId {id} must be a bodyless declaration:\n{function}"
    );
    function
}

fn assert_exact_signature(text: &str, declaration: &str, expected: &str) {
    let actual = signature(text, declaration);
    assert_eq!(actual, expected, "wrong declaration signature:\n{declaration}");
    assert!(!actual.contains("..."), "exact declaration became vararg: {actual}");
}

fn main() {
    let externs =
        compile_ir("extern_direct_fndef", "trust_ir_lower_extern_direct_fnptr_decl_sig.rs");
    assert_eq!(externs.coverage["totals"]["declarations"].as_u64(), Some(2));
    assert_clean(
        &externs.coverage,
        &[
            "direct_first_direct",
            "direct_first_pointer",
            "pointer_first_pointer",
            "pointer_first_direct",
        ],
    );
    let extern_functions = functions(&externs.text);
    let direct_first_call =
        referenced_id(named_function(&extern_functions, "direct_first_direct"), "call @func.");
    let direct_first_pointer =
        referenced_id(named_function(&extern_functions, "direct_first_pointer"), "fndef<func.");
    let pointer_first_pointer =
        referenced_id(named_function(&extern_functions, "pointer_first_pointer"), "fndef<func.");
    let pointer_first_call =
        referenced_id(named_function(&extern_functions, "pointer_first_direct"), "call @func.");
    assert_eq!(
        direct_first_call, direct_first_pointer,
        "direct-first observations minted two identities"
    );
    assert_eq!(
        pointer_first_pointer, pointer_first_call,
        "pointer-first observations minted two identities"
    );
    assert_ne!(direct_first_call, pointer_first_call, "two extern definitions aliased");
    for id in [direct_first_call, pointer_first_call] {
        assert_exact_signature(&externs.text, declaration(&extern_functions, id), "(u32) -> (u32)");
    }

    let generics =
        compile_ir("generic_fndef_instances", "trust_ir_lower_generic_fnptr_two_instantiations.rs");
    assert_eq!(generics.coverage["totals"]["declarations"].as_u64(), Some(5));
    let generic_names = [
        "forget_u32_direct",
        "forget_u32_pointer",
        "forget_u64_pointer",
        "forget_u64_direct",
        "pick_one_direct",
        "pick_one_pointer",
        "pick_two_pointer",
        "pick_two_direct",
        "single_instance_direct",
        "single_instance_pointer",
    ];
    assert_clean(&generics.coverage, &generic_names);
    let generic_functions = functions(&generics.text);
    let cases = [
        ("forget_u32_direct", "call @func.", "forget_u32_pointer", "fndef<func.", "(u32) -> ()"),
        ("forget_u64_direct", "call @func.", "forget_u64_pointer", "fndef<func.", "(u64) -> ()"),
        ("pick_one_direct", "call @func.", "pick_one_pointer", "fndef<func.", "() -> (u32)"),
        ("pick_two_direct", "call @func.", "pick_two_pointer", "fndef<func.", "() -> (u32)"),
        (
            "single_instance_direct",
            "call @func.",
            "single_instance_pointer",
            "fndef<func.",
            "(u32) -> (u32)",
        ),
    ];
    let mut generic_ids = BTreeSet::new();
    for (direct_name, direct_marker, pointer_name, pointer_marker, expected_sig) in cases {
        let direct = referenced_id(named_function(&generic_functions, direct_name), direct_marker);
        let pointer =
            referenced_id(named_function(&generic_functions, pointer_name), pointer_marker);
        assert_eq!(direct, pointer, "`{direct_name}` and `{pointer_name}` did not dedup");
        assert_exact_signature(
            &generics.text,
            declaration(&generic_functions, direct),
            expected_sig,
        );
        assert!(
            generic_ids.insert(direct),
            "distinct concrete instance aliased at FuncId {direct}"
        );
    }
    assert_eq!(generic_ids.len(), 5);

    let pick_headers: BTreeSet<_> = generic_ids
        .iter()
        .filter_map(|id| {
            let declaration = declaration(&generic_functions, *id);
            (signature(&generics.text, declaration) == "() -> (u32)")
                .then(|| declaration.lines().next().expect("declaration header"))
        })
        .collect();
    assert_eq!(pick_headers.len(), 2, "pick::<1>/<2> must have distinct declaration names");
    assert!(
        pick_headers.iter().all(|header| header.contains("!trust_bodyless_instance::")),
        "generic bodyless names must be explicitly reserved/non-linkable: {pick_headers:?}"
    );

    // A declaration must also be disambiguated from a spliced definition when there is only one
    // concrete instance, so the declaration-vs-declaration check cannot make this pass by itself.
    let single_id = referenced_id(
        named_function(&generic_functions, "single_instance_direct"),
        "call @func.",
    );
    let single_decl = declaration(&generic_functions, single_id);
    assert!(
        single_decl
            .lines()
            .next()
            .is_some_and(|header| header.contains("!trust_bodyless_instance::")),
        "the single concrete instance retained the spliced definition's name: {single_decl}"
    );
    let single_definition = named_function(&generic_functions, "single_instance");
    assert!(
        single_definition.lines().any(|line| line.trim_start().starts_with("bb")),
        "the identity definition must be present and executable for this control: \
         {single_definition}"
    );
    assert_ne!(
        single_decl.lines().next(),
        single_definition.lines().next(),
        "definition and declaration headers must remain operationally distinct"
    );

    let runtime = bin_name("generic-fndef-runtime");
    rustc()
        .input(&generics.source)
        .crate_name("generic_fndef_runtime")
        .edition("2024")
        .cfg("runtime")
        .output(&runtime)
        .run();
    run(&runtime);
}
