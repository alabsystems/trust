//! Exact bodyless declaration signatures and concrete-instance identity, end to end.
//!
//! Successful `--emit=trust-ir` includes the unconditional final validator. These controls also
//! inspect canonical text so a permissive vararg declaration, DefId-only alias, or signature-only
//! alias cannot pass merely because compilation happened to finish.

//@ ignore-cross-compile
// Trust: this recipe BUILDS AND RUNS a host binary (`generic-fndef-runtime`). Under
// the x86_64-apple-darwin cross target that bootstrap.toml also lists, the observer
// is an x86 executable this aarch64 host cannot run ("Bad CPU type in executable",
// OS 86) — the standard upstream idiom for a run-make test that executes what it
// builds is to skip cross-compilation. The signature assertions do not need it.
// (The directive sits directly under the doc block: compiletest's header scan
// stops at the first plain comment line, so a `//` explanation ABOVE a `//@`
// line silently hides the directive — measured: the test was then never run.)

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

/// WS5.2: `Function.name` is the link-time symbol; a function is found by the
/// last segment of its `; #display-path: "..."` (its def path).
fn display_path(function: &str) -> Option<&str> {
    function
        .lines()
        .find_map(|line| line.trim_start().strip_prefix("; #display-path: \""))
        .and_then(|rest| rest.strip_suffix('"'))
}

fn named_function<'a>(functions: &'a [&'a str], name: &str) -> &'a str {
    let found: Vec<_> = functions
        .iter()
        .copied()
        .filter(|function| {
            display_path(function).is_some_and(|path| path.rsplit("::").next() == Some(name))
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

// Every distinct `marker`ed FuncId in `function` — for a body with SEVERAL callees, where
// `referenced_id`'s exactly-one assertion is the wrong question.
fn referenced_ids(function: &str, marker: &str) -> BTreeSet<usize> {
    let mut ids = BTreeSet::new();
    let mut rest = function;
    while let Some(at) = rest.find(marker) {
        rest = &rest[at + marker.len()..];
        let digits = rest.bytes().take_while(|byte| byte.is_ascii_digit()).count();
        assert!(digits > 0, "malformed `{marker}` in:\n{function}");
        ids.insert(rest[..digits].parse::<usize>().expect("numeric FuncId"));
        rest = &rest[digits..];
    }
    ids
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

// Trust (2026-09-16, rvalue-snapshot admission): a `fmt` sink's signature is `(struct.K) ->
// ()` for the producer's own `core::fmt::Arguments` registration — ONE by-value struct
// parameter, no vararg. `K` is a module-local id and is returned so two sinks can be checked
// for the SAME registration. Every clause is asserted separately so a regression names the
// clause: a vararg spelling (the `params: [] + is_vararg: true` "unknown" encoding v41
// refuses), a dropped parameter (`() -> ()`), a scalar or pointer where the struct should be,
// or a second parameter.
fn assert_struct_by_value_unit_signature(text: &str, declaration: &str) -> usize {
    let actual = signature(text, declaration);
    assert!(!actual.contains("..."), "fmt sink signed vararg: {actual}\n{declaration}");
    let params = actual
        .strip_suffix(" -> ()")
        .unwrap_or_else(|| panic!("fmt sink must return unit: {actual}\n{declaration}"));
    let inner = params
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
        .unwrap_or_else(|| panic!("malformed parameter list: {actual}\n{declaration}"));
    assert!(!inner.contains(','), "fmt sink must take exactly one parameter: {actual}");
    let id = inner
        .strip_prefix("struct.")
        .unwrap_or_else(|| panic!("fmt sink parameter must be a by-value struct: {actual}"));
    id.parse::<usize>().unwrap_or_else(|_| panic!("malformed struct id in: {actual}"))
}

// `lowered` and `unsupported == []` only — NOT `spliced`. A `println!` body carries the
// wave-EL opaque collapse of `rt::Argument`'s payload and a call into the extern seam, and
// whether such a body splices is a separate gate this test makes no claim about.
/// Trust (2026-09-17): the NEGATIVE half of `assert_lowered_clean` — a body the producer
/// REFUSED, named with the refusal reason it recorded.
///
/// This exists because the refusal moved and its only pin did not follow it. `54ea2954cd`
/// made the producer refuse the BODY that mints an unsignable Rust-ABI call edge instead of
/// the whole crate, so the crate-level diagnostic
/// `tests/ui/trust/trust_ir_lower_format_args_residue_still_withdraws.rs` pinned by name
/// (`ERROR std::io::_print`) stopped arriving. The body is still refused — the sidecar says
/// `lowered: false` with an `UnsignableRustAbiDeclaration(std::io::_print)` row. When this was
/// written, `-Ztrust-ir-lower=strict` did NOT report that refusal, because strict's only per-body
/// arm read the `mir_built`-time report while the refusal is applied later, during the
/// crate-assembly re-splice fixpoint — recorded in
/// `reports/2026-09-17-two-upstream-regressions-the-ay-timeout-and-the-strict-hole.md`.
///
/// Trust (2026-09-27): that gap is CLOSED, since 2026-09-19 — see that report's own closing
/// section. `FinalizeSummary` carries a `refused_bodies` channel that strict raises at each
/// refused body's span (`compiler/rustc_mir_build/src/lib.rs`), and the UI fixture above is back
/// to `check-fail`. This assertion stays for a different reason than it was written for: it
/// observes what the PRODUCER's sidecar records, while the UI fixture observes what strict
/// REPORTS, and those are separate claims that can drift apart again. It went eight days stating
/// the gap was open after it closed, and was repeated from here into a CLOSED issue file — so
/// if you change this, re-read the report to its end first.
fn assert_body_refused(coverage: &serde_json::Value, name: &str, reason_fragment: &str) {
    let row = body_row(coverage, name);
    assert_eq!(row["lowered"], false, "`{name}` was lowered, so nothing was refused: {row}");
    assert_eq!(row["spliced"], false, "`{name}` was spliced despite refusal: {row}");
    let rows = row["unsupported"].as_array().expect("unsupported array");
    assert!(
        rows.iter().any(|r| r.to_string().contains(reason_fragment)),
        "`{name}` carries no refusal row naming `{reason_fragment}`: {row}"
    );
}

fn assert_lowered_clean(coverage: &serde_json::Value, names: &[&str]) {
    for name in names {
        let row = body_row(coverage, name);
        assert_eq!(row["lowered"], true, "`{name}` not lowered: {row}");
        assert_eq!(
            row["unsupported"].as_array().map(Vec::len),
            Some(0),
            "`{name}` unsupported: {row}"
        );
    }
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
    // RESIDUAL (WS5.2 NARROWED, docs/DECISION_QUEUE.md D17-DECL-SYMBOL-1): a concrete instance
    // of a LOCAL generic fn is the frozen D17 instance lane's appendable callee, so its
    // declaration keeps the PRE-WS5.2 name with no display path — here the pin's injective
    // `!trust_bodyless_instance::` collision form, since the two instances share one def path —
    // the one place `Function.name` is not yet the link-time symbol.
    assert!(
        pick_headers.iter().all(|header| header.contains("!trust_bodyless_instance::pick::")),
        "the instance-lane declarations keep the pin's collision form: {pick_headers:?}"
    );

    // A declaration must also be disambiguated from a spliced definition when there is only one
    // concrete instance, so the declaration-vs-declaration check cannot make this pass by itself.
    let single_id =
        referenced_id(named_function(&generic_functions, "single_instance_direct"), "call @func.");
    let single_decl = declaration(&generic_functions, single_id);
    // RESIDUAL (D17-DECL-SYMBOL-1), as above: the `::<u8>` instance's declaration keeps the
    // pre-WS5.2 name. Its path is no longer shared — the generic definition is not spliced
    // (below) — so it is the bare def path, with no display path and no symbol.
    assert!(
        single_decl.lines().next().is_some_and(|header| header.contains("fn @single_instance(")),
        "the `::<u8>` instance's declaration keeps its pre-WS5.2 name: {single_decl}"
    );
    assert_eq!(display_path(single_decl), None, "the carved-out row displays no path");
    // WS5.2 NEGATIVE TWIN: the GENERIC definition `single_instance<T>` names no symbol — each
    // caller links a different monomorphization and this pre-monomorphization body is none
    // of them — so it publishes NO definition (the module is monomorphic, SPEC §1), and its
    // coverage row names the refusal. Until WS5.2 it spliced under its def path.
    assert!(
        generic_functions.iter().all(|function| {
            display_path(function)
                .is_none_or(|path| path.rsplit("::").next() != Some("single_instance"))
                || !function.lines().any(|line| line.trim_start().starts_with("bb"))
        }),
        "the generic identity body must not be published as a definition"
    );
    assert_body_refused(&generics.coverage, "single_instance", "NoLinkTimeSymbol(");

    // Trust (2026-09-16, rvalue-snapshot admission): a crate whose `println!` / `panic!`
    // arguments are CALLS. The `format_args!` expansion for a non-trivial argument binds
    // `super let args = (&f(x),)`, and that rvalue snapshot in a tuple field used to be refused
    // (`Tuple(borrow ptr field)`), so wave-FA DROPPED the `Arguments` construction and the
    // sink's signature was withdrawn — the `RustAbiVararg` refusal every `println!("{}", f(x))`
    // crate hit at finalization. The temporary is one rustc provably cannot promote (`f` is not
    // `#[rustc_promotable]`), so the field is now admitted, the block lowers, and BOTH sinks are
    // signed `(struct.K) -> ()` for the producer's own `core::fmt::Arguments` registration —
    // the same `K` from the call shape and from the plain `println!("{}", x)` shape in one body
    // (`mixed_shapes`). No refusal, no vararg, no dropped parameter: the edge the validator
    // checks is real, which is what the two unit tests beside `crate_module.rs`'s
    // `append_declarations` pin at the module level.
    let fmt = compile_ir("rvalue_snapshot_fmt_sinks", "trust_ir_lower_rvalue_snapshot_field.rs");
    // Trust (2026-09-17): the four `through_*` names are NOT in this fixture and must not be
    // asserted clean here — they live in `trust_ir_lower_rvalue_snapshot_field_direct_residue.rs`,
    // where each is pinned `//~ ERROR could not fully lower this body`. They are the USER-WRITTEN
    // aggregate literal the admitted fixture's own header calls residue ("minted at a different
    // borrow site and still refuses `Tuple/Adt(borrow ptr field)`"), so asserting them lowered
    // CLEAN against the admitted artifact contradicts the residue pin. Landed in `65eefd9e62`
    // as a stale list against a fixture whose draft still carried them (the fixture keeps the
    // blank lines and the now-unused `S<'a>` where they were), and `x.py test --stage 1
    // tests/run-make --test-args trust` has been red on it since.
    assert_lowered_clean(&fmt.coverage, &["prints_a_call", "mixed_shapes", "panics_with_a_call"]);
    let fmt_functions = functions(&fmt.text);
    // The sinks are located by their declaration NAME (a `println!` body has several callees,
    // so the exactly-one `referenced_id` is the wrong question there); a FuncId is the
    // function's position in the dense table.
    let print_decl = named_function(&fmt_functions, "_print");
    let print_id = fmt_functions.iter().position(|f| *f == print_decl).expect("dense table");
    declaration(&fmt_functions, print_id);
    let print_struct = assert_struct_by_value_unit_signature(&fmt.text, print_decl);
    for caller in ["prints_a_call", "mixed_shapes"] {
        let body = named_function(&fmt_functions, caller);
        assert!(
            referenced_ids(body, "call @func.").contains(&print_id),
            "`{caller}` must call the `_print` declaration (FuncId {print_id}): {body}"
        );
    }
    // `panic!` with a call argument: the diverging sink is signed against the same struct.
    let panic_decl = named_function(&fmt_functions, "panic_fmt");
    let panic_id = fmt_functions.iter().position(|f| *f == panic_decl).expect("dense table");
    declaration(&fmt_functions, panic_id);
    assert!(
        referenced_ids(named_function(&fmt_functions, "panics_with_a_call"), "call @func.")
            .contains(&panic_id),
        "`panics_with_a_call` must call the `panic_fmt` declaration (FuncId {panic_id})"
    );
    let panic_struct = assert_struct_by_value_unit_signature(&fmt.text, panic_decl);
    assert_eq!(
        print_struct, panic_struct,
        "`_print` and `panic_fmt` must be signed against ONE `Arguments` registration"
    );

    // Trust (2026-09-17): the boundary `trust_ir_lower_format_args_residue_still_withdraws.rs`
    // used to pin from the ui lane. Its `format_args!` operand is a `&dyn Display`, whose
    // borrow the wave-AR2 allow-list refuses BY TYPE, so the rvalue-snapshot admission does
    // nothing for it, wave-FA drops the `Arguments` construction, and the body that mints the
    // resulting unsignable `std::io::_print` edge is REFUSED. Pinned here, on the producer's
    // own sidecar, because the ui lane can no longer observe it — see `assert_body_refused`.
    let residue =
        compile_ir("format_args_residue", "trust_ir_lower_format_args_residue_still_withdraws.rs");
    assert_body_refused(&residue.coverage, "show", "UnsignableRustAbiDeclaration");
    assert_lowered_clean(&residue.coverage, &["main"]);

    let runtime = bin_name("generic-fndef-runtime");
    rustc()
        .input(&generics.source)
        .crate_name("generic_fndef_runtime")
        .edition("2024")
        .cfg("runtime")
        // Trust: this binary is an EXECUTION OBSERVER — it is built and run only
        // to confirm the distinct generic FnDef instantiations behave at runtime;
        // the test's claims are about the emitted trust-ir signatures asserted
        // above, never a verdict about this binary. Under default strict policy
        // the direct producer cannot statically prove `single_instance_direct`'s
        // panic-freedom (the native CHC/PDR transport returns a counterexample,
        // not a proof), so strict fail-closes before the observer can run. Build
        // the observer verify-off; the signature assertions that ARE the test do
        // not depend on it.
        .arg("-Ztrust-verify=off")
        .output(&runtime)
        .run();
    run(&runtime);
}
