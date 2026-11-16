//! Trust (thir-generic-instance-callee, 2026-09-29; landed 2026-10-15): a call edge to a generic
//! std instance whose parameter is a REFERENCE TO A POINTER is SIGNED, its calling body SPLICES,
//! and the edge is TYPED against the real parameter list in the emitted module. And, because
//! `&P` and `P` share the `ptr` spelling when `P` is a thin pointer, every argument on such an
//! edge is a REAL borrow: no call site may pass `P` where `&P` is due.
//!
//! The ui twins (`tests/ui/trust/trust_ir_lower_ref_to_pointer_params_sign.rs`,
//! `…_carrier_refused.rs`) observe what `-Ztrust-ir-lower=strict` REPORTS. This observes what
//! the PRODUCER EMITS, which is a separate claim: a body can be "not refused" and still be
//! absent from the module, and a declaration can be present and still carry the vararg
//! encoding that makes every edge to it vacuously well-typed. So, on the canonical text and
//! the coverage sidecar:
//!   * every shape body is `lowered` AND `spliced`, with no refusal row;
//!   * every declaration it calls is bodyless and signed — no `...` anywhere in the module;
//!   * the class's two dominant edges carry their exact instantiated signatures:
//!     `<&A as PartialEq<&B>>::eq` is `(ptr, ptr) -> (bool)` (both `&&A` / `&&B` parameters thin
//!     pointers), and `Argument::new_display::<&str>` is `(ptr) -> (struct.N)`;
//!   * the `==` edges pass SLOT addresses (an `alloca` holding the operand), never the operand;
//!   * the negative source: `through_carrier` has no genuine borrow for its `&&dyn Debug`
//!     argument and is refused at its CALL SITE (`Call(unsupported arg)`), not spliced, and the
//!     rest of that module still validates;
//!   * `dropped_borrow.rs`: the 2026-09-15 adversarial review's DROPPED-BORROW shapes (the
//!     verbatim `take_raw(&q)` over a verify-off dependency, a raw-pointer method receiver, a
//!     receiver PLACE, a `&&dyn` and a `&&u8` place argument) are each refused at their own call
//!     site, and its two controls splice with a faithful argument: the address of a slot that
//!     holds the parameter, and, for a reborrow `&*rr`, `rr` itself.
//!
//! Before the fix every shape body carried `UnsignableRustAbiDeclaration(..)` and was neither
//! lowered nor spliced. The negative controls were measured on 2026-10-15 against stage-1 builds
//! with the call-site checks removed (docs/DECISION_QUEUE.md, REF-TO-PTR-SIGN-1).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use run_make_support::{rfs, rustc, serde_json, source_root};

struct Artifacts {
    text: String,
    coverage: serde_json::Value,
}

fn compile_ir(crate_name: &str, source: &Path, externs: &[(&str, &str)]) -> Artifacts {
    let out = PathBuf::from(format!("{crate_name}-ir"));
    rfs::create_dir(&out);
    let mut cmd = rustc();
    cmd.input(source)
        .crate_name(crate_name)
        .crate_type("lib")
        .edition("2021")
        .emit("trust-ir")
        .out_dir(&out)
        .arg("-Ztrust-verify=off");
    for (name, dir) in externs {
        cmd.extern_(name, format!("{dir}/lib{name}.rlib")).library_search_path(dir);
    }
    let stderr = cmd.run().stderr_utf8();
    for banned in [
        "final Trust-IR module validation failed",
        "CallArgTypeMismatch",
        "CallEdgeSignatureMismatch",
        "unsignable-rust-abi-declaration",
    ] {
        assert!(!stderr.contains(banned), "unexpected `{banned}`:\n{stderr}");
    }
    let text = rfs::read_to_string(out.join(format!("{crate_name}.trust-ir.txt")));
    let coverage = serde_json::from_str(&rfs::read_to_string(
        out.join(format!("{crate_name}.trust-ir.coverage.json")),
    ))
    .expect("coverage sidecar must be valid JSON");
    Artifacts { text, coverage }
}

fn ui_source(name: &str) -> PathBuf {
    source_root().join("tests/ui/trust").join(name)
}

/// Every `fn @` block of the canonical text, in dense `FuncId` order.
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

/// The def path of a function. WS5.2: the header names the link-time SYMBOL and the def path
/// is the `; #display-path:` directive; a function without one is named by its header.
fn display_path(function: &str) -> String {
    if let Some(path) =
        function.lines().find_map(|line| line.trim_start().strip_prefix("; #display-path: "))
    {
        return path.trim().trim_matches('"').to_string();
    }
    let name = function
        .lines()
        .next()
        .and_then(|line| line.split_once("fn @"))
        .and_then(|(_, tail)| tail.split_once("(functy."))
        .map(|(name, _)| name)
        .unwrap_or_else(|| panic!("malformed header:\n{function}"));
    // A name outside `[A-Za-z0-9_.$]` prints QUOTED; strip a BALANCED pair only.
    name.strip_prefix('"').and_then(|n| n.strip_suffix('"')).unwrap_or(name).to_string()
}

fn named_function<'a>(functions: &'a [&'a str], name: &str) -> &'a str {
    let found: Vec<_> = functions
        .iter()
        .copied()
        .filter(|function| display_path(function).rsplit("::").next() == Some(name))
        .collect();
    assert_eq!(found.len(), 1, "wanted one `{name}` function, got {found:?}");
    found[0]
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

fn is_declaration(function: &str) -> bool {
    !function.lines().any(|line| line.trim_start().starts_with("bb"))
}

/// Each direct call in a body: the callee's dense `FuncId` and the argument spellings.
fn calls(function: &str) -> Vec<(usize, Vec<String>)> {
    let marker = "call @func.";
    let mut out = Vec::new();
    for line in function.lines() {
        let Some(at) = line.find(marker) else { continue };
        let rest = &line[at + marker.len()..];
        let digits = rest.bytes().take_while(|byte| byte.is_ascii_digit()).count();
        assert!(digits > 0, "malformed `{marker}` in:\n{function}");
        let id = rest[..digits].parse::<usize>().expect("numeric FuncId");
        let args = rest[digits..]
            .strip_prefix('(')
            .and_then(|tail| tail.split_once(')'))
            .map(|(args, _)| args)
            .unwrap_or_else(|| panic!("malformed call in `{line}`"));
        let args = args
            .split(',')
            .map(str::trim)
            .filter(|arg| !arg.is_empty())
            .map(str::to_string)
            .collect();
        out.push((id, args));
    }
    out
}

/// The dense `FuncId`s a body calls directly.
fn callees(function: &str) -> BTreeSet<usize> {
    calls(function).into_iter().map(|(id, _)| id).collect()
}

/// The argument lists of `caller`'s calls to functions whose def path contains `needle`.
fn args_to<'a>(functions: &'a [&'a str], caller: &str, needle: &str) -> Vec<Vec<String>> {
    calls(named_function(functions, caller))
        .into_iter()
        .filter(|(id, _)| {
            functions.get(*id).is_some_and(|callee| display_path(callee).contains(needle))
        })
        .map(|(_, args)| args)
        .collect()
}

/// Is `value` a SLOT of `function`: the result of an `alloca`?
fn is_slot(function: &str, value: &str) -> bool {
    let def = format!("{value} = alloca ");
    function.lines().any(|line| line.trim_start().starts_with(&def))
}

/// The value `function` stores into `slot` (`store <ty> <value>, ptr <slot>`), if exactly one.
fn stored_into(function: &str, slot: &str) -> Option<String> {
    let suffix = format!(", ptr {slot}");
    let stored: Vec<String> = function
        .lines()
        .map(|line| line.split(';').next().unwrap_or("").trim())
        .filter(|line| line.starts_with("store ") && line.ends_with(&suffix))
        .filter_map(|line| {
            let operands = line[..line.len() - suffix.len()].strip_prefix("store ")?;
            operands.rsplit(' ').next().map(str::to_string)
        })
        .collect();
    (stored.len() == 1).then(|| stored[0].clone())
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

fn assert_clean(coverage: &serde_json::Value, name: &str) {
    let row = body_row(coverage, name);
    assert_eq!(row["lowered"], true, "`{name}` not lowered: {row}");
    assert_eq!(row["spliced"], true, "`{name}` not spliced: {row}");
    assert_eq!(row["unsupported"].as_array().map(Vec::len), Some(0), "`{name}` refused: {row}");
}

/// Refused at its own CALL SITE: neither lowered nor spliced, with the call's own refusal.
fn assert_refused_at_call(coverage: &serde_json::Value, name: &str) {
    let row = body_row(coverage, name);
    assert_eq!(row["spliced"], false, "`{name}` spliced with no genuine borrow: {row}");
    assert_eq!(row["lowered"], false, "`{name}` lowered with no genuine borrow: {row}");
    assert!(
        row["unsupported"].to_string().contains("Call(unsupported arg)"),
        "`{name}` must be refused at its call site: {row}"
    );
}

/// The signed declarations `caller` calls whose def path contains `needle`, with their
/// signatures.
fn called_declarations<'a>(
    text: &'a str,
    functions: &'a [&'a str],
    caller: &str,
    needle: &str,
) -> Vec<&'a str> {
    let body = named_function(functions, caller);
    callees(body)
        .into_iter()
        .map(|id| {
            *functions
                .get(id)
                .unwrap_or_else(|| panic!("`{caller}` calls FuncId {id}, which has no function"))
        })
        .filter(|callee| display_path(callee).contains(needle))
        .map(|callee| {
            assert!(is_declaration(callee), "`{needle}` edge of `{caller}` is not bodyless");
            signature(text, callee)
        })
        .collect()
}

const SHAPES: &[&str] = &[
    "fmt_display_str",
    "fmt_debug_str",
    "fmt_mixed",
    "eq_str",
    "ne_str",
    "eq_ref_u32",
    "ge_ref_u64",
    "eq_string",
    "string_eq_lit",
    "clone_ref",
    "size_of_ref",
];

fn main() {
    let shapes = compile_ir(
        "ref_to_pointer_params",
        &ui_source("trust_ir_lower_ref_to_pointer_params_sign.rs"),
        &[],
    );
    for name in SHAPES {
        assert_clean(&shapes.coverage, name);
    }
    // No declaration anywhere in the module may carry the unknown-signature encoding.
    for line in shapes.text.lines().filter(|line| line.starts_with("functy.")) {
        assert!(!line.contains("..."), "a declaration is still vararg: {line}");
    }
    let shape_fns = functions(&shapes.text);
    for caller in ["eq_str", "eq_ref_u32", "eq_string"] {
        let eq = called_declarations(&shapes.text, &shape_fns, caller, "PartialEq<&B> for &A>::eq");
        assert_eq!(eq, ["(ptr, ptr) -> (bool)"], "`{caller}`'s `==` edge: {eq:?}");
        // `a == b` on references is `<&A as PartialEq<&B>>::eq(&a, &b)`: each argument is the
        // address of a slot holding the operand, never the operand (a dropped borrow).
        let body = named_function(&shape_fns, caller);
        for args in args_to(&shape_fns, caller, "PartialEq<&B> for &A>::eq") {
            assert_eq!(args.len(), 2, "`{caller}`'s `==` takes two arguments: {args:?}");
            for (arg, param) in args.iter().zip(["%0", "%1"]) {
                assert!(is_slot(body, arg), "`{caller}` passes `{arg}`, not a slot:\n{body}");
                assert_eq!(
                    stored_into(body, arg).as_deref(),
                    Some(param),
                    "`{caller}`'s slot `{arg}` must hold the operand `{param}`:\n{body}"
                );
            }
        }
    }
    let display = called_declarations(&shapes.text, &shape_fns, "fmt_display_str", "new_display");
    assert_eq!(display.len(), 1, "`fmt_display_str` must call one `new_display`: {display:?}");
    let (params, ret) = display[0].split_once(" -> ").expect("signature arrow");
    assert_eq!(params, "(ptr)", "`new_display::<&str>` takes one `&&str`: {}", display[0]);
    assert!(
        ret.starts_with("(struct.") && ret.ends_with(')'),
        "`new_display::<&str>` returns the `Argument` struct: {}",
        display[0]
    );

    let negative = compile_ir(
        "ref_to_pointer_carrier",
        &ui_source("trust_ir_lower_ref_to_pointer_carrier_refused.rs"),
        &[],
    );
    assert_refused_at_call(&negative.coverage, "through_carrier");
    for control in ["thin_control", "fat_control"] {
        assert_clean(&negative.coverage, control);
    }

    // The 2026-09-15 review's shapes. `take_raw_dep` is the ui pin's own verify-off dependency.
    let aux = "take_raw_dep-aux";
    rfs::create_dir(aux);
    rustc()
        .input(ui_source("auxiliary/take_raw_dep.rs"))
        .crate_type("rlib")
        .edition("2021")
        .arg("-Ztrust-verify=off")
        .arg("-Zalways-encode-mir")
        .out_dir(aux)
        .run();
    let dropped =
        compile_ir("dropped_borrow", Path::new("dropped_borrow.rs"), &[("take_raw_dep", aux)]);
    for refused in ["call_raw", "size_raw", "recv_raw", "recv_place_raw", "place_ref", "place_dyn"]
    {
        assert_refused_at_call(&dropped.coverage, refused);
    }
    for control in ["borrow_ref_param", "reborrow_param"] {
        assert_clean(&dropped.coverage, control);
    }
    let dropped_fns = functions(&dropped.text);
    for (caller, want) in [("borrow_ref_param", "slot"), ("reborrow_param", "%0")] {
        let sig = called_declarations(&dropped.text, &dropped_fns, caller, "size_of_val");
        assert_eq!(sig, ["(ptr) -> (usize)"], "`{caller}`'s `size_of_val` edge: {sig:?}");
        let args = args_to(&dropped_fns, caller, "size_of_val");
        assert_eq!(args.len(), 1, "`{caller}` calls `size_of_val` once: {args:?}");
        assert_eq!(args[0].len(), 1, "`size_of_val` takes one argument: {args:?}");
        let body = named_function(&dropped_fns, caller);
        let arg = &args[0][0];
        if want == "slot" {
            // `size_of_val(&r)`: the address of a slot holding `r`, never `r` (`%0`) itself.
            assert!(is_slot(body, arg), "`{caller}` passes `{arg}`, not a slot:\n{body}");
            assert_eq!(
                stored_into(body, arg).as_deref(),
                Some("%0"),
                "`{caller}`'s slot `{arg}` must hold the parameter:\n{body}"
            );
        } else {
            // `size_of_val(&*rr)` IS `size_of_val(rr)` at the identical type `&&u8`.
            assert_eq!(arg, want, "`{caller}` must pass `rr` itself:\n{body}");
        }
    }
}
