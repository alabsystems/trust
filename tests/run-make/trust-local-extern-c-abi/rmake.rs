//! A LOCAL `extern "C"` declaration is declared with the C calling convention — the ABI of its
//! `extern` block — exactly as the same function reached through `libc` is.
//!
//! `admit_callee_inner` read a local callee's ABI off its own HIR header. For a foreign item that
//! header is the item's, which `rustc_ast_lowering::item::lower_foreign_item` lowers with
//! `Extern::None`; the `extern "C"` lives on the `ForeignMod`. So every local foreign fn read
//! `ExternAbi::Rust`, its declaration was minted `rustcc` (a false claim in the IR), and a
//! variadic or `*mut *mut c_void` callee became an UNSIGNABLE Rust-ABI declaration whose calling
//! body was refused at assembly (`UnsignableRustAbiDeclaration(fcntl)`). The cross-crate route
//! (`tcx.fn_sig(def).abi()`) was always right, which is why `libc::fcntl` was declared C. The
//! fix reads the block's ABI the way rustc's own `fn_sig` provider does
//! (`tcx.hir_get_foreign_abi`).
//!
//! `ffi.rs` (the measurement's `repro/ffi.rs`) pins the fix: no `rustcc` declaration for
//! `close`/`fcntl`/`flock`/`posix_spawn_file_actions_*`, and the three bodies that were refused
//! are spliced, each calling its callee.
//!
//! `ffi_repr.rs` pins the one thing the C ABI must not do: a C-ABI declaration that passes or
//! returns a by-value `repr(Rust)` struct invalidates the WHOLE crate module
//! (`FfiStructReprUnpinned`), so the call is refused with a named tag and the crate compiles.
//@ ignore-cross-compile

use std::collections::BTreeMap;

use run_make_support::{cmd, rfs, rustc_path, serde_json};

/// One function header of the dumped module: its calling-convention prefix (`rustcc`, or empty
/// for canonical C), its def path (the `; #display-path:` directive, else the header's symbol),
/// and whether a body (a `bbN` block) follows.
struct Header {
    prefix: String,
    name: String,
    body: Vec<String>,
}

/// Every `fn @` header in module order (a `call @func.N` names the N-th one), with its body lines.
fn parse_module(text: &str) -> Vec<Header> {
    let mut out: Vec<Header> = Vec::new();
    let mut open = false;
    for line in text.lines() {
        if let Some(at) = line.find("fn @") {
            if line.contains("(functy.") {
                let rest = &line[at + 4..];
                let name = if let Some(q) = rest.strip_prefix('"') {
                    q[..q.find('"').expect("quoted name closes")].to_string()
                } else {
                    rest[..rest.find('(').expect("fn header has a type")].to_string()
                };
                out.push(Header { prefix: line[..at].trim().to_string(), name, body: Vec::new() });
                open = line.trim_end().ends_with('{');
                continue;
            }
        }
        if line.starts_with('}') {
            open = false;
            continue;
        }
        if open {
            let header = out.last_mut().expect("a body follows a header");
            // WS5.2: the header names the link-time SYMBOL (mangled for a Rust item); the def
            // path this test names bodies by is the `; #display-path:` directive.
            if let Some(path) = line.trim_start().strip_prefix("; #display-path: ") {
                header.name = path.trim().trim_matches('"').to_string();
            }
            header.body.push(line.to_string());
        }
    }
    out
}

fn is_definition(h: &Header) -> bool {
    h.body.iter().any(|l| l.trim_start().starts_with("bb"))
}

/// The callee names `h` calls.
fn callees(h: &Header, module: &[Header]) -> Vec<String> {
    let mut out = Vec::new();
    for line in &h.body {
        let code = line.split(';').next().unwrap_or("");
        for (i, _) in code.match_indices("call @func.") {
            let digits: String =
                code[i + 11..].chars().take_while(|c| c.is_ascii_digit()).collect();
            if let Ok(n) = digits.parse::<usize>() {
                out.push(
                    module.get(n).map(|m| m.name.clone()).unwrap_or_else(|| format!("func.{n}")),
                );
            }
        }
    }
    out
}

/// Compile `file` on the direct producer and return `(coverage rows by def_path, module, text)`.
fn lower(
    file: &str,
    crate_name: &str,
) -> (BTreeMap<String, serde_json::Value>, Vec<Header>, String) {
    let dump = format!("{crate_name}-ir");
    let args: Vec<String> = vec![
        file.to_string(),
        "--edition=2021".to_string(),
        "--crate-type=lib".to_string(),
        format!("--crate-name={crate_name}"),
        "-Copt-level=0".to_string(),
        "-Ccodegen-units=1".to_string(),
        "-Ztrust-verify=off".to_string(),
        "-Ztrust-ir-lower=on".to_string(),
        format!("-Ztrust-dump=ir:{dump}"),
        "--out-dir".to_string(),
        "out".to_string(),
    ];
    cmd(rustc_path()).args(&args).run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read(format!("{dump}/{crate_name}.coverage.json")))
            .expect("published coverage must be valid JSON");
    let mut rows = BTreeMap::new();
    for row in report["bodies"].as_array().expect("complete body inventory") {
        let path = row["def_path"].as_str().expect("body identity").to_string();
        assert!(rows.insert(path.clone(), row.clone()).is_none(), "duplicate row {path}");
    }
    let text = rfs::read_to_string(format!("{dump}/{crate_name}.trust-ir.txt"));
    (rows, parse_module(&text), text)
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // Stock rustc has no Trust-IR artifact interface.
    }

    // ── ffi.rs: the real ABI, and the bodies it unblocks ──────────────────────
    let (rows, module, text) = lower("ffi.rs", "ffi");
    assert!(
        !rows.values().any(|r| r.to_string().contains("UnsignableRustAbiDeclaration")),
        "no body may be refused for an unsignable Rust-ABI declaration of a C function:\n{rows:#?}"
    );
    for foreign in [
        "fcntl",
        "close",
        "flock",
        "posix_spawn_file_actions_destroy",
        "posix_spawn_file_actions_adddup2",
    ] {
        let decls: Vec<&Header> = module.iter().filter(|h| h.name == foreign).collect();
        assert_eq!(decls.len(), 1, "one declaration of `{foreign}`:\n{text}");
        let decl = decls[0];
        assert!(!is_definition(decl), "`{foreign}` has no body here:\n{text}");
        assert_ne!(decl.prefix, "rustcc", "`{foreign}` is a C function, not Rust-ABI:\n{text}");
        assert_eq!(
            decl.prefix, "",
            "`{foreign}` carries the canonical C convention (no prefix), as `libc`'s do:\n{text}"
        );
    }
    for (body, foreign) in [
        ("local_variadic", "fcntl"),
        ("local_plain", "close"),
        ("local_ptrptr", "posix_spawn_file_actions_destroy"),
        ("local_ptrptr_dup2", "posix_spawn_file_actions_adddup2"),
        ("local_flock", "flock"),
    ] {
        let row = &rows[body];
        assert_eq!(row["spliced"], true, "`{body}` must lower and splice: {row}");
        assert!(
            row["unsupported"].as_array().is_some_and(|t| t.is_empty()),
            "`{body}` carries no refusal tag: {row}"
        );
        let def = module
            .iter()
            .find(|h| h.name == body && is_definition(h))
            .unwrap_or_else(|| panic!("spliced `{body}` has a body:\n{text}"));
        assert!(
            callees(def, &module).iter().any(|c| c == foreign),
            "`{body}` calls `{foreign}`:\n{}",
            def.body.join("\n")
        );
    }

    // ── ffi_repr.rs: a by-value `repr(Rust)` struct at a C boundary is refused, not fatal ──
    // `lower` runs the compile with `.run()`, so reaching the next line IS the crate-level claim:
    // the module validated, no `FfiStructReprUnpinned` failed the compilation.
    let (rows, _, _) = lower("ffi_repr.rs", "ffi_repr");
    const TAG: &str = "Callee(foreign-ABI repr(Rust) struct by value)";
    for body in ["drop_pair", "pass_pair"] {
        let row = &rows[body];
        assert_eq!(row["spliced"], false, "`{body}` crosses a repr(Rust) struct over C: {row}");
        assert!(row["unsupported"].to_string().contains(TAG), "`{body}` names the refusal: {row}");
    }
    for body in ["drop_cpair", "dup"] {
        let row = &rows[body];
        assert!(
            !row["unsupported"].to_string().contains(TAG),
            "`{body}`'s struct has a pinned FFI layout; the S2 refusal must not fire: {row}"
        );
    }
}
