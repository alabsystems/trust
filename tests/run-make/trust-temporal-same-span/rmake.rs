//@ needs-crate-type: proc-macro
//@ ignore-cross-compile

//! Trust: distinct generated attributes can have identical spans. Placement
//! accounting must identify their HIR targets, not credit every attribute with
//! the span of one supported field or method. The positive control deliberately
//! gives every token that same span too; rejecting all shared spans loses valid
//! temporal annotations.

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, dynamic_lib_name, rfs, rustc_path};

fn trustc() -> PathBuf {
    let rustc = PathBuf::from(rustc_path());
    let candidate = rustc.with_file_name(bin_name("trustc"));
    if candidate.exists() { candidate } else { rustc }
}

fn main() {
    let compiler = trustc();
    let macros = dynamic_lib_name("same_span_macros");
    cmd(&compiler)
        .arg("-Ztrust-verify=off")
        .arg("--crate-type=proc-macro")
        .arg("--crate-name=same_span_macros")
        .arg("same_span_macros.rs")
        .arg("-o")
        .arg(&macros)
        .run();

    for (case, expected) in [
        ("valid", None),
        ("wrong_var", Some("#[trust::var] is only supported on fields of local structs")),
        ("wrong_action", Some("#[trust::action] is only supported on methods in impl blocks")),
        ("statement_var", Some("#[trust::var] is only supported on fields of local structs")),
    ] {
        let source = format!("{case}.rs");
        rfs::write(
            &source,
            format!(
                "#![feature(register_tool, stmt_expr_attributes)]\n\
                 #![register_tool(trust)]\n\
                 #![allow(dead_code)]\n\
                 extern crate same_span_macros;\n\
                 same_span_macros::generate!({case});\n"
            ),
        );
        let mut command = cmd(&compiler);
        command
            .arg("-Ztrust-ir-lower")
            .arg("--crate-type=lib")
            .arg("--emit=metadata")
            .arg(format!("--crate-name={case}"))
            .arg("--extern")
            .arg(format!("same_span_macros={macros}"))
            .arg(&source)
            .arg("-o")
            .arg(format!("{case}.rmeta"));
        if let Some(expected) = expected {
            // Finalization failures are fatal only in a claiming lane. Assert
            // their specific placement diagnostic, not an unrelated refusal.
            command
                .arg("-Ztrust-verify=on")
                .arg("-Ztrust-policy=strict")
                .run_fail()
                .assert_stderr_contains("trust-ir-lower semantic finalization failed")
                .assert_stderr_contains(expected);
        } else {
            command
                .arg("-Ztrust-verify=off")
                .arg("-Ztrust-dump=ir:valid-ir")
                .run()
                .assert_stderr_not_contains("temporal annotation carry failed closed");
            let text = rfs::read_to_string("valid-ir/valid.trust-ir.txt");
            for row in [
                "spec_module \"Machine\"",
                "var \"first\" : \"Int\"",
                "var \"second\" : \"Int\"",
                "action \"Step\"",
            ] {
                assert!(text.contains(row), "same-span control lost {row}:\n{text}");
            }
        }
    }
}
