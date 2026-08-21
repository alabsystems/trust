use std::path::{Path, PathBuf};

use run_make_support::{bin_name, cmd, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    let thin = compile(&trustc, "w3_thin.rs", "w3_thin");
    assert_event(&thin, "compiled from trust-ir", "w3_thin::{impl#1}::is_zero");
    assert!(
        !target_lines(&thin, "w3_thin::{impl#1}::is_zero").any(|line| line.contains("FALLBACK")),
        "the thin W3 target reached a fallback instead of the TrustIR codegen path:\n{thin}",
    );

    let wide = compile(&trustc, "w3_wide.rs", "w3_wide");
    let wide_line = target_lines(&wide, "w3_wide::{impl#1}::all_empty")
        .find(|line| line.contains("FALLBACK"))
        .unwrap_or_else(|| panic!("the wide W3 control did not fail closed:\n{wide}"));
    assert!(
        wide_line.contains("local type outside fragment") && wide_line.contains("str"),
        "the wide W3 control failed for an unrelated reason:\n{wide_line}\n\n{wide}",
    );
    assert!(
        !target_lines(&wide, "w3_wide::{impl#1}::all_empty")
            .any(|line| line.contains("compiled from trust-ir")),
        "the wide W3 control reached the TrustIR codegen path:\n{wide}",
    );
}

fn compile(trustc: &Path, input: &str, crate_name: &str) -> String {
    cmd(trustc)
        .env_remove("TRUST_NO_VERIFY")
        .env("RUSTC_LOG", "rustc_mir_transform::trust_ir_flip=info")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Cpanic=abort")
        .arg("-Copt-level=3")
        .arg("--crate-type=lib")
        .arg("--emit=metadata")
        .arg("-Awarnings")
        .arg(format!("--crate-name={crate_name}"))
        .arg(input)
        .arg("-o")
        .arg(format!("lib{crate_name}.rmeta"))
        .run()
        .stderr_utf8()
}

fn target_lines<'a>(report: &'a str, target: &'a str) -> impl Iterator<Item = &'a str> {
    report.lines().filter(move |line| line.contains(target))
}

fn assert_event(report: &str, event: &str, target: &str) {
    assert!(
        target_lines(report, target).any(|line| line.contains(event)),
        "missing `{event}` event for `{target}`:\n{report}",
    );
}
