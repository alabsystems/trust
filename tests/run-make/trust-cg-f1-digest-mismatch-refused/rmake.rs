//! PKG-CV1: execute the actual F1 shipping consumer with original native
//! questions, then refuse a changed verified body before Compiler::compile.
//! This is the library consumer, not a rustc-plugin or direct-authority claim.
//@ only-apple
//@ only-aarch64

use std::path::PathBuf;

use run_make_support::{env_var_os, python_command, source_root};

fn main() {
    let build = PathBuf::from(env_var_os("BUILD_ROOT"));
    let target = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| build.join("f1-native-question-binding.noindex"));
    python_command()
        .arg(source_root().join("scripts/check_f1_native_question_binding.py"))
        .arg("--targo")
        .arg(build.join("stage0/bin/targo"))
        .arg("--target-dir")
        .arg(target)
        .run();
}
