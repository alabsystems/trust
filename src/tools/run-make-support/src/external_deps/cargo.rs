use std::path::Path;

use crate::command::Command;
use crate::util::set_host_compiler_dylib_path;

/// Returns a command that can be used to invoke in-tree cargo. The cargo is provided by compiletest
/// through the `CARGO` env var, and is **only** available for the `run-make-cargo` test suite.
pub fn cargo() -> Command {
    let cargo_path = std::env::var("CARGO").unwrap_or_else(|e| {
        panic!(
            "in-tree `cargo` should be available for `run-make-cargo` test suite, but not \
            `run-make` test suite: {e}"
        )
    });

    let is_targo = Path::new(&cargo_path)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .is_some_and(|stem| stem.eq_ignore_ascii_case("targo"));
    let mut cmd = Command::new(cargo_path);
    if is_targo {
        cmd.arg("--unverified");
    }
    set_host_compiler_dylib_path(&mut cmd);
    cmd
}
