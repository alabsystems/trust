use std::process::Command;

/// The six variables through which a caller's environment names a compiler or
/// a compiler wrapper to Cargo: `build.rustc`, `build.rustc-wrapper` and
/// `build.rustc-workspace-wrapper`, each under its short name and under its
/// `CARGO_BUILD_` config-key name.
///
/// `targo trust` refuses an evidence-grade invocation while any of them is
/// set and non-empty ("RUSTC is set; evidence-grade Targo invocations require
/// the selected sibling trustc with no compiler wrapper"), which is right for
/// the product and fatal to a fixture that merely inherits one: bootstrap's
/// `x.py` exports `RUSTC` and `RUSTC_WRAPPER` to every test it runs, and a
/// developer's `sccache` sets `RUSTC_WRAPPER`. The unit tests' form of this
/// list is `unset_compiler_overrides_for_command_fixture` in `src/tests.rs`.
pub(crate) const COMPILER_OVERRIDE_ENV: [&str; 6] = [
    "RUSTC",
    "CARGO_BUILD_RUSTC",
    "RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
];

/// Keep the compiler settings this test was BUILT or RUN with out of a
/// fixture that selects its own sibling `trustc`.
///
/// A control whose point is that a set override is refused sets it on the
/// command AFTER this call.
pub(crate) fn remove_inherited_compiler_overrides(command: &mut Command) -> &mut Command {
    for key in COMPILER_OVERRIDE_ENV {
        command.env_remove(key);
    }
    command
}
