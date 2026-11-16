//@ needs-target-std
// ignore-tidy-linelength

// Check that the `CURRENT_RUSTC_VERSION` placeholder is correctly replaced by the current
// `rustc` version and the `since` property in feature stability gating is properly respected.

use run_make_support::{rfs, rustc, source_root};

fn main() {
    rustc().crate_type("lib").input("stable.rs").emit("metadata").run();

    let output =
        rustc().input("main.rs").emit("metadata").extern_("stable", "libstable.rmeta").run();
    // Trust: `since = "CURRENT_RUSTC_VERSION"` parses to `StableSince::Current`
    // (`compiler/rustc_attr_parsing/src/attributes/stability.rs`), which renders
    // from `env!("CFG_RELEASE")` — bootstrap's `rust_release()`, sourced from
    // `src/rust-compat-version`. Trust's own product version in `src/version`
    // (0.x) is a different numbering entirely, so asserting against it looks
    // for "stable since 0.1.0" in a diagnostic that says 1.99.0.
    let version = rfs::read_to_string(source_root().join("src/rust-compat-version"));
    let expected_string = format!("stable since {}", version.trim());
    output.assert_stderr_contains(expected_string);
}
