use run_make_support::bare_rustc;

fn main() {
    let signalled_version = "Ceci n'est pas une rustc";
    let rustc_out = bare_rustc()
        .env("RUSTC_OVERRIDE_VERSION_STRING", signalled_version)
        .arg("--version")
        .run()
        .stdout_utf8();

    // Trust: `-V` leads with the canonical `rustc ` token, not the Trust alias —
    // the leading token is a machine-parsed contract for build scripts (see
    // rustc_driver_impl's version printer). The Trust binary identity rides the
    // trailing parenthetical and the verbose `binary:` / `trust:` lines.
    let version = rustc_out.strip_prefix("rustc ").unwrap().trim_end();

    // Trust: the override sets the VERSION; it does not and must not suppress
    // the tool's IDENTITY. `RUSTC_OVERRIDE_VERSION_STRING` is settable by anyone
    // in the environment, so honouring it for the identity parenthetical would
    // hand out a verifying compiler that reports as stock rustc — and with the
    // leading token already the hardcoded compat `rustc` and the version already
    // operator-supplied, that parenthetical is the LAST signal of what this
    // binary is. Suppressing it was implemented, measured, and reverted.
    //
    // The brand is keyed on the INVOKED name (`trust_display_binary`), so it is
    // empty under `--trust-vanilla`, whose wrapper is not called `trustc` and
    // which exists to reproduce upstream output byte-for-byte. Require the
    // identity only on the lane that should be emitting it.
    let vanilla = std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some();
    let (version, brand) = match version.split_once(" (") {
        Some((version, brand)) => (version, Some(brand.trim_end_matches(')'))),
        None => (version, None),
    };
    assert_eq!(version, signalled_version, "the overridden version must be reported verbatim");
    match brand {
        Some(brand) => assert!(
            brand.starts_with("trustc "),
            "identity parenthetical must name the Trust driver, got `{brand}`"
        ),
        None => assert!(
            vanilla,
            "Trust dropped its identity under RUSTC_OVERRIDE_VERSION_STRING: a compiler that \
             reports as stock rustc whenever an env var is set has made its own provenance \
             settable"
        ),
    }
}
