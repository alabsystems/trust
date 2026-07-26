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
    assert_eq!(version, signalled_version);
}
