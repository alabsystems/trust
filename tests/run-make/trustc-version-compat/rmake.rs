//@ needs-symlink

use std::path::PathBuf;

use run_make_support::{assert_contains, bin_name, cmd, path, rfs, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

fn main() {
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() {
        trustc
    } else {
        let link = path(bin_name("trustc"));
        rfs::symlink_file(&rustc, &link);
        link
    };

    let short = cmd(&trustc).arg("-V").run().stdout_utf8();
    assert!(
        short.starts_with("rustc 1."),
        "trustc -V must keep the rustc version protocol parseable, got: {short:?}",
    );
    assert!(
        !short.starts_with("trustc "),
        "trustc -V must not put the Trust alias in the parse-sensitive prefix, got: {short:?}",
    );
    assert!(
        !short.contains("-trust"),
        "trustc -V must not expose an unknown rustc prerelease channel, got: {short:?}",
    );

    let verbose = cmd(&trustc).arg("-Vv").run().stdout_utf8();
    let first_line = verbose.lines().next().unwrap_or_default();
    assert!(
        first_line.starts_with("rustc 1."),
        "trustc -Vv first line must keep the rustc version protocol parseable, got: {first_line:?}",
    );
    // Under --trust-vanilla the wrapper script execs the real compiler, so
    // `binary:` reports the real binary's file name — `trustc` under the
    // Trust-only bootstrap wiring, `rustc` if a compat-alias path is ever
    // configured. Derive the expectation from the env value instead of
    // hard-coding the alias era's answer.
    let expected_binary = std::env::var(TRUST_VANILLA_REAL_RUSTC_ENV)
        .ok()
        .and_then(|real| {
            PathBuf::from(real)
                .file_stem()
                .and_then(|name| name.to_str().map(str::to_string))
        })
        .unwrap_or_else(|| "trustc".to_string());
    assert_contains(&verbose, &format!("\nbinary: {expected_binary}\n"));
    let release = verbose
        .lines()
        .find_map(|line| line.strip_prefix("release: "))
        .expect("trustc -Vv must include a release line");
    assert!(
        !release.contains("-trust"),
        "trustc -Vv release must use a rustc-recognized channel, got: {release:?}",
    );

    // Trust's OWN version rides its own line and is on its own numbering
    // (major.minor.dev, from src/version). It is what `targo trust version`
    // reports and what release evidence cites; the `rustc 1.` protocol above
    // says only which Rust this toolchain is compatible with. This assertion is
    // the whole point of keeping the two apart: Trust may be 0.x while the
    // compat line stays 1.x, and neither may drift into the other's slot.
    let trust = verbose
        .lines()
        .find_map(|line| line.strip_prefix("trust: "))
        .expect("trustc -Vv must include a trust: line carrying the Trust product version");
    let components: Vec<&str> = trust.trim().split('.').collect();
    assert!(
        components.len() == 3 && components.iter().all(|c| c.parse::<u32>().is_ok()),
        "trust: must be major.minor.dev, three numbers and no suffix, got: {trust:?}",
    );
}
