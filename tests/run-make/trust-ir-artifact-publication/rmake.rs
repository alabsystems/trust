use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path, serde_json};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";
const CRATE_NAME: &str = "ir_publication_probe";
const DUMP_DIRECTORY: &str = "ir-publication";
const SUFFIXES: [&str; 3] = ["trust-ir.bin", "trust-ir.txt", "coverage.json"];

fn artifact_path(suffix: &str) -> PathBuf {
    PathBuf::from(DUMP_DIRECTORY).join(format!("{CRATE_NAME}.{suffix}"))
}

fn assert_no_current_artifacts(reason: &str) {
    for suffix in SUFFIXES {
        assert!(
            !artifact_path(suffix).exists(),
            "{reason} retained stale direct-TrustIR artifact `{CRATE_NAME}.{suffix}`"
        );
    }
    if PathBuf::from(DUMP_DIRECTORY).is_dir() {
        for entry in rfs::read_dir(DUMP_DIRECTORY) {
            let name = entry.expect("read publication directory entry").file_name();
            assert!(
                !name.to_string_lossy().contains(".trustc-publish-"),
                "{reason} retained temporary publication file `{}`",
                name.to_string_lossy()
            );
        }
    }
}

fn read_current_artifacts() -> [Vec<u8>; 3] {
    let artifacts = SUFFIXES.map(|suffix| {
        let path = artifact_path(suffix);
        assert!(path.is_file(), "successful publication omitted `{}`", path.display());
        rfs::read(path)
    });

    let mut actual = rfs::read_dir(DUMP_DIRECTORY)
        .map(|entry| {
            entry
                .expect("read successful publication entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect::<Vec<_>>();
    actual.sort();
    let mut expected = SUFFIXES.map(|suffix| format!("{CRATE_NAME}.{suffix}")).to_vec();
    expected.push(format!(".{CRATE_NAME}.coverage.json.trustc-publish.lock"));
    expected.sort();
    assert_eq!(actual, expected, "publication directory contained a partial or temporary set");
    artifacts
}

fn assert_commit_marker(artifacts: &[Vec<u8>; 3]) {
    let [binary, text, marker] = artifacts;
    assert!(!binary.is_empty(), "binary direct-TrustIR artifact was empty");
    assert!(!text.is_empty(), "text direct-TrustIR artifact was empty");

    let coverage: serde_json::Value =
        serde_json::from_slice(marker).expect("coverage commit marker must be valid JSON");
    assert_eq!(coverage["schema"], "trust.thir-lower.crate-module.coverage.v2");
    let known_verdict =
        |verdict: &str| matches!(verdict, "agreed" | "mismatch" | "unsupported" | "not-run");
    let bodies = coverage["bodies"].as_array().expect("coverage must inventory every body");
    assert!(!bodies.is_empty(), "publication probe must contain at least one body");
    let mut saw_deferred = false;
    for body in bodies {
        let differentials = body["differentials"]
            .as_object()
            .expect("each body must carry a typed differential inventory");
        let interpreter = differentials["interpreter"]["verdict"]
            .as_str()
            .expect("interpreter verdict must be typed text");
        let derived = differentials["derived_mir"]["verdict"]
            .as_str()
            .expect("derived-MIR verdict must be typed text");
        assert!(known_verdict(interpreter), "unknown interpreter verdict `{interpreter}`");
        assert!(known_verdict(derived), "unknown derived-MIR verdict `{derived}`");
        assert!(
            differentials["interpreter"]["samples"].as_u64().is_some(),
            "interpreter evidence must carry a deterministic sample count"
        );
        assert!(
            differentials["derived_mir"]["markers_exact"].as_bool().is_some(),
            "derived-MIR evidence must carry its exact marker verdict"
        );

        let deferred = differentials["deferred_to_seam"]
            .as_bool()
            .expect("deferred seam ownership must be explicit");
        let seam_state =
            differentials["seam"]["state"].as_str().expect("seam outcome state must be explicit");
        if deferred {
            saw_deferred = true;
            assert_eq!(seam_state, "resolved");
            let verdict = differentials["seam"]["verdict"]
                .as_str()
                .expect("resolved seam must carry a typed verdict");
            assert!(known_verdict(verdict), "unknown seam verdict `{verdict}`");
        } else {
            assert_eq!(seam_state, "not-applicable");
            assert!(
                differentials["seam"].get("verdict").is_none(),
                "a non-deferred body must not carry a synthetic seam verdict"
            );
        }
    }
    assert!(
        saw_deferred,
        "publication probe must exercise a call-bearing body resolved by the crate seam"
    );
    assert_eq!(coverage["publication"]["schema"], "trust.thir-lower.artifact-set.v1");
    assert_eq!(coverage["publication"]["digest_algorithm"], "sha256-domain-v1");
    assert_eq!(coverage["publication"]["digest_domain"], "trust.thir-lower.artifact.v1");
    assert_eq!(coverage["publication"]["commit_marker"], true);

    let manifest = coverage["publication"]["artifacts"]
        .as_array()
        .expect("commit marker must bind its data artifacts");
    assert_eq!(manifest.len(), 2);
    for (entry, (suffix, bytes)) in
        manifest.iter().zip([("trust-ir.bin", binary), ("trust-ir.txt", text)])
    {
        assert_eq!(entry["name"], format!("{CRATE_NAME}.{suffix}"));
        assert_eq!(entry["bytes"].as_u64(), Some(bytes.len() as u64));
        let digest = entry["digest"].as_str().expect("artifact digest must be text");
        let hex = digest.strip_prefix("sha256:").expect("artifact digest must name SHA-256");
        assert_eq!(hex.len(), 64, "artifact digest must contain 256 bits");
        assert!(
            hex.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
            "artifact digest must use canonical lower-case hexadecimal: {digest}"
        );
    }
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    let publication_command = || {
        let mut command = cmd(&trustc);
        command
            .arg("-Ztrust-verify=off")
            .arg("-Ztrust-ir-lower")
            .arg(format!("-Ztrust-dump=ir:{DUMP_DIRECTORY}"))
            .arg("--crate-type=lib")
            .arg(format!("--crate-name={CRATE_NAME}"))
            .arg("--emit=metadata");
        command
    };
    let publish_current = |value: u8| {
        rfs::write(
            "publication-current.rs",
            format!(
                "pub fn publication_helper() -> u8 {{ {value} }}\n\
                 pub fn publication_current() -> u8 {{ publication_helper() }}\n"
            ),
        );
        publication_command()
            .arg("publication-current.rs")
            .arg("-o")
            .arg("publication-current.rmeta")
            .run();
        let artifacts = read_current_artifacts();
        assert_commit_marker(&artifacts);
        artifacts
    };

    // Invalid target and identity requests fail before reading even a missing
    // input. They are not accepted publications because no safe target exists.
    rfs::write("not-a-publication-directory", "occupied\n");
    cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-dump=ir:not-a-publication-directory")
        .arg("--crate-name=invalid_target_probe")
        .arg("definitely-missing-target-input.rs")
        .run_fail()
        .assert_stderr_contains("trust-ir-lower artifact target preparation failed");

    cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg(format!("-Ztrust-dump=ir:{DUMP_DIRECTORY}"))
        .arg("definitely-missing-no-name.rs")
        .run_fail()
        .assert_stderr_contains(
            "-Ztrust-dump=ir:<dir> with -Ztrust-ir-lower requires an explicit --crate-name",
        );
    for (crate_name, expected) in [
        ("--crate-name=", "crate name must not be empty"),
        ("--crate-name=not-safe", "invalid character"),
    ] {
        cmd(&trustc)
            .arg("-Ztrust-verify=off")
            .arg("-Ztrust-ir-lower")
            .arg(format!("-Ztrust-dump=ir:{DUMP_DIRECTORY}"))
            .arg(crate_name)
            .arg("definitely-missing-invalid-name.rs")
            .run_fail()
            .assert_stderr_contains(expected);
    }

    // The response-file prohibition is publication-specific. Ordinary
    // compiler invocations retain rustc's normal argfile behavior.
    rfs::write("ordinary-response-source.rs", "pub fn ordinary_response() {}\n");
    rfs::write(
        "ordinary-nonpublication.args",
        "-Ztrust-verify=off\n--crate-type=lib\n--crate-name=ordinary_response\n\
         --emit=metadata\nordinary-response-source.rs\n-o\nordinary-response.rmeta\n",
    );
    cmd(&trustc).arg("@ordinary-nonpublication.args").run();
    assert!(PathBuf::from("ordinary-response.rmeta").is_file());

    // A complete replacement contains exactly two data files and the
    // generation-bound coverage commit marker. Changing source bytes must
    // change both direct encodings and the marker that authenticates them.
    let first = publish_current(11);
    let second = publish_current(12);
    assert_ne!(first[0], second[0], "binary artifact ignored a semantic source change");
    assert_ne!(first[1], second[1], "text artifact ignored a semantic source change");
    assert_ne!(first[2], second[2], "commit marker did not bind the replacement generation");

    // Raw help/version paths return before typed Options and therefore cannot
    // select a safe publication target. The driver explicitly rejects this
    // combination as outside the publication-attempt boundary; it must not
    // silently report success as though it published a new generation.
    let current = publish_current(11);
    publication_command()
        .arg("--version")
        .run_fail()
        .assert_stderr_contains("exits before typed publication-target validation");
    assert_eq!(read_current_artifacts(), current, "rejected raw mode mutated the current set");

    // Typed options are validated before input selection. No input, multiple
    // inputs, and invalid UTF-8 on stdin all fail before parser construction,
    // but must already have invalidated the explicit target.
    publish_current(11);
    publication_command().run_fail().assert_stderr_contains("no input filename given");
    assert_no_current_artifacts("no-input failure");

    rfs::write("first-input.rs", "pub fn first() {}\n");
    rfs::write("second-input.rs", "pub fn second() {}\n");
    publish_current(11);
    publication_command()
        .arg("first-input.rs")
        .arg("second-input.rs")
        .run_fail()
        .assert_stderr_contains("multiple input filenames provided");
    assert_no_current_artifacts("multiple-input failure");

    publish_current(11);
    publication_command()
        .arg("-")
        .stdin_buf([0xff, 0xfe, 0xfd])
        .run_fail()
        .assert_stderr_contains("couldn't read from stdin");
    assert_no_current_artifacts("invalid UTF-8 stdin");

    // Publication authority is captured from outer argv before any response
    // file is opened. Every argfile failure must therefore invalidate the old
    // generation even though typed Options are never constructed.
    publish_current(11);
    publication_command()
        .arg("@definitely-missing-publication.args")
        .arg("publication-current.rs")
        .run_fail()
        .assert_stderr_contains("failed to load argument file");
    assert_no_current_artifacts("missing response file");

    // Even an outer raw early mode cannot suppress pre-invalidation once the
    // otherwise complete publication request includes a response file.
    publish_current(11);
    publication_command()
        .arg("-vV")
        .arg("@definitely-missing-early-publication.args")
        .arg("publication-current.rs")
        .run_fail()
        .assert_stderr_contains("failed to load argument file");
    assert_no_current_artifacts("raw early mode with missing response file");

    publish_current(11);
    rfs::write("malformed-shell.args", "'unterminated\n");
    publication_command()
        .arg("-Zshell-argfiles")
        .arg("@shell:malformed-shell.args")
        .arg("publication-current.rs")
        .run_fail()
        .assert_stderr_contains("invalid shell-style arguments");
    assert_no_current_artifacts("malformed shell response file");

    publish_current(11);
    rfs::write("invalid-utf8.args", [b'i', b'n', b'p', b'u', b't', 0xff]);
    publication_command()
        .arg("@invalid-utf8.args")
        .arg("publication-current.rs")
        .run_fail()
        .assert_stderr_contains("UTF-8 error");
    assert_no_current_artifacts("invalid UTF-8 response file");

    // Parsed options cannot retain reliable response-file provenance because a
    // trailing value-taking option in one source can consume a token from the
    // next. Direct publication therefore rejects every readable response file,
    // including files containing only ordinary compiler arguments, after
    // invalidating every unambiguous, fully known target.
    publish_current(11);
    rfs::write(
        "ordinary-publication.args",
        "publication-current.rs\n-o\nordinary-response.rmeta\n",
    );
    publication_command()
        .arg("@ordinary-publication.args")
        .run_fail()
        .assert_stderr_contains("cannot use @response-files");
    assert_no_current_artifacts("ordinary response file in publication");

    // Rejection must precede effectful/successful option handlers. Inserting a
    // separator can otherwise hide every following outer publication control
    // from the expanded matches while an early mode returns success.
    publish_current(11);
    rfs::write("early-exit-publication.args", "-vV\n--\n");
    cmd(&trustc)
        .arg("@early-exit-publication.args")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg(format!("-Ztrust-dump=ir:{DUMP_DIRECTORY}"))
        .arg(format!("--crate-name={CRATE_NAME}"))
        .arg("publication-current.rs")
        .run_fail()
        .assert_stderr_contains("cannot use @response-files");
    assert_no_current_artifacts("response-file early-exit publication bypass");

    publish_current(11);
    rfs::write(
        "publication-authority.args",
        format!(
            "-Ztrust-verify=off\n-Ztrust-ir-lower\n-Ztrust-dump=ir:{DUMP_DIRECTORY}\n\
             --crate-type=lib\n--crate-name={CRATE_NAME}\n--emit=metadata\n\
             publication-current.rs\n-o\nresponse-authority.rmeta\n"
        ),
    );
    cmd(&trustc)
        .arg("@publication-authority.args")
        .run_fail()
        .assert_stderr_contains("cannot use @response-files");
    assert_no_current_artifacts("response-file-owned publication authority");

    // Regression for cross-origin value capture: the response-owned remap
    // option consumes the following outer dump token, while the response-owned
    // dump becomes the sole parsed dump value. Matching parsed identities must
    // not make that mixed-origin invocation acceptable.
    publish_current(11);
    rfs::write(
        "cross-origin-publication.args",
        format!("-Ztrust-dump=ir:{DUMP_DIRECTORY}\n--remap-path-prefix\n"),
    );
    cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("@cross-origin-publication.args")
        .arg(format!("-Ztrust-dump=ir:{DUMP_DIRECTORY}"))
        .arg("--crate-type=lib")
        .arg(format!("--crate-name={CRATE_NAME}"))
        .arg("--emit=metadata")
        .arg("publication-current.rs")
        .arg("-o")
        .arg("cross-origin-response.rmeta")
        .run_fail()
        .assert_stderr_contains("cannot use @response-files");
    assert_no_current_artifacts("cross-origin response-file publication authority");

    publish_current(11);
    rfs::write(
        "duplicate-publication-authority.args",
        format!("-Ztrust-dump=ir:{DUMP_DIRECTORY}\n--crate-name={CRATE_NAME}\n"),
    );
    publication_command()
        .arg("@duplicate-publication-authority.args")
        .arg("publication-current.rs")
        .run_fail()
        .assert_stderr_contains("cannot use @response-files");
    assert_no_current_artifacts("duplicated response-file publication authority");

    // getopts permits clustered short options. Preflight must use the same
    // grammar or `-vZtrust-dump=ir:...` can bypass the early lease.
    publish_current(11);
    cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg(format!("-vZtrust-dump=ir:{DUMP_DIRECTORY}"))
        .arg("--crate-type=lib")
        .arg(format!("--crate-name={CRATE_NAME}"))
        .arg("--emit=metadata")
        .arg("@definitely-missing-clustered-publication.args")
        .arg("publication-current.rs")
        .run_fail()
        .assert_stderr_contains("failed to load argument file");
    assert_no_current_artifacts("clustered response-file publication failure");

    // These successful early exits occur after typed target validation but
    // before parsing/analysis. They produce no direct-TrustIR set, so the old
    // marker must be absent rather than authenticating stale data as current.
    for (mode, argument) in [
        ("error explanation", "--explain=E0001"),
        ("print request", "--print=cfg"),
        ("lint help", "-Whelp"),
    ] {
        publish_current(11);
        publication_command().arg(argument).run();
        assert_no_current_artifacts(mode);
    }

    rfs::write("metadata-source.rs", "pub fn metadata_source() {}\n");
    cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("--crate-type=lib")
        .arg("metadata-source.rs")
        .arg("-o")
        .arg("metadata-source.rlib")
        .run();
    publish_current(11);
    publication_command().arg("-Zls=root").arg("metadata-source.rlib").run();
    assert_no_current_artifacts("metadata listing");

    // Parser construction, input decoding, crate-identity agreement, injected
    // attributes, and semantic analysis all share the same fail-closed target.
    publish_current(11);
    rfs::write("syntax-failure.rs", "pub fn syntax_failure() { let _ = ; }\n");
    publication_command().arg("syntax-failure.rs").arg("-o").arg("syntax-failure.rmeta").run_fail();
    assert_no_current_artifacts("syntax failure");

    publish_current(11);
    rfs::write(
        "eager-token-failure.rs",
        format!("#![crate_name = \"{CRATE_NAME}\"]\npub fn eager_token_failure(\n"),
    );
    publication_command()
        .arg("eager-token-failure.rs")
        .arg("-o")
        .arg("eager-token-failure.rmeta")
        .run_fail()
        .assert_stderr_contains("unclosed delimiter");
    assert_no_current_artifacts("eager token-tree failure");

    publish_current(11);
    rfs::write("invalid-utf8-file.rs", [b'p', b'u', b'b', b' ', 0xff, b'\n']);
    publication_command()
        .arg("invalid-utf8-file.rs")
        .arg("-o")
        .arg("invalid-utf8-file.rmeta")
        .run_fail()
        .assert_stderr_contains("stream did not contain valid UTF-8");
    assert_no_current_artifacts("invalid UTF-8 file input");

    publish_current(11);
    publication_command()
        .arg("definitely-missing-publication-input.rs")
        .arg("-o")
        .arg("missing-publication-input.rmeta")
        .run_fail()
        .assert_stderr_contains("couldn't read");
    assert_no_current_artifacts("missing file input");

    publish_current(11);
    rfs::write(
        "source-name-mismatch.rs",
        "#![crate_name = \"different_name\"]\npub fn mismatch() {}\n",
    );
    publication_command()
        .arg("source-name-mismatch.rs")
        .arg("-o")
        .arg("source-name-mismatch.rmeta")
        .run_fail()
        .assert_stderr_contains("required to match");
    assert_no_current_artifacts("source crate-name disagreement");

    publish_current(11);
    rfs::write("injected-name-mismatch.rs", "pub fn mismatch() {}\n");
    publication_command()
        .arg("-Zcrate-attr=crate_name=\"different_name\"")
        .arg("injected-name-mismatch.rs")
        .arg("-o")
        .arg("injected-name-mismatch.rmeta")
        .run_fail()
        .assert_stderr_contains("required to match");
    assert_no_current_artifacts("injected crate-name disagreement");

    publish_current(11);
    rfs::write("malformed-injected-attr.rs", "pub fn never_checked() {}\n");
    publication_command()
        .arg(format!("-Zcrate-attr=crate_name=\"{CRATE_NAME}\""))
        .arg("-Zcrate-attr=allow=")
        .arg("malformed-injected-attr.rs")
        .arg("-o")
        .arg("malformed-injected-attr.rmeta")
        .run_fail();
    assert_no_current_artifacts("malformed injected attribute");

    for (label, source) in [
        ("type", "pub fn type_error() { let _: u8 = \"not a byte\"; }\n"),
        (
            "borrow",
            "pub fn borrow_error() { let mut x = 0_u8; let a = &mut x; \
             let b = &mut x; *a += *b; }\n",
        ),
    ] {
        publish_current(11);
        rfs::write("semantic-failure.rs", source);
        publication_command()
            .arg("semantic-failure.rs")
            .arg("-o")
            .arg(format!("{label}-failure.rmeta"))
            .run_fail();
        assert_no_current_artifacts(&format!("{label}-checking failure"));
    }
}
