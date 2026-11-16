use super::*;
use crate::common::trust_verification_isolation_tests::trust_lane_config_from;

// Trust: all fixtures belong to this test, never an existing compiler cache.
struct SupportLayoutFixture(Utf8PathBuf);

impl SupportLayoutFixture {
    fn new() -> Self {
        let root = Utf8PathBuf::try_from(env::temp_dir().join(format!(
            "compiletest-support-layout-{}-{}",
            std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
        )))
        .unwrap();
        fs::create_dir_all(&root).unwrap();
        Self(root)
    }

    fn directory(&self, relative: &str) -> Utf8PathBuf {
        let path = self.0.join(relative);
        fs::create_dir_all(&path).unwrap();
        path
    }
}

impl Drop for SupportLayoutFixture {
    fn drop(&mut self) {
        ignore_not_found(|| recursive_remove(&self.0)).unwrap();
    }
}

#[test]
fn run_make_support_paths_follow_the_supplied_cache_and_profile() {
    for domain in ["bootstrap-tools", "bootstrap-seed-tools", "custom-producer"] {
        for profile in ["release", "debug"] {
            let root = Utf8Path::new("build/build-host").join(domain);
            let qualified = root.join("recipe-host").join(profile);
            let rlib = qualified.join("librun_make_support.rlib");
            let rmeta = qualified.join("deps/librun_make_support-123.rmeta");
            assert_eq!(
                run_make_support_dependency_dirs(&rlib, Some(&rmeta), "recipe-host").unwrap(),
                vec![
                    qualified.join("deps").into_std_path_buf(),
                    root.join(profile).join("deps").into_std_path_buf(),
                ],
            );
            let legacy_rlib = qualified.join("deps/librun_make_support-123.rlib");
            assert_eq!(run_make_support_profile_dir(&legacy_rlib, "rlib").unwrap(), qualified,);
        }
    }
}

#[test]
fn run_make_support_paths_accept_uplifted_rlib_and_build_unit_rmeta() {
    let profile = Utf8Path::new("producer/recipe-host/debug");
    let rlib = profile.join("librun_make_support.rlib");
    let rmeta = profile.join("build/run-make-support/123/out/librun_make_support-123.rmeta");
    assert_eq!(run_make_support_profile_dir(&rmeta, "rmeta").unwrap(), profile);
    assert_eq!(
        run_make_support_dependency_dirs(&rlib, Some(&rmeta), "recipe-host").unwrap(),
        vec![profile.join("deps").into_std_path_buf(), PathBuf::from("producer/debug/deps"),],
    );
    let unit_rlib = rmeta.with_extension("rlib");
    assert_eq!(run_make_support_profile_dir(&unit_rlib, "rlib").unwrap(), profile);
}

#[test]
fn run_make_support_paths_reject_mixed_producer_closures() {
    let rlib = Utf8Path::new("seed/recipe-host/release/librun_make_support.rlib");
    for other in [
        "current/recipe-host/release/deps/librun_make_support-123.rmeta",
        "seed/recipe-host/debug/deps/librun_make_support-123.rmeta",
        "seed/other-host/release/build/run-make-support/123/out/librun_make_support-123.rmeta",
    ] {
        let error =
            run_make_support_dependency_dirs(rlib, Some(Utf8Path::new(other)), "recipe-host")
                .unwrap_err();
        assert!(error.contains("different Cargo producer profiles"), "{error}");
    }
    let rlib = Utf8Path::new("seed/recipe-host/release/deps/librun_make_support-123.rlib");
    let rmeta = Utf8Path::new("seed/recipe-host/release/deps/librun_make_support-456.rmeta");
    let error = run_make_support_dependency_dirs(rlib, Some(rmeta), "recipe-host").unwrap_err();
    assert!(error.contains("different Cargo artifact hashes"), "{error}");
}

#[test]
fn run_make_support_paths_keep_an_unqualified_producer_unqualified() {
    let rlib = Utf8Path::new("producer/release/deps/librun_make_support-123.rlib");
    assert_eq!(
        run_make_support_dependency_dirs(rlib, None, "recipe-host").unwrap(),
        vec![PathBuf::from("producer/release/deps")],
    );
}

#[test]
fn run_make_support_paths_include_both_build_layouts_and_only_the_selected_host() {
    let fixture = SupportLayoutFixture::new();
    let profile = fixture.directory("seed/recipe-host/debug");
    let legacy = fixture.directory("seed/recipe-host/debug/build/native-123/out");
    let unit = fixture.directory("seed/recipe-host/debug/build/rust-dep/456/out");
    let host = fixture.directory("seed/debug/build/proc-macro/789/out");
    fixture.directory("current/recipe-host/debug/build/foreign-123/out");
    fixture.directory("seed/other-target/debug/build/foreign-456/out");
    fixture.directory("seed/recipe-host/debug/build/native-123/out/nested/out");
    let rlib = profile.join("librun_make_support.rlib");
    let rmeta = profile.join("build/run-make-support/abc/out/librun_make_support-abc.rmeta");
    let paths = run_make_support_dependency_dirs(&rlib, Some(&rmeta), "recipe-host").unwrap();
    assert_eq!(
        paths,
        vec![
            profile.join("deps").into_std_path_buf(),
            fixture.0.join("seed/debug/deps").into_std_path_buf(),
            legacy.into_std_path_buf(),
            unit.into_std_path_buf(),
            host.into_std_path_buf(),
        ],
    );
}

#[test]
fn run_make_support_paths_disclose_unreadable_build_tree() {
    let fixture = SupportLayoutFixture::new();
    let profile = fixture.directory("producer/recipe-host/release");
    fs::write(profile.join("build"), b"not a directory").unwrap();
    let error = run_make_support_dependency_dirs(
        &profile.join("librun_make_support.rlib"),
        None,
        "recipe-host",
    )
    .unwrap_err();
    assert!(error.contains("could not read support producer directory"), "{error}");
}

// Trust: a loop gives a real non-NotFound metadata error even under a root
// test runner, unlike a chmod-based permission fixture.
#[cfg(unix)]
#[test]
fn run_make_support_paths_propagate_output_metadata_errors() {
    use std::os::unix::fs::symlink;

    for layout in ["native-123/out", "native/123/out"] {
        let fixture = SupportLayoutFixture::new();
        let build = fixture.directory("producer/recipe-host/release/build");
        let out = build.join(layout);
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        symlink("out", &out).unwrap();
        let error = discover_out_dirs(build.as_std_path()).unwrap_err();
        assert_eq!(error.raw_os_error(), Some(libc::ELOOP), "{layout}: {error}");
        let error = run_make_support_dependency_dirs(
            &fixture.0.join("producer/recipe-host/release/librun_make_support.rlib"),
            None,
            "recipe-host",
        )
        .unwrap_err();
        assert!(error.contains("could not read support producer directory"), "{error}");
    }
}

#[test]
fn run_make_support_paths_allow_absent_and_non_directory_outputs() {
    let fixture = SupportLayoutFixture::new();
    let build = fixture.directory("producer/recipe-host/release/build");
    for layout in ["absent-123", "absent/123", "file-123", "file/123"] {
        let unit = build.join(layout);
        fs::create_dir_all(&unit).unwrap();
        if layout.starts_with("file") {
            fs::write(unit.join("out"), b"a non-output file").unwrap();
        }
    }
    assert!(discover_out_dirs(build.as_std_path()).unwrap().is_empty());
    assert_eq!(
        run_make_support_dependency_dirs(
            &fixture.0.join("producer/recipe-host/release/librun_make_support.rlib"),
            None,
            "recipe-host",
        )
        .unwrap(),
        vec![
            fixture.0.join("producer/recipe-host/release/deps").into_std_path_buf(),
            fixture.0.join("producer/release/deps").into_std_path_buf(),
        ],
    );
}

#[test]
fn run_make_support_paths_reject_invalid_support_artifact_shapes() {
    for path in [
        "producer/debug/libanother_crate.rlib",
        "producer/debug/librun_make_support.rmeta",
        "producer/debug/librun_make_support-.rlib",
        "producer/debug/build/incomplete/out/librun_make_support.rlib",
        "librun_make_support.rlib",
    ] {
        assert!(run_make_support_profile_dir(Utf8Path::new(path), "rlib").is_err(), "{path}");
    }
}

#[test]
fn trust_off_wrapper_passes_real_rustc_and_flag() {
    let script = trust_off_rustc_wrapper_script();
    assert!(script.contains(TRUST_OFF_REAL_RUSTC_ENV));
    assert!(script.contains(TRUST_VANILLA_RUSTC_FLAG));
    assert!(
        script.contains("if [ \"$#\" -eq 0 ]") || script.contains("if \"%~1\"==\"\""),
        "wrapper must preserve zero-argument compiler behavior"
    );
    assert!(!script.contains("RUSTC_BOOTSTRAP"));
    // The transport is not the vanilla lane's signal: `version-check` reads
    // that signal to relax its identity assertion, which must stay strict on
    // the default lane.
    assert!(!script.contains(TRUST_VANILLA_REAL_RUSTC_ENV));
}

#[test]
fn trust_off_wrapper_path_is_under_run_make_output() {
    let base_dir = Utf8Path::new("run-make-output");
    let wrapper = trust_off_rustc_wrapper_path(base_dir);
    assert!(wrapper.starts_with(base_dir));
    // `rustc_interface::util::rustc_path` recognises exactly this name.
    assert_eq!(
        wrapper.file_name(),
        Some(if cfg!(windows) { "rustc-trust-vanilla.cmd" } else { "rustc-trust-vanilla" })
    );
}

#[test]
fn writes_trust_off_wrapper() {
    let base_dir = Utf8PathBuf::try_from(env::temp_dir().join(format!(
        "compiletest-trust-off-wrapper-{}-{}",
        std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    )))
    .unwrap();

    ignore_not_found(|| recursive_remove(&base_dir)).unwrap();
    fs::create_dir_all(&base_dir).unwrap();

    let wrapper = write_trust_off_rustc_wrapper(&base_dir);
    assert_eq!(fs::read_to_string(&wrapper).unwrap(), trust_off_rustc_wrapper_script());

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        assert_ne!(fs::metadata(&wrapper).unwrap().permissions().mode() & 0o111, 0);
    }

    ignore_not_found(|| recursive_remove(&base_dir)).unwrap();
}

fn run_make_test(relative_dir: &str, name: &str) -> TestPaths {
    let relative_dir = Utf8PathBuf::from(relative_dir);
    let file = Utf8Path::new("/src/tests/run-make").join(&relative_dir).join(name);
    TestPaths { file, relative_dir }
}

#[test]
fn trust_run_make_tests_are_the_top_level_trust_directories() {
    assert!(is_trust_run_make_test(&run_make_test("", "trust-slice-unit")));
    assert!(is_trust_run_make_test(&run_make_test("", "trustc-version-compat")));
    assert!(is_trust_run_make_test(&run_make_test("trust-group", "case")));
    assert!(!is_trust_run_make_test(&run_make_test("", "bin-emit-no-symbols")));
    assert!(!is_trust_run_make_test(&run_make_test("", "version-check")));
    assert!(!is_trust_run_make_test(&run_make_test("autodiff/type-trees", "iter")));
    // Only the top-level directory decides.
    assert!(!is_trust_run_make_test(&run_make_test("autodiff", "trust-like")));
}

/// Argv in, recipe `RUSTC` out, through a real `Config`.
#[test]
fn default_lane_isolates_inherited_recipes_and_only_them() {
    let upstream = run_make_test("", "bin-emit-no-symbols");
    let inventory = run_make_test("", "tool-inputs-dlltool-boundary");
    let trust = run_make_test("", "trust-slice-unit");

    // Default lane: inherited recipes are isolated; Trust's own keep the real
    // driver, exactly as before.
    let default_lane = trust_lane_config_from(&["--rustc-supports-trust-verification"]);
    assert_eq!(recipe_rustc(&default_lane, &upstream), RecipeRustc::Isolated);
    assert_eq!(recipe_rustc(&default_lane, &inventory), RecipeRustc::Isolated);
    assert_eq!(recipe_rustc(&default_lane, &trust), RecipeRustc::Real);

    // Vanilla lane: unchanged, every recipe (Trust's own self-skip on the signal).
    let vanilla =
        trust_lane_config_from(&["--rustc-supports-trust-verification", "--trust-vanilla"]);
    assert_eq!(recipe_rustc(&vanilla, &upstream), RecipeRustc::Vanilla);
    assert_eq!(recipe_rustc(&vanilla, &trust), RecipeRustc::Vanilla);

    // Verified lane: untouched -- the real driver at its shipping default.
    let verified =
        trust_lane_config_from(&["--rustc-supports-trust-verification", "--trust-verified"]);
    assert_eq!(recipe_rustc(&verified, &upstream), RecipeRustc::Real);
    assert_eq!(recipe_rustc(&verified, &trust), RecipeRustc::Real);

    // A driver without the verifier must never see a `-Ztrust-*` flag.
    let unsupported = trust_lane_config_from(&[]);
    assert_eq!(recipe_rustc(&unsupported, &upstream), RecipeRustc::Real);
    assert_eq!(recipe_rustc(&unsupported, &trust), RecipeRustc::Real);
}

/// Verifier-dependent recipes must keep the real driver. Tool-input inventory
/// is independent of verification and remains legal in isolated recipes.
#[test]
fn run_make_recipes_stating_trust_flags_are_trust_owned() {
    let tests_root = Utf8Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests");
    let mut trust_flagged = 0;
    let mut misclassified = Vec::new();
    for suite in ["run-make", "run-make-cargo", "build-std"] {
        let suite_root = tests_root.join(suite);
        for entry in walkdir::WalkDir::new(&suite_root).sort_by_file_name() {
            let entry = entry.unwrap_or_else(|error| panic!("walking {suite_root}: {error}"));
            if entry.file_name() != "rmake.rs" {
                continue;
            }
            let recipe = Utf8Path::from_path(entry.path()).unwrap();
            let text = fs::read_to_string(recipe).unwrap();
            let verification_text = text.replace("\"-Ztrust-tool-inputs\"", "");
            if !(verification_text.contains("-Ztrust")
                || verification_text.contains("trust-verify="))
            {
                continue;
            }
            trust_flagged += 1;
            let file = recipe.parent().unwrap().to_owned();
            let relative_dir = file.parent().unwrap().strip_prefix(&suite_root).unwrap().to_owned();
            if !is_trust_run_make_test(&TestPaths { file, relative_dir }) {
                misclassified.push(recipe.to_string());
            }
        }
    }
    assert!(trust_flagged > 0, "no Trust-flagged recipe found under {tests_root}");
    assert!(
        misclassified.is_empty(),
        "recipes stating Trust flags outside a top-level `trust*` directory:\n{misclassified:#?}"
    );
}

// Trust: retain TG10's artifact-domain cases against the stronger shared
// implementation, including cache roots containing spaces and real triples.
#[test]
fn support_profiles_follow_the_selected_artifact_domain() {
    for domain in ["bootstrap-seed-tools", "bootstrap-tools", "arbitrary cache root"] {
        let root = Utf8Path::new("/owned/output").join(domain);
        let target = root.join("aarch64-apple-darwin/release");
        let artifact = target.join("librun_make_support.rlib");
        assert_eq!(run_make_support_profile_dir(&artifact, "rlib").unwrap(), target);
        assert_eq!(
            run_make_support_dependency_dirs(&artifact, None, "aarch64-apple-darwin").unwrap(),
            vec![
                target.join("deps").into_std_path_buf(),
                root.join("release/deps").into_std_path_buf()
            ],
        );
    }
}

#[test]
fn support_profiles_accept_a_hashed_dependency_artifact() {
    let artifact = Utf8Path::new(
        "/owned/seed/x86_64-unknown-linux-gnu/debug/deps/librun_make_support-abcd.rlib",
    );
    assert_eq!(
        run_make_support_dependency_dirs(artifact, None, "x86_64-unknown-linux-gnu").unwrap(),
        vec![
            PathBuf::from("/owned/seed/x86_64-unknown-linux-gnu/debug/deps"),
            PathBuf::from("/owned/seed/debug/deps")
        ],
    );
}

#[test]
fn support_profiles_keep_untargeted_native_artifacts_in_their_profile() {
    let profile = Utf8PathBuf::from("/owned/seed/debug");
    assert_eq!(
        run_make_support_dependency_dirs(
            &profile.join("librun_make_support.rlib"),
            None,
            "aarch64-apple-darwin"
        )
        .unwrap(),
        vec![profile.join("deps").into_std_path_buf()],
    );
}
