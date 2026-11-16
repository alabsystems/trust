// Copyright 2026 Andrew Yates
// Selected namespace DATA and real generated-header plumbing, not SDK identity.
use super::*;

#[test]
fn build_cache_namespace_data_binds_source_target_recipe_and_link_mode() {
    let temp = tempfile::tempdir().unwrap();
    let owner = OwnSourceGeneration {
        source: temp.path().join("source"),
        anchor: temp.path().to_owned(),
        output: temp.path().join("output"),
        observed: Some("a".repeat(64)),
    };
    let key =
        SourceRecipeKey { request: "b".repeat(64), dependency: "none".into(), link_shared: false };
    let first = LlvmBuildCacheIdentity::derive(&owner, "fixture-target", Some(&key));
    let same = LlvmBuildCacheIdentity::derive(&owner, "fixture-target", Some(&key));
    assert_eq!(first.bytes, same.bytes);
    assert!(String::from_utf8(first.bytes.clone()).unwrap().contains("\nknown "));
    for changed in [
        SourceRecipeKey { request: "c".repeat(64), ..key.clone() },
        SourceRecipeKey { dependency: "d".repeat(64), ..key.clone() },
        SourceRecipeKey { link_shared: true, ..key.clone() },
    ] {
        assert_ne!(
            first.bytes,
            LlvmBuildCacheIdentity::derive(&owner, "fixture-target", Some(&changed)).bytes
        );
    }
    assert_ne!(
        first.bytes,
        LlvmBuildCacheIdentity::derive(&owner, "other-target", Some(&key)).bytes
    );
    assert_eq!(
        LlvmBuildCacheIdentity::derive(&owner, "fixture-target", None).bytes,
        b"trust.llvm-build-cache-namespace/v1\nunknown\n"
    );
    let malformed_key = SourceRecipeKey { request: "malformed".into(), ..key.clone() };
    assert_eq!(
        LlvmBuildCacheIdentity::derive(&owner, "fixture-target", Some(&malformed_key)).bytes,
        b"trust.llvm-build-cache-namespace/v1\nunknown\n"
    );
    let mut changed_owner = OwnSourceGeneration { observed: Some("e".repeat(64)), ..owner };
    assert_ne!(
        first.bytes,
        LlvmBuildCacheIdentity::derive(&changed_owner, "fixture-target", Some(&key)).bytes
    );
    changed_owner.observed = None;
    for unknown in [
        LlvmBuildCacheIdentity::derive(&changed_owner, "fixture-target", Some(&key)),
        LlvmBuildCacheIdentity::derive(&changed_owner, "fixture-target", None),
    ] {
        assert_eq!(unknown.bytes, b"trust.llvm-build-cache-namespace/v1\nunknown\n");
    }
    fs::create_dir(&changed_owner.output).unwrap();
    first.write().unwrap();
    assert!(first.matches());
    fs::write(&first.path, b"malformed namespace").unwrap();
    assert!(!first.matches());
    first.write().unwrap();
    assert!(first.matches());
    fs::remove_file(&first.path).unwrap();
    fs::create_dir(&first.path).unwrap();
    assert!(first.write().is_err());
    assert!(first.path.is_dir());
    #[cfg(unix)]
    {
        fs::remove_dir(&first.path).unwrap();
        let outside = temp.path().join("outside-record");
        fs::write(&outside, b"outside sentinel").unwrap();
        std::os::unix::fs::symlink(&outside, &first.path).unwrap();
        assert!(first.write().is_err());
        assert_eq!(fs::read(&outside).unwrap(), b"outside sentinel");
        assert!(!first.matches());
    }
}

#[cfg(unix)]
#[test]
#[ignore = "run only under maintained owned-process CMake qualification lane"]
fn real_none_build_tracks_namespace_file_without_explicit_reconfiguration() {
    use crate::core::session::Session;
    use crate::utils::tests::TestCtx;
    let ctx = TestCtx::new();
    let retained = tempfile::Builder::new()
        .prefix("llvm-build-namespace-")
        .suffix(".noindex")
        .tempdir()
        .unwrap()
        .keep();
    println!("retained namespace propagation evidence: {}", retained.display());
    let source = retained.join("source");
    let output = retained.join("output");
    fs::create_dir(&source).unwrap();
    fs::create_dir(&output).unwrap();
    let mut config = ctx
        .config("build")
        .stage(1)
        .path("library/std")
        .args(&["--set", "rust.trust-source-identity=false"])
        .create_config_with_fixed_budget(Some(1));
    assert_eq!(
        crate::utils::trust_preparation::PreparationScope::for_config(&config),
        crate::utils::trust_preparation::PreparationScope::RequestSources
    );
    config.set_dry_run(crate::core::config::DryRun::Disabled);
    let session = Session::new(config);
    let builder = Builder::new(&session);
    assert!(builder.config.is_host_target(builder.host_target));
    let helper = builder.src.join("src/llvm-project/llvm/cmake/modules/BuildCacheIdentity.cmake");
    fs::write(source.join("CMakeLists.txt"), format!(r#"cmake_minimum_required(VERSION 3.20)
project(BuildNamespace NONE)
include("{}")
llvm_configure_build_cache_identity("${{CMAKE_BINARY_DIR}}/BuildCacheIdentity.inc")
file(WRITE "${{CMAKE_BINARY_DIR}}/parent-scope.txt" "${{LLVM_BUILD_CACHE_IDENTITY_AVAILABLE}}\n${{LLVM_BUILD_CACHE_IDENTITY_VALUE}}\n")
add_custom_target(observe DEPENDS "${{CMAKE_BINARY_DIR}}/BuildCacheIdentity.inc")
"#, helper.display())).unwrap();
    // Explicit fixture namespace DATA. No source/provider readiness is inferred.
    let namespace_dir = retained.join("namespace;input space");
    fs::create_dir(&namespace_dir).unwrap();
    let mut owner = OwnSourceGeneration {
        source: source.clone(),
        anchor: retained.clone(),
        output: namespace_dir,
        observed: Some("a".repeat(64)),
    };
    let key =
        SourceRecipeKey { request: "b".repeat(64), dependency: "none".into(), link_shared: false };
    let first = LlvmBuildCacheIdentity::derive(&owner, &builder.host_target.triple, Some(&key));
    first.write().unwrap();
    let mut cfg = cmake::Config::new(&source);
    cfg.out_dir(&output)
        .profile("Release")
        .host(&builder.host_target.triple)
        .target(&builder.host_target.triple)
        .generator("Ninja")
        .define_input_program(
            "CMAKE_MAKE_PROGRAM",
            &[OsStr::new("ninja-build"), OsStr::new("ninja")],
        )
        .define_input_path("LLVM_BUILD_KEY_FILE", &first.path)
        .always_configure(false)
        .build_arg("-j")
        .build_arg("1")
        .build_target("observe");
    let generated = output.join("build/BuildCacheIdentity.inc");
    fs::remove_file(&first.path).unwrap();
    cfg.clone().try_prepare().unwrap().build();
    let missing = fs::read_to_string(&generated).unwrap();
    assert!(missing.contains("#define LLVM_BUILD_CACHE_IDENTITY_AVAILABLE 0"), "{missing}");
    assert_eq!(fs::read_to_string(output.join("build/parent-scope.txt")).unwrap(), "0\n\n");
    // The known-record byte count deliberately matches, so the real decoder
    // must reject the nonhex digest after its bounded read too.
    fs::write(
        &first.path,
        format!("trust.llvm-build-cache-namespace/v1\nknown {}\n", "g".repeat(64)),
    )
    .unwrap();
    // An input absent at initial configure has no dependency registration yet.
    // Reconfigure once with the actual malformed existing file; fixing it below
    // must then trigger Ninja's automatic CMake regeneration.
    cfg.clone().always_configure(true).try_prepare().unwrap().build();
    let malformed = fs::read_to_string(&generated).unwrap();
    assert!(malformed.contains("#define LLVM_BUILD_CACHE_IDENTITY_AVAILABLE 0"), "{malformed}");
    assert_eq!(fs::read_to_string(output.join("build/parent-scope.txt")).unwrap(), "0\n\n");
    let mut previous = Some(malformed);
    let mut prepared_request = None;
    for state in [Some("a".repeat(64)), Some("c".repeat(64)), None] {
        owner.observed = state;
        let prepared = cfg.clone().try_prepare().unwrap();
        let request = prepared.cache_inputs().expect("explicit native fixture request").to_vec();
        if let Some(before) = &prepared_request {
            assert_eq!(before, &request);
        }
        prepared_request = Some(request);
        // The path is frozen first. Derived contents change afterwards and the
        // exact same Prepared executes; they are not recursively hashed inputs.
        let identity =
            LlvmBuildCacheIdentity::derive(&owner, &builder.host_target.triple, Some(&key));
        identity.write().unwrap();
        prepared.build();
        let header = fs::read_to_string(&generated).unwrap();
        if let Some(before) = &previous {
            assert_ne!(before, &header);
        }
        let actual_record = fs::read(&identity.path).unwrap();
        let record = std::str::from_utf8(&actual_record).unwrap();
        if let Some(digest) = record
            .strip_prefix("trust.llvm-build-cache-namespace/v1\nknown ")
            .and_then(|s| s.strip_suffix('\n'))
        {
            assert!(header.contains("#define LLVM_BUILD_CACHE_IDENTITY_AVAILABLE 1"), "{header}");
            assert!(
                header.contains(&format!("trust.llvm-build-cache-namespace/v1:{digest}")),
                "{header}"
            );
            assert_eq!(
                fs::read_to_string(output.join("build/parent-scope.txt")).unwrap(),
                format!("1\ntrust.llvm-build-cache-namespace/v1:{digest}\n")
            );
        } else {
            assert!(header.contains("#define LLVM_BUILD_CACHE_IDENTITY_AVAILABLE 0"), "{header}");
            assert!(header.contains("#define LLVM_BUILD_CACHE_IDENTITY_VALUE \"\""), "{header}");
            assert_eq!(fs::read_to_string(output.join("build/parent-scope.txt")).unwrap(), "0\n\n");
        }
        println!("actual namespace header: {header}");
        previous = Some(header);
    }
}
