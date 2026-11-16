// Copyright 2026 Andrew Yates
// DATA controls and explicit real NONE observations, not LLVM/provider readiness.
use super::*;

#[test]
fn source_recipe_data_requires_exact_request_mode_and_known_completion() {
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("source");
    let output = temp.path().join("owned/llvm");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("input"), b"unchanged source").unwrap();
    let owner = OwnSourceGeneration {
        source: source.clone(),
        anchor: temp.path().to_owned(),
        output: output.clone(),
        observed: observe_cmake_sources(&source, &output).unwrap(),
    };
    // These are explicitly synthetic request DATA. No Prepared/provider object
    // is forged and no inference about selected tools follows from these keys.
    let base =
        SourceRecipeKey { request: "a".repeat(64), dependency: "none".into(), link_shared: false };
    let stamp = owner.stamp("llvm", "fixture-target", Some(&base));
    begin_cmake_miss(&stamp, CmakeGeneration::Known).unwrap();
    let artifact = output.join("llvm-config");
    fs::write(&artifact, b"fixture output").unwrap();
    fixture_install_manifest(&output, &[&artifact]);
    assert!(owner.complete(&stamp, || true).unwrap());
    assert!(owner.cache_matches("llvm", &stamp, &artifact));
    for key in [
        SourceRecipeKey { request: "b".repeat(64), ..base.clone() },
        SourceRecipeKey { link_shared: true, ..base.clone() },
        SourceRecipeKey { dependency: "c".repeat(64), ..base.clone() },
    ] {
        let changed = owner.stamp("llvm", "fixture-target", Some(&key));
        assert_ne!(stamp.stamp(), changed.stamp());
        assert!(!owner.cache_matches("llvm", &changed, &artifact));
    }
    let unknown = owner.stamp("llvm", "fixture-target", None);
    assert!(!owner.cache_matches("llvm", &unknown, &artifact));
    stamp.remove().unwrap();
    assert!(!owner.complete(&unknown, || true).unwrap());
    assert!(!stamp.path().exists(), "unknown recipe cannot publish completion");
}

#[cfg(unix)]
fn resolved_host_recipe(
    session: &crate::core::session::Session,
    source: &Path,
    output: &Path,
    shared: bool,
    adjust: impl FnOnce(&mut cmake::Config),
) -> ResolvedSourceRecipe {
    let builder = Builder::new(session);
    let target = builder.host_target;
    assert!(
        builder.config.is_host_target(target),
        "no cross-provider construction in this fixture"
    );
    let native = target.to_string();
    let LlvmCmakeConfig { mut config, postprocess_version_suffix } = llvm_cmake_config(
        &builder,
        target,
        LlvmCmakeRequest { source, output, target_native: &native, link_shared: shared },
    );
    config.build_target("install");
    adjust(&mut config);
    ResolvedSourceRecipe::from_config(config, postprocess_version_suffix, Vec::new(), shared)
        .unwrap()
}

#[cfg(unix)]
#[test]
#[ignore = "requires owned CMake lane without ambient CC/CXX/CFLAGS/CXXFLAGS selectors; x.py injects opaque selectors"]
fn real_fixed_source_recipe_changes_reset_and_apply_the_same_prepared_request() {
    use crate::core::session::Session;
    use crate::utils::tests::TestCtx;
    let ctx = TestCtx::new();
    let evidence = tempfile::Builder::new()
        .prefix("llvm-recipe-guard-")
        .suffix(".noindex")
        .tempdir()
        .unwrap()
        .keep();
    println!("retained LLVM recipe guard evidence: {}", evidence.display());
    let source = evidence.join("source");
    let output = evidence.join("output");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("CMakeLists.txt"), r#"cmake_minimum_required(VERSION 3.20)
project(RecipeGuard NONE)
file(WRITE "${CMAKE_BINARY_DIR}/configured.txt"
 "assertions=${LLVM_ENABLE_ASSERTIONS}\nlinking=${LLVM_LINK_LLVM_DYLIB}\nbuild-dylib=${LLVM_BUILD_LLVM_DYLIB}\nprofile=${CMAKE_BUILD_TYPE}\ncompile-jobs=${LLVM_PARALLEL_COMPILE_JOBS}\nforce=${LLVM_FORCE_VC_REVISION}\n")
add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/payload.txt"
 COMMAND "${CMAKE_COMMAND}" -E copy "${CMAKE_BINARY_DIR}/configured.txt" "${CMAKE_BINARY_DIR}/payload.txt"
 DEPENDS "${CMAKE_BINARY_DIR}/configured.txt" VERBATIM)
add_custom_target(observe ALL DEPENDS "${CMAKE_BINARY_DIR}/payload.txt")
install(FILES "${CMAKE_BINARY_DIR}/payload.txt" DESTINATION lib)
"#).unwrap();
    let mut config = ctx
        .config("build")
        .stage(1)
        .path("library/std")
        .args(&["--set", "rust.trust-source-identity=false"])
        .create_config_with_fixed_budget(Some(1));
    config.set_dry_run(crate::core::config::DryRun::Disabled);
    config.ninja_in_file = true;
    config.llvm_optimize = true;
    config.llvm_release_debuginfo = false;
    config.llvm_assertions = false;
    assert_eq!(
        crate::utils::trust_preparation::PreparationScope::for_config(&config),
        crate::utils::trust_preparation::PreparationScope::RequestSources
    );
    let mut session = Session::new(config);
    // x.py's Cargo producer injects target-qualified CC/CXX and flags even for
    // its own tests. The unchanged conservative cleanup judge correctly treats
    // those consumed operands as opaque. This positive NONE observation needs
    // the maintained direct owning lane, not an ambient selector waiver.
    assert!(
        session.opaque_cc_operands.is_empty(),
        "positive CMake observation requires the direct owning lane; ambient compiler selectors intentionally refuse cleanup"
    );
    let target = session.config.host_target.to_string();
    let digest = observe_cmake_sources(&source, &output).unwrap().unwrap();

    // These resolutions are metadata-only. The larger scheduling value never
    // reaches build(); only the admitted one-credit recipe below is executed.
    assert_eq!(session.jobs(), 1);
    let one = resolved_host_recipe(&session, &source, &output, false, |_| {});
    session.config.jobs = Some(2);
    assert_eq!(session.jobs(), 2);
    let many = resolved_host_recipe(&session, &source, &output, false, |_| {});
    session.config.jobs = Some(1);
    assert_eq!(
        one.key.as_ref().unwrap().request,
        many.key.as_ref().unwrap().request,
        "scheduling-only definitions must not invalidate artifact identity"
    );
    let base = one.key.as_ref().unwrap().request.clone();
    let old_link_jobs = session.config.llvm_link_jobs;
    session.config.llvm_link_jobs = Some(2);
    let link_budget = resolved_host_recipe(&session, &source, &output, false, |_| {});
    assert_eq!(base, link_budget.key.as_ref().unwrap().request);
    drop(link_budget);
    session.config.llvm_link_jobs = old_link_jobs;
    drop(many);
    drop(one);
    for (name, recipe) in [
        (
            "profile",
            resolved_host_recipe(&session, &source, &output, false, |cfg| {
                cfg.profile("Debug");
            }),
        ),
        (
            "FORCE",
            resolved_host_recipe(&session, &source, &output, false, |cfg| {
                cfg.define("LLVM_FORCE_VC_REVISION", "explicit-request");
            }),
        ),
        (
            "user-last",
            resolved_host_recipe(&session, &source, &output, false, |cfg| {
                cfg.define("LLVM_ENABLE_ASSERTIONS", "ON");
            }),
        ),
    ] {
        assert_ne!(
            base,
            recipe.key.as_ref().unwrap().request,
            "independent request change: {name}"
        );
    }
    // Exercise the actual LLD constructor's recipe with the same NONE project,
    // without inventing an LLVM provider/Ready object or executing an LLD build.
    // The exports path is input DATA and is never loaded by that project.
    let selected_exports = evidence.join("unexecuted LLVM exports data");
    fs::create_dir(&selected_exports).unwrap();
    let selected_exports = selected_exports.canonicalize().unwrap();
    let lld_output = evidence.join("lld-output");
    let lld_request = |session: &Session| {
        let builder = Builder::new(session);
        let config = lld_cmake_config(
            &builder,
            builder.host_target,
            LldCmakeRequest {
                source: &source,
                output: &lld_output,
                llvm_cmake: &selected_exports,
                link_shared: false,
                host_tablegen: None,
            },
        )
        .unwrap();
        ResolvedSourceRecipe::from_config(config, None, Vec::new(), false).unwrap()
    };
    let lld_base = lld_request(&session).key.unwrap().request;
    session.config.llvm_optimize = false;
    assert_ne!(lld_base, lld_request(&session).key.unwrap().request);
    session.config.llvm_optimize = true;
    session.config.llvm_cflags = Some("-DLLD_REQUEST_ONLY=1".into());
    assert_ne!(lld_base, lld_request(&session).key.unwrap().request);
    session.config.llvm_cflags = None;

    // Execute that SAME prepared LLD constructor recipe, still only on NONE.
    // Actual cache spelling must satisfy the unchanged strict provider reader;
    // this observation establishes no LLVM/provider or LLD readiness.
    let recipe = lld_request(&session);
    let key = recipe.key.as_ref().expect("actual native LLD fixture recipe must be reusable");
    let lld_owner = OwnSourceGeneration {
        source: source.clone(),
        anchor: evidence.clone(),
        output: lld_output.clone(),
        observed: Some(digest.clone()),
    };
    let stamp = lld_owner.stamp("lld", &target, Some(key));
    // NONE loads no LLVM provider: a known LLD dependency is deliberately absent.
    // Preserve the real known-generation refusal, then execute the ordinary
    // fresh unknown-generation path without publishing readiness or completion.
    assert_eq!(key.dependency, "none");
    assert!(lld_owner.begin(&stamp, &recipe.prepared, CmakeGeneration::Known, &[]).is_err());
    lld_owner.begin(&stamp, &recipe.prepared, CmakeGeneration::Unknown, &[]).unwrap();
    assert!(!lld_cached_provider(&lld_output, &selected_exports));
    recipe.prepared.build();
    let cache = fs::read_to_string(lld_output.join("build/CMakeCache.txt")).unwrap();
    let provider = format!("LLVM_DIR:PATH={}", selected_exports.display());
    assert!(cache.lines().any(|line| line == provider), "typed provider absent from actual cache");
    assert!(lld_cached_provider(&lld_output, &selected_exports));

    // A successful but opaque preparation is not replaced by raw Config.build.
    // The real selected commands exist, but this request has no reusable key or
    // admitted cleanup namespace; both forms of begin must preserve old files.
    let opaque = resolved_host_recipe(&session, &source, &output, false, |config| {
        config.configure_arg("-DOPAQUE_CONTROL=1");
    });
    assert!(opaque.prepared.cache_inputs().is_none());
    assert!(opaque.key.is_none());
    let owner = OwnSourceGeneration {
        source: source.clone(),
        anchor: evidence.clone(),
        output: output.clone(),
        observed: Some(digest.clone()),
    };
    let unknown = owner.stamp("llvm", &target, None);
    fs::create_dir_all(&output).unwrap();
    let sentinel = output.join("keep-before-admission");
    fs::write(&sentinel, b"untouched").unwrap();
    fs::write(unknown.path(), b"existing completion control").unwrap();
    for generation in [CmakeGeneration::Known, CmakeGeneration::Unknown] {
        assert!(owner.begin(&unknown, &opaque.prepared, generation, &[]).is_err());
        assert_eq!(fs::read(&sentinel).unwrap(), b"untouched");
        assert_eq!(fs::read(unknown.path()).unwrap(), b"existing completion control");
    }
    drop(opaque);

    let mut previous_request = None;
    let mut previous_stamp: Option<BuildStamp> = None;
    for (assertions, shared) in [(false, false), (true, false), (true, true)] {
        session.config.llvm_assertions = assertions;
        let recipe = resolved_host_recipe(&session, &source, &output, shared, |_| {});
        let key = recipe.key.as_ref().expect("actual native recipe must be reusable");
        assert_eq!(
            observe_cmake_sources(&source, &output).unwrap().as_deref(),
            Some(digest.as_str())
        );
        if let Some(previous) = &previous_request {
            assert_ne!(previous, &key.request);
        }
        let owner = OwnSourceGeneration {
            source: source.clone(),
            anchor: evidence.clone(),
            output: output.clone(),
            observed: Some(digest.clone()),
        };
        let stamp = owner.stamp("llvm", &target, Some(key));
        let payload = output.join("build/payload.txt");
        if let Some(previous) = &previous_stamp {
            assert!(
                previous.is_up_to_date(),
                "the earlier completion remains present before lookup"
            );
            assert!(!owner.cache_matches("llvm", &stamp, &payload));
        }
        let request = key.request.clone();
        owner.begin(&stamp, &recipe.prepared, CmakeGeneration::Known, &[]).unwrap();
        assert!(!payload.exists(), "a changed request resets the retained output generation");
        recipe.prepared.build();
        let actual = fs::read_to_string(&payload).unwrap();
        let boolean = |value| if value { "ON" } else { "OFF" };
        assert!(actual.contains(&format!("assertions={}\n", boolean(assertions))), "{actual}");
        assert!(actual.contains(&format!("linking={}\n", boolean(shared))), "{actual}");
        assert!(actual.contains(&format!("build-dylib={}\n", boolean(shared))), "{actual}");
        assert!(actual.contains("profile=Release\n"), "{actual}");
        assert!(actual.contains("compile-jobs=1\n"), "{actual}");
        assert!(owner.complete(&stamp, || true).unwrap());
        assert!(owner.cache_matches("llvm", &stamp, &payload));
        assert_eq!(
            observe_cmake_sources(&source, &output).unwrap().as_deref(),
            Some(digest.as_str())
        );
        println!("recipe guard applied assertions={assertions} shared={shared}: {actual}");
        previous_request = Some(request);
        previous_stamp = Some(stamp);
    }
}

#[test]
fn cross_lookup_does_not_acquire_or_construct_a_ci_host_provider() {
    let ctx = crate::utils::tests::TestCtx::new();
    let mut session =
        crate::core::session::Session::new(ctx.config("build").stage(1).create_config());
    // Ordinary initialization is complete before selecting controlled filesystem
    // inputs. The real lookup resolves no compiler command while HOST is unknown.
    session.config.src = ctx.dir().join("fixture-source");
    session.config.out = ctx.dir().join("unmaterialized-output");
    let source = session.config.src.join("src/llvm-project");
    fs::create_dir_all(&source).unwrap();
    fs::write(source.join("input"), b"fixed source fixture").unwrap();
    session.config.set_dry_run(crate::core::config::DryRun::Disabled);
    session.config.llvm_ci_mode = LlvmCiMode::Download;
    let host = session.config.host_target;
    if let Some(config) = session.config.target_config.get_mut(&host) {
        config.llvm_config = None;
    }
    let target = TargetSelection::from_user(if &*host.triple == "x86_64-unknown-linux-gnu" {
        "aarch64-unknown-linux-gnu"
    } else {
        "x86_64-unknown-linux-gnu"
    });
    assert_ne!(target, host);
    let builder = Builder::new(&session);
    let before = builder.step_cache().executed_steps().len();
    let LlvmBuildStatus::ShouldBuild(info) = get_locally_built_llvm_build_status(&builder, target)
    else {
        panic!("unknown HOST cannot authorize a target cache hit");
    };
    assert!(matches!(info.recipe, SourceRecipeResolution::UnresolvedCross));
    assert!(info.source_generation.observed.is_some());
    assert_eq!(before, builder.step_cache().executed_steps().len());
    assert!(builder.step_cache().get(&LlvmFromCi { target: host }).is_none());
    assert!(builder.step_cache().get(&Llvm { target: host }).is_none());
    assert!(!session.config.out.exists(), "lookup cannot materialize output");
    assert_eq!(fs::read(source.join("input")).unwrap(), b"fixed source fixture");
}
