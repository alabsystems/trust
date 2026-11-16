// Copyright 2026 Andrew Yates
// This exercises the actual host recipe on a NONE project, not an LLVM build.
use super::*;
use crate::core::session::Session;
use crate::utils::tests::TestCtx;

fn host_recipe(
    session: &Session,
    source: &Path,
    output: &Path,
    link_shared: bool,
) -> cmake::Config {
    let builder = Builder::new(session);
    let target = builder.host_target;
    assert!(
        builder.config.is_host_target(target),
        "the fixture must not enter cross-host dependency construction"
    );
    let target_native = target.to_string();
    llvm_cmake_config(
        &builder,
        target,
        LlvmCmakeRequest { source, output, target_native: &target_native, link_shared },
    )
    .config
}

#[test]
#[ignore = "run only under maintained owned-process CMake qualification lane"]
fn real_host_llvm_recipe_applies_the_same_prepared_configuration() {
    let ctx = TestCtx::new();
    let evidence = tempfile::Builder::new()
        .prefix("llvm-recipe-")
        .suffix(".noindex")
        .tempdir()
        .unwrap()
        .keep();
    println!("retained LLVM recipe evidence: {}", evidence.display());
    let source = evidence.join("NONE source space");
    let output = evidence.join("NONE output space");
    fs::create_dir(&source).unwrap();
    let mut config = ctx
        .config("build")
        .stage(1)
        .path("library/std")
        .args(&["--set", "rust.trust-source-identity=false"])
        .create_config_with_fixed_budget(Some(1));
    config.set_dry_run(crate::core::config::DryRun::Disabled);
    config.ninja_in_file = true;
    config.rust_remap_debuginfo = false;
    config.llvm_optimize = true;
    config.llvm_release_debuginfo = false;
    config.llvm_assertions = true;
    config.llvm_cflags = Some("-DLLVM_RECIPE_C=1".into());
    config.llvm_cxxflags = Some("-DLLVM_RECIPE_CXX=2".into());
    config.llvm_ldflags = Some("-Wl,llvm-recipe-request".into());
    config.llvm_build_config.insert("LLVM_ENABLE_ASSERTIONS".into(), "OFF".into());
    config.llvm_build_config.insert("LLVM_VERSION_SUFFIX".into(), "-actual-user-last".into());
    config.llvm_build_config.insert("LLVM_FORCE_VC_REVISION".into(), "selected-vcs-first".into());
    config
        .llvm_build_config
        .insert("LLVM_FORCE_VC_REPOSITORY".into(), "https://example.invalid/recipe".into());
    assert_eq!(
        crate::utils::trust_preparation::PreparationScope::for_config(&config),
        crate::utils::trust_preparation::PreparationScope::RequestSources
    );
    let mut session = Session::new(config);
    let llvm_source = session.config.src.join("src/llvm-project/llvm/cmake/modules");
    fs::write(source.join("CMakeLists.txt"), format!(r#"cmake_minimum_required(VERSION 3.20)
project(ActualLLVMRecipe NONE)
set(header "${{CMAKE_CURRENT_BINARY_DIR}}/VCSRevision.h")
include("{helper}")
llvm_add_vcs_command("${{header}}" OUTPUT "${{header}}"
 DEPENDS "{generator}"
 COMMAND "${{CMAKE_COMMAND}}" "-DNAMES=LLVM" "-DLLVM_SOURCE_DIR="
 "-DLLVM_FORCE_VC_REVISION=${{LLVM_FORCE_VC_REVISION}}"
 "-DLLVM_FORCE_VC_REPOSITORY=${{LLVM_FORCE_VC_REPOSITORY}}"
 "-DHEADER_FILE=${{header}}" -P "{generator}")
add_custom_target(metadata ALL DEPENDS "${{header}}")
file(WRITE "${{CMAKE_CURRENT_BINARY_DIR}}/observed.txt"
 "c=${{CMAKE_C_FLAGS}}\ncxx=${{CMAKE_CXX_FLAGS}}\nmodule=${{CMAKE_MODULE_LINKER_FLAGS}}\nprofile=${{CMAKE_BUILD_TYPE}}\nassertions=${{LLVM_ENABLE_ASSERTIONS}}\nsuffix=${{LLVM_VERSION_SUFFIX}}\nrevision=${{LLVM_FORCE_VC_REVISION}}\nrepository=${{LLVM_FORCE_VC_REPOSITORY}}\ncompile_jobs=${{LLVM_PARALLEL_COMPILE_JOBS}}\ntarget=${{LLVM_DEFAULT_TARGET_TRIPLE}}\narch=${{LLVM_TARGET_ARCH}}\nshared=${{LLVM_BUILD_LLVM_DYLIB}}\ncommand=${{CMAKE_COMMAND}}\n")
install(FILES "${{header}}" "${{CMAKE_CURRENT_BINARY_DIR}}/observed.txt" DESTINATION share/recipe)
"#, helper=llvm_source.join("LLVMVCSRequest.cmake").display(), generator=llvm_source.join("GenerateVersionFromVCS.cmake").display())).unwrap();
    let mut first_config = host_recipe(&session, &source, &output, false);
    let first = first_config.try_prepare().expect("actual host LLVM recipe preparation");
    let first_key = first.cache_inputs().expect("ordinary native recipe must be reusable").to_vec();
    first_config
        .define("LLVM_FORCE_VC_REVISION", "mutation-after-prepare")
        .define("LLVM_ENABLE_ASSERTIONS", "ON");
    first.build();
    let installed = output.join("share/recipe");
    let first_observed = fs::read_to_string(installed.join("observed.txt")).unwrap();
    for expected in [
        "-DLLVM_RECIPE_C=1",
        "-DLLVM_RECIPE_CXX=2",
        "-Wl,llvm-recipe-request",
        "profile=Release\n",
        "assertions=OFF\n",
        "suffix=-actual-user-last\n",
        "revision=selected-vcs-first\n",
        "compile_jobs=1\n",
        "shared=OFF\n",
    ] {
        assert!(first_observed.contains(expected), "{expected}: {first_observed}");
    }
    assert!(first_observed.contains(&format!("target={}\n", session.config.host_target.triple)));
    assert!(first_observed.contains(&format!(
        "arch={}\n",
        session.config.host_target.triple.split('-').next().unwrap()
    )));
    let command = first_observed.lines().find_map(|line| line.strip_prefix("command=")).unwrap();
    assert_eq!(
        fs::canonicalize(command).unwrap(),
        fs::canonicalize(env::var_os("CMAKE").expect("managed CMAKE supplied by lane")).unwrap()
    );
    let first_header = fs::read_to_string(installed.join("VCSRevision.h")).unwrap();
    assert!(
        first_header.contains("selected-vcs-first")
            && first_header.contains("https://example.invalid/recipe")
    );
    fs::copy(installed.join("observed.txt"), evidence.join("first-observed.txt")).unwrap();
    fs::copy(installed.join("VCSRevision.h"), evidence.join("first-VCSRevision.h")).unwrap();

    session.config.llvm_cflags = Some("-DLLVM_RECIPE_C=9".into());
    let changed_flags = host_recipe(&session, &source, &output, false).try_prepare().unwrap();
    assert_ne!(changed_flags.cache_inputs().unwrap(), first_key.as_slice());
    drop(changed_flags);
    session.config.llvm_cflags = Some("-DLLVM_RECIPE_C=1".into());
    let changed_link = host_recipe(&session, &source, &output, true).try_prepare().unwrap();
    assert_ne!(changed_link.cache_inputs().unwrap(), first_key.as_slice());
    drop(changed_link);
    let shared_output = evidence.join("shared output space");
    host_recipe(&session, &source, &shared_output, true).try_prepare().unwrap().build();
    assert!(
        fs::read_to_string(shared_output.join("share/recipe/observed.txt"))
            .unwrap()
            .contains("shared=ON\n")
    );
    session
        .config
        .llvm_build_config
        .insert("LLVM_FORCE_VC_REVISION".into(), "selected-vcs-second".into());
    let second = host_recipe(&session, &source, &output, false).try_prepare().unwrap();
    assert_ne!(second.cache_inputs().unwrap(), first_key.as_slice());
    drop(second);
    let second_output = evidence.join("second FORCE output space");
    host_recipe(&session, &source, &second_output, false).try_prepare().unwrap().build();
    let second_installed = second_output.join("share/recipe");
    let second_observed = fs::read_to_string(second_installed.join("observed.txt")).unwrap();
    assert!(second_observed.contains("revision=selected-vcs-second\n"));
    assert!(
        second_observed.contains("assertions=OFF\n")
            && second_observed.contains("suffix=-actual-user-last\n")
    );
    assert!(
        fs::read_to_string(second_installed.join("VCSRevision.h"))
            .unwrap()
            .contains("selected-vcs-second")
    );
}
