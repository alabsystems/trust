// Copyright 2026 Andrew Yates
// Real CMake/Git observations in the explicit owned-process lane only.
use super::*;
use crate::core::session::Session;
use crate::utils::tests::TestCtx;

fn literal(value: &str) -> String {
    let mut equals = String::new();
    while value.contains(&format!("]{equals}]")) {
        equals.push('=');
    }
    format!("[{equals}[{value}]{equals}]")
}

fn constructor_blocks(text: &str) -> Vec<String> {
    let mut rest = text;
    let mut blocks = Vec::new();
    while let Some(start) = rest.find("llvm_add_vcs_command(") {
        let command = &rest[start..];
        let end = command.find("-P \"${generate_vcs_version_script}\")").unwrap()
            + "-P \"${generate_vcs_version_script}\")".len();
        blocks.push(command[..end].to_owned());
        rest = &command[end..];
    }
    blocks
}

fn baseline(block: &str) -> String {
    let body = block.strip_prefix("llvm_add_vcs_command(\"").unwrap();
    let (_, body) = body.split_once("\" ").unwrap();
    format!("add_custom_command({body}")
}

#[cfg(unix)]
#[test]
#[ignore = "run only under maintained owned-process CMake qualification lane"]
fn real_cmake_vcs_constructor_preserves_native_argv_and_headers() {
    use crate::utils::trust_repo_cache::git;
    let ctx = TestCtx::new();
    let evidence = tempfile::Builder::new()
        .prefix("vcs-constructor-")
        .suffix(".noindex")
        .tempdir()
        .unwrap()
        .keep();
    println!("retained VCS constructor evidence: {}", evidence.display());
    let root = evidence.as_path();
    let mut config = ctx
        .config("build")
        .stage(1)
        .path("library/std")
        .args(&["--set", "rust.trust-source-identity=false"])
        .create_config_with_fixed_budget(Some(1));
    config.set_dry_run(crate::core::config::DryRun::Disabled);
    config.ninja_in_file = true;
    assert_eq!(
        crate::utils::trust_preparation::PreparationScope::for_config(&config),
        crate::utils::trust_preparation::PreparationScope::RequestSources
    );
    let session = Session::new(config);
    let builder = Builder::new(&session);
    let repo = builder.src.join("src/llvm-project");
    let helper = repo.join("llvm/cmake/modules/LLVMVCSRequest.cmake");
    let modules = root.join("actual modules space");
    fs::create_dir(&modules).unwrap();
    for name in ["GenerateVersionFromVCS.cmake", "VersionFromVCS.cmake"] {
        fs::copy(repo.join("llvm/cmake/modules").join(name), modules.join(name)).unwrap();
    }
    // Measurement wrapper delegates to the unchanged actual generator and Git.
    let capture = modules.join("CaptureAndGenerate.cmake");
    fs::write(
        &capture,
        r#"file(APPEND "${HEADER_FILE}.calls" "run\n")
file(WRITE "${HEADER_FILE}.argv" "${CMAKE_ARGC}\n")
math(EXPR last "${CMAKE_ARGC} - 1")
foreach(index RANGE 0 ${last})
  string(HEX "${CMAKE_ARGV${index}}" value)
  string(LENGTH "${CMAKE_ARGV${index}}" length)
  file(APPEND "${HEADER_FILE}.argv" "${length}:${value}\n")
endforeach()
include("${CMAKE_CURRENT_LIST_DIR}/GenerateVersionFromVCS.cmake")
"#,
    )
    .unwrap();
    let add_llvm = fs::read_to_string(repo.join("llvm/cmake/modules/AddLLVM.cmake")).unwrap();
    let start = add_llvm.find("function(find_first_existing_vc_file ").unwrap();
    let end = add_llvm[start..].find("endfunction()").unwrap() + start + "endfunction()".len();
    let actual_find_vc = &add_llvm[start..end];
    let sources = root.join("real Git source space");
    fs::create_dir(&sources).unwrap();
    for name in ["llvm", "clang", "lld", "lldb", "bolt", "flang"] {
        fs::create_dir(sources.join(name)).unwrap();
    }
    fs::write(sources.join("tracked"), b"actual Git fixture").unwrap();
    git(&sources, &["init", "-q"]).unwrap();
    git(&sources, &["add", "."]).unwrap();
    git(
        &sources,
        &[
            "-c",
            "user.name=VCS fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-qm",
            "fixture",
        ],
    )
    .unwrap();
    git(&sources, &["remote", "add", "origin", "https://example.invalid/vcs-fixture.git"]).unwrap();
    let git_head = String::from_utf8(git(&sources, &["rev-parse", "HEAD"]).unwrap()).unwrap();
    let tarball = root.join("non Git tarball source");
    fs::create_dir(&tarball).unwrap();

    // The seven construction variants are the six actual producer sites plus
    // LLVM's existing missing-fake-output branch. No production project registry.
    let variants = [
        ("llvm/include/llvm/Support", 1, "git"),
        ("llvm/include/llvm/Support", 0, "missing-source"),
        ("clang/lib/Basic", 0, "git"),
        ("clang/lib/Basic", 0, "per-name"),
        ("clang/lib/Basic", 0, "both-forced"),
        ("lld/Common", 0, "revision-only"),
        ("lldb/source/Version", 0, "repository-only"),
        ("bolt/lib/Utils", 0, "off"),
        ("bolt/lib/Utils", 0, "off-forced"),
        ("flang/lib/Support", 0, "both-forced"),
    ];
    let project = root.join("constructor project space");
    let output = root.join("constructor output space");
    fs::create_dir(&project).unwrap();
    let header = output.join("build/VCSVersion.inc");
    let argv = output.join("build/VCSVersion.inc.argv");
    let observations_dir = root.join("paired observations");
    fs::create_dir(&observations_dir).unwrap();
    fs::copy(&helper, root.join("LLVMVCSRequest.cmake.observed")).unwrap();
    for (case_index, (site, variant, case)) in variants.into_iter().enumerate() {
        let text = fs::read_to_string(repo.join(site).join("CMakeLists.txt")).unwrap();
        let prefix = &text[..text.find("include(\"${CMAKE_CURRENT_LIST_DIR}/").unwrap()];
        let block = constructor_blocks(&text).remove(variant);
        let mut observations = Vec::new();
        for refactored in [false, true] {
            let _ = fs::remove_file(&header);
            let _ = fs::remove_file(&argv);
            let _ = fs::remove_file(header.with_extension("inc.calls"));
            let main_source =
                if case == "missing-source" { tarball.clone() } else { sources.join("llvm") };
            let force_rev = if ["revision-only", "off-forced", "both-forced"].contains(&case) {
                "forced-revision"
            } else {
                ""
            };
            let force_repo = if ["repository-only", "both-forced"].contains(&case) {
                "https://example.invalid/forced-repository"
            } else {
                ""
            };
            let append = if case.starts_with("off") { "OFF" } else { "ON" };
            let per_name = if case == "per-name" {
                "set(LLVM_VC_REVISION per-llvm)\nset(LLVM_VC_REPOSITORY https://example.invalid/per-llvm)\nset(CLANG_VC_REVISION per-clang)\nset(CLANG_VC_REPOSITORY https://example.invalid/per-clang)\n"
            } else {
                ""
            };
            let vars = format!(
                "set(llvm_vc [=[]=])\nset(clang_vc [=[]=])\nset(lld_vc [=[]=])\nset(lldb_vc [=[]=])\nset(bolt_vc [=[]=])\nset(flang_vc [=[]=])\nset(LLVM_MAIN_SRC_DIR {})\nset(LLVM_SOURCE_DIR {})\nset(CLANG_SOURCE_DIR {})\nset(LLD_SOURCE_DIR {})\nset(LLDB_SOURCE_DIR {})\nset(BOLT_SOURCE_DIR {})\nset(FLANG_SOURCE_DIR {})\nset(LLVM_CMAKE_DIR {})\nset(LLVM_APPEND_VC_REV {append})\nset(LLVM_FORCE_VC_REVISION {})\nset(LLVM_FORCE_VC_REPOSITORY {})\n{per_name}",
                literal(main_source.to_str().unwrap()),
                literal(sources.join("llvm").to_str().unwrap()),
                literal(sources.join("clang").to_str().unwrap()),
                literal(sources.join("lld").to_str().unwrap()),
                literal(sources.join("lldb").to_str().unwrap()),
                literal(sources.join("bolt").to_str().unwrap()),
                literal(sources.join("flang").to_str().unwrap()),
                literal(modules.to_str().unwrap()),
                literal(force_rev),
                literal(force_repo)
            );
            // Prefix computes actual producer-specific source/FORCE choices.
            // Set the same absolute output and measurement script after it.
            let selected_block = if refactored { block.clone() } else { baseline(&block) };
            let fake_check = if case == "missing-source" {
                "if(NOT fake_version_inc)\nmessage(FATAL_ERROR \"actual prefix must select the fake output\")\nendif()\n"
            } else if site == "llvm/include/llvm/Support" {
                "if(fake_version_inc)\nmessage(FATAL_ERROR \"Git prefix must not select fake output\")\nendif()\n"
            } else {
                ""
            };
            let body = format!(
                "cmake_minimum_required(VERSION 3.20)\nproject(VCSConstructor NONE)\n{actual_find_vc}\n{vars}\n{prefix}\n{fake_check}\nset(version_inc {})\nset(vcs_version_inc {})\nset(generate_vcs_version_script {})\ninclude({})\n{selected_block}\nadd_custom_target(observe DEPENDS {})\nfile(WRITE \"${{CMAKE_BINARY_DIR}}/observed-cmake.txt\" \"${{CMAKE_COMMAND}}\")\n",
                literal(header.to_str().unwrap()),
                literal(header.to_str().unwrap()),
                literal(capture.to_str().unwrap()),
                literal(helper.to_str().unwrap()),
                literal(header.to_str().unwrap())
            );
            fs::write(project.join("CMakeLists.txt"), body).unwrap();
            let mut cmake = cmake::Config::new(&project);
            cmake
                .out_dir(&output)
                .profile("Release")
                .target(&builder.host_target.triple)
                .host(&builder.host_target.triple)
                .generator("Ninja")
                .env("TRUST_VCS_REQUEST_DECLARATIONS", "")
                .build_arg("-j")
                .build_arg("1")
                .build_target("observe");
            cmake.build();
            if case == "missing-source" {
                assert!(!output.join("build/__FakeVCSRevision.h").exists());
                cmake.build();
                let calls = fs::read_to_string(header.with_extension("inc.calls")).unwrap();
                assert_eq!(
                    calls.lines().count(),
                    2,
                    "missing fake output must force each native build"
                );
            }
            assert!(
                !output.join("build/.trust-vcs-request-declarations").exists(),
                "default recording is off"
            );
            let actual = fs::read_to_string(output.join("build/observed-cmake.txt")).unwrap();
            assert_eq!(
                fs::canonicalize(actual).unwrap(),
                fs::canonicalize(env::var_os("CMAKE").expect("managed CMAKE supplied by lane"))
                    .unwrap()
            );
            let mode = if refactored { "refactored" } else { "baseline" };
            let label = format!("{case_index:02}-{case}-{mode}");
            fs::copy(&header, observations_dir.join(format!("{label}.header"))).unwrap();
            fs::copy(&argv, observations_dir.join(format!("{label}.argv"))).unwrap();
            fs::copy(
                project.join("CMakeLists.txt"),
                observations_dir.join(format!("{label}.CMakeLists.txt")),
            )
            .unwrap();
            observations.push((fs::read(&header).unwrap(), fs::read(&argv).unwrap()));
        }
        let emitted = String::from_utf8(observations[0].0.clone()).unwrap();
        match case {
            "git" => assert!(
                emitted.contains(git_head.trim())
                    && emitted.contains("https://example.invalid/vcs-fixture.git"),
                "{emitted}"
            ),
            "missing-source" => assert!(
                emitted.contains("#undef LLVM_REVISION")
                    && emitted.contains("#undef LLVM_REPOSITORY"),
                "{emitted}"
            ),
            "per-name" => {
                assert!(emitted.contains("per-llvm") && emitted.contains("per-clang"), "{emitted}")
            }
            "revision-only" => assert!(
                emitted.contains("#define LLD_REVISION")
                    && emitted.contains("#undef LLD_REPOSITORY"),
                "{emitted}"
            ),
            "repository-only" => assert!(
                emitted.contains("#undef LLDB_REVISION")
                    && emitted.contains("#define LLDB_REPOSITORY"),
                "{emitted}"
            ),
            "off" => assert!(
                emitted.contains("#undef BOLT_REVISION")
                    && emitted.contains("#undef BOLT_REPOSITORY"),
                "{emitted}"
            ),
            "off-forced" => assert!(
                emitted.contains("#define BOLT_REVISION")
                    && emitted.contains("#undef BOLT_REPOSITORY"),
                "{emitted}"
            ),
            "both-forced" => assert!(
                emitted.contains("#define")
                    && emitted.contains("forced-revision")
                    && emitted.contains("https://example.invalid/forced-repository"),
                "{emitted}"
            ),
            _ => unreachable!(),
        }
        assert_eq!(
            observations[0], observations[1],
            "native header/argv differs for {site} / {case}"
        );
        println!("VCS native baseline/refactor matched: {site} / {case}");
    }
    controls::run(&builder, root, &helper, &capture);
}

#[cfg(unix)]
#[path = "vcs_constructor_controls.rs"]
mod controls;
