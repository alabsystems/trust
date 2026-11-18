//! Trust (DC-16a): a stage 2 whose change leaves the verification batteries alone takes
//! them from its source toolchain (`Stage2VerifierTools`), and builds them otherwise.

use sha2::Digest as _;

use super::*;
use crate::utils::channel::Info;
use crate::utils::tests::git::{GitCtx, git_test};

const BATTERIES: [&str; 2] = ["first-party/ay", "first-party/ty"];

/// The profile a pack is cut on, as the checkout holds it and the pack's build record
/// names it.
const PROFILE: &str = "src/bootstrap/defaults/bootstrap.compiler.toml";
const PROFILE_TEXT: &str = "[rust]\ndebug-assertions = true\n";

/// Writes the checkout's profile as `text` exactly (`GitCtx::write` appends a line).
fn write_profile(ctx: &GitCtx, text: &str) {
    let path = ctx.get_path().join(PROFILE);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn submodules() -> Vec<String> {
    BATTERIES.iter().map(|root| (*root).to_owned()).collect()
}

fn sha256(bytes: &[u8]) -> String {
    helpers::hex_encode(sha2::Sha256::digest(bytes).as_slice())
}

fn head_of(ctx: &GitCtx) -> Info {
    let sha = ctx.get_current_commit();
    Info { short_sha: sha[..9].to_owned(), sha, commit_date: "2026-11-16".to_owned() }
}

/// A checkout with a compiler and the two takeable batteries as submodules, each a
/// workspace whose path dependencies stay inside it, committed as gitlinks.
fn battery_checkout(ctx: &GitCtx) {
    ctx.write("compiler/rustc/src/main.rs", "fn main() {}");
    write_profile(ctx, PROFILE_TEXT);
    for root in BATTERIES {
        fs::create_dir_all(ctx.get_path().join(root)).unwrap();
        ctx.run_git(&["-C", root, "init"]);
        ctx.run_git(&["-C", root, "config", "user.name", "Tester"]);
        ctx.run_git(&["-C", root, "config", "user.email", "tester@example.invalid"]);
        ctx.write(&format!("{root}/Cargo.toml"), "[workspace]\nmembers = [\"crates/cli\"]");
        ctx.write(
            &format!("{root}/crates/cli/Cargo.toml"),
            "[package]\nname = \"cli\"\n[[bin]]\nname = \"cli\"\npath = \"src/main.rs\"\n\
             [dependencies]\nsolver = { path = \"../solver\" }",
        );
        ctx.write(&format!("{root}/crates/cli/src/main.rs"), "fn main() {}");
        ctx.write(&format!("{root}/crates/solver/Cargo.toml"), "[package]\nname = \"solver\"");
        ctx.write(&format!("{root}/crates/solver/src/lib.rs"), "pub fn solve() {}");
        ctx.run_git(&["-C", root, "add", "."]);
        ctx.run_git(&["-C", root, "commit", "-m", "battery"]);
    }
    ctx.commit();
}

/// The batteries a pack built at `commit` ships: `ay` names only std's remapped
/// sources, and `ty` records that `ay`'s bytes as trust-cg-verify does.
fn batteries_built_at(commit: &str) -> (Vec<u8>, Vec<u8>) {
    let ay = format!("ay solver\0/rustc/{commit}/library/core/src/panic.rs\0").into_bytes();
    let ty = format!("ty checker\0{}\0/rustc/{commit}/library/std/src/io.rs\0", sha256(&ay));
    (ay, ty.into_bytes())
}

/// Writes a sealed pack built at `commit` holding `ay` and `ty` into `dir`; `seal` is
/// the `PROVENANCE` the seal of those bytes is (it may be edited before it is written).
fn write_pack(dir: &Path, commit: &str, ay: &[u8], ty: &[u8], seal: impl FnOnce(&mut String)) {
    let host = helpers::get_host_target();
    let bin = dir.join("bin");
    let _ = fs::remove_dir_all(dir);
    fs::create_dir_all(&bin).unwrap();
    fs::write(bin.join(exe("ay", host)), ay).unwrap();
    fs::write(bin.join(exe("ty", host)), ty).unwrap();
    let mut record = format!(
        "# PROVENANCE — what this sealed toolchain actually is\n\
         provenance_class=BUILD-STAMPED-CLEAN\n\
         reported_commit={commit}\n\
         sealtime_repo_tree=clean\n\
         build_stamp:tree_state=clean\n\
         artifact_bin_ay_sha256={}\n\
         artifact_bin_ty_sha256={}\n",
        sha256(ay),
        sha256(ty)
    );
    seal(&mut record);
    fs::write(dir.join(SOURCE_TOOLCHAIN_RECORD), record).unwrap();
    write_build_record(
        dir,
        &[("bootstrap.toml", "0".repeat(64)), (PROFILE, sha256(PROFILE_TEXT.as_bytes()))],
    );
}

/// The build record of the pack at `dir`, naming the configuration files its cut parsed.
fn write_build_record(dir: &Path, files: &[(&str, String)]) {
    let files: Vec<_> = files
        .iter()
        .map(|(path, sha256)| serde_json::json!({ "relative_path": path, "sha256": sha256 }))
        .collect();
    let record = serde_json::json!({
        "bootstrap_lineage": { "mint_configuration": { "configuration_closure": { "files": files } } }
    });
    fs::write(dir.join(SOURCE_TOOLCHAIN_BUILD_RECORD), record.to_string()).unwrap();
}

fn decide_with(
    ctx: &GitCtx,
    pack: &Path,
    head: &Info,
    tools: &[(&'static str, trust_source_identity::IndependentToolComponent)],
    debug_assertions: bool,
) -> Stage2VerifierTools {
    decide_stage2_verifier_tools(
        &ExecutionContext::new(0, false),
        ctx.get_path(),
        head,
        &submodules(),
        pack,
        helpers::get_host_target(),
        WantedVerifierTools { tools, debug_assertions },
    )
}

fn decide_for(
    ctx: &GitCtx,
    pack: &Path,
    wanted: &[(&'static str, trust_source_identity::IndependentToolComponent)],
) -> Stage2VerifierTools {
    decide_with(ctx, pack, &head_of(ctx), wanted, true)
}

fn decide(ctx: &GitCtx, pack: &Path) -> Stage2VerifierTools {
    decide_for(ctx, pack, &STAGE2_TAKEABLE_VERIFIER_TOOLS)
}

#[track_caller]
fn assert_taken(decision: &Stage2VerifierTools, pack: &Path, names: &[&str]) {
    let Stage2VerifierTools::Taken(taken) = decision else {
        panic!("expected {names:?} taken from {}: {decision:?}", pack.display());
    };
    let host = helpers::get_host_target();
    let taken_names: Vec<_> = taken.tools.iter().map(|tool| tool.name).collect();
    assert_eq!(taken_names, names);
    for tool in &taken.tools {
        assert_eq!(tool.path, pack.join("bin").join(exe(tool.name, host)));
        assert_eq!(tool.sha256, sha256(&fs::read(&tool.path).unwrap()));
    }
    assert_eq!(taken.source, pack);
}

#[track_caller]
fn assert_built(decision: Stage2VerifierTools, because: &str) {
    match decision {
        Stage2VerifierTools::Built(why) => {
            assert!(why.contains(because), "built, but not because {because:?}: {why}")
        }
        Stage2VerifierTools::Taken(taken) => {
            panic!("expected every battery built ({because}), but took {taken:?}")
        }
    }
}

/// The verifier batteries the graph has a producer for at `output_stage`.
fn built_batteries(builder: &Builder<'_>, output_stage: u32) -> Vec<&'static str> {
    let mut tools: Vec<_> = builder
        .step_cache()
        .inspect_all_steps_of_type::<ToolBuild, _>(|step, _| {
            (step.output_compiler.stage == output_stage
                && ["ay", "clean", "targo", "targo-trust", "trustd", "ty"].contains(&step.tool))
            .then_some(step.tool)
        })
        .into_iter()
        .flatten()
        .collect();
    tools.sort_unstable();
    tools
}

fn hand_the_decision(decision: Option<Stage2VerifierTools>) {
    STAGE2_VERIFIER_TOOLS_FOR_TEST.with_borrow_mut(|slot| *slot = decision);
}

#[cfg(unix)]
#[test]
fn stage2_verifier_tools_are_installed_from_the_source_toolchain_when_their_inputs_match() {
    let packs = tempfile::TempDir::new().unwrap();
    let pack = packs.path().join("27009");
    let mut taken = None;
    git_test(|ctx| {
        battery_checkout(ctx);
        let source = ctx.get_current_commit();
        let (ay, ty) = batteries_built_at(&source);
        write_pack(&pack, &source, &ay, &ty, |_| {});

        // The same commit, and then a compiler change and a document after it:
        // neither is an input of a battery.
        assert_taken(&decide(ctx, &pack), &pack, &["ay", "ty"]);
        ctx.write("compiler/rustc/src/main.rs", "// the compiler moves");
        ctx.write("docs/STATUS.md", "measured");
        ctx.commit();
        assert_taken(&decide(ctx, &pack), &pack, &["ay", "ty"]);
        // So does an uncommitted edit outside the batteries' pins.
        ctx.write("compiler/rustc/src/lib.rs", "pub fn edited() {}");
        let decision = decide(ctx, &pack);
        assert_taken(&decision, &pack, &["ay", "ty"]);
        let Stage2VerifierTools::Taken(found) = decision else { unreachable!() };
        assert_eq!(found.commit, source);
        // A build that selects only `ay` takes only `ay`.
        assert_taken(&decide_for(ctx, &pack, &STAGE2_TAKEABLE_VERIFIER_TOOLS[..1]), &pack, &["ay"]);
        taken = Some(found);
    });

    // The source toolchain is the installed atpkg pack `current` names, never a
    // directory beside it.
    let home = tempfile::TempDir::new().unwrap();
    let prefix = if cfg!(target_os = "macos") {
        home.path().join("Library/Application Support/aterm/pkg")
    } else {
        home.path().join(".local/share/aterm/pkg")
    };
    let store = prefix.join("store/trust");
    fs::create_dir_all(store.join("27009/bin")).unwrap();
    assert!(installed_trust_pack(home.path()).is_err(), "no `current`, no source toolchain");
    std::os::unix::fs::symlink("27009", store.join("current")).unwrap();
    assert_eq!(
        installed_trust_pack(home.path()).unwrap(),
        store.join("27009").canonicalize().unwrap()
    );
    fs::remove_file(store.join("current")).unwrap();
    fs::create_dir_all(home.path().join("elsewhere/27010")).unwrap();
    std::os::unix::fs::symlink(home.path().join("elsewhere/27010"), store.join("current")).unwrap();
    assert!(installed_trust_pack(home.path()).is_err(), "a pack outside the store");
    fs::remove_file(store.join("current")).unwrap();
    std::os::unix::fs::symlink("27009", store.join("current")).unwrap();
    std::os::unix::fs::symlink("../../toolchains/x", store.join("27009/toolchain")).unwrap();
    assert!(installed_trust_pack(home.path()).is_err(), "a wired sysroot is no sealed pack");
    // atpkg's own layout: `<N>` links to `<N>.noindex`, which holds the pack.
    fs::create_dir_all(store.join("27010.noindex/bin")).unwrap();
    std::os::unix::fs::symlink("27010.noindex", store.join("27010")).unwrap();
    fs::remove_file(store.join("current")).unwrap();
    std::os::unix::fs::symlink(store.join("27010"), store.join("current")).unwrap();
    assert_eq!(
        installed_trust_pack(home.path()).unwrap(),
        store.join("27010.noindex").canonicalize().unwrap()
    );
    for name in ["x.noindex", "027011.noindex", ".noindex"] {
        fs::create_dir_all(store.join(name)).unwrap();
        fs::remove_file(store.join("current")).unwrap();
        std::os::unix::fs::symlink(name, store.join("current")).unwrap();
        assert!(installed_trust_pack(home.path()).is_err(), "{name} is no numbered pack");
    }

    // The graph: the stage-2 sysroot installs the taken `ay` before its compiler
    // records it, and `ty` after assembly, in place of compiling them. The batteries
    // that record this build's compiler are still built, by stage 1.
    let context = crate::utils::tests::TestCtx::new();
    let mut build = crate::core::session::Session::new(
        context
            .config("build")
            .stage(2)
            .args(&["--set", "build.extended=true", "--set", "rust.trust-source-identity=false"])
            .create_config(),
    );
    intermediate_tool_source_fixture(&context, &mut build);
    hand_the_decision(taken.map(Stage2VerifierTools::Taken));
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    builder.compiler(2, target);
    hand_the_decision(None);
    assert_eq!(built_batteries(&builder, 2), ["clean", "targo", "targo-trust", "trustd"]);
    assert_eq!(built_batteries(&builder, 1).first(), Some(&"ay"), "stage 1 is not this rule's");
    let decisions = builder.step_cache().inspect_all_steps_of_type::<Stage2VerifierToolSource, _>(
        |step, decision| (step.compiler.stage, matches!(decision, Stage2VerifierTools::Taken(_))),
    );
    assert_eq!(decisions, [(2, true)], "one decision for the one stage-2 sysroot");
    let names = |builder: &Builder<'_>| -> Vec<&str> {
        stage2_wanted_verifier_tools(builder).into_iter().map(|(name, _)| name).collect()
    };
    assert_eq!(names(&builder), ["ay", "ty"]);
    drop(builder);
    // A build whose tools leave `ty` out wants only `ay`.
    build.config.tools = Some(["targo-trust".to_owned()].into_iter().collect());
    assert_eq!(names(&Builder::new(&build)), ["ay"]);
}

#[cfg(unix)]
#[test]
fn stage2_verifier_tools_are_built_when_a_pin_or_a_source_moved() {
    let packs = tempfile::TempDir::new().unwrap();
    let pack = packs.path().join("pack");
    git_test(|ctx| {
        battery_checkout(ctx);
        let source = ctx.get_current_commit();
        let (ay, ty) = batteries_built_at(&source);
        write_pack(&pack, &source, &ay, &ty, |_| {});
        assert_taken(&decide(ctx, &pack), &pack, &["ay", "ty"]);

        // An edit in a battery's checkout, an untracked file there, the battery
        // checked out at another commit, and a new pin: each moves its input.
        ctx.write("first-party/ty/crates/cli/src/main.rs", "// edited");
        assert_built(decide(ctx, &pack), "departs from HEAD");
        ctx.run_git(&["-C", "first-party/ty", "commit", "-am", "ty moves"]);
        assert_built(decide(ctx, &pack), "departs from HEAD");
        ctx.commit();
        // Moving one battery builds the whole set: `ay` is not taken alone.
        assert_built(decide(ctx, &pack), "first-party/ty is");
    });
    git_test(|ctx| {
        // HEAD moves while the inputs are read: what was read is not known to be HEAD's.
        battery_checkout(ctx);
        let source = ctx.get_current_commit();
        let (ay, ty) = batteries_built_at(&source);
        write_pack(&pack, &source, &ay, &ty, |_| {});
        let read = head_of(ctx);
        ctx.write("compiler/rustc/src/main.rs", "// HEAD moves on");
        ctx.commit();
        let decision = decide_with(ctx, &pack, &read, &STAGE2_TAKEABLE_VERIFIER_TOOLS, true);
        assert_built(decision, "HEAD moved");
        assert_taken(&decide(ctx, &pack), &pack, &["ay", "ty"]);
    });
    git_test(|ctx| {
        battery_checkout(ctx);
        let source = ctx.get_current_commit();
        let (ay, ty) = batteries_built_at(&source);
        write_pack(&pack, &source, &ay, &ty, |_| {});
        ctx.write("first-party/ay/crates/solver/src/fresh.rs", "pub fn fresh() {}");
        assert_built(decide(ctx, &pack), "departs from HEAD");
    });
    git_test(|ctx| {
        // A path dependency that leaves the battery's repository is a source its pin
        // does not name: the battery is built even though every pin is equal.
        battery_checkout(ctx);
        ctx.write(
            "first-party/ay/crates/solver/Cargo.toml",
            "[dependencies]\nshared = { path = \"../../../../compiler/shared\" }",
        );
        ctx.run_git(&["-C", "first-party/ay", "commit", "-am", "reach out"]);
        ctx.commit();
        let source = ctx.get_current_commit();
        let (ay, ty) = batteries_built_at(&source);
        write_pack(&pack, &source, &ay, &ty, |_| {});
        assert_built(decide(ctx, &pack), "outside first-party/ay");
    });
    git_test(|ctx| {
        // A source toolchain built from a commit this repository does not hold, or
        // from one that is not a commit at all, proves nothing equal.
        battery_checkout(ctx);
        let (ay, ty) = batteries_built_at("0123456789abcdef0123456789abcdef01234567");
        write_pack(&pack, "0123456789abcdef0123456789abcdef01234567", &ay, &ty, |_| {});
        assert_built(decide(ctx, &pack), "holds no commit");
        let tree = ctx.run_git(&["rev-parse", "HEAD^{tree}"]);
        let (ay, ty) = batteries_built_at(&tree);
        write_pack(&pack, &tree, &ay, &ty, |_| {});
        assert_built(decide(ctx, &pack), "holds no commit");
        // A battery that is not a submodule of this checkout has no pin to compare.
        let source = ctx.get_current_commit();
        let (ay, ty) = batteries_built_at(&source);
        write_pack(&pack, &source, &ay, &ty, |_| {});
        let decision = decide_stage2_verifier_tools(
            &ExecutionContext::new(0, false),
            ctx.get_path(),
            &head_of(ctx),
            &submodules()[..1],
            &pack,
            helpers::get_host_target(),
            WantedVerifierTools { tools: &STAGE2_TAKEABLE_VERIFIER_TOOLS, debug_assertions: true },
        );
        assert_built(decision, "is not a submodule");
    });
}

#[test]
fn stage2_verifier_tools_are_built_for_dist_and_for_an_unknown_configuration() {
    use crate::core::backend::CodegenBackendKind;
    let context = crate::utils::tests::TestCtx::new();
    let mut build =
        crate::core::session::Session::new(context.config("build").stage(2).create_config());
    build.config.external_rustc = None;
    build.config.external_cargo = None;
    build.config.external_rustdoc = None;
    // As in `intermediate_tool_deferral_policy_is_fail_closed`: a source tree whose only
    // Cargo configuration is the tracked one, and an empty Cargo home.
    let source = context.dir().join("source");
    fs::create_dir_all(source.join(".cargo")).unwrap();
    fs::write(
        source.join(".cargo/config.toml"),
        include_str!("../../../../../../../.cargo/config.toml"),
    )
    .unwrap();
    build.config.src = source;
    let native = helpers::get_host_target();
    let ambient = vec![
        (OsString::from("CARGO_HOME"), context.dir().join("cargo-home").into_os_string()),
        (OsString::from("RUSTFLAGS_BOOTSTRAP"), OsString::from("-Ztrust-verify=off")),
    ];
    let eligible = |build: &crate::core::session::Session,
                    kind,
                    top,
                    stage,
                    host,
                    ambient: Vec<(OsString, OsString)>| {
        let mut builder = Builder::new(build);
        builder.kind = kind;
        builder.top_stage = top;
        stage2_verifier_tools_eligible(&builder, Compiler::new(stage, host), ambient)
    };
    let ordinary = |build: &crate::core::session::Session, ambient| {
        eligible(build, Kind::Build, 2, 2, native, ambient).is_ok()
    };
    assert_eq!(eligible(&build, Kind::Build, 2, 2, native, ambient.clone()), Ok(()));
    // Dist, install and every other command compile every battery with the compiler
    // they ship; the pack cut's double compile compares those bytes.
    for kind in [Kind::Dist, Kind::Install, Kind::Test, Kind::Check, Kind::Doc, Kind::Run] {
        assert!(eligible(&build, kind, 2, 2, native, ambient.clone()).is_err(), "{kind:?}");
    }
    for (top, stage) in [(1, 1), (2, 1), (3, 2), (3, 3), (2, 0)] {
        assert!(eligible(&build, Kind::Build, top, stage, native, ambient.clone()).is_err());
    }
    let foreign = TargetSelection::from_user("i686-unknown-haiku");
    assert!(eligible(&build, Kind::Build, 2, 2, foreign, ambient.clone()).is_err());
    build.config.hosts.push(foreign);
    assert!(!ordinary(&build, ambient.clone()));
    build.config.hosts = vec![native];
    // A configuration the audited rule does not recognise keeps the batteries-on graph.
    build.config.full_bootstrap = true;
    assert!(!ordinary(&build, ambient.clone()));
    build.config.full_bootstrap = false;
    build.config.rust_codegen_backends = vec![CodegenBackendKind::TrustCg];
    assert!(!ordinary(&build, ambient.clone()));
    build.config.rust_codegen_backends = vec![CodegenBackendKind::Llvm];
    build.config.rust_rustflags.push("-Ztrust-verify=on".into());
    assert!(!ordinary(&build, ambient.clone()));
    build.config.rust_rustflags.clear();
    assert!(ordinary(&build, ambient.clone()));
    for key in
        ["RUSTFLAGS", "RUSTC_WRAPPER", "TRUST_UNKNOWN_CONTROL", "TOOLCHAIN_AY_EXPECTED_SYSROOT"]
    {
        let mut changed = ambient.clone();
        changed.push((key.into(), "unknown".into()));
        assert!(!ordinary(&build, changed), "{key}");
    }
    // Without the announced bootstrap posture, and in a pack cut's environment
    // (scripts/mint_and_prove_seed.sh's run_clean: its own empty HOME and the pinned
    // Lean inputs), nothing is taken.
    assert!(!ordinary(&build, vec![ambient[0].clone()]));
    let mut cut = ambient.clone();
    cut.push(("CLEAN_OLEAN_REQUIRE_PINNED_LEAN".into(), "1".into()));
    assert!(!ordinary(&build, cut));
    // The whole decision says why it builds; an eligible build without a pack, too.
    let decision = |build: &crate::core::session::Session, kind, ambient| {
        let mut builder = Builder::new(build);
        builder.kind = kind;
        builder.top_stage = 2;
        stage2_verifier_tools(&builder, Compiler::new(2, native), ambient)
    };
    assert_built(decision(&build, Kind::Dist, ambient.clone()), "`x.py dist` compiles");
    let mut homeless = ambient.clone();
    homeless.push(("HOME".into(), context.dir().join("home").into_os_string()));
    assert_built(decision(&build, Kind::Build, homeless), "no installed trust pack");

    // The graph of `x.py dist`, even when a decision to take is at hand: every
    // battery of the shipped sysroot is built by the compiler before it.
    #[cfg(unix)]
    {
        let context = crate::utils::tests::TestCtx::new();
        let mut build = crate::core::session::Session::new(
            context
                .config("dist")
                .stage(2)
                .args(&[
                    "--set",
                    "build.extended=true",
                    "--set",
                    "rust.trust-source-identity=false",
                ])
                .create_config(),
        );
        intermediate_tool_source_fixture(&context, &mut build);
        let pack = context.dir().join("pack");
        hand_the_decision(Some(Stage2VerifierTools::Taken(TakenVerifierTools {
            source: pack.clone(),
            commit: "0123456789abcdef0123456789abcdef01234567".into(),
            tools: ["ay", "ty"]
                .into_iter()
                .map(|name| TakenVerifierTool {
                    name,
                    path: pack.join("bin").join(name),
                    sha256: "0".repeat(64),
                })
                .collect(),
        })));
        let builder = Builder::new(&build);
        let target = builder.config.host_target;
        let image = context.dir().join("image");
        ensure_default_verifier_tool_bins(&builder, Compiler::new(2, target), &image);
        hand_the_decision(None);
        assert_eq!(
            built_batteries(&builder, 2),
            ["ay", "clean", "targo", "targo-trust", "trustd", "ty"]
        );
        assert!(
            builder
                .step_cache()
                .inspect_all_steps_of_type::<Stage2VerifierToolSource, _>(|_, _| ())
                .is_empty(),
            "dist never asks for a source toolchain"
        );
    }
}

#[cfg(unix)]
#[test]
fn stage2_verifier_tools_are_taken_with_the_ay_they_recorded_or_not_at_all() {
    let packs = tempfile::TempDir::new().unwrap();
    let pack = packs.path().join("pack");
    git_test(|ctx| {
        battery_checkout(ctx);
        let source = ctx.get_current_commit();
        let (ay, ty) = batteries_built_at(&source);
        write_pack(&pack, &source, &ay, &ty, |_| {});
        assert_taken(&decide(ctx, &pack), &pack, &["ay", "ty"]);

        // `ty` records another `ay` than the one beside it: neither is taken.
        let other_ay = b"another ay".to_vec();
        let ty_of_other = format!("ty checker\0{}\0", sha256(&other_ay)).into_bytes();
        write_pack(&pack, &source, &ay, &ty_of_other, |_| {});
        assert_built(decide(ctx, &pack), "does not record the ay");

        // The pack's `ay` was replaced after the seal (an overlay put a newer one in
        // place, as installed pack 27009 had on 2026-11-16): it is not the file the
        // sealed commit built, and `ty` recorded the sealed one.
        write_pack(&pack, &source, &ay, &ty, |_| {});
        fs::write(pack.join("bin").join(exe("ay", helpers::get_host_target())), &other_ay).unwrap();
        assert_built(decide(ctx, &pack), "is not the file its seal records");

        // A battery that records its compiler's commit is bound to that compiler.
        let short = &source[..9];
        for record in [
            format!("\0{source}\0"),
            format!("rustc 1.101.0-dev ({short} "),
            format!("0.14.0+g{short}"),
        ] {
            let mut bound = ty.clone();
            bound.extend_from_slice(record.as_bytes());
            write_pack(&pack, &source, &ay, &bound, |_| {});
            assert_built(decide(ctx, &pack), "records its compiler");
            let mut bound = ay.clone();
            bound.extend_from_slice(record.as_bytes());
            let ty = format!("ty\0{}\0", sha256(&bound)).into_bytes();
            write_pack(&pack, &source, &bound, &ty, |_| {});
            assert_built(decide(ctx, &pack), "records its compiler");
        }

        // A seal that is not a clean build's, or not one record, takes nothing.
        let seals: [(&str, fn(&mut String)); 6] = [
            ("not BUILD-STAMPED-CLEAN", |seal| {
                *seal = seal.replace("BUILD-STAMPED-CLEAN", "BUILD-STAMPED-DIRTY")
            }),
            ("says sealtime_repo_tree", |seal| {
                *seal = seal.replace("sealtime_repo_tree=clean", "sealtime_repo_tree=dirty")
            }),
            ("says build_stamp:tree_state", |seal| {
                *seal = seal.replace("build_stamp:tree_state=clean", "build_stamp:tree_state=dirty")
            }),
            ("names `reported_commit` twice", |seal| {
                seal.push_str("reported_commit=0123456789abcdef0123456789abcdef01234567\n")
            }),
            ("records no bin/ty", |seal| {
                *seal = seal
                    .lines()
                    .filter(|line| !line.starts_with("artifact_bin_ty"))
                    .collect::<Vec<_>>()
                    .join("\n")
            }),
            ("no full reported_commit", |seal| {
                *seal = seal
                    .lines()
                    .filter(|line| !line.starts_with("reported_commit"))
                    .collect::<Vec<_>>()
                    .join("\n")
            }),
        ];
        for (why, edit) in seals {
            write_pack(&pack, &source, &ay, &ty, edit);
            assert_built(decide(ctx, &pack), why);
        }
        write_pack(&pack, &source, &ay, &ty, |_| {});
        fs::remove_file(pack.join(SOURCE_TOOLCHAIN_RECORD)).unwrap();
        assert_built(decide(ctx, &pack), "cannot read");
        write_pack(&pack, &source, &ay, &ty, |_| {});
        fs::remove_file(pack.join("bin").join(exe("ty", helpers::get_host_target()))).unwrap();
        assert_built(decide(ctx, &pack), "No such file");

        // A battery's own checks are part of what it answers: a build that compiles the
        // batteries with debug assertions off does not take ones cut with them on, nor
        // from a cut whose profile is not this checkout's, or is not recorded.
        write_pack(&pack, &source, &ay, &ty, |_| {});
        let head = head_of(ctx);
        let wanted = &STAGE2_TAKEABLE_VERIFIER_TOOLS;
        assert_built(decide_with(ctx, &pack, &head, wanted, false), "debug assertions off");
        write_build_record(&pack, &[(PROFILE, sha256(b"[rust]\ndebug-assertions = false\n"))]);
        assert_built(decide(ctx, &pack), "cut on other bytes");
        write_build_record(&pack, &[("bootstrap.toml", sha256(PROFILE_TEXT.as_bytes()))]);
        assert_built(decide(ctx, &pack), "no single configuration profile");
        fs::remove_file(pack.join(SOURCE_TOOLCHAIN_BUILD_RECORD)).unwrap();
        assert_built(decide(ctx, &pack), "cannot read");
        // The profile decides by `debug-assertions-tools`, then `debug-assertions`, then
        // `debug`, as `Config` does.
        for (profile, on) in [
            ("[rust]\ndebug = true\n", true),
            ("[rust]\ndebug = true\ndebug-assertions = false\n", false),
            ("[rust]\ndebug-assertions = false\ndebug-assertions-tools = true\n", true),
            ("[llvm]\nassertions = true\n", false),
        ] {
            write_profile(ctx, profile);
            write_build_record(&pack, &[(PROFILE, sha256(profile.as_bytes()))]);
            assert_eq!(source_toolchain_tools_debug_assertions(&pack, ctx.get_path()), Ok(on));
        }
        write_profile(ctx, PROFILE_TEXT);

        // Nothing is taken without the `ay` every taken battery records.
        write_pack(&pack, &source, &ay, &ty, |_| {});
        assert_built(
            decide_for(ctx, &pack, &STAGE2_TAKEABLE_VERIFIER_TOOLS[1..]),
            "without the ay",
        );
        assert_taken(&decide(ctx, &pack), &pack, &["ay", "ty"]);
    });
    // Std's remapped sources name the commit that built it, and record nothing.
    let commit = "0123456789abcdef0123456789abcdef01234567";
    assert!(!records_its_compiler(format!("/rustc/{commit}/library/core").as_bytes(), commit));
    assert!(records_its_compiler(format!("x/rustc/{commit}/ {commit}").as_bytes(), commit));
    assert!(!records_its_compiler(b"0123456789 (012345678x", commit));
}

#[cfg(unix)]
#[test]
fn installed_ay_arrives_newer_than_any_record_of_another_ay() {
    use std::os::unix::fs::MetadataExt as _;
    use std::time::{Duration, SystemTime};

    let dir = tempfile::TempDir::new().unwrap();
    let tools = dir.path().join("stage2-tools-bin");
    let bin = dir.path().join("stage2/bin");
    fs::create_dir_all(&tools).unwrap();
    fs::create_dir_all(&bin).unwrap();
    let at = |secs| SystemTime::UNIX_EPOCH + Duration::from_secs(secs);
    let mtime = |path: &Path| fs::metadata(path).unwrap().modified().unwrap();
    // An `ay` as a pack or Cargo's output holds it: with a time long past.
    let produced = |name: &str, bytes: &[u8]| {
        let path = dir.path().join(name);
        fs::write(&path, bytes).unwrap();
        helpers::set_file_times(&path, fs::FileTimes::new().set_modified(at(1_000))).unwrap();
        path
    };
    let recorders: Vec<(String, Vec<String>)> =
        [("targo", &["targo", "cargo"][..]), ("ty", &["ty"])]
            .into_iter()
            .map(|(tool, bins)| {
                (tool.to_owned(), bins.iter().map(|bin| (*bin).to_owned()).collect())
            })
            .collect();
    // A tool restored from the tools directory, which records `ay` (or none).
    let restore = |tool: &str, records: Option<&[u8]>| {
        let bytes = format!("{tool}\0{}\0", records.map(sha256).unwrap_or_default());
        fs::write(tools.join(tool), &bytes).unwrap();
        for bin_name in sysroot_bin_names_for_tool_source(tool) {
            fs::write(bin.join(bin_name), &bytes).unwrap();
        }
    };
    let settle = |from: &Path, sealed: Option<&str>| {
        settle_installed_ay(from, sealed, &tools, &bin, "ay", &recorders)
    };
    let record = tools.join(INSTALLED_AY_RECORD);
    let (p, a) = (b"ay P".as_slice(), b"ay A".as_slice());

    // The first `ay` in a directory without a record: the tools that do not record it
    // are removed with their sysroot names, and the copy is the directory's own.
    restore("targo", None);
    restore("ty", Some(p));
    let from = produced("pack-ay", p);
    let installed = settle(&from, Some(&sha256(p))).unwrap();
    assert_eq!(installed, tools.join("ay"));
    assert_eq!(fs::read(&installed).unwrap(), p);
    assert_eq!(fs::read_to_string(&record).unwrap(), format!("{}\n", sha256(p)));
    assert!(mtime(&installed) > at(1_000), "the arrival is now, not the pack's time");
    assert_eq!(mtime(&installed), mtime(&record));
    assert_ne!(fs::metadata(&installed).unwrap().ino(), fs::metadata(&from).unwrap().ino());
    assert_eq!(mtime(&from), at(1_000), "the source is never touched");
    for gone in [tools.join("targo"), bin.join("targo"), bin.join("cargo")] {
        assert!(!gone.exists(), "{} records no P", gone.display());
    }
    assert!(tools.join("ty").exists() && bin.join("ty").exists());

    // The same bytes again keep the time they arrived with, however old the source's.
    helpers::set_file_times(&record, fs::FileTimes::new().set_modified(at(5_000))).unwrap();
    settle(&from, None).unwrap();
    assert_eq!(mtime(&installed), at(5_000));
    assert!(tools.join("ty").exists(), "nothing changed, nothing removed");

    // Another `ay` (Cargo's, unrelinked since long ago) arrives now, newer than any run
    // that recorded P; the tools that recorded P go, one that records A stays.
    restore("targo", Some(a));
    let built = produced("cargo-ay", a);
    settle(&built, None).unwrap();
    assert_eq!(fs::read(&installed).unwrap(), a);
    assert!(mtime(&installed) > at(5_000));
    assert!(!tools.join("ty").exists() && !bin.join("ty").exists(), "ty recorded P");
    assert!(tools.join("targo").exists() && bin.join("cargo").exists(), "targo records A");

    // And back to P: newer again, never the pack's own time.
    helpers::set_file_times(&record, fs::FileTimes::new().set_modified(at(7_000))).unwrap();
    settle(&from, Some(&sha256(p))).unwrap();
    assert_eq!(fs::read(&installed).unwrap(), p);
    assert!(mtime(&installed) > at(7_000));
    assert!(!tools.join("targo").exists(), "targo recorded A");

    // A source that is not the file the decision read installs nothing.
    let error = settle(&built, Some(&sha256(p))).unwrap_err();
    assert!(error.to_string().contains("changed while it was taken"), "{error}");
    assert_eq!(fs::read(&installed).unwrap(), p);

    // A taken battery is copied, never linked into its pack, and only as sealed.
    let taken = produced("pack-ty", b"ty");
    let into = tools.join("ty");
    copy_taken_verifier_tool(&taken, &sha256(b"ty"), &into).unwrap();
    assert_eq!(fs::read(&into).unwrap(), b"ty");
    assert_ne!(fs::metadata(&into).unwrap().ino(), fs::metadata(&taken).unwrap().ino());
    let error = copy_taken_verifier_tool(&taken, &sha256(b"other"), &into).unwrap_err();
    assert!(error.to_string().contains("changed while it was taken"), "{error}");
}
