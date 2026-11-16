//! Trust: compiler-owned lifecycle controls using actual source and codegen.
//!
//! Bootstrap supplies the matching sysroot. Every world is retained, including
//! failed native links; no installed SDK, tool wrapper or model compiler is used.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::{AtomicU64, Ordering};

use trust_fs_observation::tool_lookup::{DEP_INFO_PREFIX, ToolInputs, UNAVAILABLE};

static NEXT_WORLD: AtomicU64 = AtomicU64::new(0);

fn world() -> PathBuf {
    let stamp =
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let world = std::env::temp_dir().join(format!(
        "trust-tool-inputs-unit-{}-{stamp}-{}",
        std::process::id(),
        NEXT_WORLD.fetch_add(1, Ordering::Relaxed),
    ));
    let mut builder = std::fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder.create(&world).unwrap();
    eprintln!("retained compiler tool-input world: {}", world.display());
    world
}

struct Probe {
    deps: PathBuf,
    expected_early: Option<bool>,
    stop: bool,
    analyzed: bool,
}

impl crate::Callbacks for Probe {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        _: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> crate::Compilation {
        assert_eq!(Some(self.deps.exists()), self.expected_early);
        assert!(!self.analyzed);
        self.analyzed = true;
        if self.stop { crate::Compilation::Stop } else { crate::Compilation::Continue }
    }
}

fn compile(world: &Path, extra: &[&str], expected_early: Option<bool>, stop: bool) -> ExitCode {
    let sysroot = std::env::var_os("TEST_SYSROOT")
        .map(PathBuf::from)
        .expect("run through x.py test compiler/rustc_driver_impl (TEST_SYSROOT)");
    assert!(sysroot.is_dir(), "canonical TEST_SYSROOT is missing");
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/tests/tool_inputs_subject.rs");
    assert!(source.is_file());
    let deps = world.join("subject.d");
    let emit = extra.iter().find_map(|arg| arg.strip_prefix("--emit=")).unwrap_or("dep-info,link");
    let emit = emit
        .split(',')
        .map(|kind| {
            if kind == "dep-info" {
                format!("dep-info={}", deps.display())
            } else {
                kind.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join(",");
    let mut args = vec![
        "trustc-tool-inputs-unit".into(),
        source.to_str().unwrap().into(),
        "--sysroot".into(),
        sysroot.to_str().unwrap().into(),
        "--edition=2024".into(),
        "--crate-name=tool_inputs_subject".into(),
        "-Ztrust-verify=off".into(),
        "-Ztrust-ir-lower=no".into(),
        "-Cdebuginfo=0".into(),
        "--out-dir".into(),
        world.to_str().unwrap().into(),
        format!("--emit={emit}"),
    ];
    args.extend(
        extra.iter().filter(|arg| !arg.starts_with("--emit=")).map(|arg| (*arg).to_owned()),
    );
    std::fs::write(world.join("compiler-args.txt"), args.join("\n")).unwrap();
    std::thread::Builder::new()
        .stack_size(128 * 1024 * 1024)
        .spawn(move || {
            let mut probe = Probe { deps, expected_early, stop, analyzed: false };
            // This crate-private dispatch is the executable's canonical route.
            // The public embedded frontend intentionally rejects evidence data
            // controls and cannot qualify this producer by setting a callback.
            let status = crate::catch_with_exit_code(|| {
                crate::run_compiler_with_argfile_mode(
                    &args,
                    &mut probe,
                    false,
                    crate::FrontendTrustPolicy::CanonicalTrustc,
                );
            });
            assert_eq!(probe.analyzed, expected_early.is_some());
            status
        })
        .unwrap()
        .join()
        .unwrap()
}

fn terminal(world: &Path) -> String {
    let deps = std::fs::read_to_string(world.join("subject.d")).unwrap();
    let markers: Vec<_> =
        deps.lines().filter_map(|line| line.strip_prefix(DEP_INFO_PREFIX)).collect();
    assert_eq!(markers.len(), 1, "one complete terminal marker: {deps}");
    markers[0].to_owned()
}

#[test]
fn tool_inputs_deferred_no_link_and_legacy_timing_use_actual_compiler_phases() {
    let late = world();
    assert_eq!(
        compile(&late, &["-Ztrust-tool-inputs", "--emit=dep-info,metadata"], Some(false), false),
        ExitCode::SUCCESS
    );
    assert!(ToolInputs::decode(terminal(&late).as_bytes()).unwrap().records().is_empty());
    assert!(late.join("libtool_inputs_subject.rmeta").is_file());

    let legacy = world();
    assert_eq!(
        compile(&legacy, &["--emit=dep-info,metadata"], Some(true), false),
        ExitCode::SUCCESS
    );
    let deps = std::fs::read_to_string(legacy.join("subject.d")).unwrap();
    assert!(!deps.contains(DEP_INFO_PREFIX), "the disabled default must retain its original bytes");

    let callback = world();
    assert_eq!(
        compile(&callback, &["-Ztrust-tool-inputs", "--emit=dep-info,metadata"], Some(false), true),
        ExitCode::SUCCESS
    );
    assert_eq!(terminal(&callback), UNAVAILABLE);

    let deps_only = world();
    assert_eq!(
        compile(&deps_only, &["-Ztrust-tool-inputs", "--emit=dep-info"], None, false),
        ExitCode::SUCCESS
    );
    assert_eq!(terminal(&deps_only), UNAVAILABLE);

    let no_analysis = world();
    assert_eq!(
        compile(&no_analysis, &["-Ztrust-tool-inputs", "-Zno-analysis"], None, false),
        ExitCode::SUCCESS
    );
    assert_eq!(terminal(&no_analysis), UNAVAILABLE);
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn tool_inputs_native_launch_and_failed_link_use_the_actual_driver_and_wait() {
    let linked = world();
    assert_eq!(compile(&linked, &["-Ztrust-tool-inputs"], Some(false), false), ExitCode::SUCCESS);
    let observation = terminal(&linked);
    // Trust: successful Apple SDK discovery cannot report reusable inputs.
    // The separate real-SDKROOT producer pair requires an available native
    // link without discovery, so always-unavailable Darwin is not a positive.
    let unavailable_discovery = cfg!(target_os = "macos") && observation == UNAVAILABLE;
    if !unavailable_discovery {
        let inputs = ToolInputs::decode(observation.as_bytes()).expect(
            "this native qualification needs a supported actual local native linker profile",
        );
        assert!(
            !inputs.records().is_empty(),
            "a real native link must not report the no-link envelope"
        );
    }
    let output = std::process::Command::new(linked.join("tool_inputs_subject")).output().unwrap();
    assert!(output.status.success());
    assert_eq!(output.stdout, b"7\n");
    std::fs::write(linked.join("program.stdout"), output.stdout).unwrap();
    std::fs::write(linked.join("program.stderr"), output.stderr).unwrap();

    let failed = world();
    let missing_linker = format!("-Clinker={}", failed.join("absent-native-linker").display());
    assert_ne!(
        compile(&failed, &["-Ztrust-tool-inputs", &missing_linker], Some(false), false),
        ExitCode::SUCCESS
    );
    assert!(
        !failed.join("subject.d").exists(),
        "failed linking must not publish newly completed dep-info"
    );
}
