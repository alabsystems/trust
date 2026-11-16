//! Private produced-Targo build/check entry. Startup authenticates the actual
//! parent-bank continuation before normal Cargo configuration or queries.
use crate::{
    ops,
    util::{CargoResult, Filesystem, GlobalContext},
    workspace::Workspace,
};
use anyhow::Context as _;
use std::ffi::OsString;
use std::os::unix::ffi::{OsStrExt as _, OsStringExt as _};
use std::sync::Arc;
use std::time::Instant;
use trust_resource_controller::workload::host::coordinator::{Mode, Plan, STARTUP_ARGUMENT};

pub fn requested(args: &[OsString]) -> bool {
    args.first()
        .is_some_and(|argument| argument == STARTUP_ARGUMENT)
}
pub fn run(
    args: &[OsString],
    bootstrap: crate::workload_service::Bootstrap,
    configure_lane: impl FnOnce() -> CargoResult<()>,
) -> CargoResult<()> {
    let entered = Instant::now();
    let bytes = args
        .iter()
        .map(|arg| arg.as_bytes().to_vec())
        .collect::<Vec<_>>();
    let plan = Plan::from_startup_args(&bytes)?;
    let startup = crate::resource_v3::candidate_coordinator::startup::prepare(
        plan.clone(),
        bootstrap,
        entered,
    )?;
    let original = startup
        .candidate
        .as_ref()
        .context("candidate startup lost its actual originals")?;
    configure_lane()?;
    let path = |bytes: &[u8]| std::path::PathBuf::from(OsString::from_vec(bytes.to_vec()));
    let manifest = path(&plan.manifest.path);
    let mut gctx = GlobalContext::new(
        cargo_util_terminal::Shell::new(),
        manifest
            .parent()
            .context("candidate manifest has no parent")?
            .into(),
        path(&plan.cargo_home),
    );
    configure_context(&mut gctx, &plan)?;
    original.check()?;
    let workspace = selected_workspace(&gctx, &plan)?;
    let options = compile_options(&gctx, &plan)?;
    let compiled = ops::compile(&workspace, &options);
    let post = original.finish();
    // Retain the original Cargo/compiler error alongside a failed bookend.
    // Neither successful waiting nor a report returns the parent bank's loan.
    match (compiled, post) {
        (Ok(_), Ok(())) => Ok(()),
        (Err(error), Ok(())) => Err(error),
        (Ok(_), Err(error)) => Err(error.context("candidate original postcheck failed")),
        (Err(error), Err(post)) => Err(error.context(format!(
            "candidate original postcheck also failed: {post:#}"
        ))),
    }
}

/// The same selected CLI configuration is used by the actual child and its
/// independent parent. These functions create no execution runtime or Layout.
pub(super) fn configure_context(gctx: &mut GlobalContext, plan: &Plan) -> CargoResult<()> {
    let target = std::path::PathBuf::from(OsString::from_vec(plan.output_root.clone()));
    gctx.configure(
        0,
        false,
        Some("never"),
        false,
        true,
        true,
        &Some(target),
        &[],
        &[],
    )
}
pub(super) fn selected_workspace<'gctx>(
    gctx: &'gctx GlobalContext,
    plan: &Plan,
) -> CargoResult<Workspace<'gctx>> {
    let manifest = std::path::PathBuf::from(OsString::from_vec(plan.manifest.path.clone()));
    let target = std::path::PathBuf::from(OsString::from_vec(plan.output_root.clone()));
    let mut workspace = Workspace::new(&manifest, gctx)?;
    workspace.set_target_dir(Filesystem::new(target));
    Ok(workspace)
}
pub(super) fn compile_options(
    gctx: &GlobalContext,
    plan: &Plan,
) -> CargoResult<ops::CompileOptions> {
    let intent = match plan.mode {
        Mode::Build => super::UserIntent::Build,
        Mode::Check => super::UserIntent::Check { test: false },
    };
    let mut options = ops::CompileOptions::new(gctx, intent)?;
    options.build_config.jobs = 1;
    options.spec = ops::Packages::Packages(vec![plan.package.clone()]);
    options.cli_features =
        crate::resolver::features::CliFeatures::from_command_line(&plan.features, false, true)?;
    options.filter = ops::CompileFilter::from_raw_arguments(
        false,
        vec![plan.binary.clone()],
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
        false,
    );
    Ok(options)
}

/// Structural selection checks precede ANY Layout acquisition or producing
/// dispatch. The shared parent/child semantic projection must additionally
/// compare the actual configuration and full coverage; plan bytes alone are
/// not that authority.
pub(crate) fn validate_graph(
    runner: &super::BuildRunner<'_, '_>,
    original: &Arc<crate::resource_v3::candidate_coordinator::Original>,
) -> CargoResult<()> {
    let bcx = runner.bcx;
    original.check()?;
    let plan = &original.originals.observation().plan;
    anyhow::ensure!(
        bcx.jobs() == 1 && bcx.roots.len() == 1 && !bcx.unit_graph.is_empty(),
        "candidate requires one selected binary and serial nonempty native graph"
    );
    anyhow::ensure!(
        bcx.rustc().wrapper.is_none()
            && bcx.rustc().workspace_wrapper.is_none()
            && bcx.extra_compiler_args.values().all(Vec::is_empty),
        "candidate refuses compiler wrappers and extra arguments"
    );
    let root = &bcx.roots[0];
    anyhow::ensure!(
        root.pkg.name().as_str() == plan.package
            && root.target.name() == plan.binary
            && root.target.is_bin(),
        "candidate selected a different original binary"
    );
    for unit in bcx.unit_graph.keys() {
        anyhow::ensure!(
            unit.kind == super::CompileKind::Host
                && !unit.target.proc_macro()
                && !unit.target.is_custom_build()
                && matches!(
                    unit.mode,
                    super::CompileMode::Build | super::CompileMode::Check { test: false }
                ),
            "candidate refuses build scripts, proc macros and non-native/non-compile actions"
        );
        anyhow::ensure!(
            original
                .sources
                .iter()
                .any(|source| source.path() == unit.pkg.root()),
            "candidate dependency is outside original selected sources"
        );
    }
    let path = |bytes: &[u8]| std::path::PathBuf::from(OsString::from_vec(bytes.to_vec()));
    let sources = plan
        .sources
        .iter()
        .map(|source| path(&source.root))
        .collect::<Vec<_>>();
    let manifest = path(&plan.manifest.path);
    let output = path(&plan.output_root);
    let cargo_home = path(&plan.cargo_home);
    let sdk = path(&plan.sdk_root);
    let compiler = path(&plan.compiler.path);
    let selected = super::candidate_semantics::Selected {
        mode: match plan.mode {
            Mode::Build => super::candidate_semantics::Mode::Build,
            Mode::Check => super::candidate_semantics::Mode::Check,
        },
        sources: &sources,
        manifest: &manifest,
        package: &plan.package,
        binary: &plan.binary,
        output_root: &output,
        cargo_home: &cargo_home,
        sdk_root: &sdk,
        compiler: &compiler,
        compiler_sha256: plan.compiler.sha256,
    };
    super::candidate_semantics::validate_child(
        runner,
        &selected,
        original.originals.observation().configuration_sha256,
        original.originals.observation().coverage_sha256,
    )?;
    original.check()?;
    Ok(())
}
