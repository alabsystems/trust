//! Trust: initial enforced compiler action boundary. No shared-cache authority.

use super::{BuildRunner, Unit};
use crate::CargoResult;
use cargo_util::{ActionSandbox, ProcessBuilder};
use std::path::Path;

pub(super) fn apply(
    build: &BuildRunner<'_, '_>,
    unit: &Unit,
    command: &mut ProcessBuilder,
) -> CargoResult<()> {
    if !build.bcx.confines(unit) {
        return Ok(());
    }
    let environment = build
        .bcx
        .action_environment
        .as_ref()
        .ok_or_else(|| anyhow::anyhow!("confined action has no captured environment"))?;
    command.environment_snapshot(environment.clone());
    // Confined library actions have a file input, never an ambient stdin
    // dependency. A closed empty pipe gives that input a fixed identity.
    command.stdin(Vec::new());
    if build.bcx.shared_dependency_units.contains(unit) {
        // An unrelated workspace's proc-macro search paths must not become
        // inputs of a pure shared dependency that cannot load proc macros.
        let mut libraries = crate::util::process_authority::verified_tool_runtime_library_paths(
            &build.bcx.rustc().path,
        )?;
        libraries.push(std::path::PathBuf::from("/usr/lib"));
        command.env(
            cargo_util::paths::dylib_path_envvar(),
            std::env::join_paths(libraries)?,
        );
    }
    let mut sandbox = ActionSandbox::new();
    let compiler_inputs = build.bcx.rustc().compiler_inputs()?;
    for path in &compiler_inputs.files {
        sandbox.read_file(path)?;
    }
    for path in &compiler_inputs.executables {
        sandbox.executable(path)?;
    }
    for path in compiler_inputs.directories() {
        sandbox.read_directory_entry(path)?;
    }
    sandbox.read_directory(unit.pkg.root())?;
    let cwd = command
        .get_cwd()
        .map(Path::new)
        .unwrap_or_else(|| build.bcx.gctx.cwd());
    sandbox.read_directory_entry(cwd)?;
    for path in cargo_util::PLATFORM_READ_DIRECTORIES {
        sandbox.read_directory(Path::new(path))?;
    }
    for path in cargo_util::PLATFORM_READ_FILES {
        sandbox.read_file(Path::new(path))?;
    }
    let mut seen = crate::util::data_structures::HashSet::default();
    let mut pending = vec![unit.clone()];
    while let Some(current) = pending.pop() {
        if !seen.insert(current.clone()) {
            continue;
        }
        sandbox.read_directory(current.pkg.root())?;
        let output = build.files().output_dir(&current);
        std::fs::create_dir_all(&output)?;
        sandbox.read_directory(&output)?;
        pending.extend(build.unit_deps(&current).iter().map(|dep| dep.unit.clone()));
    }
    let output = build.files().output_dir(unit);
    sandbox.write_directory(&output)?;
    // Per-action scratch, never the user's ambient temporary directory.
    let scratch = output.join("scratch");
    std::fs::create_dir_all(&scratch)?;
    command.env("TMPDIR", &scratch);
    command.env("TMP", &scratch);
    command.env("TEMP", &scratch);
    command.action_sandbox(sandbox)?;
    Ok(())
}
