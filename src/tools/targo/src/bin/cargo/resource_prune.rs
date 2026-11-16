//! Native manual pruning of this original fixed job's Bootstrap caches.

use std::ffi::OsString;
use std::io::Write as _;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{Context as _, Result, ensure};
use clap::{Arg, ArgAction};
use trust_build_tree::trust_output_lock::OutputLock;
use trust_build_tree::trust_repo_lock::management::{Acquire, Kind, LeaseAcquisition, Manager};

pub(super) fn help_command() -> clap::Command {
    clap::Command::new("repo-prune")
        .about("Maintain Bootstrap caches under original native ownership")
        .after_help("Run through `targo --unverified resource fixed -- repo-prune ...`. A preview deletes nothing and writes no cleanup stamp; it retains the same real repository/output/Cargo exclusion as removal.")
        .arg(Arg::new("repo-root").long("repo-root").value_parser(clap::value_parser!(PathBuf)))
        .arg(Arg::new("host").long("host").required_unless_present("tool-target-trees").value_parser(clap::value_parser!(PathBuf)))
        .arg(Arg::new("dry-run").long("dry-run").action(ArgAction::SetTrue))
        .arg(Arg::new("dead-variants").long("dead-variants").action(ArgAction::SetTrue))
        .arg(Arg::new("rlib-objects").long("rlib-objects").action(ArgAction::SetTrue))
        .arg(Arg::new("tool-target-trees").long("tool-target-trees").action(ArgAction::SetTrue).conflicts_with_all(["dead-variants","rlib-objects"]).help("Reclaim whole tool targets, safe interrupted reclaims, old private sysroots and scratch"))
        .arg(Arg::new("seed-tools-only").long("seed-tools-only").action(ArgAction::SetTrue).requires("tool-target-trees").conflicts_with("rustc-caches").help("Explicit tools-before-compiler profile: genuine contained stage0 health and BOTH later stages absent; tool targets only"))
        .arg(Arg::new("rustc-caches").long("rustc-caches").action(ArgAction::SetTrue).requires("tool-target-trees").help("Also reclaim compiler targets; the next compiler build starts cold"))
}

#[expect(
    clippy::disallowed_methods,
    reason = "validate live original Host, SDK and Manager advertisements before pruning; configured environment values cannot replace their native owners"
)]
pub(super) fn run(
    args: &[OsString],
    input: Option<super::resource_fixed::NestedInput>,
) -> Result<i32> {
    if args.len() == 1 && (args[0] == "--help" || args[0] == "-h") {
        help_command().print_help()?;
        let mut output = std::io::stdout().lock();
        writeln!(output)?;
        output.flush()?;
        return Ok(0);
    }
    let options = help_command().try_get_matches_from(
        std::iter::once(OsString::from("repo-prune")).chain(args.iter().cloned()),
    )?;
    let whole = options.get_flag("tool-target-trees");
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    if whole {
        anyhow::bail!(
            "native contained cache-version probes are unavailable on this target; no cache work started"
        );
    }
    // Locators and numbers cannot replace this early native-entry capture.
    let original = match input.context("repo-prune requires its original native fixed admission")? {
        super::resource_fixed::NestedInput::Direct(early) => early.capture()?,
        super::resource_fixed::NestedInput::Courier(advertisement) => {
            trust_build_tree::admission::InheritedFixedClaim::from_descendant(&advertisement)?
        }
    };
    for name in [
        "ATERM_RESOURCE_JOB_V3",
        "ATERM_SDK_LEASE_V3",
        "TRUST_BUILD_LOCK_TOKEN",
    ] {
        ensure!(
            std::env::var_os(name).is_none(),
            "repo-prune cannot replace original {name}"
        );
    }
    let root = options
        .get_one::<PathBuf>("repo-root")
        .cloned()
        .unwrap_or(std::env::current_dir()?);
    let root = root.canonicalize()?;
    let repository = git2::Repository::discover(&root)?;
    ensure!(
        repository
            .workdir()
            .context("repo-prune needs an actual worktree")?
            .canonicalize()?
            == root,
        "repo-prune root must be this actual repository's top-level directory"
    );
    let worktree = repository.path().canonicalize()?.join("build-slot.lock");
    original.check_nested(original.budget()?, Some(&worktree), false)?;
    let variants = options.get_flag("dead-variants");
    let objects = options.get_flag("rlib-objects");
    let lease = match Manager::open(&root)?.acquire_lease(&Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "native manual Bootstrap cache pruning".into(),
        contract: "retain original repository and output ownership through all cache work".into(),
        wait: Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    })? {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => anyhow::bail!("repository is held; no cache pruning started"),
    };
    // Acquire real repository exclusion BEFORE reading its config namespace.
    // The retained selection supplies DATA only; this actual existing lock
    // remains the sole output exclusion owner, with no creation/alias fallback.
    let selection = bootstrap::cache::SelectedOutput::capture(&root).map_err(anyhow::Error::msg)?;
    let output_path = selection.output().to_owned();
    let output = OutputLock::try_acquire_existing(&output_path)
        .with_context(|| {
            format!(
                "cannot open existing original output lock at {}",
                output_path.display()
            )
        })?
        .context("output is held; no cache pruning started")?;
    selection.check_current().map_err(anyhow::Error::msg)?;
    original.check_current()?;
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if whole {
        let host = match options.get_one::<PathBuf>("host") {
            Some(host) => host.clone(),
            None => PathBuf::from(
                bootstrap::cache::WholeRequest::detect_host(&selection, &output)
                    .map_err(anyhow::Error::msg)?,
            ),
        };
        let request = bootstrap::cache::WholeRequest::from_selection(
            selection,
            &host,
            options.get_flag("rustc-caches"),
            options.get_flag("dry-run"),
        )
        .and_then(|request| {
            request.with_profile(if options.get_flag("seed-tools-only") {
                bootstrap::cache::WholeProfile::SeedTools
            } else {
                bootstrap::cache::WholeProfile::Compilers
            })
        })
        .map_err(anyhow::Error::msg)?;
        let context = crate::GlobalContext::default()?;
        let scheduler = context
            .jobserver_from_env()?
            .context("whole-tree reclaim requires its SAME original GNU transport")?
            .clone();
        // SAFETY: original main imported this same scheduler once; original
        // fixed/worktree validation above succeeded, the actual outer group
        // owner stays alive, and probes serialize its implicit continuation.
        let mut owner = unsafe {
            trust_build_tree::admission::cache_probe::Owner::new(
                original,
                scheduler,
                lease,
                output,
                root.clone(),
                worktree,
            )?
        };
        let report = bootstrap::cache::reclaim(&request, &mut owner).map_err(anyhow::Error::msg)?;
        let mut output = std::io::stdout().lock();
        serde_json::to_writer_pretty(&mut output, &report)?;
        writeln!(output)?;
        output.flush()?;
        return Ok(i32::from(!report.is_complete()));
    }
    let request = bootstrap::cache::Request::from_selection(
        selection,
        options
            .get_one::<PathBuf>("host")
            .expect("required host for unit pruning"),
        variants,
        objects,
        options.get_flag("dry-run"),
    )
    .map_err(anyhow::Error::msg)?;
    let report = bootstrap::cache::prune(&request, &lease, &output).map_err(anyhow::Error::msg)?;
    original.check_current()?;
    let mut stdout = std::io::stdout().lock();
    serde_json::to_writer_pretty(&mut stdout, &report)?;
    writeln!(stdout)?;
    stdout.flush()?;
    Ok(i32::from(!report.is_complete()))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn seed_profile_requires_explicit_tools_and_cannot_select_compiler_targets() {
        assert!(
            help_command()
                .try_get_matches_from(["repo-prune", "--seed-tools-only", "--host", "host"])
                .is_err()
        );
        assert!(
            help_command()
                .try_get_matches_from([
                    "repo-prune",
                    "--tool-target-trees",
                    "--seed-tools-only",
                    "--rustc-caches"
                ])
                .is_err()
        );
        let request = help_command()
            .try_get_matches_from([
                "repo-prune",
                "--tool-target-trees",
                "--seed-tools-only",
                "--dry-run",
            ])
            .unwrap();
        assert!(request.get_flag("seed-tools-only"));
        assert!(!request.get_flag("rustc-caches"));
        assert!(
            !help_command()
                .try_get_matches_from(["repo-prune", "--tool-target-trees"])
                .unwrap()
                .get_flag("seed-tools-only")
        );
    }
}
