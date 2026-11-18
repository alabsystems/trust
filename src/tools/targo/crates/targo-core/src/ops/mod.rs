use crate::sources::CRATES_IO_DOMAIN;

pub use self::cargo_clean::{CleanContext, CleanOptions, clean};
pub use self::cargo_compile::unit_generator::{
    NativeTestArgumentScope, NativeTestRunnerScope, UnitGenerator, native_test_argument_scope,
    native_test_runner_scope,
};
pub use self::cargo_compile::{CompileFilter, FilterRule, LibRule, Packages};
pub use self::cargo_compile::{
    CompileOptions, compile, compile_with_exec, create_bcx, print, resolve_all_features,
};
pub use self::cargo_doc::{DocOptions, OutputFormat, doc};
pub use self::cargo_fetch::{FetchOptions, fetch};
pub use self::cargo_fix::{EditionFixMode, FixOptions, fix, fix_edition, fix_exec_rustc};
pub use self::cargo_install::{install, install_list};
pub use self::cargo_metadata::{ExportInfo, OutputMetadataOptions, output_metadata};
pub use self::cargo_new::{NewOptions, NewProjectKind, init, new};
pub use self::cargo_package::PackageMessageFormat;
pub use self::cargo_package::PackageOpts;
pub use self::cargo_package::check_yanked;
pub use self::cargo_package::package;
pub use self::cargo_pkgid::pkgid;
pub use self::cargo_read_manifest::read_package;
pub use self::cargo_report::rebuilds::ReportRebuildsOptions;
pub use self::cargo_report::rebuilds::report_rebuilds;
// Trust: strict, bounded observational cache-work reports.
pub use self::cargo_report::cache_work::{ReportCacheWorkOptions, report_cache_work};
pub use self::cargo_report::execution::{ReportExecutionOptions, report_execution};
pub use self::cargo_report::sessions::ReportSessionsOptions;
pub use self::cargo_report::sessions::report_sessions;
pub use self::cargo_report::timings::ReportTimingsOptions;
pub use self::cargo_report::timings::report_timings;
pub use self::cargo_run::run;
pub use self::cargo_test::{
    NativeTestBudgetRefusal, TestOptions, run_benches, run_tests, try_run_prepared_tests,
    validate_native_test_arguments,
};
// Trust: `targo test --plan`.
pub use self::cargo_test::plan as test_plan;
// Trust: a plan's unit graph against its requests' standalone graphs.
pub use self::cargo_test::plan_parity as test_plan_parity;
// Trust: a plan's phases outside the invocation's workspace.
pub use self::cargo_test::plan_phases as test_plan_phases;
// Trust: a plan run's selection, for the refusal the CLI maps to exit 2.
pub use self::cargo_test::plan_select as test_plan_select;
// Trust: a plan run's exit status and closing record.
pub use self::cargo_test::plan_outcome as test_plan_outcome;
pub use self::cargo_uninstall::uninstall;
pub use self::cargo_update::UpdateOptions;
pub use self::cargo_update::generate_lockfile;
pub use self::cargo_update::print_lockfile_changes;
pub use self::cargo_update::update_lockfile;
pub use self::cargo_vendor::{VendorOptions, vendor, vendor_cohort_check, vendor_cohort_plan};
pub use self::common_for_install_and_uninstall::{InstallTracker, resolve_root};
// Trust: `fix_get_proxy_lock_addr` is deliberately absent — the fix proxy is
// entered through the authenticated `prepare_fix_proxy_dispatch` handoff
// instead, so the ambient-marker entry point must not remain reachable.
pub use self::cargo_fix::{prepare_fix_proxy_dispatch, seal_targo_fix_proxy_handoff};
pub use self::lockfile::{load_pkg_lockfile, resolve_to_string, write_pkg_lockfile};
pub use self::registry::OwnersOptions;
pub use self::registry::PublishOpts;
pub use self::registry::RegistryCredentialConfig;
pub use self::registry::RegistryOrIndex;
pub use self::registry::info;
pub use self::registry::modify_owners;
pub use self::registry::publish;
pub use self::registry::registry_login;
pub use self::registry::registry_logout;
pub use self::registry::search;
pub use self::registry::yank;
pub use self::resolve::{
    WorkspaceResolve, add_overrides, get_resolved_packages, resolve_with_previous, resolve_ws,
    resolve_ws_with_opts,
};

pub mod cargo_add;
mod cargo_clean;
pub(crate) mod cargo_compile;
pub mod cargo_config;
mod cargo_doc;
mod cargo_fetch;
mod cargo_fix;
mod cargo_install;
mod cargo_metadata;
mod cargo_new;
mod cargo_package;
mod cargo_pkgid;
mod cargo_read_manifest;
pub mod cargo_remove;
pub(crate) mod cargo_report;
mod cargo_run;
pub(crate) mod cargo_test;
pub mod cargo_tree;
mod cargo_uninstall;
mod cargo_update;
mod cargo_vendor;
#[cfg(unix)]
pub mod checkout_inputs;
mod common_for_install_and_uninstall;
pub(crate) mod lockfile;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod paired_qualification;
pub(crate) mod registry;
pub(crate) mod resolve;

/// Returns true if the dependency is either git or path, false otherwise
/// Error if a git/path dep is transitive, but has no version (registry source).
/// This check is performed on dependencies before publishing or packaging
fn check_dep_has_version(
    dep: &crate::workspace::Dependency,
    publish: bool,
) -> crate::CargoResult<bool> {
    let which = if dep.source_id().is_path() {
        "path"
    } else if dep.source_id().is_git() {
        "git"
    } else {
        return Ok(false);
    };

    if !dep.specified_req() && dep.is_transitive() {
        let dep_version_source = dep.registry_id().map_or_else(
            || CRATES_IO_DOMAIN.to_string(),
            |registry_id| registry_id.display_registry_name(),
        );
        anyhow::bail!(
            "all dependencies must have a version requirement specified when {}.\n\
             dependency `{}` does not specify a version\n\
             Note: The {} dependency will use the version from {},\n\
             the `{}` specification will be removed from the dependency declaration.",
            if publish { "publishing" } else { "packaging" },
            dep.package_name(),
            if publish { "published" } else { "packaged" },
            dep_version_source,
            which,
        )
    }
    Ok(true)
}
