//! Handles the vendoring process for the bootstrap system.
//!
//! This module ensures that all required Cargo dependencies are gathered
//! and stored in the `<src>/<VENDOR_DIR>` directory.
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};

use crate::core::builder::{Builder, RunConfig, ShouldRun, Step};
use crate::t;
use crate::utils::exec::command;

/// The name of the directory where vendored dependencies are stored.
pub const VENDOR_DIR: &str = "vendor";

/// Returns the cargo workspaces to vendor for `x vendor` and dist tarballs.
///
/// Returns a `Vec` of `(path_to_manifest, submodules_required)` where
/// `path_to_manifest` is the cargo workspace, and `submodules_required` is
/// the set of submodules that must be available.
pub fn default_paths_to_vendor(builder: &Builder<'_>) -> Vec<(PathBuf, Vec<&'static str>)> {
    let paths: Vec<(&str, Vec<&'static str>)> = vec![
        ("src/tools/targo/Cargo.toml", vec!["src/tools/targo"]),
        ("targo-trust/Cargo.toml", vec![]),
        ("src/tools/tippy/clippy_test_deps/Cargo.toml", vec![]),
        ("src/tools/rust-analyzer/Cargo.toml", vec![]),
        ("library/Cargo.toml", vec![]),
        ("library/stdarch/Cargo.toml", vec![]),
        ("src/bootstrap/Cargo.toml", vec![]),
        ("src/tools/rustbook/Cargo.toml", vec![]),
        ("src/tools/opt-dist/Cargo.toml", vec![]),
    ];

    paths.into_iter().map(|(path, submodules)| (builder.src.join(path), submodules)).collect()
}

/// Defines the vendoring step in the bootstrap process.
///
/// This step executes `cargo vendor` to collect all dependencies
/// and store them in the `<src>/<VENDOR_DIR>` directory.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub(crate) struct Vendor {
    /// Additional paths to synchronize during vendoring.
    pub(crate) sync_args: Vec<PathBuf>,
    /// Determines whether vendored dependencies use versioned directories.
    pub(crate) versioned_dirs: bool,
    /// The root directory of the source code.
    ///
    /// Vendored dependencies will be stored in <root_dir>/vendor and
    /// <root_dir>/library/vendor unless overridden by `output_dir`.
    pub(crate) root_dir: PathBuf,
    /// The root directory for storing vendored dependencies in <output_dir>/vendor
    /// and <output_dir>/library/vendor.
    pub(crate) output_dir: Option<PathBuf>,
    /// Only vendor crates necessary by the library workspace.
    pub(crate) only_library_workspace: bool,
}

impl Step for Vendor {
    type Output = VendorOutput;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("placeholder")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Vendor {
            sync_args: run.builder.config.cmd.vendor_sync_args(),
            versioned_dirs: run.builder.config.cmd.vendor_versioned_dirs(),
            root_dir: run.builder.src.clone(),
            output_dir: None,
            only_library_workspace: false,
        });
    }

    /// Executes the vendoring process.
    ///
    /// This function runs `cargo vendor` and ensures all required submodules
    /// are initialized before vendoring begins.
    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let _guard = builder.group(&format!("Vendoring sources to {:?}", self.root_dir));
        let root_dir = self.root_dir.clone();

        // Trust: `default_paths_to_vendor` (and any explicit `--sync` args) yields
        // manifest paths rooted at `builder.src`; remap them onto `root_dir` so
        // `x vendor` / `x dist` can vendor a source tree rooted somewhere other than
        // the in-tree checkout (e.g. the copied dist source under `dst_src`).
        let map_to_root_dir = |path: PathBuf| {
            path.strip_prefix(&builder.src).map(|relative| root_dir.join(relative)).unwrap_or(path)
        };

        let config = if self.only_library_workspace {
            String::new()
        } else {
            let mut cmd = command(&builder.initial_cargo);
            cmd.arg("vendor");

            if self.versioned_dirs {
                cmd.arg("--versioned-dirs");
            }

            let to_vendor = default_paths_to_vendor(builder);
            // These submodules must be present for `x vendor` to work.
            for (_, submodules) in &to_vendor {
                for submodule in submodules {
                    builder.build.require_submodule(submodule, None);
                }
            }

            // Sync these paths by default.
            for (p, _) in &to_vendor {
                cmd.arg("--sync").arg(map_to_root_dir(p.clone()));
            }

            // Also sync explicitly requested paths.
            for sync_arg in self.sync_args {
                cmd.arg("--sync").arg(map_to_root_dir(sync_arg));
            }

            // Reuse vendored dependencies when building source tarball for offline support.
            if builder.config.vendor {
                cmd.arg("--respect-source-config")
                    .arg("--config")
                    .arg(builder.src.join(".cargo").join("config.toml"));
            }

            // Will read the libstd Cargo.toml
            // which uses the unstable `public-dependency` feature.
            cmd.env("RUSTC_BOOTSTRAP", "1");
            cmd.env("RUSTC", &builder.initial_rustc);

            cmd.current_dir(&root_dir);
            // Trust: keep the concrete output path so we can prune the vendored tree
            // afterwards; this mirrors what `cargo vendor` writes.
            let output_arg = match &self.output_dir {
                None => PathBuf::from(VENDOR_DIR),
                Some(output_dir) => output_dir.join(VENDOR_DIR),
            };
            cmd.arg(&output_arg);

            let stdout = cmd.run_capture_stdout(builder).stdout();
            // Trust: strip vendored `.gitmodules` so the vendored tree carries no
            // submodule wiring of its own.
            prune_vendor_gitmodules(&root_dir, &output_arg);
            stdout
        };

        let mut cmd = command(&builder.initial_cargo);
        cmd.arg("vendor");

        if self.versioned_dirs {
            cmd.arg("--versioned-dirs");
        }

        // Reuse vendored dependencies when building source tarball for offline support.
        if builder.config.vendor {
            cmd.arg("--respect-source-config")
                .arg("--config")
                .arg(builder.src.join("library").join(".cargo").join("config.toml"));
        }

        // Will read the libstd Cargo.toml
        // which uses the unstable `public-dependency` feature.
        cmd.env("RUSTC_BOOTSTRAP", "1");
        cmd.env("RUSTC", &builder.initial_rustc);

        let library_dir = root_dir.join("library");
        cmd.current_dir(&library_dir);
        // Trust: keep the concrete library vendor output path for pruning as well.
        let library_output_arg = match &self.output_dir {
            None => PathBuf::from(VENDOR_DIR),
            Some(output_dir) => output_dir.join("library").join(VENDOR_DIR),
        };
        cmd.arg(&library_output_arg);

        let config_library = cmd.run_capture_stdout(builder).stdout();
        // Trust: strip vendored `.gitmodules` from the library vendor tree too.
        prune_vendor_gitmodules(&library_dir, &library_output_arg);

        VendorOutput { config, config_library }
    }
}

fn prune_vendor_gitmodules(root_dir: &Path, output_dir: &Path) {
    let vendor_root =
        if output_dir.is_absolute() { output_dir.to_path_buf() } else { root_dir.join(output_dir) };
    if !vendor_root.exists() {
        return;
    }

    for entry in walkdir::WalkDir::new(vendor_root).into_iter().filter_map(Result::ok) {
        if entry.file_type().is_file()
            && entry.path().file_name() == Some(OsStr::new(".gitmodules"))
        {
            t!(fs::remove_file(entry.path()));
        }
    }
}

/// Stores the result of the vendoring step.
#[derive(Debug, Clone)]
pub(crate) struct VendorOutput {
    pub(crate) config: String,
    pub(crate) config_library: String,
}
