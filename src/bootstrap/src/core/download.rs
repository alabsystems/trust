use std::collections::{BTreeMap, HashMap};
use std::env;
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, ErrorKind, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

use build_helper::ci::CiEnv;
use build_helper::git::PathFreshness;
use xz2::bufread::XzDecoder;

use crate::core::config::{BUILDER_CONFIG_FILENAME, TargetSelection};
use crate::utils::build_stamp::BuildStamp;
use crate::utils::exec::{ExecutionContext, command};
use crate::utils::helpers::{exe, hex_encode, move_file};
use crate::{Config, t};

static SHOULD_FIX_BINS_AND_DYLIBS: OnceLock<bool> = OnceLock::new();

fn extract_curl_version(out: String) -> semver::Version {
    // The output should look like this: "curl <major>.<minor>.<patch> ..."
    out.lines()
        .next()
        .and_then(|line| line.split(" ").nth(1))
        .and_then(|version| semver::Version::parse(version).ok())
        .unwrap_or(semver::Version::new(1, 0, 0))
}

/// Generic helpers that are useful anywhere in bootstrap.
impl Config {
    pub fn is_verbose(&self) -> bool {
        self.exec_ctx.is_verbose()
    }

    pub(crate) fn create<P: AsRef<Path>>(&self, path: P, s: &str) {
        if self.dry_run() {
            return;
        }
        t!(fs::write(path, s));
    }

    pub(crate) fn remove(&self, f: &Path) {
        remove(&self.exec_ctx, f);
    }

    /// Create a temporary directory in `out` and return its path.
    ///
    /// NOTE: this temporary directory is shared between all steps;
    /// if you need an empty directory, create a new subdirectory inside it.
    pub(crate) fn tempdir(&self) -> PathBuf {
        let tmp = self.out.join("tmp");
        t!(fs::create_dir_all(&tmp));
        tmp
    }

    /// Whether or not `fix_bin_or_dylib` needs to be run; can only be true
    /// on NixOS
    fn should_fix_bins_and_dylibs(&self) -> bool {
        should_fix_bins_and_dylibs(self.patch_binaries_for_nix, &self.exec_ctx)
    }

    /// Modifies the interpreter section of 'fname' to fix the dynamic linker,
    /// or the RPATH section, to fix the dynamic library search path
    ///
    /// This is only required on NixOS and uses the PatchELF utility to
    /// change the interpreter/RPATH of ELF executables.
    ///
    /// Please see <https://nixos.org/patchelf.html> for more information
    fn fix_bin_or_dylib(&self, fname: &Path) {
        fix_bin_or_dylib(&self.out, fname, &self.exec_ctx);
    }

    fn download_file(&self, url: &str, dest_path: &Path, help_on_error: &str) {
        let dwn_ctx: DownloadContext<'_> = self.into();
        download_file(dwn_ctx, &self.out, url, dest_path, help_on_error);
    }

    fn unpack(&self, tarball: &Path, dst: &Path, pattern: &str) {
        unpack(&self.exec_ctx, tarball, dst, pattern);
    }

    /// Returns whether the SHA256 checksum of `path` matches `expected`.
    #[cfg(test)]
    pub(crate) fn verify(&self, path: &Path, expected: &str) -> bool {
        verify(&self.exec_ctx, path, expected)
    }
}

fn recorded_entries(dst: &Path, pattern: &str) -> Option<BufWriter<File>> {
    let name = if pattern == "rustc-dev" {
        ".rustc-dev-contents"
    } else if pattern.starts_with("rust-std") {
        ".rust-std-contents"
    } else {
        return None;
    };
    Some(BufWriter::new(t!(File::create(dst.join(name)))))
}

#[derive(Clone)]
enum DownloadSource {
    CI,
    Dist,
}

#[derive(Debug, PartialEq, Eq)]
struct TargoStage0Download {
    filename: String,
    prefix: String,
    legacy: bool,
}

fn select_stage0_targo_download(
    checksums: &BTreeMap<String, String>,
    date: &str,
    version: &str,
    host: &str,
    component: &str,
) -> TargoStage0Download {
    let legacy_component = match component {
        "targo" => "tcargo",
        "targo-trust" => "tcargo-trust",
        _ => panic!("not a Targo stage0 component: {component}"),
    };

    let canonical_filename = format!("{component}-{version}-{host}.tar.xz");
    let canonical_url = format!("dist/{date}/{canonical_filename}");
    if checksums.contains_key(&canonical_url) {
        return TargoStage0Download {
            filename: canonical_filename,
            prefix: component.to_owned(),
            legacy: false,
        };
    }

    let legacy_filename = format!("{legacy_component}-{version}-{host}.tar.xz");
    let legacy_url = format!("dist/{date}/{legacy_filename}");
    if checksums.contains_key(&legacy_url) {
        return TargoStage0Download {
            filename: legacy_filename,
            prefix: legacy_component.to_owned(),
            legacy: true,
        };
    }

    // Preserve the canonical checksum-miss diagnostic when neither spelling
    // is pinned. Merely finding a legacy archive on disk is not admission.
    TargoStage0Download {
        filename: canonical_filename,
        prefix: component.to_owned(),
        legacy: false,
    }
}

fn translate_legacy_targo_stage0_surface(
    bin_root: &Path,
    host: TargetSelection,
    legacy_components: &[&str],
) {
    #[cfg(not(unix))]
    panic!("legacy Trust stage0 tcargo pins require a native canonical regeneration on this host");

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        const BACKEND_DIR: &str = "libexec";
        let legacy_targo = legacy_components.contains(&"targo");
        let legacy_targo_trust = legacy_components.contains(&"targo-trust");
        assert!(
            legacy_components.iter().all(|component| matches!(*component, "targo" | "targo-trust")),
            "unknown legacy Targo component selection"
        );

        let bin_dir = bin_root.join("bin");
        // Keep the admitted executable at the same depth as bin/<tool>. Its
        // published rpath resolves ../lib, which remains valid from libexec.
        let backend_dir = bin_root.join(BACKEND_DIR);
        t!(fs::create_dir_all(&backend_dir));

        let copy_executable = |source: &Path, destination: &Path| {
            assert!(
                source.exists(),
                "legacy Trust stage0 Targo payload lacks {}",
                source.display()
            );
            t!(fs::copy(source, destination));
            let mut permissions = t!(fs::metadata(destination)).permissions();
            permissions.set_mode(permissions.mode() | 0o111);
            t!(fs::set_permissions(destination, permissions));
        };
        let write_executable = |destination: &Path, contents: &str| {
            t!(fs::write(destination, contents));
            t!(fs::set_permissions(destination, fs::Permissions::from_mode(0o755)));
        };

        if legacy_targo {
            let source = bin_dir.join(exe("tcargo", host));
            assert!(
                bin_dir.join(exe("cargo", host)).exists(),
                "legacy Trust stage0 tcargo payload lacks bin/cargo"
            );
            copy_executable(&source, &backend_dir.join("tcargo"));
            write_executable(
                &bin_dir.join(exe("targo", host)),
                &format!(
                    r#"#!/bin/sh
backend="$(dirname "$0")/../{BACKEND_DIR}/tcargo"
rewrite_version() {{
    output=$("$backend" "$@")
    status=$?
    printf '%s\n' "$output" | sed -e '1s/^tcargo /targo /' -e 's/^binary: tcargo$/binary: targo/'
    return "$status"
}}
if [ "$#" -eq 1 ]; then
    case "$1" in --version|-V|-vV) rewrite_version "$@"; exit $? ;; esac
fi
if [ "$#" -eq 2 ] && {{ [ "$1" = "--version" ] && [ "$2" = "--verbose" ] || [ "$1" = "--verbose" ] && [ "$2" = "--version" ]; }}; then
    rewrite_version "$@"
    exit $?
fi
exec "$backend" "$@"
"#
                ),
            );

            for (canonical_tool, retired_tool) in [
                ("trustdoc", "rustdoc"),
                ("trustfmt", "rustfmt"),
                ("trust-analyzer", "rust-analyzer"),
            ] {
                let canonical_path = bin_dir.join(exe(canonical_tool, host));
                let retired_path = bin_dir.join(exe(retired_tool, host));
                if !canonical_path.exists() && retired_path.exists() {
                    copy_executable(&retired_path, &canonical_path);
                }
            }

            // The legacy frontend resolves compiler tools next to its own
            // executable. Forward privately to the canonical public tools now
            // that tcargo itself no longer lives in stage0/bin.
            for compiler_tool in ["trustc", "trustdoc"] {
                assert!(
                    bin_dir.join(exe(compiler_tool, host)).exists(),
                    "legacy Trust stage0 tcargo adapter lacks bin/{compiler_tool}"
                );
                write_executable(
                    &backend_dir.join(compiler_tool),
                    &format!(
                        "#!/bin/sh\nexec \"$(dirname \"$0\")/../bin/{compiler_tool}\" \"$@\"\n"
                    ),
                );
            }

            // Companion archives in this checksum-pinned seed predate the
            // public alias purge. Keep this normalization behind the tcargo
            // selection so canonical producer regressions remain fatal.
            let legacy_fmt = bin_dir.join(exe("tcargo-fmt", host));
            let canonical_fmt = bin_dir.join(exe("targo-fmt", host));
            if !canonical_fmt.exists() && legacy_fmt.exists() {
                copy_executable(&legacy_fmt, &canonical_fmt);
            }
            for retired in ["tcargo-fmt", "cargo-fmt", "rustfmt", "rustdoc", "rust-analyzer"] {
                let path = bin_dir.join(exe(retired, host));
                if path.exists() {
                    t!(fs::remove_file(&path));
                }
            }
            let retired_analyzer_helper =
                bin_root.join("libexec").join(exe("rust-analyzer-proc-macro-srv", host));
            let canonical_analyzer_helper =
                bin_root.join("libexec").join(exe("trust-analyzer-proc-macro-srv", host));
            if !canonical_analyzer_helper.exists() && retired_analyzer_helper.exists() {
                copy_executable(&retired_analyzer_helper, &canonical_analyzer_helper);
            }
            if retired_analyzer_helper.exists() {
                t!(fs::remove_file(&retired_analyzer_helper));
            }
        }

        if legacy_targo_trust {
            let source = bin_dir.join(exe("tcargo-trust", host));
            copy_executable(&source, &backend_dir.join("tcargo-trust-stage0-backend"));
            write_executable(
                &bin_dir.join(exe("targo-trust", host)),
                &format!(
                    r#"#!/bin/sh
backend="$(dirname "$0")/../{BACKEND_DIR}/tcargo-trust-stage0-backend"
rewrite_version=0
if [ "$#" -eq 1 ] && {{ [ "$1" = "--version" ] || [ "$1" = "-V" ]; }}; then
    rewrite_version=1
fi
if [ "$#" -eq 2 ] && [ "$1" = "trust" ] && {{ [ "$2" = "--version" ] || [ "$2" = "-V" ]; }}; then
    rewrite_version=1
fi
if [ "$rewrite_version" -eq 1 ]; then
    output=$("$backend" "$@")
    status=$?
    printf '%s\n' "$output" | sed 's/tcargo/targo/g'
    exit "$status"
fi
exec "$backend" "$@"
"#
                ),
            );
        }

        // The old frontend searches its own directory for tcargo-trust. Keep
        // this spelling private and route it through the canonical public
        // adapter/binary so no legacy leaf survives in stage0/bin.
        if legacy_targo {
            for (legacy_subcommand, canonical_subcommand) in [
                ("tcargo-trust", "targo-trust"),
                ("tcargo-fmt", "targo-fmt"),
                ("tcargo-tippy", "targo-tippy"),
            ] {
                write_executable(
                    &backend_dir.join(legacy_subcommand),
                    &format!(
                        "#!/bin/sh\nexec \"$(dirname \"$0\")/../bin/{canonical_subcommand}\" \"$@\"\n"
                    ),
                );
            }
        }

        for legacy in ["tcargo", "tcargo-trust", "tcargo-fmt", "cargo-trust"] {
            let path = bin_dir.join(exe(legacy, host));
            if path.exists() {
                t!(fs::remove_file(&path));
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct TippyStage0Download {
    filename: String,
    prefix: &'static str,
    legacy: bool,
}

fn select_stage0_tippy_download(
    checksums: &BTreeMap<String, String>,
    date: &str,
    version: &str,
    host: &str,
) -> TippyStage0Download {
    let canonical_filename = format!("tippy-{version}-{host}.tar.xz");
    let canonical_url = format!("dist/{date}/{canonical_filename}");
    if checksums.contains_key(&canonical_url) {
        return TippyStage0Download {
            // Trust: the stage0 seed tarball produced by prepare.py carries the
            // CANONICAL `tippy/` image dir (not `tippy-preview/`), consistent with
            // the other preview components (see `component_unpack_prefix`). `unpack`
            // selects members by `short_path.starts_with(prefix)`, so this must be
            // the canonical dir or every tippy file is skipped and
            // `stage0/bin/tippy` never lands.
            filename: canonical_filename,
            prefix: "tippy",
            legacy: false,
        };
    }

    let legacy_filename = format!("trust-clippy-{version}-{host}.tar.xz");
    let legacy_url = format!("dist/{date}/{legacy_filename}");
    if checksums.contains_key(&legacy_url) {
        return TippyStage0Download {
            filename: legacy_filename,
            prefix: "trust-clippy-preview",
            legacy: true,
        };
    }

    // Keep the canonical checksum-miss diagnostic if no admitted spelling is
    // pinned. This is a narrow compatibility boundary, not a network fallback.
    TippyStage0Download { filename: canonical_filename, prefix: "tippy-preview", legacy: false }
}

fn legacy_tippy_adapter_script(
    backend: &str,
    public_name: &str,
    prelude: &str,
    inject_marker: bool,
) -> String {
    let marker = if inject_marker { " clippy" } else { "" };
    let canonical_cargo =
        if inject_marker { "CARGO=\"$adapter_dir/targo\"\nexport CARGO\n" } else { "" };
    let version_flags =
        if public_name == "tippy-driver" { "--version|-V" } else { "--version|-V|-vV|-Vv" };
    format!(
        r#"#!/bin/sh
{prelude}case "$0" in
    */*) adapter_dir=${{0%/*}} ;;
    *) adapter_dir=. ;;
esac
backend="$adapter_dir/../libexec/{backend}"
{canonical_cargo}version_query=0
if [ "$#" -eq 1 ]; then
    case "$1" in {version_flags}) version_query=1 ;; esac
elif [ "$#" -eq 2 ]; then
    if [ "$1:$2" = "--version:--verbose" ] || [ "$1:$2" = "--verbose:--version" ]; then
        version_query=1
    fi
fi
if [ "$version_query" -eq 1 ]; then
    output=$("$backend"{marker} --version)
    status=$?
    printf '%s\n' "$output" | command -p sed -e '1s/^[^ ][^ ]*/tippy/' -e 's/^binary: .*/binary: {public_name}/'
    exit "$status"
fi
exec "$backend"{marker} "$@"
"#
    )
}

fn translate_legacy_tippy_stage0_surface(bin_root: &Path, host: TargetSelection) {
    #[cfg(not(unix))]
    panic!("legacy Trust stage0 Tippy pins require a native canonical regeneration on this host");

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        const FRONTENDS: &[&str] = &["trust-clippy", "cargo-clippy", "targo-clippy"];
        const DRIVERS: &[&str] = &["trust-clippy-driver", "clippy-driver"];
        const BACKEND: &str = "tippy-stage0-backend";
        const DRIVER_BACKEND: &str = "tippy-driver-stage0-backend";

        let bin_dir = bin_root.join("bin");
        let libexec_dir = bin_root.join("libexec");
        t!(fs::create_dir_all(&libexec_dir));

        let find_legacy = |names: &[&str]| {
            names.iter().map(|name| bin_dir.join(exe(name, host))).find(|path| path.exists())
        };
        let frontend = find_legacy(FRONTENDS)
            .expect("legacy Trust stage0 Tippy payload lacks a frontend executable");
        let driver = find_legacy(DRIVERS)
            .expect("legacy Trust stage0 Tippy payload lacks a compiler driver executable");

        for (source, backend_name) in [(&frontend, BACKEND), (&driver, DRIVER_BACKEND)] {
            let backend = libexec_dir.join(backend_name);
            t!(fs::copy(source, &backend));
            let mut backend_permissions = t!(fs::metadata(&backend)).permissions();
            backend_permissions.set_mode(backend_permissions.mode() | 0o111);
            t!(fs::set_permissions(&backend, backend_permissions));
        }

        // The admitted legacy frontend derives its compiler wrapper path from
        // its own executable directory. Depending on the seed vintage that
        // private protocol name is either `trust-clippy-driver` or
        // `clippy-driver`. Moving the payloads to canonically named libexec
        // backends without preserving that private discovery protocol yields
        // a frontend that launches but cannot lint a crate. Materialize only
        // private forwarding shims here; retired names remain absent from bin/.
        for legacy_driver in DRIVERS {
            let destination = libexec_dir.join(exe(legacy_driver, host));
            let contents = format!(
                "#!/bin/sh\ncase \"$0\" in\n    */*) adapter_dir=${{0%/*}} ;;\n    *) adapter_dir=. ;;\nesac\nexec \"$adapter_dir/{DRIVER_BACKEND}\" \"$@\"\n"
            );
            t!(fs::write(&destination, contents));
            t!(fs::set_permissions(&destination, fs::Permissions::from_mode(0o755)));
        }

        // cargo-clippy-style frontends discard argv[1] as Cargo's external
        // subcommand marker. A direct byte copy to `tippy` would therefore
        // drop the user's first option. Keep the admitted binary as a private
        // backend and normalize both public invocation forms semantically.
        let adapters = [
            ("tippy", BACKEND, "", true),
            ("targo-tippy", BACKEND, "if [ \"${1-}\" = \"tippy\" ]; then\n    shift\nfi\n", true),
            ("tippy-driver", DRIVER_BACKEND, "", false),
        ];
        for (canonical, adapter_backend, prelude, inject_marker) in adapters {
            let destination = bin_dir.join(exe(canonical, host));
            let contents =
                legacy_tippy_adapter_script(adapter_backend, canonical, prelude, inject_marker);
            t!(fs::write(&destination, contents));
            t!(fs::set_permissions(&destination, fs::Permissions::from_mode(0o755)));
        }

        for legacy in FRONTENDS.iter().chain(DRIVERS) {
            let path = bin_dir.join(exe(legacy, host));
            if path.exists() {
                t!(fs::remove_file(&path));
            }
        }
    }
}

/// Functions that are only ever called once, but named for clarity and to avoid thousand-line functions.
impl Config {
    pub(crate) fn download_tippy(&self) -> PathBuf {
        self.do_if_verbose(|| println!("downloading stage0 tippy artifacts"));

        let date = &self.stage0_metadata.compiler.date;
        let version = &self.stage0_metadata.compiler.version;
        let host = self.host_target;

        let tippy_stamp =
            BuildStamp::new(&self.initial_sysroot).with_prefix("tippy").add_stamp(date);
        let tippy_paths = ["tippy", "targo-tippy", "tippy-driver"]
            .map(|name| self.initial_sysroot.join("bin").join(exe(name, host)));
        let targo_tippy = tippy_paths[1].clone();
        if tippy_paths.iter().all(|path| path.exists()) && tippy_stamp.is_up_to_date() {
            return targo_tippy;
        }

        let selected = select_stage0_tippy_download(
            &self.stage0_metadata.checksums_sha256,
            date,
            version,
            host.triple.as_ref(),
        );
        self.download_component(
            DownloadSource::Dist,
            selected.filename,
            selected.prefix,
            date,
            "stage0",
        );
        if selected.legacy && !self.dry_run() {
            translate_legacy_tippy_stage0_surface(&self.initial_sysroot, host);
        }
        if self.should_fix_bins_and_dylibs() {
            for path in &tippy_paths {
                self.fix_bin_or_dylib(path);
            }
        }

        t!(tippy_stamp.write());
        targo_tippy
    }

    pub(crate) fn ci_rust_std_contents(&self) -> Vec<String> {
        self.ci_component_contents(".rust-std-contents")
    }

    pub(crate) fn ci_rustc_dev_contents(&self) -> Vec<String> {
        self.ci_component_contents(".rustc-dev-contents")
    }

    fn ci_component_contents(&self, stamp_file: &str) -> Vec<String> {
        assert!(self.download_rustc());
        if self.dry_run() {
            return vec![];
        }

        let ci_rustc_dir = self.ci_rustc_dir();
        let stamp_file = ci_rustc_dir.join(stamp_file);
        let contents_file = t!(File::open(&stamp_file), stamp_file.display().to_string());
        t!(BufReader::new(contents_file).lines().collect())
    }

    pub(crate) fn download_ci_rustc(&self, commit: &str) {
        self.do_if_verbose(|| {
            println!("using downloaded stage2 artifacts from CI (commit {commit})")
        });

        let version = self.artifact_version_part(commit);
        // download-rustc doesn't need its own cargo, it can just use beta's. But it does need the
        // `rustc_private` crates for tools.
        let extra_components = ["rustc-dev"];

        self.download_toolchain(
            &version,
            "ci-rustc",
            &format!("{commit}-{}", self.llvm_assertions),
            &extra_components,
            Self::download_ci_component,
        );
    }

    fn download_toolchain(
        &self,
        version: &str,
        sysroot: &str,
        stamp_key: &str,
        extra_components: &[&str],
        download_component: fn(&Config, String, &str, &str),
    ) {
        let host = self.host_target.triple;
        let bin_root = self.out.join(host).join(sysroot);
        let rustc_stamp = BuildStamp::new(&bin_root).with_prefix("rustc").add_stamp(stamp_key);

        let needs_refresh = !bin_root.join("bin").join(exe("rustc", self.host_target)).exists()
            || !rustc_stamp.is_up_to_date();

        if needs_refresh {
            if self.dry_run() {
                return;
            }
            if bin_root.exists() {
                t!(fs::remove_dir_all(&bin_root));
            }
            let filename = format!("rust-std-{version}-{host}.tar.xz");
            let pattern = format!("rust-std-{host}");
            download_component(self, filename, &pattern, stamp_key);
            let filename = format!("rustc-{version}-{host}.tar.xz");
            download_component(self, filename, "rustc", stamp_key);

            for component in extra_components {
                let filename = format!("{component}-{version}-{host}.tar.xz");
                download_component(self, filename, component, stamp_key);
            }

            if self.should_fix_bins_and_dylibs() {
                self.fix_bin_or_dylib(&bin_root.join("bin").join("rustc"));
                self.fix_bin_or_dylib(&bin_root.join("bin").join("rustdoc"));
                self.fix_bin_or_dylib(
                    &bin_root.join("libexec").join("rust-analyzer-proc-macro-srv"),
                );
                let lib_dir = bin_root.join("lib");
                for lib in t!(fs::read_dir(&lib_dir), lib_dir.display().to_string()) {
                    let lib = t!(lib);
                    if path_is_dylib(&lib.path()) {
                        self.fix_bin_or_dylib(&lib.path());
                    }
                }
            }

            t!(rustc_stamp.write());
        }
    }

    /// Download a single component of a CI-built toolchain (not necessarily a published nightly).
    // NOTE: intentionally takes an owned string to avoid downloading multiple times by accident
    fn download_ci_component(&self, filename: String, prefix: &str, commit_with_assertions: &str) {
        Self::download_component(
            self,
            DownloadSource::CI,
            filename,
            prefix,
            commit_with_assertions,
            "ci-rustc",
        )
    }

    fn download_component(
        &self,
        mode: DownloadSource,
        filename: String,
        prefix: &str,
        key: &str,
        destination: &str,
    ) {
        let dwn_ctx: DownloadContext<'_> = self.into();
        download_component(dwn_ctx, &self.out, mode, filename, prefix, key, destination);
    }

    #[cfg(test)]
    pub(crate) fn maybe_download_ci_llvm(&self) {}

    #[cfg(not(test))]
    pub(crate) fn maybe_download_ci_llvm(&self) {
        use build_helper::exit;
        use build_helper::git::PathFreshness;

        use crate::core::build_steps::llvm::detect_llvm_freshness;
        use crate::core::config::toml::llvm::check_incompatible_options_for_ci_llvm;

        if !self.llvm_from_ci {
            return;
        }

        let llvm_root = self.ci_llvm_root();
        let llvm_freshness =
            detect_llvm_freshness(self, self.rust_info.is_managed_git_subrepository());
        self.do_if_verbose(|| {
            eprintln!("LLVM freshness: {llvm_freshness:?}");
        });
        let llvm_sha = match llvm_freshness {
            PathFreshness::LastModifiedUpstream { upstream } => upstream,
            PathFreshness::HasLocalModifications { upstream, modifications: _ } => upstream,
            PathFreshness::MissingUpstream => {
                eprintln!("error: could not find commit hash for downloading LLVM");
                eprintln!("HELP: maybe your repository history is too shallow?");
                eprintln!("HELP: consider disabling `download-ci-llvm`");
                eprintln!("HELP: or fetch enough history to include one upstream commit");
                crate::exit!(1);
            }
        };
        let stamp_key = format!("{}{}", llvm_sha, self.llvm_assertions);
        let llvm_stamp = BuildStamp::new(&llvm_root).with_prefix("llvm").add_stamp(stamp_key);
        if !llvm_stamp.is_up_to_date() && !self.dry_run() {
            self.download_ci_llvm(&llvm_sha);

            if self.should_fix_bins_and_dylibs() {
                for entry in t!(fs::read_dir(llvm_root.join("bin"))) {
                    self.fix_bin_or_dylib(&t!(entry).path());
                }
            }

            // Update the timestamp of llvm-config to force rustc_llvm to be
            // rebuilt. This is a hacky workaround for a deficiency in Cargo where
            // the rerun-if-changed directive doesn't handle changes very well.
            // https://github.com/rust-lang/cargo/issues/10791
            // Cargo only compares the timestamp of the file relative to the last
            // time `rustc_llvm` build script ran. However, the timestamps of the
            // files in the tarball are in the past, so it doesn't trigger a
            // rebuild.
            let now = std::time::SystemTime::now();
            let file_times = fs::FileTimes::new().set_accessed(now).set_modified(now);

            let llvm_config = llvm_root.join("bin").join(exe("llvm-config", self.host_target));
            t!(crate::utils::helpers::set_file_times(llvm_config, file_times));

            if self.should_fix_bins_and_dylibs() {
                let llvm_lib = llvm_root.join("lib");
                for entry in t!(fs::read_dir(llvm_lib)) {
                    let lib = t!(entry).path();
                    if path_is_dylib(&lib) {
                        self.fix_bin_or_dylib(&lib);
                    }
                }
            }

            t!(llvm_stamp.write());
        }

        if let Some(config_path) = &self.config {
            let current_config_toml = Self::get_toml(config_path).unwrap();

            match self.get_builder_toml("ci-llvm") {
                Ok(ci_config_toml) => {
                    t!(check_incompatible_options_for_ci_llvm(current_config_toml, ci_config_toml));
                }
                Err(e) if e.to_string().contains("unknown field") => {
                    println!(
                        "WARNING: CI LLVM has some fields that are no longer supported in bootstrap; download-ci-llvm will be disabled."
                    );
                    println!("HELP: Consider rebasing to a newer commit if available.");
                }
                Err(e) => {
                    eprintln!("ERROR: Failed to parse CI LLVM bootstrap.toml: {e}");
                    exit!(2);
                }
            };
        };
    }

    #[cfg(not(test))]
    fn download_ci_llvm(&self, llvm_sha: &str) {
        let llvm_assertions = self.llvm_assertions;

        let cache_prefix = format!("llvm-{llvm_sha}-{llvm_assertions}");
        let cache_dst =
            self.bootstrap_cache_path.as_ref().cloned().unwrap_or_else(|| self.out.join("cache"));

        let rustc_cache = cache_dst.join(cache_prefix);
        if !rustc_cache.exists() {
            t!(fs::create_dir_all(&rustc_cache));
        }
        let base = if llvm_assertions {
            &self.stage0_metadata.config.artifacts_with_llvm_assertions_server
        } else {
            &self.stage0_metadata.config.artifacts_server
        };
        reject_inherited_upstream_rust_download_url(base);
        let version = self.artifact_version_part(llvm_sha);
        let filename = format!("rust-dev-{}-{}.tar.xz", version, self.host_target.triple);
        let tarball = rustc_cache.join(&filename);
        if !tarball.exists() {
            let help_on_error = "ERROR: failed to download llvm from ci

    HELP: There could be two reasons behind this:
        1) The host triple is not supported for `download-ci-llvm`.
        2) Old builds get deleted after a certain time.
    HELP: In either case, disable `download-ci-llvm` in your bootstrap.toml:

    [llvm]
    download-ci-llvm = false
    ";
            self.download_file(&format!("{base}/{llvm_sha}/{filename}"), &tarball, help_on_error);
        }
        let llvm_root = self.ci_llvm_root();
        self.unpack(&tarball, &llvm_root, "rust-dev");
    }
}

/// Only should be used for pre config initialization downloads.
pub(crate) struct DownloadContext<'a> {
    pub path_modification_cache: Arc<Mutex<HashMap<Vec<&'static str>, PathFreshness>>>,
    pub src: &'a Path,
    pub submodules: &'a Option<bool>,
    pub host_target: TargetSelection,
    pub patch_binaries_for_nix: Option<bool>,
    pub exec_ctx: &'a ExecutionContext,
    pub stage0_metadata: &'a build_helper::stage0_parser::Stage0,
    pub llvm_assertions: bool,
    pub bootstrap_cache_path: &'a Option<PathBuf>,
    pub ci_env: CiEnv,
}

impl<'a> DownloadContext<'a> {
    pub fn is_running_on_ci(&self) -> bool {
        self.ci_env.is_running_in_ci()
    }
}

impl<'a> AsRef<DownloadContext<'a>> for DownloadContext<'a> {
    fn as_ref(&self) -> &DownloadContext<'a> {
        self
    }
}

impl<'a> From<&'a Config> for DownloadContext<'a> {
    fn from(value: &'a Config) -> Self {
        DownloadContext {
            path_modification_cache: value.path_modification_cache.clone(),
            src: &value.src,
            host_target: value.host_target,
            submodules: &value.submodules,
            patch_binaries_for_nix: value.patch_binaries_for_nix,
            exec_ctx: &value.exec_ctx,
            stage0_metadata: &value.stage0_metadata,
            llvm_assertions: value.llvm_assertions,
            bootstrap_cache_path: &value.bootstrap_cache_path,
            ci_env: value.ci_env,
        }
    }
}

fn path_is_dylib(path: &Path) -> bool {
    // The .so is not necessarily the extension, it might be libLLVM.so.18.1
    path.to_str().is_some_and(|path| path.contains(".so"))
}

/// Checks whether the CI rustc is available for the given target triple.
pub(crate) fn is_download_ci_available(target_triple: &str, llvm_assertions: bool) -> bool {
    // All tier 1 targets and tier 2 targets with host tools.
    const SUPPORTED_PLATFORMS: &[&str] = &[
        "aarch64-apple-darwin",
        "aarch64-pc-windows-gnullvm",
        "aarch64-pc-windows-msvc",
        "aarch64-unknown-linux-gnu",
        "aarch64-unknown-linux-musl",
        "arm-unknown-linux-gnueabi",
        "arm-unknown-linux-gnueabihf",
        "armv7-unknown-linux-gnueabihf",
        "i686-pc-windows-gnu",
        "i686-pc-windows-msvc",
        "i686-unknown-linux-gnu",
        "loongarch64-unknown-linux-gnu",
        "powerpc-unknown-linux-gnu",
        "powerpc64-unknown-linux-gnu",
        "powerpc64-unknown-linux-musl",
        "powerpc64le-unknown-linux-gnu",
        "powerpc64le-unknown-linux-musl",
        "riscv64gc-unknown-linux-gnu",
        "s390x-unknown-linux-gnu",
        "x86_64-apple-darwin",
        "x86_64-pc-windows-gnu",
        "x86_64-pc-windows-gnullvm",
        "x86_64-pc-windows-msvc",
        "x86_64-unknown-freebsd",
        "x86_64-unknown-illumos",
        "x86_64-unknown-linux-gnu",
        "x86_64-unknown-linux-musl",
        "x86_64-unknown-netbsd",
    ];

    const SUPPORTED_PLATFORMS_WITH_ASSERTIONS: &[&str] =
        &["x86_64-unknown-linux-gnu", "x86_64-pc-windows-msvc"];

    if llvm_assertions {
        SUPPORTED_PLATFORMS_WITH_ASSERTIONS.contains(&target_triple)
    } else {
        SUPPORTED_PLATFORMS.contains(&target_triple)
    }
}

#[cfg(test)]
pub(crate) fn maybe_download_rustfmt<'a>(
    dwn_ctx: impl AsRef<DownloadContext<'a>>,
    out: &Path,
) -> Option<PathBuf> {
    Some(PathBuf::new())
}

fn dedicated_trustfmt_component_prefix() -> &'static str {
    // Trust's formatter dist archive uses the canonical `trustfmt/` component.
    // The inherited upstream `rustfmt-preview/` prefix matches no archive
    // entries, so `unpack` otherwise succeeds while installing no formatter.
    "trustfmt"
}

fn dedicated_trustfmt_payload_is_complete(rustfmt_path: &Path, targo_fmt_path: &Path) -> bool {
    // Test the exact two public formatter entrypoints as regular files. A stale
    // stamp must never bless a partial sysroot after an interrupted extraction
    // or manual deletion.
    rustfmt_path.is_file() && targo_fmt_path.is_file()
}

/// NOTE: rustfmt is a completely different toolchain than the bootstrap compiler, so it can't
/// reuse target directories or artifacts
#[cfg(not(test))]
pub(crate) fn maybe_download_rustfmt<'a>(
    dwn_ctx: impl AsRef<DownloadContext<'a>>,
    out: &Path,
) -> Option<PathBuf> {
    use build_helper::stage0_parser::VersionMetadata;

    let dwn_ctx = dwn_ctx.as_ref();

    if dwn_ctx.exec_ctx.dry_run() {
        return Some(PathBuf::new());
    }

    let VersionMetadata { date, version, .. } = dwn_ctx.stage0_metadata.rustfmt.as_ref()?;
    let channel = format!("{version}-{date}");

    let host = dwn_ctx.host_target;
    let bin_root = out.join(host).join("trustfmt");
    let rustfmt_path = bin_root.join("bin").join(exe("trustfmt", host));
    let targo_fmt_path = bin_root.join("bin").join(exe("targo-fmt", host));
    let rustfmt_stamp = BuildStamp::new(&bin_root).with_prefix("trustfmt").add_stamp(channel);
    if dedicated_trustfmt_payload_is_complete(&rustfmt_path, &targo_fmt_path)
        && rustfmt_stamp.is_up_to_date()
    {
        return Some(rustfmt_path);
    }

    download_component(
        dwn_ctx,
        out,
        DownloadSource::Dist,
        format!("trustfmt-{version}-{build}.tar.xz", build = host.triple),
        dedicated_trustfmt_component_prefix(),
        date,
        "trustfmt",
    );

    download_component(
        dwn_ctx,
        out,
        DownloadSource::Dist,
        format!("trustc-{version}-{build}.tar.xz", build = host.triple),
        "trustc",
        date,
        "trustfmt",
    );

    assert!(
        dedicated_trustfmt_payload_is_complete(&rustfmt_path, &targo_fmt_path),
        "Trust formatter extraction was incomplete: expected {} and {}",
        rustfmt_path.display(),
        targo_fmt_path.display(),
    );

    if should_fix_bins_and_dylibs(dwn_ctx.patch_binaries_for_nix, dwn_ctx.exec_ctx) {
        fix_bin_or_dylib(out, &bin_root.join("bin").join("trustfmt"), dwn_ctx.exec_ctx);
        fix_bin_or_dylib(out, &bin_root.join("bin").join("targo-fmt"), dwn_ctx.exec_ctx);
        let lib_dir = bin_root.join("lib");
        for lib in t!(fs::read_dir(&lib_dir), lib_dir.display().to_string()) {
            let lib = t!(lib);
            if path_is_dylib(&lib.path()) {
                fix_bin_or_dylib(out, &lib.path(), dwn_ctx.exec_ctx);
            }
        }
    }

    t!(rustfmt_stamp.write());
    Some(rustfmt_path)
}

#[cfg(test)]
pub(crate) fn download_beta_toolchain<'a>(dwn_ctx: impl AsRef<DownloadContext<'a>>, out: &Path) {}

#[cfg(not(test))]
pub(crate) fn download_beta_toolchain<'a>(dwn_ctx: impl AsRef<DownloadContext<'a>>, out: &Path) {
    let dwn_ctx = dwn_ctx.as_ref();
    dwn_ctx.exec_ctx.do_if_verbose(|| {
        println!("downloading stage0 beta artifacts");
    });

    let date = dwn_ctx.stage0_metadata.compiler.date.clone();
    let version = dwn_ctx.stage0_metadata.compiler.version.clone();
    let sysroot = "stage0";
    download_toolchain(
        dwn_ctx,
        out,
        &version,
        sysroot,
        &date,
        stage0_beta_extra_components(),
        "stage0",
        DownloadSource::Dist,
    );
}

fn stage0_beta_extra_components() -> &'static [&'static str] {
    &["targo", "targo-trust", "trustfmt", "tippy", "trust-analyzer"]
}

fn component_unpack_prefix<'a>(component: &'a str, _destination: &str) -> &'a str {
    // Trust: the stage0 seed tarballs produced by
    // `src/tools/trust-stage0-dist/prepare.py` carry CANONICAL Trust image dirs
    // (`trustfmt/`, `tippy/`, `trust-analyzer/`) — `prepare.py`'s
    // STAGE0_IMAGE_DIR_RENAMES canonicalizes the `-preview` producer image dir
    // to its non-preview stage0 name, and its archive contract validates that
    // canonical form. `unpack` selects members by `short_path.starts_with(prefix)`,
    // so the prefix must be the canonical image dir. Mapping these to
    // `<tool>-preview` here made `unpack` skip every file of the preview
    // components, leaving `stage0/bin/{trustfmt,tippy,trust-analyzer}` absent and
    // failing `assert_stage0_tool_surface`. Use the canonical component name so
    // the consumer matches the producer.
    component
}

fn missing_extra_component_bin(
    bin_root: &Path,
    host: TargetSelection,
    extra_components: &[&str],
) -> bool {
    extra_components
        .iter()
        .any(|component| !bin_root.join("bin").join(exe(component, host)).exists())
}

fn stage0_tool_surface_needs_refresh(
    bin_root: &Path,
    host: TargetSelection,
    destination: &str,
) -> bool {
    if destination != "stage0" {
        return false;
    }

    let bin = bin_root.join("bin");
    stage0_required_bins().iter().any(|name| !bin.join(exe(name, host)).exists())
        || stage0_required_libexec_bins()
            .iter()
            .any(|name| !bin_root.join("libexec").join(exe(name, host)).exists())
        || stage0_forbidden_bins()
            .iter()
            .any(|name| path_entry_exists(&bin.join(stage0_bin_filename(name, host))))
        || stage0_forbidden_libexec_bins()
            .iter()
            .any(|name| path_entry_exists(&bin_root.join("libexec").join(exe(name, host))))
}

fn stage0_required_bins() -> &'static [&'static str] {
    &[
        "trustc",
        "rustc",
        "trustdoc",
        "targo",
        "cargo",
        "targo-trust",
        "trustfmt",
        "targo-fmt",
        "tippy",
        "targo-tippy",
        "tippy-driver",
        "trust-analyzer",
    ]
}

fn stage0_required_libexec_bins() -> &'static [&'static str] {
    &["trust-analyzer-proc-macro-srv"]
}

fn stage0_forbidden_bins() -> &'static [&'static str] {
    &[
        "cargo-trust",
        "tcargo",
        "tcargo-trust",
        "tcargo-fmt",
        "rustdoc",
        "rustfmt",
        "cargo-fmt",
        "cargo-clippy",
        "clippy-driver",
        "targo-clippy",
        "trust-clippy",
        "trust-clippy-driver",
        "rust-analyzer",
        "miri",
        "trust-miri",
        "cargo-miri",
        "targo-miri",
        "rust-gdb",
        "rust-gdbgui",
        "rust-lldb",
        "rust-windbg.cmd",
    ]
}

fn stage0_bin_filename(name: &str, host: TargetSelection) -> String {
    if name.ends_with(".cmd") { name.to_string() } else { exe(name, host) }
}

fn path_entry_exists(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok()
}

fn stage0_forbidden_libexec_bins() -> &'static [&'static str] {
    &["rust-analyzer-proc-macro-srv"]
}

fn assert_stage0_tool_surface(bin_root: &Path, host: TargetSelection, destination: &str) {
    if destination != "stage0" {
        return;
    }

    let bin = bin_root.join("bin");
    for name in stage0_required_bins() {
        let path = bin.join(exe(name, host));
        assert!(path.exists(), "stage0 Trust seed is missing required {}", path.display());
    }
    for name in stage0_required_libexec_bins() {
        let path = bin_root.join("libexec").join(exe(name, host));
        assert!(path.exists(), "stage0 Trust seed is missing required {}", path.display());
    }
    for name in stage0_forbidden_bins() {
        let path = bin.join(stage0_bin_filename(name, host));
        assert!(!path_entry_exists(&path), "stage0 Trust seed must not contain {}", path.display());
    }
    for name in stage0_forbidden_libexec_bins() {
        let path = bin_root.join("libexec").join(exe(name, host));
        assert!(!path_entry_exists(&path), "stage0 Trust seed must not contain {}", path.display());
    }
}

#[allow(clippy::too_many_arguments)]
fn download_toolchain<'a>(
    dwn_ctx: impl AsRef<DownloadContext<'a>>,
    out: &Path,
    version: &str,
    sysroot: &str,
    stamp_key: &str,
    extra_components: &[&str],
    destination: &str,
    mode: DownloadSource,
) {
    let dwn_ctx = dwn_ctx.as_ref();
    let host = dwn_ctx.host_target.triple;
    let bin_root = out.join(host).join(sysroot);
    let stamp_prefix = if destination == "stage0" { "trustc" } else { "rustc" };
    let primary_compiler = if destination == "stage0" { "trustc" } else { "rustc" };
    let rustc_stamp = BuildStamp::new(&bin_root).with_prefix(stamp_prefix).add_stamp(stamp_key);
    let missing_extra_components =
        missing_extra_component_bin(&bin_root, dwn_ctx.host_target, extra_components);

    let needs_refresh =
        !bin_root.join("bin").join(exe(primary_compiler, dwn_ctx.host_target)).exists()
            || missing_extra_components
            || stage0_tool_surface_needs_refresh(&bin_root, dwn_ctx.host_target, destination)
            || !rustc_stamp.is_up_to_date();

    if needs_refresh {
        if dwn_ctx.exec_ctx.dry_run() {
            return;
        }
        // Fail-closed (2026-07-29 seed-destruction incident): never delete
        // the live toolchain before its replacement is fully downloaded,
        // extracted, and surface-verified. Everything lands in a staging
        // sibling first; the live tree is only touched by the final atomic
        // swap in `swap_verified_toolchain`.
        let staging_destination = format!("{destination}.staging");
        let staging_root = out.join(host).join(&staging_destination);
        if staging_root.exists() {
            t!(fs::remove_dir_all(&staging_root));
        }
        t!(fs::create_dir_all(&staging_root));
        let std_component = if destination == "stage0" { "trust-std" } else { "rust-std" };
        let compiler_component = if destination == "stage0" { "trustc" } else { "rustc" };

        let filename = format!("{std_component}-{version}-{host}.tar.xz");
        let pattern = format!("{std_component}-{host}");
        download_component(
            dwn_ctx,
            out,
            mode.clone(),
            filename,
            &pattern,
            stamp_key,
            &staging_destination,
        );
        let filename = format!("{compiler_component}-{version}-{host}.tar.xz");
        download_component(
            dwn_ctx,
            out,
            mode.clone(),
            filename,
            compiler_component,
            stamp_key,
            &staging_destination,
        );

        let mut legacy_targo_components = Vec::new();
        let mut translate_legacy_tippy = false;
        for component in extra_components {
            let (filename, prefix) =
                if destination == "stage0" && matches!(&mode, DownloadSource::Dist) {
                    match *component {
                        "targo" | "targo-trust" => {
                            let selected = select_stage0_targo_download(
                                &dwn_ctx.stage0_metadata.checksums_sha256,
                                stamp_key,
                                version,
                                host.as_ref(),
                                component,
                            );
                            if selected.legacy {
                                legacy_targo_components.push(*component);
                            }
                            (selected.filename, selected.prefix)
                        }
                        "tippy" => {
                            let selected = select_stage0_tippy_download(
                                &dwn_ctx.stage0_metadata.checksums_sha256,
                                stamp_key,
                                version,
                                host.as_ref(),
                            );
                            translate_legacy_tippy = selected.legacy;
                            (selected.filename, selected.prefix.to_owned())
                        }
                        _ => (
                            format!("{component}-{version}-{host}.tar.xz"),
                            component_unpack_prefix(component, destination).to_owned(),
                        ),
                    }
                } else {
                    (
                        format!("{component}-{version}-{host}.tar.xz"),
                        component_unpack_prefix(component, destination).to_owned(),
                    )
                };
            download_component(
                dwn_ctx,
                out,
                mode.clone(),
                filename,
                &prefix,
                stamp_key,
                &staging_destination,
            );
        }

        if !legacy_targo_components.is_empty() {
            translate_legacy_targo_stage0_surface(
                &staging_root,
                dwn_ctx.host_target,
                &legacy_targo_components,
            );
        }
        if translate_legacy_tippy {
            translate_legacy_tippy_stage0_surface(&staging_root, dwn_ctx.host_target);
        }

        // Verify the STAGED surface before the live tree is touched: an
        // incomplete replacement panics here with the working toolchain
        // still in place.
        assert_stage0_tool_surface(&staging_root, dwn_ctx.host_target, destination);

        if should_fix_bins_and_dylibs(dwn_ctx.patch_binaries_for_nix, dwn_ctx.exec_ctx) {
            if destination == "stage0" {
                for tool in stage0_required_bins() {
                    fix_bin_or_dylib(
                        out,
                        &staging_root.join("bin").join(exe(tool, dwn_ctx.host_target)),
                        dwn_ctx.exec_ctx,
                    );
                }
                for tool in stage0_required_libexec_bins() {
                    fix_bin_or_dylib(
                        out,
                        &staging_root.join("libexec").join(exe(tool, dwn_ctx.host_target)),
                        dwn_ctx.exec_ctx,
                    );
                }
            } else {
                fix_bin_or_dylib(
                    out,
                    &staging_root.join("bin").join(exe("rustc", dwn_ctx.host_target)),
                    dwn_ctx.exec_ctx,
                );
                fix_bin_or_dylib(
                    out,
                    &staging_root.join("bin").join(exe("rustdoc", dwn_ctx.host_target)),
                    dwn_ctx.exec_ctx,
                );
                fix_bin_or_dylib(
                    out,
                    &staging_root
                        .join("libexec")
                        .join(exe("rust-analyzer-proc-macro-srv", dwn_ctx.host_target)),
                    dwn_ctx.exec_ctx,
                );
            }
            let lib_dir = staging_root.join("lib");
            for lib in t!(fs::read_dir(&lib_dir), lib_dir.display().to_string()) {
                let lib = t!(lib);
                if path_is_dylib(&lib.path()) {
                    fix_bin_or_dylib(out, &lib.path(), dwn_ctx.exec_ctx);
                }
            }
        }

        swap_verified_toolchain(&bin_root, &staging_root);

        t!(rustc_stamp.write());
    }
}

/// Atomically promote a fully-extracted, surface-verified staging tree to be
/// the live toolchain root. The live root is only ever touched here, and a
/// failed promotion restores the previous tree — the root is never left
/// absent. (2026-07-29: the previous delete-then-redownload order destroyed
/// the stage0 seed when a partial refresh deleted the whole surface but
/// reinstalled only part of it.)
fn swap_verified_toolchain(bin_root: &Path, staging_root: &Path) {
    let previous_root = bin_root.with_extension("previous");
    if previous_root.exists() {
        t!(fs::remove_dir_all(&previous_root));
    }
    if bin_root.exists() {
        t!(fs::rename(bin_root, &previous_root));
        if let Err(err) = fs::rename(staging_root, bin_root) {
            // Roll the working toolchain back; never leave the root absent.
            t!(fs::rename(&previous_root, bin_root));
            panic!(
                "failed to swap staged toolchain {} into {}: {err}",
                staging_root.display(),
                bin_root.display()
            );
        }
        t!(fs::remove_dir_all(&previous_root));
    } else {
        t!(fs::rename(staging_root, bin_root));
    }
}

pub(crate) fn remove(exec_ctx: &ExecutionContext, f: &Path) {
    if exec_ctx.dry_run() {
        return;
    }
    fs::remove_file(f).unwrap_or_else(|_| panic!("failed to remove {f:?}"));
}

fn fix_bin_or_dylib(out: &Path, fname: &Path, exec_ctx: &ExecutionContext) {
    assert_eq!(SHOULD_FIX_BINS_AND_DYLIBS.get(), Some(&true));
    println!("attempting to patch {}", fname.display());

    // Only build `.nix-deps` once.
    static NIX_DEPS_DIR: OnceLock<PathBuf> = OnceLock::new();
    let mut nix_build_succeeded = true;
    let nix_deps_dir = NIX_DEPS_DIR.get_or_init(|| {
        // Run `nix-build` to "build" each dependency (which will likely reuse
        // the existing `/nix/store` copy, or at most download a pre-built copy).
        //
        // Importantly, we create a gc-root called `.nix-deps` in the `build/`
        // directory, but still reference the actual `/nix/store` path in the rpath
        // as it makes it significantly more robust against changes to the location of
        // the `.nix-deps` location.
        //
        // bintools: Needed for the path of `ld-linux.so` (via `nix-support/dynamic-linker`).
        // cc.lib: Needed similarly for `libstdc++.so.6`.
        // zlib: Needed as a system dependency of `libLLVM-*.so`.
        // zstd.out: Needed as a system dependency of `libLLVM-*.so` when LLVM is built with
        //           zstd support. `.out` is necessary as the default output of the `zstd`
        //           derivation is `.bin`.
        // patchelf: Needed for patching ELF binaries (see doc comment above).
        let nix_deps_dir = out.join(".nix-deps");
        const NIX_EXPR: &str = "
        with (import <nixpkgs> {});
        symlinkJoin {
            name = \"rust-stage0-dependencies\";
            paths = [
                zlib
                zstd.out
                patchelf
                stdenv.cc.bintools
                stdenv.cc.cc.lib
            ];
        }
        ";
        nix_build_succeeded = command("nix-build")
            .allow_failure()
            .args([Path::new("-E"), Path::new(NIX_EXPR), Path::new("-o"), &nix_deps_dir])
            .run_capture_stdout(exec_ctx)
            .is_success();
        nix_deps_dir
    });
    if !nix_build_succeeded {
        return;
    }

    let mut patchelf = command(nix_deps_dir.join("bin/patchelf"));
    patchelf.args(&[
        OsString::from("--add-rpath"),
        OsString::from(t!(fs::canonicalize(nix_deps_dir)).join("lib")),
    ]);
    if !path_is_dylib(fname) {
        // Finally, set the correct .interp for binaries
        let dynamic_linker_path = nix_deps_dir.join("nix-support/dynamic-linker");
        let dynamic_linker = t!(fs::read_to_string(dynamic_linker_path));
        patchelf.args(["--set-interpreter", dynamic_linker.trim_end()]);
    }
    patchelf.arg(fname);
    let _ = patchelf.allow_failure().run_capture_stdout(exec_ctx);
}

fn should_fix_bins_and_dylibs(
    patch_binaries_for_nix: Option<bool>,
    exec_ctx: &ExecutionContext,
) -> bool {
    let val = *SHOULD_FIX_BINS_AND_DYLIBS.get_or_init(|| {
        let uname = command("uname").allow_failure().arg("-s").run_capture_stdout(exec_ctx);
        if uname.is_failure() {
            return false;
        }
        let output = uname.stdout();
        if !output.starts_with("Linux") {
            return false;
        }
        // If the user has asked binaries to be patched for Nix, then
        // don't check for NixOS or `/lib`.
        // NOTE: this intentionally comes after the Linux check:
        // - patchelf only works with ELF files, so no need to run it on Mac or Windows
        // - On other Unix systems, there is no stable syscall interface, so Nix doesn't manage the global libc.
        if let Some(explicit_value) = patch_binaries_for_nix {
            return explicit_value;
        }

        // Use `/etc/os-release` instead of `/etc/NIXOS`.
        // The latter one does not exist on NixOS when using tmpfs as root.
        let is_nixos = match File::open("/etc/os-release") {
            Err(e) if e.kind() == ErrorKind::NotFound => false,
            Err(e) => panic!("failed to access /etc/os-release: {e}"),
            Ok(os_release) => BufReader::new(os_release).lines().any(|l| {
                let l = l.expect("reading /etc/os-release");
                matches!(l.trim(), "ID=nixos" | "ID='nixos'" | "ID=\"nixos\"")
            }),
        };
        if !is_nixos {
            let in_nix_shell = env::var("IN_NIX_SHELL");
            if let Ok(in_nix_shell) = in_nix_shell {
                eprintln!(
                    "The IN_NIX_SHELL environment variable is `{in_nix_shell}`; \
                     you may need to set `patch-binaries-for-nix=true` in bootstrap.toml"
                );
            }
        }
        is_nixos
    });
    if val {
        eprintln!("INFO: You seem to be using Nix.");
    }
    val
}

fn download_component<'a>(
    dwn_ctx: impl AsRef<DownloadContext<'a>>,
    out: &Path,
    mode: DownloadSource,
    filename: String,
    prefix: &str,
    key: &str,
    destination: &str,
) {
    let dwn_ctx = dwn_ctx.as_ref();

    if dwn_ctx.exec_ctx.dry_run() {
        return;
    }

    let cache_dst =
        dwn_ctx.bootstrap_cache_path.as_ref().cloned().unwrap_or_else(|| out.join("cache"));

    let cache_dir = cache_dst.join(key);
    if !cache_dir.exists() {
        t!(fs::create_dir_all(&cache_dir));
    }

    let bin_root = out.join(dwn_ctx.host_target).join(destination);
    let tarball = cache_dir.join(&filename);
    let (base_url, url, should_verify) = match mode {
        DownloadSource::CI => {
            let dist_server = if dwn_ctx.llvm_assertions {
                dwn_ctx.stage0_metadata.config.artifacts_with_llvm_assertions_server.clone()
            } else {
                dwn_ctx.stage0_metadata.config.artifacts_server.clone()
            };
            let url = format!(
                "{}/{filename}",
                key.strip_suffix(&format!("-{}", dwn_ctx.llvm_assertions)).unwrap()
            );
            (dist_server, url, false)
        }
        DownloadSource::Dist => {
            let dist_server = dwn_ctx.stage0_metadata.config.dist_server.to_string();
            // NOTE: make `dist` part of the URL because that's how it's stored in src/stage0
            (dist_server, format!("dist/{key}/{filename}"), true)
        }
    };
    reject_inherited_upstream_rust_download_url(&base_url);

    // For the stage0 compiler, put special effort into ensuring the checksums are valid.
    let checksum = if should_verify {
        let error = format!(
            "src/stage0 doesn't contain a checksum for {url}. \
            Pre-built artifacts might not be available for this \
            target at this time, see https://doc.rust-lang.org/nightly\
            /rustc/platform-support.html for more information."
        );
        let sha256 = dwn_ctx.stage0_metadata.checksums_sha256.get(&url).expect(&error);
        if tarball.exists() {
            if verify(dwn_ctx.exec_ctx, &tarball, sha256) {
                unpack(dwn_ctx.exec_ctx, &tarball, &bin_root, prefix);
                return;
            } else {
                dwn_ctx.exec_ctx.do_if_verbose(|| {
                    println!(
                        "ignoring cached file {} due to failed verification",
                        tarball.display()
                    )
                });
                remove(dwn_ctx.exec_ctx, &tarball);
            }
        }
        Some(sha256)
    } else if tarball.exists() {
        unpack(dwn_ctx.exec_ctx, &tarball, &bin_root, prefix);
        return;
    } else {
        None
    };

    let mut help_on_error = "";
    if destination == "ci-rustc" {
        help_on_error = "ERROR: failed to download pre-built rustc from CI

NOTE: old builds get deleted after a certain time
HELP: if trying to compile an old commit of rustc, disable `download-rustc` in bootstrap.toml:

[rust]
download-rustc = false
";
    }
    download_file(dwn_ctx, out, &format!("{base_url}/{url}"), &tarball, help_on_error);
    if let Some(sha256) = checksum
        && !verify(dwn_ctx.exec_ctx, &tarball, sha256)
    {
        panic!("failed to verify {}", tarball.display());
    }

    unpack(dwn_ctx.exec_ctx, &tarball, &bin_root, prefix);
}

pub(crate) fn verify(exec_ctx: &ExecutionContext, path: &Path, expected: &str) -> bool {
    use sha2::Digest;

    exec_ctx.do_if_verbose(|| {
        println!("verifying {}", path.display());
    });

    if exec_ctx.dry_run() {
        return false;
    }

    let mut hasher = sha2::Sha256::new();

    let file = t!(File::open(path));
    let mut reader = BufReader::new(file);

    loop {
        let buffer = t!(reader.fill_buf());
        let l = buffer.len();
        // break if EOF
        if l == 0 {
            break;
        }
        hasher.update(buffer);
        reader.consume(l);
    }

    let checksum = hex_encode(hasher.finalize().as_slice());
    let verified = checksum == expected;

    if !verified {
        println!(
            "invalid checksum: \n\
            found:    {checksum}\n\
            expected: {expected}",
        );
    }

    verified
}

fn unpack(exec_ctx: &ExecutionContext, tarball: &Path, dst: &Path, pattern: &str) {
    eprintln!("extracting {} to {}", tarball.display(), dst.display());
    if !dst.exists() {
        t!(fs::create_dir_all(dst));
    }

    // `tarball` ends with `.tar.xz`; strip that suffix
    // example: `rust-dev-nightly-x86_64-unknown-linux-gnu`
    let uncompressed_filename =
        Path::new(tarball.file_name().expect("missing tarball filename")).file_stem().unwrap();
    let directory_prefix = Path::new(Path::new(uncompressed_filename).file_stem().unwrap());

    // decompress the file
    let data = t!(File::open(tarball), format!("file {} not found", tarball.display()));
    let decompressor = XzDecoder::new(BufReader::new(data));

    let mut tar = tar::Archive::new(decompressor);

    let is_ci_rustc = dst.ends_with("ci-rustc");
    let is_ci_llvm = dst.ends_with("ci-llvm");

    // `compile::Sysroot` needs to know the contents of the `rustc-dev` tarball to avoid adding
    // it to the sysroot unless it was explicitly requested. But parsing the 100 MB tarball is slow.
    // Cache the entries when we extract it so we only have to read it once.
    let mut recorded_entries = if is_ci_rustc { recorded_entries(dst, pattern) } else { None };

    for member in t!(tar.entries()) {
        let mut member = t!(member);
        let original_path = t!(member.path()).into_owned();
        // skip the top-level directory
        if original_path == directory_prefix {
            continue;
        }
        let mut short_path = t!(original_path.strip_prefix(directory_prefix));
        let is_builder_config = short_path.to_str() == Some(BUILDER_CONFIG_FILENAME);

        if !(short_path.starts_with(pattern) || ((is_ci_rustc || is_ci_llvm) && is_builder_config))
        {
            continue;
        }
        short_path = short_path.strip_prefix(pattern).unwrap_or(short_path);
        let dst_path = dst.join(short_path);

        exec_ctx.do_if_verbose(|| {
            println!("extracting {} to {}", original_path.display(), dst.display());
        });

        if !t!(member.unpack_in(dst)) {
            panic!("path traversal attack ??");
        }
        if let Some(record) = &mut recorded_entries {
            t!(writeln!(record, "{}", short_path.to_str().unwrap()));
        }
        let src_path = dst.join(original_path);
        if src_path.is_dir() && dst_path.exists() {
            continue;
        }
        if let Some(parent) = dst_path.parent() {
            t!(fs::create_dir_all(parent));
        }
        t!(move_file(src_path, dst_path));
    }
    let dst_dir = dst.join(directory_prefix);
    if dst_dir.exists() {
        t!(fs::remove_dir_all(&dst_dir), format!("failed to remove {}", dst_dir.display()));
    }
}

fn download_file<'a>(
    dwn_ctx: impl AsRef<DownloadContext<'a>>,
    out: &Path,
    url: &str,
    dest_path: &Path,
    help_on_error: &str,
) {
    let dwn_ctx = dwn_ctx.as_ref();

    dwn_ctx.exec_ctx.do_if_verbose(|| {
        println!("download {url}");
    });
    reject_inherited_upstream_rust_download_url(url);
    // Use a temporary file in case we crash while downloading, to avoid a corrupt download in cache/.
    let tempfile = tempdir(out).join(dest_path.file_name().unwrap());
    // While bootstrap itself only supports http and https downloads, downstream forks might
    // need to download components from other protocols. The match allows them adding more
    // protocols without worrying about merge conflicts if we change the HTTP implementation.
    match url.split_once("://").map(|(proto, _)| proto) {
        Some("http") | Some("https") => download_http_with_retries(
            dwn_ctx.host_target,
            dwn_ctx.is_running_on_ci(),
            dwn_ctx.exec_ctx,
            &tempfile,
            url,
            help_on_error,
        ),
        Some("file") => copy_file_url(url, &tempfile, dwn_ctx.src),
        Some(other) => panic!("unsupported protocol {other} in {url}"),
        None => panic!("no protocol in {url}"),
    }
    t!(move_file(&tempfile, dest_path), format!("failed to rename {tempfile:?} to {dest_path:?}"));
}

fn copy_file_url(url: &str, dest_path: &Path, src_root: &Path) {
    let source = resolve_file_url_path(url, src_root);
    t!(
        fs::copy(&source, dest_path),
        format!("failed to copy {} to {}", source.display(), dest_path.display())
    );
}

fn inherited_upstream_rust_download_host(url: &str) -> Option<String> {
    let (scheme, rest) = url.split_once("://")?;
    if !matches!(scheme.to_ascii_lowercase().as_str(), "http" | "https") {
        return None;
    }
    let authority = rest.split('/').next().unwrap_or_default();
    let host_port = authority.rsplit('@').next().unwrap_or(authority);
    let host = if host_port.starts_with('[') {
        host_port.split_once(']').map(|(host, _)| host.trim_start_matches('[')).unwrap_or(host_port)
    } else {
        host_port.split(':').next().unwrap_or(host_port)
    };
    let host = host.trim_end_matches('.').to_ascii_lowercase();
    if host == "rust-lang.org" || host.ends_with(".rust-lang.org") { Some(host) } else { None }
}

fn reject_inherited_upstream_rust_download_url(url: &str) {
    if let Some(host) = inherited_upstream_rust_download_host(url) {
        panic!("Trust bootstrap refuses inherited upstream Rust download host {host}: {url}");
    }
}

fn resolve_file_url_path(url: &str, src_root: &Path) -> PathBuf {
    let Some(raw_path) = url.strip_prefix("file://") else {
        panic!("not a file URL: {url}");
    };
    let raw_path = raw_path
        .strip_prefix("localhost/")
        .map(|path| format!("/{path}"))
        .unwrap_or_else(|| raw_path.to_string());
    let decoded_path = percent_decode_url_path(&raw_path);
    if decoded_path == "{trust-root}" {
        return src_root.to_path_buf();
    }
    if let Some(repo_relative) = decoded_path.strip_prefix("{trust-root}/") {
        return src_root.join(repo_relative);
    }
    PathBuf::from(decoded_path)
}

fn percent_decode_url_path(path: &str) -> String {
    let bytes = path.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut idx = 0;
    while idx < bytes.len() {
        if bytes[idx] == b'%' && idx + 2 < bytes.len() {
            let high = bytes[idx + 1];
            let low = bytes[idx + 2];
            if let (Some(high), Some(low)) = (hex_value(high), hex_value(low)) {
                decoded.push(high << 4 | low);
                idx += 3;
                continue;
            }
        }
        decoded.push(bytes[idx]);
        idx += 1;
    }
    String::from_utf8(decoded).expect("file URL path is not valid UTF-8")
}

fn hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests;

/// Create a temporary directory in `out` and return its path.
///
/// NOTE: this temporary directory is shared between all steps;
/// if you need an empty directory, create a new subdirectory inside it.
pub(crate) fn tempdir(out: &Path) -> PathBuf {
    let tmp = out.join("tmp");
    t!(fs::create_dir_all(&tmp));
    tmp
}

fn download_http_with_retries(
    host_target: TargetSelection,
    is_running_on_ci: bool,
    exec_ctx: &ExecutionContext,
    tempfile: &Path,
    url: &str,
    help_on_error: &str,
) {
    println!("downloading {url}");
    // Try curl. If that fails and we are on windows, fallback to PowerShell.
    // options should be kept in sync with
    // src/bootstrap/src/core/download.rs
    // for consistency
    let mut curl = command("curl").allow_failure();
    curl.args([
        // follow redirect
        "--location",
        // timeout if speed is < 10 bytes/sec for > 30 seconds
        "--speed-time",
        "30",
        "--speed-limit",
        "10",
        // timeout if cannot connect within 30 seconds
        "--connect-timeout",
        "30",
        // output file
        "--output",
        tempfile.to_str().unwrap(),
        // if there is an error, don't restart the download,
        // instead continue where it left off.
        "--continue-at",
        "-",
        // retry up to 3 times.  note that this means a maximum of 4
        // attempts will be made, since the first attempt isn't a *re*try.
        "--retry",
        "3",
        // show errors, even if --silent is specified
        "--show-error",
        // set timestamp of downloaded file to that of the server
        "--remote-time",
        // fail on non-ok http status
        "--fail",
    ]);
    // Don't print progress in CI; the \r wrapping looks bad and downloads don't take long enough for progress to be useful.
    if is_running_on_ci {
        curl.arg("--silent");
    } else {
        curl.arg("--progress-bar");
    }
    // --retry-all-errors was added in 7.71.0, don't use it if curl is old.
    if curl_version(exec_ctx) >= semver::Version::new(7, 71, 0) {
        curl.arg("--retry-all-errors");
    }
    curl.arg(url);
    if !curl.run(exec_ctx) {
        if host_target.contains("windows-msvc") {
            eprintln!("Fallback to PowerShell");
            for _ in 0..3 {
                let powershell = command("PowerShell.exe").allow_failure().args([
                    "/nologo",
                    "-Command",
                    "[Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12;",
                    &format!(
                        "(New-Object System.Net.WebClient).DownloadFile('{}', '{}')",
                        url, tempfile.to_str().expect("invalid UTF-8 not supported with powershell downloads"),
                    ),
                ]).run_capture_stdout(exec_ctx);

                if powershell.is_success() {
                    return;
                }

                eprintln!("\nspurious failure, trying again");
            }
        }
        if !help_on_error.is_empty() {
            eprintln!("{help_on_error}");
        }
        crate::exit!(1);
    }
}

fn curl_version(exec_ctx: &ExecutionContext) -> semver::Version {
    let mut curl = command("curl");
    curl.arg("-V");
    let curl = curl.run_capture_stdout(exec_ctx);
    if curl.is_failure() {
        return semver::Version::new(1, 0, 0);
    }
    let output = curl.stdout();
    extract_curl_version(output)
}
