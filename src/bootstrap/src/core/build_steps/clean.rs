//! `./x.py clean`
//!
//! Responsible for cleaning out a build directory of all old and stale
//! artifacts to prepare for a fresh build. Currently doesn't remove the
//! `build/cache` directory (download cache) or the `build/$target/llvm`
//! directory unless the `--all` flag is present.

use std::fs;
use std::io::{self, ErrorKind};
use std::path::{Component, Path, PathBuf};

use crate::core::builder::{
    Builder, CommandLineStep, Kind, RunConfig, ShouldRun, crate_description,
};
use crate::core::compiler::Compiler;
use crate::core::config::flags::Subcommand;
use crate::core::session::{Mode, Session};
use crate::utils::build_stamp::BuildStamp;
use crate::utils::helpers::t;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CleanAll {}

impl CommandLineStep for CleanAll {
    type Output = ();

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        // Normally this step is invoked implicitly via `./x clean`, but all
        // steps are required to register at least one explicit path/alias.
        run.alias("default")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(CleanAll {})
    }

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let Subcommand::Clean { all, stage } = builder.config.cmd else {
            unreachable!("wrong subcommand?")
        };

        if all && stage.is_some() {
            panic!("--all and --stage can't be used at the same time for `x clean`");
        }

        clean(builder.sess, all, stage)
    }
}

macro_rules! clean_crate_tree {
    ( $( $name:ident, $mode:path, $root_crate:literal);+ $(;)? ) => { $(
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub struct $name {
            compiler: Compiler,
            crates: Vec<String>,
        }

        impl CommandLineStep for $name {
            type Output = ();

            fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
                run.crate_or_deps($root_crate)
            }

            fn make_run(run: RunConfig<'_>) {
                let builder = run.builder;
                let compiler = builder.compiler(builder.top_stage, run.target);
                builder.ensure(Self { crates: run.cargo_crates_in_set(), compiler });
            }

            fn run(self, builder: &Builder<'_>) -> Self::Output {
                let compiler = self.compiler;
                let target = compiler.host;
                let mut cargo = builder.bare_cargo(compiler, $mode, target, Kind::Clean);

                // Since https://github.com/rust-lang/rust/pull/111076 enables
                // unstable cargo feature (`public-dependency`), we need to ensure
                // that unstable features are enabled before reading libstd Cargo.toml.
                cargo.env("RUSTC_BOOTSTRAP", "1");

                for krate in &*self.crates {
                    cargo.arg("-p");
                    cargo.arg(krate);
                }

                builder.info(&format!(
                    "Cleaning{} stage{} {} artifacts ({} -> {})",
                    crate_description(&self.crates), compiler.stage, stringify!($name).to_lowercase(), &compiler.host, target,
                ));

                // NOTE: doesn't use `run_cargo` because we don't want to save a stamp file,
                // and doesn't use `stream_cargo` to avoid passing `--message-format` which `clean` doesn't accept.
                cargo.run(builder);
            }
        }
    )+ }
}

clean_crate_tree! {
    Rustc, Mode::Rustc, "rustc-main";
    Std, Mode::Std, "sysroot";
}

fn clean(sess: &Session, all: bool, stage: Option<u32>) {
    if sess.config.dry_run() {
        return;
    }

    // Trust: reject malformed target names before deleting even temporary
    // artifacts. Cleanup helpers also validate when called independently.
    if !all {
        clean_host_paths(sess, stage.is_none());
    }
    rm_rf("tmp".as_ref());

    // Clean the entire build directory
    if all {
        // Trust: `rm_rf` never follows a link, so on a symlinked build directory
        // (docs/BUILD_AND_INSTALL.md, "Keeping Spotlight out of build/")
        // it removed only the link and left every artifact behind.
        rm_rf_build_dir(&sess.out);
        return;
    }

    // Clean the target stage artifacts
    if let Some(stage) = stage {
        clean_specific_stage(sess, stage);
        return;
    }

    // Follow the default behaviour
    clean_default(sess);
}

// Trust: a target name is deletion authority only over a direct child of out.
// TargetSelection may retain a nonexistent user string verbatim, including
// `..` or an absolute path. Validate the entire selection before any deletion.
fn clean_host_paths(sess: &Session, include_build_host: bool) -> Vec<PathBuf> {
    let mut hosts = Vec::new();
    for host in sess.hosts.iter().copied().chain(include_build_host.then_some(sess.host_target)) {
        let path = host.as_ref();
        let mut components = path.components();
        assert!(
            matches!(components.next(), Some(Component::Normal(name)) if name == path.as_os_str())
                && components.next().is_none(),
            "cleanup host must be a single directory name: {host:?}"
        );
        let host = sess.out.join(path);
        if !hosts.contains(&host) {
            hosts.push(host);
        }
    }
    hosts
}

fn clean_specific_stage(sess: &Session, stage: u32) {
    for host in clean_host_paths(sess, false) {
        // Trust: a nested host alias is an entry to remove, never a directory
        // whose external or ancestor contents may be cleaned through it.
        if host.symlink_metadata().is_ok_and(|metadata| metadata.file_type().is_symlink()) {
            rm_rf(&host);
            continue;
        }
        let entries = match host.read_dir() {
            Ok(iter) => iter,
            Err(_) => continue,
        };

        for entry in entries {
            let entry = t!(entry);
            let stage_prefix = format!("stage{}", stage + 1);

            // if current entry is not related with the target stage, continue
            if !entry.file_name().to_str().unwrap_or("").contains(&stage_prefix) {
                continue;
            }

            // Trust: rm_rf removes a nested link itself; resolving it first
            // could delete another tree or even this output root and its lock.
            rm_rf(&entry.path());
        }
    }
}

fn clean_default(sess: &Session) {
    // Trust: clean the actual build host too, which may differ from build.host.
    // Session::new points out/host at this directory; do not traverse an
    // arbitrary replacement of that convenience alias during deletion.
    let hosts = clean_host_paths(sess, true);
    rm_rf(&sess.out.join("tmp"));
    rm_rf(&sess.out.join("dist"));
    rm_rf(&sess.out.join("bootstrap").join(".last-warned-change-id"));
    rm_rf(&sess.out.join("bootstrap-shims-dump"));
    rm_rf(BuildStamp::new(&sess.out).with_prefix("rustfmt").path());

    for host in hosts {
        if host.symlink_metadata().is_ok_and(|metadata| metadata.file_type().is_symlink()) {
            rm_rf(&host);
            continue;
        }
        let entries = match host.read_dir() {
            Ok(iter) => iter,
            Err(_) => continue,
        };

        for entry in entries {
            let entry = t!(entry);
            if entry.file_name().to_str() == Some("llvm") {
                continue;
            }
            // Trust: never turn a nested symlink into deletion authority over
            // the target it names.
            rm_rf(&entry.path());
        }
    }
}

// Trust: empty artifacts while preserving the physical output directory and
// its persistent `lock` inode. A still-open unlinked lock permits a second
// owner to lock a replacement inode, so it must outlive clean --all.
// Under the sanctioned Spotlight layout
// (`build` is a symlink to the real sibling `build.noindex`) the artifacts live
// behind the link: remove the directory's CONTENTS and keep the link, so the next
// build writes into the same excluded directory instead of recreating a real,
// indexed `build/`. Nothing below `out` is followed: each entry goes through
// `rm_rf`, which removes a nested link without entering it. Any other link (to a
// shared build tree, another volume, or a `build.noindex` that is itself a link),
// and a dangling link keep the upstream behavior: `rm_rf` removes the link
// itself and never deletes through it.
fn rm_rf_build_dir(out: &Path) {
    let real_directory = out.symlink_metadata().is_ok_and(|metadata| metadata.is_dir());
    if !real_directory && !is_sanctioned_build_link(out) {
        rm_rf(out);
        return;
    }
    for entry in t!(fs::read_dir(out)) {
        let entry = t!(entry);
        if entry.file_name() != "lock" {
            rm_rf(&entry.path());
        }
    }
}

// Trust: the Rust twin of `stage2_tools::is_sanctioned_build_link` and the
// scripts' copies: `out` is a symlink that resolves to `<canonical parent of
// out>/build.noindex`, and that directory is real, not itself a link.
fn is_sanctioned_build_link(out: &Path) -> bool {
    if !out.symlink_metadata().is_ok_and(|m| m.file_type().is_symlink()) {
        return false;
    }
    let Some(parent) = out.parent() else {
        return false;
    };
    let Ok(parent) =
        fs::canonicalize(if parent.as_os_str().is_empty() { Path::new(".") } else { parent })
    else {
        return false;
    };
    let physical = parent.join("build.noindex");
    physical.symlink_metadata().is_ok_and(|m| m.file_type().is_dir())
        && fs::canonicalize(out).is_ok_and(|resolved| resolved == physical)
}

fn rm_rf(path: &Path) {
    match fs::remove_dir_all(path) {
        Ok(()) => return,
        // Already deleted, nothing for us to do.
        Err(e) if e.kind() == ErrorKind::NotFound => return,
        _ => {}
    }

    // If remove_dir_all fails then retry.
    // We do so manually so we can provide better diagnostics,
    // e.g. pointing to the exact file that failed.
    match path.symlink_metadata() {
        Err(e) => {
            if e.kind() == ErrorKind::NotFound {
                return;
            }
            panic!("failed to get metadata for file {}: {}", path.display(), e);
        }
        Ok(metadata) => {
            if !metadata.file_type().is_dir() {
                do_op(path, "remove file", |p| match fs::remove_file(p) {
                    #[cfg(windows)]
                    Err(e)
                        if e.kind() == std::io::ErrorKind::PermissionDenied
                            && p.file_name().and_then(std::ffi::OsStr::to_str)
                                == Some("bootstrap.exe") =>
                    {
                        eprintln!("WARNING: failed to delete '{}'.", p.display());
                        Ok(())
                    }
                    r => r,
                });

                return;
            }

            for file in t!(fs::read_dir(path)) {
                rm_rf(&t!(file).path());
            }

            do_op(path, "remove dir", |p| match fs::remove_dir(p) {
                // Check for dir not empty on Windows
                #[cfg(windows)]
                Err(e) if e.kind() == ErrorKind::DirectoryNotEmpty => Ok(()),
                r => r,
            });
        }
    };
}

fn do_op<F>(path: &Path, desc: &str, mut f: F)
where
    F: FnMut(&Path) -> io::Result<()>,
{
    match f(path) {
        Ok(()) => {}
        // On windows we can't remove a readonly file, and git will often clone files as readonly.
        // As a result, we have some special logic to remove readonly files on windows.
        // This is also the reason that we can't use things like fs::remove_dir_all().
        #[cfg(windows)]
        Err(ref e) if e.kind() == ErrorKind::PermissionDenied => {
            let m = t!(path.symlink_metadata());
            let mut p = m.permissions();
            // this os not unix, so clippy gives FP
            #[expect(clippy::permissions_set_readonly_false)]
            p.set_readonly(false);
            t!(fs::set_permissions(path, p));
            f(path).unwrap_or_else(|e| {
                // Delete symlinked directories on Windows
                if fs::remove_dir(path).is_ok() {
                    return;
                }
                panic!("failed to {} {}: {}", desc, path.display(), e);
            });
        }
        Err(e) => {
            panic!("failed to {} {}: {}", desc, path.display(), e);
        }
    }
}

// Trust: `x clean --all` through a symlinked build directory.
#[cfg(test)]
mod tests;
