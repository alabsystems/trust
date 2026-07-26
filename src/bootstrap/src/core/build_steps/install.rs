//! Implementation of the install aspects of the compiler.
//!
//! This module is responsible for installing the standard library,
//! compiler, and documentation.

use std::path::{Component, Path, PathBuf};
use std::{env, fs};

use crate::core::build_steps::dist;
use crate::core::build_steps::tool::{self, RustcPrivateCompilers};
use crate::core::builder::{Builder, RunConfig, ShouldRun, Step};
use crate::core::config::{Config, TargetSelection};
use crate::utils::exec::command;
use crate::utils::helpers::t;
use crate::utils::tarball::GeneratedTarball;
use crate::{Compiler, Kind};

#[cfg(target_os = "illumos")]
const SHELL: &str = "bash";
#[cfg(not(target_os = "illumos"))]
const SHELL: &str = "sh";

/// We have to run a few shell scripts, which choke quite a bit on both `\`
/// characters and on `C:\` paths, so normalize both of them away.
fn sanitize_sh(path: &Path, is_cygwin: bool) -> String {
    let path = path.to_str().unwrap().replace('\\', "/");
    return if is_cygwin { path } else { change_drive(unc_to_lfs(&path)).unwrap_or(path) };

    fn unc_to_lfs(s: &str) -> &str {
        s.strip_prefix("//?/").unwrap_or(s)
    }

    fn change_drive(s: &str) -> Option<String> {
        let mut ch = s.chars();
        let drive = ch.next().unwrap_or('C');
        if ch.next() != Some(':') {
            return None;
        }
        if ch.next() != Some('/') {
            return None;
        }
        // The prefix for Windows drives in Cygwin/MSYS2 is configurable, but
        // /proc/cygdrive is available regardless of configuration since 1.7.33
        Some(format!("/proc/cygdrive/{}/{}", drive, &s[drive.len_utf8() + 2..]))
    }
}

fn is_dir_writable_for_user(dir: &Path) -> bool {
    let tmp = dir.join(".tmp");
    match fs::create_dir_all(&tmp) {
        Ok(_) => {
            fs::remove_dir_all(tmp).unwrap();
            true
        }
        Err(e) => {
            if e.kind() == std::io::ErrorKind::PermissionDenied {
                false
            } else {
                panic!("Failed the write access check for the current user. {e}");
            }
        }
    }
}

fn install_sh(
    builder: &Builder<'_>,
    package: &str,
    build_compiler: impl Into<Option<Compiler>>,
    target: Option<TargetSelection>,
    tarball: &GeneratedTarball,
) {
    let _guard = match build_compiler.into() {
        Some(build_compiler) => builder.msg(Kind::Install, package, None, build_compiler, target),
        None => builder.msg_unstaged(Kind::Install, package, target.unwrap_or(builder.host_target)),
    };

    let prefix = default_path(&builder.config.prefix, "/usr/local");
    let sysconfdir = prefix.join(default_path(&builder.config.sysconfdir, "/etc"));
    let destdir_env = env::var_os("DESTDIR").map(PathBuf::from);
    let is_cygwin = builder.config.host_target.is_cygwin();

    // Sanity checks on the write access of user.
    //
    // When the `DESTDIR` environment variable is present, there is no point to
    // check write access for `prefix` and `sysconfdir` individually, as they
    // are combined with the path from the `DESTDIR` environment variable. In
    // this case, we only need to check the `DESTDIR` path, disregarding the
    // `prefix` and `sysconfdir` paths.
    if let Some(destdir) = &destdir_env {
        assert!(is_dir_writable_for_user(destdir), "User doesn't have write access on DESTDIR.");
    } else {
        assert!(
            is_dir_writable_for_user(&prefix),
            "User doesn't have write access on `install.prefix` path in the `bootstrap.toml`.",
        );
        assert!(
            is_dir_writable_for_user(&sysconfdir),
            "User doesn't have write access on `install.sysconfdir` path in `bootstrap.toml`."
        );
    }

    let datadir = prefix.join(default_path(&builder.config.datadir, "share"));
    let docdir = prefix.join(default_path(&builder.config.docdir, &format!("share/doc/{package}")));
    let mandir = prefix.join(default_path(&builder.config.mandir, "share/man"));
    let libdir = prefix.join(default_path(&builder.config.libdir, "lib"));
    let bindir = prefix.join(&builder.config.bindir); // Default in config.rs

    let empty_dir = builder.out.join("tmp/empty_dir");
    t!(fs::create_dir_all(&empty_dir));

    let mut cmd = command(SHELL);
    cmd.current_dir(&empty_dir)
        .arg(sanitize_sh(&tarball.decompressed_output().join("install.sh"), is_cygwin))
        .arg(format!("--prefix={}", prepare_dir(&destdir_env, prefix, is_cygwin)))
        .arg(format!("--sysconfdir={}", prepare_dir(&destdir_env, sysconfdir, is_cygwin)))
        .arg(format!("--datadir={}", prepare_dir(&destdir_env, datadir, is_cygwin)))
        .arg(format!("--docdir={}", prepare_dir(&destdir_env, docdir, is_cygwin)))
        .arg(format!("--bindir={}", prepare_dir(&destdir_env, bindir, is_cygwin)))
        .arg(format!("--libdir={}", prepare_dir(&destdir_env, libdir, is_cygwin)))
        .arg(format!("--mandir={}", prepare_dir(&destdir_env, mandir, is_cygwin)))
        .arg("--disable-ldconfig");
    cmd.run(builder);
    t!(fs::remove_dir_all(&empty_dir));
}

fn default_path(config: &Option<PathBuf>, default: &str) -> PathBuf {
    config.as_ref().cloned().unwrap_or_else(|| PathBuf::from(default))
}

fn prepare_dir(destdir_env: &Option<PathBuf>, mut path: PathBuf, is_cygwin: bool) -> String {
    // The DESTDIR environment variable is a standard way to install software in a subdirectory
    // while keeping the original directory structure, even if the prefix or other directories
    // contain absolute paths.
    //
    // More information on the environment variable is available here:
    // https://www.gnu.org/prep/standards/html_node/DESTDIR.html
    if let Some(destdir) = destdir_env {
        let without_destdir = path.clone();
        path.clone_from(destdir);
        // Custom .join() which ignores disk roots.
        for part in without_destdir.components() {
            if let Component::Normal(s) = part {
                path.push(s)
            }
        }
    }

    // The installation command is not executed from the current directory, but from a temporary
    // directory. To prevent relative paths from breaking this converts relative paths to absolute
    // paths. std::fs::canonicalize is not used as that requires the path to actually be present.
    if path.is_relative() {
        path = std::env::current_dir().expect("failed to get the current directory").join(path);
        assert!(path.is_absolute(), "could not make the path relative");
    }

    sanitize_sh(&path, is_cygwin)
}

fn should_install_extended_tool_for_tool_settings(
    extended: bool,
    tools: Option<&std::collections::HashSet<String>>,
    tool: &str,
) -> bool {
    extended
        && tools.is_none_or(|tools| {
            tools.iter().any(|entry| install_package_contains_selected_tool(entry, tool))
        })
}

fn should_install_extended_tool(config: &Config, tool: &str) -> bool {
    should_install_extended_tool_for_tool_settings(config.extended, config.tools.as_ref(), tool)
}

fn install_package_contains_selected_tool(config_tool: &str, package_tool: &str) -> bool {
    tool::tool_config_entry_selects_user_tool(config_tool, package_tool)
        || match package_tool {
            "trustfmt" => tool::tool_config_entry_selects_user_tool(config_tool, "targo-fmt"),
            "tippy" => tool::tool_config_entry_selects_user_tool(config_tool, "tippy-driver"),
            "trust-miri" => tool::tool_config_entry_selects_user_tool(config_tool, "targo-miri"),
            _ => false,
        }
}

macro_rules! install {
    (($sel:ident, $builder:ident, $_config:ident),
       $($name:ident,
       $condition_name: ident = $path_or_alias: literal,
       $default_cond:expr,
       IS_HOST: $IS_HOST:expr,
       $(ALIASES: [$($alias:literal),* $(,)?],)?
       $run_item:block $(, $c:ident)*;)+) => {
        $(
        #[derive(Debug, Clone, Hash, PartialEq, Eq)]
        pub struct $name {
            build_compiler: Compiler,
            target: TargetSelection,
        }

        impl $name {
            #[allow(dead_code)]
            fn should_build(config: &Config) -> bool {
                should_install_extended_tool(config, $path_or_alias)
            }
        }

        impl Step for $name {
            type Output = ();
            const IS_HOST: bool = $IS_HOST;
            $(const $c: bool = true;)*

            fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
                let run = run.$condition_name($path_or_alias);
                $(let run = run$(.alias($alias))*;)?
                run
            }

            fn is_default_step(builder: &Builder<'_>) -> bool {
                let $_config = &builder.config;
                $default_cond
            }

            fn make_run(run: RunConfig<'_>) {
                run.builder.ensure($name {
                    build_compiler: run.builder.compiler(run.builder.top_stage - 1, run.builder.config.host_target),
                    target: run.target,
                });
            }

            fn run($sel, $builder: &Builder<'_>) {
                $run_item
            }
        })+
    }
}

install!((self, builder, _config),
    Docs, path = "src/doc", _config.docs, IS_HOST: false, {
        let tarball = builder.ensure(dist::Docs { host: self.target }).expect("missing docs");
        install_sh(builder, "docs", self.build_compiler, Some(self.target), &tarball);
    };
    Std, path = "library/std", true, IS_HOST: false, ALIASES: ["trust-std", "rust-std"], {
        // `expect` should be safe, only None when host != build, but this
        // only runs when host == build
        let std = dist::Std::new(builder, self.target);
        let build_compiler = std.build_compiler;
        let tarball = builder.ensure(std).expect("missing std");
        install_sh(builder, "std", build_compiler, Some(self.target), &tarball);
    };
    Cargo, alias = "targo", Self::should_build(_config), IS_HOST: true, {
        let tarball = builder
            .ensure(dist::Cargo { build_compiler: self.build_compiler, target: self.target })
            .expect("missing targo");
        install_sh(builder, "targo", self.build_compiler, Some(self.target), &tarball);
    };
    // `path`, not `alias`: `targo-trust/` is a real source dir at the repo
    // root (unlike upstream's `cargo`, which lives under `src/tools/`), and
    // `ShouldRun::alias` asserts the name matches no on-disk path.
    TCargoTrust, path = "targo-trust", Self::should_build(_config), IS_HOST: true, {
        // `targo-trust` is a protected Targo external subcommand and invokes
        // the selected Trust compiler on ordinary crates. Installing it alone
        // would omit its package-manager, compiler, and standard-library
        // runtime and create an unusable public interface.
        builder.ensure(Rustc {
            build_compiler: self.build_compiler,
            target: self.target,
        });
        builder.ensure(Std {
            build_compiler: self.build_compiler,
            target: self.target,
        });
        builder.ensure(Cargo {
            build_compiler: self.build_compiler,
            target: self.target,
        });
        let tarball = builder
            .ensure(dist::TCargoTrust { build_compiler: self.build_compiler, target: self.target })
            .expect("missing targo-trust");
        install_sh(builder, "targo-trust", self.build_compiler, Some(self.target), &tarball);
    };
    RustAnalyzer, alias = "trust-analyzer", Self::should_build(_config), IS_HOST: true, {
        if let Some(tarball) =
            builder.ensure(dist::RustAnalyzer { compilers: RustcPrivateCompilers::from_build_compiler(builder, self.build_compiler, self.target), target: self.target })
        {
            install_sh(builder, "trust-analyzer", self.build_compiler, Some(self.target), &tarball);
        } else {
            builder.info(
                &format!("skipping Install trust-analyzer stage{} ({})", self.build_compiler.stage + 1, self.target),
            );
        }
    };
    Clippy, alias = "tippy", Self::should_build(_config), IS_HOST: true, {
        // Public Tippy refuses ambient Cargo and requires a coherent sibling
        // `targo`, compiler, and standard library. An explicit
        // `x install tippy` must install that runtime closure too; otherwise
        // it succeeds while leaving ordinary frontend invocations unusable.
        builder.ensure(Rustc {
            build_compiler: self.build_compiler,
            target: self.target,
        });
        builder.ensure(Std {
            build_compiler: self.build_compiler,
            target: self.target,
        });
        builder.ensure(Cargo {
            build_compiler: self.build_compiler,
            target: self.target,
        });
        let tarball = builder
            .ensure(dist::Clippy { compilers: RustcPrivateCompilers::from_build_compiler(builder, self.build_compiler, self.target), target: self.target })
            .expect("missing tippy");
        install_sh(builder, "tippy", self.build_compiler, Some(self.target), &tarball);
    };
    Miri, alias = "trust-miri", Self::should_build(_config), IS_HOST: true, {
        if let Some(tarball) = builder.ensure(dist::Miri { compilers: RustcPrivateCompilers::from_build_compiler(builder, self.build_compiler, self.target) , target: self.target }) {
            install_sh(builder, "trust-miri", self.build_compiler, Some(self.target), &tarball);
        } else {
            // Miri is only available on nightly
            builder.info(
                &format!("skipping Install trust-miri stage{} ({})", self.build_compiler.stage + 1, self.target),
            );
        }
    };
    LlvmTools, alias = "trust-llvm-tools", _config.llvm_tools_enabled && _config.llvm_enabled(_config.host_target), IS_HOST: true, {
        if let Some(tarball) = builder.ensure(dist::LlvmTools { target: self.target }) {
            install_sh(builder, "trust-llvm-tools", None, Some(self.target), &tarball);
        } else {
            builder.info(
                &format!("skipping trust-llvm-tools ({}): external LLVM", self.target),
            );
        }
    };
    Rustfmt, alias = "trustfmt", Self::should_build(_config), IS_HOST: true, {
        if let Some(tarball) = builder.ensure(dist::Rustfmt {
            compilers: RustcPrivateCompilers::from_build_compiler(builder, self.build_compiler, self.target),
            target: self.target
        }) {
            install_sh(builder, "trustfmt", self.build_compiler, Some(self.target), &tarball);
        } else {
            builder.info(
                &format!("skipping Install Trustfmt stage{} ({})", self.build_compiler.stage + 1, self.target),
            );
        }
    };
    Rustc, path = "compiler/rustc", true, IS_HOST: true, ALIASES: ["trustc", "rustc"], {
        let tarball = builder.ensure(dist::Rustc {
            target_compiler: builder.compiler(self.build_compiler.stage + 1, self.target),
        });
        install_sh(builder, "trustc", self.build_compiler, Some(self.target), &tarball);
    };
    RustcDev, alias = "trustc-dev", Self::should_build(_config), IS_HOST: true, {
        if let Some(tarball) = builder.ensure(dist::RustcDev {
            build_compiler: self.build_compiler, target: self.target
        }) {
            install_sh(builder, "trustc-dev", self.build_compiler, Some(self.target), &tarball);
        } else {
            builder.info(
                &format!("skipping Install TrustcDev stage{} ({})", self.build_compiler.stage + 1, self.target),
            );
        }
    };
    LlvmBitcodeLinker, alias = "llvm-bitcode-linker", Self::should_build(_config), IS_HOST: true, {
        if let Some(tarball) = builder.ensure(dist::LlvmBitcodeLinker { build_compiler: self.build_compiler, target: self.target }) {
            install_sh(builder, "llvm-bitcode-linker", self.build_compiler, Some(self.target), &tarball);
        } else {
            builder.info(
                &format!("skipping llvm-bitcode-linker stage{} ({})", self.build_compiler.stage + 1, self.target),
            );
        }
    };
);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Src {
    stage: u32,
}

impl Step for Src {
    type Output = ();
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("src")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        let config = &builder.config;
        config.extended && config.tools.as_ref().is_none_or(|t| t.contains("src"))
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Src { stage: run.builder.top_stage });
    }

    fn run(self, builder: &Builder<'_>) {
        let tarball = builder.ensure(dist::Src);
        install_sh(builder, "src", None, None, &tarball);
    }
}

#[cfg(test)]
mod tests;
