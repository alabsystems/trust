//! Implementation of the various distribution aspects of the compiler.
//!
//! This module is responsible for creating tarballs of the standard library,
//! compiler, and documentation. This ends up being what we distribute to
//! everyone as well.
//!
//! No tarball is actually created literally in this file, but rather we shell
//! out to `rust-installer` still. This may one day be replaced with bits and
//! pieces of `rustup.rs`!

use std::collections::HashSet;
use std::ffi::OsStr;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::{env, fs};

use object::BinaryFormat;
use object::read::archive::ArchiveFile;
#[cfg(feature = "tracing")]
use tracing::instrument;

use crate::core::build_steps::doc::DocumentationFormat;
use crate::core::build_steps::tool::{
    self, RustcPrivateCompilers, ToolTargetBuildMode, get_tool_target_compiler,
};
use crate::core::build_steps::vendor::Vendor;
use crate::core::build_steps::{compile, llvm};
use crate::core::builder::{Builder, Kind, RunConfig, ShouldRun, Step, StepMetadata};
use crate::core::config::TargetSelection;
use crate::utils::build_stamp::{self, BuildStamp};
use crate::utils::channel::{self, Info};
use crate::utils::exec::{BootstrapCommand, command};
use crate::utils::helpers::{
    exe, is_dylib, move_file, t, timeit,
};
use crate::utils::tarball::{GeneratedTarball, OverlayKind, Tarball};
use crate::{Compiler, DependencyType, FileType, LLVM_TOOLS, Mode, trace};

pub fn pkgname(builder: &Builder<'_>, component: &str) -> String {
    format!("{}-{}", component, builder.rust_package_vers())
}

pub(crate) fn distdir(builder: &Builder<'_>) -> PathBuf {
    builder.out.join("dist")
}

pub fn tmpdir(builder: &Builder<'_>) -> PathBuf {
    builder.out.join("tmp/dist")
}

/// `tool` here is the Trust-preferred user-facing tool-settings alias. The
/// `tools = [...]` list also accepts Rust-compatible spellings such as
/// `rustfmt`, `clippy`, and `rust-analyzer` as selectors for the same Trust
/// tools.
fn should_build_extended_tool(builder: &Builder<'_>, tool: &str) -> bool {
    if !builder.config.extended {
        return false;
    }
    builder.config.tools.as_ref().is_none_or(|tools| {
        tools.iter().any(|entry| {
            crate::core::build_steps::tool::tool_config_entry_selects_user_tool(entry, tool)
        })
    })
}

fn cargo_dist_bin_names(target: TargetSelection) -> [String; 2] {
    [exe("targo", target), exe("cargo", target)]
}

fn compiler_dist_bin_names(target: TargetSelection) -> [String; 2] {
    [exe("trustc", target), exe("rustc", target)]
}

/// The VERIFICATION BACKENDS the trustc component must carry: the temporal model
/// checker, the SAT/SMT solver, and the CIC kernel.
///
/// These ship INSIDE the compiler component rather than as their own rustup
/// components, for the same reason `trust-analyzer-proc-macro-srv` does (see the
/// comment at its copy site below): they are REQUIRED ENTRYPOINTS of what a Trust
/// compiler is, not optional add-ons like clippy or miri. `trustc` verifies as it
/// compiles — `TrustVerify::On` is the default and `trust_verify_level` defaults to
/// the maximum — so a distributed trustc without these is a compiler whose
/// advertised behaviour silently cannot happen. It does not fail; it just never
/// proves anything.
///
/// That is not hypothetical. Until this function existed, `x.py dist` shipped
/// exactly `[trustc, rustc]`, and a locally-built stage2 was separately observed
/// shipping no `ty` at all because `bootstrap.toml`'s `tools` allowlist omitted it —
/// a toolchain that compiled perfectly and could not model-check a thing, reported
/// as a successful build. Shipping that to users is the same defect at distribution
/// scale, which is why absence here is an ERROR rather than a quiet skip.
///
/// No collision with a dedicated component (the concern that keeps cargo and the
/// extended tools out of this image): none of these three HAS one — there is no
/// `dist::Ty`/`Ay`/`Clean` step, so before this they were shipped by nothing.
fn verifier_dist_bin_names(target: TargetSelection) -> [String; 3] {
    [exe("ty", target), exe("ay", target), exe("clean", target)]
}

fn trustdoc_dist_bin_names(target: TargetSelection) -> [String; 1] {
    [exe("trustdoc", target)]
}

fn rust_analyzer_proc_macro_dist_bin_names(target: TargetSelection) -> [String; 1] {
    [exe("trust-analyzer-proc-macro-srv", target)]
}

fn tippy_dist_bin_names(target: TargetSelection) -> [String; 3] {
    [exe("tippy", target), exe("targo-tippy", target), exe("tippy-driver", target)]
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Docs {
    pub host: TargetSelection,
}

impl Step for Docs {
    type Output = Option<GeneratedTarball>;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trust-docs")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        builder.config.docs
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Docs { host: run.target });
    }

    /// Builds the `trust-docs` installer component.
    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let host = self.host;
        // FIXME: explicitly enumerate the steps that should be executed here, and gather their
        // documentation, rather than running all default steps and then read their output
        // from a shared directory.
        builder.run_default_doc_steps();

        // In case no default doc steps are run for host, it is possible that `<host>/doc` directory
        // is never created.
        if !builder.config.dry_run() {
            t!(fs::create_dir_all(builder.doc_out(host)));
        }

        let dest = "share/doc/rust/html";

        let mut tarball = Tarball::new(builder, "trust-docs", &host.triple);
        tarball.set_product_name("Trust Documentation");
        tarball.add_bulk_dir(builder.doc_out(host), dest);
        tarball.add_file(builder.src.join("src/doc/robots.txt"), dest, FileType::Regular);
        tarball.add_file(builder.src.join("src/doc/sitemap.txt"), dest, FileType::Regular);
        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("docs", self.host))
    }
}

/// Builds the `trust-docs-json` installer component.
/// It contains the documentation of the standard library in JSON format.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct JsonDocs {
    build_compiler: Compiler,
    target: TargetSelection,
}

impl Step for JsonDocs {
    type Output = Option<GeneratedTarball>;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trust-docs-json")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        builder.config.docs
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(JsonDocs {
            build_compiler: run.builder.compiler_for_std(run.builder.top_stage),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let target = self.target;
        let directory = builder.ensure(crate::core::build_steps::doc::Std::from_build_compiler(
            self.build_compiler,
            target,
            DocumentationFormat::Json,
        ));

        let dest = "share/doc/rust/json";

        let mut tarball = Tarball::new(builder, "trust-docs-json", &target.triple);
        tarball.set_product_name("Trust Documentation In JSON Format");
        tarball.is_preview(true);
        tarball.add_bulk_dir(directory, dest);
        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("json-docs", self.target).built_by(self.build_compiler))
    }
}

/// Builds the `trustc-docs` installer component.
/// Apart from the documentation of the `rustc_*` crates, it also includes the documentation of
/// various in-tree helper tools (bootstrap, build_helper, tidy),
/// and also rustc_private tools like rustdoc, clippy, miri or rustfmt.
///
/// It is currently hosted at <https://doc.rust-lang.org/nightly/nightly-rustc>.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct RustcDocs {
    target: TargetSelection,
}

impl Step for RustcDocs {
    type Output = GeneratedTarball;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trustc-docs").alias("rustc-docs")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        builder.config.compiler_docs
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(RustcDocs { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let target = self.target;
        builder.run_default_doc_steps();

        let mut tarball = Tarball::new(builder, "trustc-docs", &target.triple);
        tarball.set_product_name("Trustc Documentation");
        tarball.add_bulk_dir(builder.compiler_doc_out(target), "share/doc/rust/html/rustc-docs");
        tarball.generate()
    }
}

fn find_files(files: &[&str], path: &[PathBuf]) -> Vec<PathBuf> {
    let mut found = Vec::with_capacity(files.len());

    for file in files {
        let file_path = path.iter().map(|dir| dir.join(file)).find(|p| p.exists());

        if let Some(file_path) = file_path {
            found.push(file_path);
        } else {
            panic!("Could not find '{file}' in {path:?}");
        }
    }

    found
}

fn make_win_dist(plat_root: &Path, target: TargetSelection, builder: &Builder<'_>) {
    if builder.config.dry_run() {
        return;
    }

    let (bin_path, lib_path) = get_cc_search_dirs(target, builder);

    let compiler = if target == "i686-pc-windows-gnu" {
        "i686-w64-mingw32-gcc.exe"
    } else if target == "x86_64-pc-windows-gnu" {
        "x86_64-w64-mingw32-gcc.exe"
    } else {
        "gcc.exe"
    };
    let target_tools = [compiler, "ld.exe", "dlltool.exe", "libwinpthread-1.dll"];

    // Libraries necessary to link the windows-gnu toolchains.
    // System libraries will be preferred if they are available (see #67429).
    let target_libs = [
        //MinGW libs
        "libgcc.a",
        "libgcc_eh.a",
        "libgcc_s.a",
        "libm.a",
        "libmingw32.a",
        "libmingwex.a",
        "libstdc++.a",
        "libiconv.a",
        "libmoldname.a",
        "libpthread.a",
        // Windows import libs
        // This *should* contain only the set of libraries necessary to link the standard library,
        // however we've had problems with people accidentally depending on extra libs being here,
        // so we can't easily remove entries.
        "libadvapi32.a",
        "libbcrypt.a",
        "libcomctl32.a",
        "libcomdlg32.a",
        "libcredui.a",
        "libcrypt32.a",
        "libdbghelp.a",
        "libgdi32.a",
        "libimagehlp.a",
        "libiphlpapi.a",
        "libkernel32.a",
        "libmsimg32.a",
        "libmsvcrt.a",
        "libntdll.a",
        "libodbc32.a",
        "libole32.a",
        "liboleaut32.a",
        "libopengl32.a",
        "libpsapi.a",
        "librpcrt4.a",
        "libsecur32.a",
        "libsetupapi.a",
        "libshell32.a",
        "libsynchronization.a",
        "libuser32.a",
        "libuserenv.a",
        "libuuid.a",
        "libwinhttp.a",
        "libwinmm.a",
        "libwinspool.a",
        "libws2_32.a",
        "libwsock32.a",
    ];

    //Find mingw artifacts we want to bundle
    let target_tools = find_files(&target_tools, &bin_path);
    let target_libs = find_files(&target_libs, &lib_path);

    //Copy platform tools to platform-specific bin directory
    let plat_target_bin_self_contained_dir =
        plat_root.join("lib/rustlib").join(target).join("bin/self-contained");
    fs::create_dir_all(&plat_target_bin_self_contained_dir)
        .expect("creating plat_target_bin_self_contained_dir failed");
    for src in target_tools {
        builder.copy_link_to_folder(&src, &plat_target_bin_self_contained_dir);
    }

    // Warn windows-gnu users that the bundled GCC cannot compile C files
    builder.create(
        &plat_target_bin_self_contained_dir.join("GCC-WARNING.txt"),
        "gcc.exe contained in this folder cannot be used for compiling C files - it is only \
         used as a linker. In order to be able to compile projects containing C code use \
         the GCC provided by MinGW or Cygwin.",
    );

    //Copy platform libs to platform-specific lib directory
    let plat_target_lib_self_contained_dir =
        plat_root.join("lib/rustlib").join(target).join("lib/self-contained");
    fs::create_dir_all(&plat_target_lib_self_contained_dir)
        .expect("creating plat_target_lib_self_contained_dir failed");
    for src in target_libs {
        builder.copy_link_to_folder(&src, &plat_target_lib_self_contained_dir);
    }
}

fn make_win_llvm_dist(plat_root: &Path, target: TargetSelection, builder: &Builder<'_>) {
    if builder.config.dry_run() {
        return;
    }

    let (_, lib_path) = get_cc_search_dirs(target, builder);

    // Libraries necessary to link the windows-gnullvm toolchains.
    // System libraries will be preferred if they are available (see #67429).
    let target_libs = [
        // MinGW libs
        "libunwind.a",
        "libunwind.dll.a",
        "libmingw32.a",
        "libmingwex.a",
        "libmsvcrt.a",
        // Windows import libs, remove them once std transitions to raw-dylib
        "libkernel32.a",
        "libuser32.a",
        "libntdll.a",
        "libuserenv.a",
        "libws2_32.a",
        "libdbghelp.a",
    ];

    //Find mingw artifacts we want to bundle
    let target_libs = find_files(&target_libs, &lib_path);

    //Copy platform libs to platform-specific lib directory
    let plat_target_lib_self_contained_dir =
        plat_root.join("lib/rustlib").join(target).join("lib/self-contained");
    fs::create_dir_all(&plat_target_lib_self_contained_dir)
        .expect("creating plat_target_lib_self_contained_dir failed");
    for src in target_libs {
        builder.copy_link_to_folder(&src, &plat_target_lib_self_contained_dir);
    }
}

fn runtime_dll_dist(rust_root: &Path, target: TargetSelection, builder: &Builder<'_>) {
    if builder.config.dry_run() {
        return;
    }

    let (bin_path, _) = get_cc_search_dirs(target, builder);

    let mut rustc_dlls = vec![];
    // windows-gnu and windows-gnullvm require different runtime libs
    if target.is_windows_gnu() {
        rustc_dlls.push("libwinpthread-1.dll");
        if target.starts_with("i686-") {
            rustc_dlls.push("libgcc_s_dw2-1.dll");
        } else {
            rustc_dlls.push("libgcc_s_seh-1.dll");
        }
    } else if target.is_windows_gnullvm() {
        rustc_dlls.push("libunwind.dll");
    } else {
        panic!("Vendoring of runtime DLLs for `{target}` is not supported`");
    }
    let rustc_dlls = find_files(&rustc_dlls, &bin_path);

    // Copy runtime dlls next to rustc.exe
    let rust_bin_dir = rust_root.join("bin/");
    fs::create_dir_all(&rust_bin_dir).expect("creating rust_bin_dir failed");
    for src in &rustc_dlls {
        builder.copy_link_to_folder(src, &rust_bin_dir);
    }

    if builder.config.lld_enabled {
        // rust-lld.exe also needs runtime dlls
        let rust_target_bin_dir = rust_root.join("lib/rustlib").join(target).join("bin");
        fs::create_dir_all(&rust_target_bin_dir).expect("creating rust_target_bin_dir failed");
        for src in &rustc_dlls {
            builder.copy_link_to_folder(src, &rust_target_bin_dir);
        }
    }
}

fn get_cc_search_dirs(
    target: TargetSelection,
    builder: &Builder<'_>,
) -> (Vec<PathBuf>, Vec<PathBuf>) {
    //Ask gcc where it keeps its stuff
    let mut cmd = command(builder.cc(target));
    cmd.arg("-print-search-dirs");
    let gcc_out = cmd.run_capture_stdout(builder).stdout();

    let mut bin_path: Vec<_> = env::split_paths(&env::var_os("PATH").unwrap_or_default()).collect();
    let mut lib_path = Vec::new();

    for line in gcc_out.lines() {
        let idx = line.find(':').unwrap();
        let key = &line[..idx];
        let trim_chars: &[_] = &[' ', '='];
        let value = env::split_paths(line[(idx + 1)..].trim_start_matches(trim_chars));

        if key == "programs" {
            bin_path.extend(value);
        } else if key == "libraries" {
            lib_path.extend(value);
        }
    }
    (bin_path, lib_path)
}

/// Builds the `trust-mingw` installer component.
///
/// This contains all the bits and pieces to run the MinGW Windows targets
/// without any extra installed software (e.g., we bundle gcc, libraries, etc.).
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Mingw {
    target: TargetSelection,
}

impl Step for Mingw {
    type Output = Option<GeneratedTarball>;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trust-mingw").alias("rust-mingw")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Mingw { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let target = self.target;
        if !target.contains("pc-windows-gnu") || !builder.config.dist_include_mingw_linker {
            return None;
        }

        let mut tarball = Tarball::new(builder, "trust-mingw", &target.triple);
        tarball.set_product_name("Trust MinGW");

        if target.ends_with("pc-windows-gnu") {
            make_win_dist(tarball.image_dir(), target, builder);
        } else if target.ends_with("pc-windows-gnullvm") {
            make_win_llvm_dist(tarball.image_dir(), target, builder);
        } else {
            unreachable!();
        }

        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("mingw", self.target))
    }
}

/// Creates the `trustc` installer component.
///
/// This includes:
/// - The compiler and LLVM.
/// - Debugger scripts.
/// - Various helper tools, e.g. LLD or Rust Analyzer proc-macro server (if enabled).
/// - The licenses of all code used by the compiler.
///
/// It does not include any standard library.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Rustc {
    /// This is the compiler that we will *ship* in this dist step.
    pub target_compiler: Compiler,
}

impl Step for Rustc {
    type Output = GeneratedTarball;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("compiler/rustc").alias("trustc").alias("rustc")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Rustc {
            target_compiler: run.builder.compiler(run.builder.top_stage, run.target),
        });
    }

    fn run(self, builder: &Builder<'_>) -> GeneratedTarball {
        let target_compiler = self.target_compiler;
        let target = self.target_compiler.host;

        let tarball = Tarball::new(builder, "trustc", &target.triple);

        // Prepare the rustc "image", what will actually end up getting installed
        prepare_image(builder, target_compiler, tarball.image_dir());

        // On MinGW we've got a few runtime DLL dependencies that we need to
        // include.
        // On 32-bit MinGW we're always including a DLL which needs some extra
        // licenses to distribute. On 64-bit MinGW we don't actually distribute
        // anything requiring us to distribute a license, but it's likely the
        // install will *also* include the trust-mingw package, which also needs
        // licenses, so to be safe we just include it here in all MinGW packages.
        if target.contains("pc-windows-gnu") && builder.config.dist_include_mingw_linker {
            runtime_dll_dist(tarball.image_dir(), target, builder);
            tarball.add_dir(builder.src.join("src/etc/third-party"), "share/doc");
        }

        return tarball.generate();

        fn prepare_image(builder: &Builder<'_>, target_compiler: Compiler, image: &Path) {
            let target = target_compiler.host;
            let src = builder.sysroot(target_compiler);

            // Copy only compiler binaries. The stage sysroot `bin` also
            // contains Cargo and extended tools; shipping those inside the
            // rustc component collides with their dedicated rustup components.
            t!(fs::create_dir_all(image.join("bin")));
            for compiler in compiler_dist_bin_names(target) {
                builder.copy_link(
                    &src.join("bin").join(&compiler),
                    &image.join("bin").join(&compiler),
                    FileType::Executable,
                );
            }

            // The VERIFICATION BACKENDS (see `verifier_dist_bin_names`).
            //
            // They must be ENSURED here, not assumed present: a local `x.py build`
            // installs them into the sysroot via
            // `should_ensure_default_verifier_tool_bins`, which is deliberately
            // `kind == Kind::Build` ONLY — "dist/install/test steps have explicit
            // component graphs" (compile.rs). So during dist the sysroot has the
            // compiler and nothing else, and reading it directly finds no `ty`. This
            // call IS the trustc component's explicit graph entry for them, and it is
            // the same shape as the `RustAnalyzerProcMacroSrv` ensure below.
            tool::ensure_default_verifier_tool_bins(builder, target_compiler, &src);

            // ABSENCE IS FATAL, deliberately. After the ensure above, a backend is
            // missing only when this build CANNOT produce it (its `tools = [...]`
            // allowlist entry was omitted, or its source is absent), and quietly
            // omitting it is exactly how a compile-only "Trust toolchain" gets
            // published. Narrowing a build stays possible — you just cannot narrow it
            // and still call the result a distributable trustc component. The panic
            // names the backend, what the toolchain loses without it, and the two ways
            // to resolve it.
            for bin in verifier_dist_bin_names(target) {
                let from = src.join("bin").join(&bin);
                // Bootstrap executes every step TWICE — a dry-run pass that builds
                // the step graph, then the real one. `copy_link` is a no-op in the
                // first, so the backend legitimately does not exist on disk yet and
                // an existence assertion there fires before anything has had a
                // chance to run. Only the real pass can answer this question.
                if !builder.config.dry_run() && !from.exists() {
                    let role = match bin.split('.').next().unwrap_or(&bin) {
                        "ty" => "the temporal model checker (every derived-model \
                                 obligation is discharged by it)",
                        "ay" => "the SAT/SMT solver behind the native verifier",
                        _ => "the CIC proof kernel",
                    };
                    panic!(
                        "\n\ndist trustc: REQUIRED verification backend `{bin}` is not in the \
                         stage sysroot at {}.\n  It is {role}.\n  Shipping this component would \
                         distribute a trustc that COMPILES BUT CANNOT VERIFY — the failure is \
                         silent, because nothing that merely compiles ever notices.\n  Fix: add \
                         it to `tools = [...]` in bootstrap.toml (the list is an ALLOWLIST — \
                         absent means all, present means ONLY these), or drop `tools` entirely \
                         to build everything; then rebuild before dist.\n",
                        from.display()
                    );
                }
                builder.copy_link(&from, &image.join("bin").join(&bin), FileType::Executable);
            }

            // If enabled, copy the Trust-named rustdoc binary. The inherited
            // `rustdoc` spelling remains a source-build config selector, not a
            // shipped secondary alias.
            if builder.config.tools.as_ref().is_none_or(|tools| {
                tools
                    .iter()
                    .any(|entry| tool::tool_config_entry_selects_user_tool(entry, "trustdoc"))
            }) {
                let rustdoc = builder.rustdoc_for_compiler(target_compiler);
                for bin in trustdoc_dist_bin_names(target) {
                    builder.copy_link(&rustdoc, &image.join("bin").join(bin), FileType::Executable);
                }
            }

            let compilers = RustcPrivateCompilers::from_target_compiler(builder, target_compiler);

            // Trust: the trustc component ALWAYS ships the Trust-named
            // proc-macro server — the stage0 archive contract lists
            // `trustc/libexec/trust-analyzer-proc-macro-srv` as a REQUIRED
            // entrypoint (src/tools/trust-stage0-dist/prepare.py). Gating it on
            // `builder.ensure_if_default` (which is only true when
            // `tools = ["trust-analyzer"]`) left it absent for a plain
            // `x.py dist trustc`, so the trustc component failed its own
            // contract and blocked stage0 seed minting. Build it unconditionally
            // for the compiler component to keep dist consistent with the
            // contract. See docs/OFF_STOCK_RUST_PLAN.md.
            let ra_proc_macro_srv =
                builder.ensure(tool::RustAnalyzerProcMacroSrv::from_compilers(compilers));
            let dst = image.join("libexec");
            t!(fs::create_dir_all(&dst));
            for bin in rust_analyzer_proc_macro_dist_bin_names(target) {
                builder.copy_link(&ra_proc_macro_srv.tool_path, &dst.join(bin), FileType::Executable);
            }

            let libdir_relative = builder.libdir_relative(target_compiler);

            // Copy runtime DLLs needed by the compiler
            if libdir_relative.to_str() != Some("bin") {
                let libdir = builder.rustc_libdir(target_compiler);
                for entry in builder.read_dir(&libdir) {
                    if is_dylib(&entry.path()) {
                        // Don't use custom libdir here because ^lib/ will be resolved again
                        // with installer
                        builder.install(&entry.path(), &image.join("lib"), FileType::NativeLibrary);
                    }
                }
            } else {
                // Windows: the compiler's own runtime dylibs (`rustc_driver-*.dll`,
                // and `std-*.dll` when std is dynamically linked) live in `bin/` next
                // to `rustc.exe`, so `libdir == bin` and the branch above never runs.
                // The exe-by-name loop earlier copies ONLY `rustc.exe`/`trustc.exe`,
                // not the `rustc_driver` DLL they dynamically link — so without this
                // the shipped toolchain cannot start ("error while loading shared
                // libraries: rustc_driver-*.dll: cannot open shared object file").
                // Ship every dylib from the sysroot `bin` into the image `bin`
                // (the installer resolves `bin/` again, mirroring the `lib/`
                // note above).
                let bindir = src.join("bin");
                for entry in builder.read_dir(&bindir) {
                    let path = entry.path();
                    if is_dylib(&path) {
                        builder.install(&path, &image.join("bin"), FileType::NativeLibrary);
                    }
                }
            }

            // Copy libLLVM.so to the lib dir as well, if needed. While not
            // technically needed by rustc itself it's needed by lots of other
            // components like the llvm tools and LLD. LLD is included below and
            // tools/LLDB come later, so let's just throw it in the rustc
            // component for now.
            maybe_install_llvm_runtime(builder, target, image);

            let dst_dir = image.join("lib/rustlib").join(target).join("bin");
            t!(fs::create_dir_all(&dst_dir));

            // Copy over lld if it's there
            if builder.config.lld_enabled {
                let src_dir = builder.sysroot_target_bindir(target_compiler, target);
                let rust_lld = exe("rust-lld", target_compiler.host);
                builder.copy_link(
                    &src_dir.join(&rust_lld),
                    &dst_dir.join(&rust_lld),
                    FileType::Executable,
                );
                let self_contained_lld_src_dir = src_dir.join("gcc-ld");
                let self_contained_lld_dst_dir = dst_dir.join("gcc-ld");
                t!(fs::create_dir(&self_contained_lld_dst_dir));
                for name in crate::LLD_FILE_NAMES {
                    let exe_name = exe(name, target_compiler.host);
                    builder.copy_link(
                        &self_contained_lld_src_dir.join(&exe_name),
                        &self_contained_lld_dst_dir.join(&exe_name),
                        FileType::Executable,
                    );
                }
            }

            if builder.config.llvm_enabled(target_compiler.host)
                && builder.config.llvm_tools_enabled
            {
                let src_dir = builder.sysroot_target_bindir(target_compiler, target);
                let llvm_objcopy = exe("llvm-objcopy", target_compiler.host);
                let rust_objcopy = exe("rust-objcopy", target_compiler.host);
                builder.copy_link(
                    &src_dir.join(&llvm_objcopy),
                    &dst_dir.join(&rust_objcopy),
                    FileType::Executable,
                );
            }

            if builder.tool_enabled("wasm-component-ld") {
                let src_dir = builder.sysroot_target_bindir(target_compiler, target);
                let ld = exe("wasm-component-ld", target_compiler.host);
                builder.copy_link(&src_dir.join(&ld), &dst_dir.join(&ld), FileType::Executable);
            }

            // Man pages
            t!(fs::create_dir_all(image.join("share/man/man1")));
            let man_src = builder.src.join("src/doc/man");
            let man_dst = image.join("share/man/man1");

            // don't use our `bootstrap::{copy_internal, cp_r}`, because those try
            // to hardlink, and we don't want to edit the source templates
            for file_entry in builder.read_dir(&man_src) {
                let page_src = file_entry.path();
                let page_dst = man_dst.join(file_entry.file_name());
                let src_text = t!(std::fs::read_to_string(&page_src));
                let version = builder.rust_info().version(builder.build, &builder.version);
                let new_text = src_text.replace("<INSERT VERSION HERE>", &version);
                t!(std::fs::write(&page_dst, &new_text));
            }

            // Debugger scripts
            builder.ensure(DebuggerScripts { sysroot: image.to_owned(), target });

            generate_target_spec_json_schema(builder, image);

            // HTML copyright files
            let file_list = builder.ensure(super::run::GenerateCopyright);
            for file in file_list {
                builder.install(&file, &image.join("share/doc/rust"), FileType::Regular);
            }

            // README
            builder.install(
                &builder.src.join("README.md"),
                &image.join("share/doc/rust"),
                FileType::Regular,
            );

            // The REUSE-managed license files
            let license = |path: &Path| {
                builder.install(path, &image.join("share/doc/rust/licenses"), FileType::Regular);
            };
            for entry in t!(std::fs::read_dir(builder.src.join("LICENSES"))).flatten() {
                license(&entry.path());
            }
        }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("trustc", self.target_compiler.host))
    }
}

fn generate_target_spec_json_schema(builder: &Builder<'_>, sysroot: &Path) {
    // Since we run rustc in bootstrap, we need to ensure that we use the host compiler.
    // We do this by using the stage 1 compiler, which is always compiled for the host,
    // even in a cross build.
    let stage1_host = builder.compiler(1, builder.host_target);
    let mut rustc = builder.rustc_cmd(stage1_host).fail_fast();
    rustc
        .env("RUSTC_BOOTSTRAP", "1")
        .args(["--print=target-spec-json-schema", "-Zunstable-options"]);
    let schema = rustc.run_capture(builder).stdout();

    let schema_dir = tmpdir(builder);
    t!(fs::create_dir_all(&schema_dir));
    let schema_file = schema_dir.join("target-spec-json-schema.json");
    t!(std::fs::write(&schema_file, schema));

    let dst = sysroot.join("etc");
    t!(fs::create_dir_all(&dst));

    builder.install(&schema_file, &dst, FileType::Regular);
}

/// Copies debugger scripts for `target` into the given compiler `sysroot`.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct DebuggerScripts {
    /// Sysroot of a compiler into which will the debugger scripts be copied to.
    pub sysroot: PathBuf,
    pub target: TargetSelection,
}

impl Step for DebuggerScripts {
    type Output = ();

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.never()
    }

    fn run(self, builder: &Builder<'_>) {
        let target = self.target;
        let sysroot = self.sysroot;
        let dst = sysroot.join("lib/rustlib/etc");
        t!(fs::create_dir_all(&dst));
        let cp_debugger_script = |file: &str| {
            builder.install(&builder.src.join("src/etc/").join(file), &dst, FileType::Regular);
        };
        if target.contains("windows-msvc") {
            cp_debugger_script("natvis/intrinsic.natvis");
            cp_debugger_script("natvis/liballoc.natvis");
            cp_debugger_script("natvis/libcore.natvis");
            cp_debugger_script("natvis/libstd.natvis");
        }

        cp_debugger_script("rust_types.py");

        // Trust: debugger launchers are public entrypoints too. Install each
        // upstream source script once under its canonical Trust name; copying
        // the source basename first used to leak rust-gdb/rust-lldb aliases
        // into every otherwise canonical distribution.
        for (source, destination) in debugger_script_entrypoints(target) {
            builder.copy_link(
                &builder.src.join("src/etc").join(source),
                &sysroot.join("bin").join(destination),
                FileType::Script,
            );
        }

        cp_debugger_script("gdb_load_rust_pretty_printers.py");
        cp_debugger_script("gdb_lookup.py");
        cp_debugger_script("gdb_providers.py");

        cp_debugger_script("lldb_lookup.py");
        cp_debugger_script("lldb_providers.py");
    }
}

fn debugger_script_entrypoints(target: TargetSelection) -> Vec<(&'static str, String)> {
    let mut scripts = Vec::with_capacity(4);
    if target.contains("windows-msvc") {
        scripts.push(("rust-windbg.cmd", "trust-windbg.cmd".to_string()));
    }
    scripts.extend([
        // These are POSIX shell scripts even in a Windows distribution. Giving
        // their text payloads an `.exe` suffix makes Windows try to load them
        // as PE binaries. Preserve script-style extensionless destinations;
        // only the native windbg batch launcher carries `.cmd`.
        ("rust-gdb", "trust-gdb".to_string()),
        ("rust-gdbgui", "trust-gdbgui".to_string()),
        ("rust-lldb", "trust-lldb".to_string()),
    ]);
    scripts
}

fn skip_host_target_lib(builder: &Builder<'_>, compiler: Compiler) -> bool {
    // The only true set of target libraries came from the build triple, so
    // let's reduce redundant work by only producing archives from that host.
    if !builder.config.is_host_target(compiler.host) {
        builder.info("\tskipping, not a build host");
        true
    } else {
        false
    }
}

/// Check that all objects in rlibs for UEFI targets are COFF. This
/// ensures that the C compiler isn't producing ELF objects, which would
/// not link correctly with the COFF objects.
fn verify_uefi_rlib_format(builder: &Builder<'_>, target: TargetSelection, stamp: &BuildStamp) {
    if !target.ends_with("-uefi") {
        return;
    }

    for (path, _) in builder.read_stamp_file(stamp) {
        if path.extension() != Some(OsStr::new("rlib")) {
            continue;
        }

        let data = t!(fs::read(&path));
        let data = data.as_slice();
        let archive = t!(ArchiveFile::parse(data));
        for member in archive.members() {
            let member = t!(member);
            let member_data = t!(member.data(data));

            let is_coff = match object::File::parse(member_data) {
                Ok(member_file) => member_file.format() == BinaryFormat::Coff,
                Err(_) => false,
            };

            if !is_coff {
                let member_name = String::from_utf8_lossy(member.name());
                panic!("member {} in {} is not COFF", member_name, path.display());
            }
        }
    }
}

/// Copy stamped files into an image's `target/lib` directory.
fn copy_target_libs(
    builder: &Builder<'_>,
    target: TargetSelection,
    image: &Path,
    stamp: &BuildStamp,
) {
    let dst = image.join("lib/rustlib").join(target).join("lib");
    let self_contained_dst = dst.join("self-contained");
    t!(fs::create_dir_all(&dst));
    t!(fs::create_dir_all(&self_contained_dst));
    for (path, dependency_type) in builder.read_stamp_file(stamp) {
        if dependency_type == DependencyType::TargetSelfContained {
            builder.copy_link(
                &path,
                &self_contained_dst.join(path.file_name().unwrap()),
                FileType::NativeLibrary,
            );
        } else if dependency_type == DependencyType::Target || builder.config.is_host_target(target)
        {
            builder.copy_link(&path, &dst.join(path.file_name().unwrap()), FileType::NativeLibrary);
        }
    }
}

/// Builds the standard library (`trust-std`) dist component for a given `target`.
/// This includes the standard library dynamic library file (e.g. .so/.dll), along with stdlib
/// .rlibs.
///
/// Note that due to uplifting, we actually ship the stage 1 library
/// (built using the stage1 compiler) even with a stage 2 dist, unless `full-bootstrap` is enabled.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Std {
    /// Compiler that will build the standard library.
    pub build_compiler: Compiler,
    pub target: TargetSelection,
}

impl Std {
    pub fn new(builder: &Builder<'_>, target: TargetSelection) -> Self {
        Std { build_compiler: builder.compiler_for_std(builder.top_stage), target }
    }
}

impl Step for Std {
    type Output = Option<GeneratedTarball>;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("library/std").alias("trust-std").alias("rust-std")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Std::new(run.builder, run.target));
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let build_compiler = self.build_compiler;
        let target = self.target;

        if skip_host_target_lib(builder, build_compiler) {
            return None;
        }

        // It's possible that std was uplifted and thus built with a different build compiler
        // So we need to read the stamp that was actually generated when std was built
        let stamp =
            builder.std(build_compiler, target).expect("Standard library has to be built for dist");

        let mut tarball = Tarball::new(builder, "trust-std", &target.triple);
        tarball.include_target_in_component_name(true);

        verify_uefi_rlib_format(builder, target, &stamp);
        copy_target_libs(builder, target, tarball.image_dir(), &stamp);

        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("std", self.target).built_by(self.build_compiler))
    }
}

/// Tarball containing the compiler that gets downloaded and used by
/// `rust.download-rustc`.
///
/// (Don't confuse this with [`RustDev`], without the `c`!)
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct RustcDev {
    /// The compiler that will build rustc which will be shipped in this component.
    pub build_compiler: Compiler,
    pub target: TargetSelection,
}

impl RustcDev {
    pub fn new(builder: &Builder<'_>, target: TargetSelection) -> Self {
        Self {
            // We currently always ship a stage 2 trustc-dev component, so we build it with the
            // stage 1 compiler. This might change in the future.
            // The precise stage used here is important, so we hard-code it.
            build_compiler: builder.compiler(1, builder.config.host_target),
            target,
        }
    }
}

impl Step for RustcDev {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trustc-dev").alias("rustc-dev")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(RustcDev::new(run.builder, run.target));
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let build_compiler = self.build_compiler;
        let target = self.target;
        if skip_host_target_lib(builder, build_compiler) {
            return None;
        }

        // Build the compiler that we will ship
        builder.ensure(compile::Rustc::new(build_compiler, target));

        let tarball = Tarball::new(builder, "trustc-dev", &target.triple);

        let stamp = build_stamp::librustc_stamp(builder, build_compiler, target);
        copy_target_libs(builder, target, tarball.image_dir(), &stamp);

        let src_files = &["Cargo.lock"];
        // This is the reduced set of paths which will become the trustc-dev component
        // (essentially the compiler crates and all of their path dependencies).
        copy_src_dirs(
            builder,
            &builder.src,
            // The compiler has a path dependency on proc_macro, so make sure to include it.
            &["compiler", "library/proc_macro"],
            &[],
            &tarball.image_dir().join("lib/rustlib/rustc-src/rust"),
        );
        for file in src_files {
            tarball.add_file(
                builder.src.join(file),
                "lib/rustlib/rustc-src/rust",
                FileType::Regular,
            );
        }

        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("trustc-dev", self.target).built_by(self.build_compiler))
    }
}

/// The `trust-analysis` component used to create a tarball of save-analysis metadata.
///
/// This component has been deprecated and its contents now only include a warning about
/// its non-availability.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Analysis {
    build_compiler: Compiler,
    target: TargetSelection,
}

impl Step for Analysis {
    type Output = Option<GeneratedTarball>;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trust-analysis").alias("rust-analysis")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        should_build_extended_tool(builder, "trust-analysis")
    }

    fn make_run(run: RunConfig<'_>) {
        // The step just produces a deprecation notice, so we just hardcode stage 1
        run.builder.ensure(Analysis {
            build_compiler: run.builder.compiler(1, run.builder.config.host_target),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let compiler = self.build_compiler;
        let target = self.target;
        if skip_host_target_lib(builder, compiler) {
            return None;
        }

        let src = builder
            .stage_out(compiler, Mode::Std)
            .join(target)
            .join(builder.cargo_dir(Mode::Std))
            .join("deps")
            .join("save-analysis");

        // Write a file indicating that this component has been removed.
        t!(std::fs::create_dir_all(&src));
        let mut removed = src.clone();
        removed.push("removed.json");
        let mut f = t!(std::fs::File::create(removed));
        t!(write!(f, r#"{{ "warning": "The `trust-analysis` component has been removed." }}"#));

        let mut tarball = Tarball::new(builder, "trust-analysis", &target.triple);
        tarball.include_target_in_component_name(true);
        tarball.add_dir(src, format!("lib/rustlib/{}/analysis", target.triple));
        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("analysis", self.target).built_by(self.build_compiler))
    }
}

/// Use the `builder` to make a filtered copy of `base`/X for X in (`src_dirs` - `exclude_dirs`) to
/// `dst_dir`.
fn copy_src_dirs(
    builder: &Builder<'_>,
    base: &Path,
    src_dirs: &[&str],
    exclude_dirs: &[&str],
    dst_dir: &Path,
) {
    // The src directories should be relative to `base`, we depend on them not being absolute
    // paths below.
    for src_dir in src_dirs {
        assert!(Path::new(src_dir).is_relative());
    }

    // Iterating, filtering and copying a large number of directories can be quite slow.
    // Avoid doing it in dry run (and thus also tests).
    if builder.config.dry_run() {
        return;
    }

    fn filter_fn(base: &Path, exclude_dirs: &[&str], dir: &str, path: &Path) -> bool {
        // The paths are relative, e.g. `llvm-project/...`.
        let spath = match path.to_str() {
            Some(path) => path,
            None => return false,
        };
        if spath.ends_with('~') || spath.ends_with(".pyc") {
            return false;
        }
        // Normalize slashes
        let spath = spath.replace("\\", "/");

        // Trust: in-tree Cargo workspaces (crates/, targo-trust/, the bootstrap
        // tool, a stray src/tools/cargo build, ...) build in place, leaving multi-GB
        // `target/` artifact dirs that must never enter the plain-source tarball. A
        // real Cargo target dir either sits next to the `Cargo.toml` that produced it
        // OR carries Cargo's own `CACHEDIR.TAG`; source dirs merely named `target`
        // (rustfmt/cargo test fixtures, llvm test inputs) have neither. Use the OR:
        // per-crate target dirs can lack CACHEDIR.TAG, and a stray build can lack a
        // sibling Cargo.toml, so a single marker misses some. Drop either match.
        if path.file_name().and_then(|n| n.to_str()) == Some("target") {
            let abs = base.join(dir).join(path);
            if abs.parent().is_some_and(|p| p.join("Cargo.toml").exists())
                || abs.join("CACHEDIR.TAG").exists()
            {
                return false;
            }
        }

        static LLVM_PROJECTS: &[&str] = &[
            "llvm-project/clang",
            "llvm-project/libunwind",
            "llvm-project/lld",
            "llvm-project/lldb",
            "llvm-project/llvm",
            "llvm-project/compiler-rt",
            "llvm-project/cmake",
            "llvm-project/runtimes",
            "llvm-project/third-party",
        ];
        if spath.starts_with("llvm-project") && spath != "llvm-project" {
            if !LLVM_PROJECTS.iter().any(|path| spath.starts_with(path)) {
                return false;
            }

            // Keep siphash third-party dependency
            if spath.starts_with("llvm-project/third-party")
                && spath != "llvm-project/third-party"
                && !spath.starts_with("llvm-project/third-party/siphash")
            {
                return false;
            }

            if spath.starts_with("llvm-project/llvm/test")
                && (spath.ends_with(".ll") || spath.ends_with(".td") || spath.ends_with(".s"))
            {
                return false;
            }
        }

        // Cargo tests use some files like `.gitignore` that we would otherwise exclude.
        if spath.starts_with("tools/cargo/tests") {
            return true;
        }

        if !exclude_dirs.is_empty() {
            let full_path = Path::new(dir).join(path);
            if exclude_dirs.iter().any(|excl| full_path == Path::new(excl)) {
                return false;
            }
        }

        static EXCLUDES: &[&str] = &[
            "CVS",
            "RCS",
            "SCCS",
            ".git",
            ".gitignore",
            ".gitmodules",
            ".gitattributes",
            ".cvsignore",
            ".svn",
            ".arch-ids",
            "{arch}",
            "=RELEASE-ID",
            "=meta-update",
            "=update",
            ".bzr",
            ".bzrignore",
            ".bzrtags",
            ".hg",
            ".hgignore",
            ".hgrags",
            "_darcs",
        ];

        // We want to check if any component of `path` doesn't contain the strings in `EXCLUDES`.
        // However, since we traverse directories top-down in `Builder::cp_link_filtered`,
        // it is enough to always check only the last component:
        // - If the path is a file, we will iterate to it and then check it's filename
        // - If the path is a dir, if it's dir name contains an excluded string, we will not even
        //   recurse into it.
        let last_component = path.iter().next_back().map(|s| s.to_str().unwrap()).unwrap();
        !EXCLUDES.contains(&last_component)
    }

    // Copy the directories using our filter
    for item in src_dirs {
        let src = base.join(item);
        let dst = &dst_dir.join(item);
        t!(fs::create_dir_all(dst));
        builder.cp_link_filtered(&src, dst, &|path| filter_fn(base, exclude_dirs, item, path));
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Src;

impl Step for Src {
    /// The output path of the src installer tarball
    type Output = GeneratedTarball;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trust-src")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Src);
    }

    /// Creates the `trust-src` installer component
    fn run(self, builder: &Builder<'_>) -> GeneratedTarball {
        if !builder.config.dry_run() {
            builder.require_submodule("src/llvm-project", None);
        }

        let tarball = Tarball::new_targetless(builder, "trust-src");

        // A lot of tools expect the Trust source component to be entirely in this directory, so if you
        // change that (e.g. by adding another directory `lib/rustlib/src/foo` or
        // `lib/rustlib/src/rust/foo`), you will need to go around hunting for implicit assumptions
        // and fix them...
        //
        // NOTE: if you update the paths here, you also should update the "virtual" path
        // translation code in `imported_source_files` in `src/librustc_metadata/rmeta/decoder.rs`
        let dst_src = tarball.image_dir().join("lib/rustlib/src/rust");

        // This is the reduced set of paths which will become the trust-src component
        // (essentially libstd and all of its path dependencies).
        copy_src_dirs(
            builder,
            &builder.src,
            &["library", "src/llvm-project/libunwind"],
            &[
                // not needed and contains symlinks which rustup currently
                // chokes on when unpacking.
                "library/backtrace/crates",
            ],
            &dst_src,
        );

        // Vendor all Cargo dependencies
        let vendor = builder.ensure(Vendor {
            sync_args: vec![],
            versioned_dirs: true,
            root_dir: dst_src.clone(),
            output_dir: None,
            only_library_workspace: true,
        });

        let library_cargo_config_dir = dst_src.join("library").join(".cargo");
        builder.create_dir(&library_cargo_config_dir);
        builder.create(&library_cargo_config_dir.join("config.toml"), &vendor.config_library);

        tarball.generate()
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("src", TargetSelection::default()))
    }
}

/// Tarball for people who want to build Trust components from the source.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct PlainSourceTarball;

impl Step for PlainSourceTarball {
    /// Produces the location of the tarball generated
    type Output = GeneratedTarball;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trust-source")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        builder.config.rust_dist_src
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(PlainSourceTarball);
    }

    /// Creates the plain source tarball
    fn run(self, builder: &Builder<'_>) -> GeneratedTarball {
        let tarball = prepare_source_tarball(builder, "trust-src");
        tarball.bare()
    }
}

fn prepare_source_tarball<'a>(builder: &'a Builder<'a>, name: &str) -> Tarball<'a> {
    // NOTE: This is a strange component in a lot of ways. It uses `src` as the target, which
    // means neither rustup nor rustup-toolchain-install-master know how to download it.
    // It also contains symbolic links, unlike other any other dist tarball.
    // It's used for distros building Trust from source in a pre-vendored environment.
    let mut tarball = Tarball::new(builder, "trust", name);
    tarball.permit_symlinks(true);
    let plain_dst_src = tarball.image_dir();
    // Trust: `first-party/trust` is a developer-convenience symlink back to the
    // superproject root (`first-party/trust -> ..`), not a submodule — it is absent
    // from `.gitmodules` and from the root workspace's member list. Copying it would
    // plant a self-referential symlink at the top of the source tarball.
    let source_exclude_dirs = ["targo-trust/target", "first-party/trust"];

    // This is the set of root paths which will become part of the source package
    let src_files = [
        // tidy-alphabetical-start
        "CONTRIBUTING.md",
        "COPYRIGHT",
        "Cargo.lock",
        "Cargo.toml",
        "LICENSE-APACHE",
        "LICENSE-MIT",
        "README.md",
        "REUSE.toml",
        "bootstrap.example.toml",
        "configure",
        "license-metadata.json",
        "x",
        "x.ps1",
        "x.py",
        // tidy-alphabetical-end
    ];
    // Trust: `crates`, `targo-trust`, and `LICENSES` are Trust-owned trees that must
    // reach the source tarball alongside the inherited ones.
    //
    // `first-party` and `vendor` are load-bearing for *resolution*, not just for the
    // eventual build. The nine `first-party/*` submodules are `exclude`d from the root
    // workspace (each is its own workspace), but the root, `crates/` and `targo-trust/`
    // manifests all carry `[patch.*]` tables that redirect the sibling Git sources to
    // `path =` targets under `first-party/` and `vendor/`, so `crates/*` members reach
    // them as ordinary path dependencies. Without those trees the `cargo vendor` run
    // below cannot even load the graph ("failed to load manifest for dependency
    // `trust-ir`"). Nothing else materializes them: `build.submodules = false` is
    // deliberate in this fork, so the tarball contains exactly what is copied here.
    let src_dirs = [
        "src",
        "compiler",
        "library",
        "tests",
        "crates",
        "targo-trust",
        "first-party",
        "vendor",
        "LICENSES",
    ];

    copy_src_dirs(builder, &builder.src, &src_dirs, &source_exclude_dirs, plain_dst_src);

    // Copy the files normally
    for item in &src_files {
        builder.copy_link(&builder.src.join(item), &plain_dst_src.join(item), FileType::Regular);
    }

    // Create the version file
    builder.create(&plain_dst_src.join("version"), &builder.rust_version());

    // Create the files containing git info, to ensure --version outputs the same.
    let write_git_info = |info: Option<&Info>, path: &Path| {
        if let Some(info) = info {
            t!(std::fs::create_dir_all(path));
            channel::write_commit_hash_file(path, &info.sha);
            channel::write_commit_info_file(path, info);
        }
    };
    write_git_info(builder.rust_info().info(), plain_dst_src);
    write_git_info(builder.cargo_info.info(), &plain_dst_src.join("./src/tools/targo"));

    if builder.config.dist_vendor {
        builder.require_and_update_all_submodules();

        // Vendor all Cargo dependencies.
        //
        // Trust: the source tarball carries no PGO training corpus. opt-dist trains
        // against an external `rustc-perf` checkout that brings its own vendored
        // dependencies, so there is nothing here to pre-sync for it.
        let vendor = builder.ensure(Vendor {
            sync_args: vec![],
            versioned_dirs: true,
            root_dir: plain_dst_src.into(),
            output_dir: None,
            only_library_workspace: false,
        });

        let cargo_config_dir = plain_dst_src.join(".cargo");
        builder.create_dir(&cargo_config_dir);
        builder.create(&cargo_config_dir.join("config.toml"), &vendor.config);

        let library_cargo_config_dir = plain_dst_src.join("library").join(".cargo");
        builder.create_dir(&library_cargo_config_dir);
        builder.create(&library_cargo_config_dir.join("config.toml"), &vendor.config_library);
    }

    // Delete extraneous directories
    // FIXME: if we're managed by git, we should probably instead ask git if the given path
    // is managed by it?
    for entry in walkdir::WalkDir::new(tarball.image_dir())
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
    {
        if entry.path().is_dir() && entry.path().file_name() == Some(OsStr::new("__pycache__")) {
            t!(fs::remove_dir_all(entry.path()));
        }
    }
    tarball
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Cargo {
    pub build_compiler: Compiler,
    pub target: TargetSelection,
}

impl Step for Cargo {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("targo")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        should_build_extended_tool(builder, "targo")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Cargo {
            build_compiler: get_tool_target_compiler(
                run.builder,
                ToolTargetBuildMode::Build(run.target),
            ),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let build_compiler = self.build_compiler;
        let target = self.target;

        let cargo = builder.ensure(tool::Cargo::from_build_compiler(build_compiler, target));
        let src = builder.src.join("src/tools/targo");
        let etc = src.join("src/etc");

        // Prepare the image directory
        let mut tarball = Tarball::new(builder, "targo", &target.triple);
        tarball.set_overlay(OverlayKind::Cargo);

        for bin_name in cargo_dist_bin_names(target) {
            tarball.add_renamed_file(&cargo.tool_path, "bin", &bin_name, FileType::Executable);
        }
        tarball.add_file(etc.join("_cargo"), "share/zsh/site-functions", FileType::Regular);
        tarball.add_renamed_file(
            etc.join("cargo.bashcomp.sh"),
            "etc/bash_completion.d",
            "targo",
            FileType::Regular,
        );
        tarball.add_dir(etc.join("man"), "share/man/man1");
        tarball.add_legal_and_readme_to("share/doc/targo");

        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("targo", self.target).built_by(self.build_compiler))
    }
}

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TCargoTrust {
    pub build_compiler: Compiler,
    pub target: TargetSelection,
}

impl Step for TCargoTrust {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("targo-trust")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        should_build_extended_tool(builder, "targo-trust")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(TCargoTrust {
            build_compiler: get_tool_target_compiler(
                run.builder,
                ToolTargetBuildMode::Build(run.target),
            ),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let targo_trust = builder
            .ensure(tool::TCargoTrust::from_build_compiler(self.build_compiler, self.target));
        let trustd =
            builder.ensure(tool::Trustd::from_build_compiler(self.build_compiler, self.target));

        let mut tarball = Tarball::new(builder, "targo-trust", &self.target.triple);
        tarball.set_overlay(OverlayKind::TCargoTrust);
        tarball.add_renamed_file(
            &targo_trust.tool_path,
            "bin",
            &exe("targo-trust", self.target),
            FileType::Executable,
        );
        tarball.add_renamed_file(
            &trustd.tool_path,
            "bin",
            &exe("trustd", self.target),
            FileType::Executable,
        );
        tarball.add_legal_and_readme_to("share/doc/targo-trust");

        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("targo-trust", self.target).built_by(self.build_compiler))
    }
}

/// Distribute the rust-analyzer component, which is used as a LSP by various IDEs.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct RustAnalyzer {
    pub compilers: RustcPrivateCompilers,
    pub target: TargetSelection,
}

impl Step for RustAnalyzer {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trust-analyzer")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        should_build_extended_tool(builder, "trust-analyzer")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(RustAnalyzer {
            compilers: RustcPrivateCompilers::new(run.builder, run.builder.top_stage, run.target),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let target = self.target;
        let rust_analyzer = builder.ensure(tool::RustAnalyzer::from_compilers(self.compilers));

        let mut tarball = Tarball::new(builder, "trust-analyzer", &target.triple);
        tarball.set_overlay(OverlayKind::RustAnalyzer);
        tarball.is_preview(true);
        tarball.add_renamed_file(
            &rust_analyzer.tool_path,
            "bin",
            &exe("trust-analyzer", target),
            FileType::Executable,
        );
        tarball.add_legal_and_readme_to("share/doc/rust-analyzer");
        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(
            StepMetadata::dist("trust-analyzer", self.target)
                .built_by(self.compilers.build_compiler()),
        )
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Clippy {
    pub compilers: RustcPrivateCompilers,
    pub target: TargetSelection,
}

impl Step for Clippy {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        // Trust: the produced dist component/tarball is `tippy` (build-manifest
        // PkgType::Clippy = "tippy"). Keep `targo-clippy` as a build-selector
        // compatibility alias; the emitted archive and executables remain
        // exclusively Tippy-named.
        run.alias("tippy").alias("targo-clippy")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        should_build_extended_tool(builder, "tippy")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Clippy {
            compilers: RustcPrivateCompilers::new(run.builder, run.builder.top_stage, run.target),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let target = self.target;

        // Prepare the image directory
        // We expect clippy to build, because we've exited this step above if tool
        // state for clippy isn't testing.
        let cargoclippy = builder.ensure(tool::CargoClippy::from_compilers(self.compilers));
        let clippy_driver = builder.ensure(tool::Clippy::from_compilers(self.compilers));
        let [tippy, targo_tippy, tippy_driver] = tippy_dist_bin_names(target);

        let mut tarball = Tarball::new(builder, "tippy", &target.triple);
        tarball.set_overlay(OverlayKind::Clippy);
        tarball.is_preview(true);
        tarball.add_renamed_file(&cargoclippy.tool_path, "bin", &tippy, FileType::Executable);
        tarball.add_renamed_file(&cargoclippy.tool_path, "bin", &targo_tippy, FileType::Executable);
        tarball.add_renamed_file(
            &clippy_driver.tool_path,
            "bin",
            &tippy_driver,
            FileType::Executable,
        );
        tarball.add_legal_and_readme_to("share/doc/tippy");
        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("tippy", self.target).built_by(self.compilers.build_compiler()))
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Miri {
    pub compilers: RustcPrivateCompilers,
    pub target: TargetSelection,
}

impl Step for Miri {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trust-miri")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        should_build_extended_tool(builder, "trust-miri")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Miri {
            compilers: RustcPrivateCompilers::new(run.builder, run.builder.top_stage, run.target),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        // This prevents miri from being built for "dist" or "install"
        // on the stable/beta channels. It is a nightly-only tool and should
        // not be included.
        if !builder.build.unstable_features() {
            return None;
        }

        let miri = builder.ensure(tool::Miri::from_compilers(self.compilers));
        let cargomiri = builder.ensure(tool::CargoMiri::from_compilers(self.compilers));

        let mut tarball = Tarball::new(builder, "trust-miri", &self.target.triple);
        tarball.set_overlay(OverlayKind::Miri);
        tarball.is_preview(true);
        tarball.add_renamed_file(
            &miri.tool_path,
            "bin",
            &exe("trust-miri", self.target),
            FileType::Executable,
        );
        tarball.add_renamed_file(
            &cargomiri.tool_path,
            "bin",
            &exe("targo-miri", self.target),
            FileType::Executable,
        );
        tarball.add_legal_and_readme_to("share/doc/trust-miri");
        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(
            StepMetadata::dist("trust-miri", self.target).built_by(self.compilers.build_compiler()),
        )
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Rustfmt {
    pub compilers: RustcPrivateCompilers,
    pub target: TargetSelection,
}

impl Step for Rustfmt {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("trustfmt")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        should_build_extended_tool(builder, "trustfmt")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Rustfmt {
            compilers: RustcPrivateCompilers::new(run.builder, run.builder.top_stage, run.target),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let rustfmt = builder.ensure(tool::Rustfmt::from_compilers(self.compilers));
        let cargofmt = builder.ensure(tool::Cargofmt::from_compilers(self.compilers));

        let mut tarball = Tarball::new(builder, "trustfmt", &self.target.triple);
        tarball.set_overlay(OverlayKind::Rustfmt);
        tarball.is_preview(true);
        tarball.add_renamed_file(
            &rustfmt.tool_path,
            "bin",
            &exe("trustfmt", self.target),
            FileType::Executable,
        );
        tarball.add_renamed_file(
            &cargofmt.tool_path,
            "bin",
            &exe("targo-fmt", self.target),
            FileType::Executable,
        );
        tarball.add_legal_and_readme_to("share/doc/rustfmt");
        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("trustfmt", self.target).built_by(self.compilers.build_compiler()))
    }
}

/// Extended archive that contains the compiler, standard library and a bunch of tools.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Extended {
    build_compiler: Compiler,
    target: TargetSelection,
}

impl Step for Extended {
    type Output = ();
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("extended").alias("trust")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        builder.config.extended
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Extended {
            build_compiler: run
                .builder
                .compiler(run.builder.top_stage - 1, run.builder.host_target),
            target: run.target,
        });
    }

    /// Creates a combined installer for the specified target in the provided stage.
    fn run(self, builder: &Builder<'_>) {
        let target = self.target;
        builder.info(&format!("Dist extended stage{} ({target})", builder.top_stage));

        let mut tarballs = Vec::new();
        let mut built_tools = HashSet::new();
        macro_rules! add_component {
            ($name:expr => $step:expr) => {
                if let Some(Some(tarball)) = builder.ensure_if_default($step, Kind::Dist) {
                    tarballs.push(tarball);
                    built_tools.insert($name);
                }
            };
        }

        let rustc_private_compilers =
            RustcPrivateCompilers::from_build_compiler(builder, self.build_compiler, target);
        let build_compiler = rustc_private_compilers.build_compiler();
        let target_compiler = rustc_private_compilers.target_compiler();

        // When trust-std package split from trustc, we needed to ensure that during
        // upgrades trustc was upgraded before trust-std. To avoid trustc clobbering
        // the std files during uninstall. To do this ensure that trustc comes
        // before trust-std in the list below.
        tarballs.push(builder.ensure(Rustc { target_compiler }));
        tarballs.push(builder.ensure(Std { build_compiler, target }).expect("missing std"));

        if target.is_windows_gnu() || target.is_windows_gnullvm() {
            tarballs.push(builder.ensure(Mingw { target }).expect("missing mingw"));
        }

        add_component!("trust-docs" => Docs { host: target });
        // Std stage N is documented with compiler stage N
        add_component!("trust-docs-json" => JsonDocs { build_compiler: target_compiler, target });
        add_component!("targo" => Cargo { build_compiler, target });
        add_component!("targo-trust" => TCargoTrust { build_compiler, target });
        add_component!("trustfmt" => Rustfmt { compilers: rustc_private_compilers, target });
        add_component!("trust-analyzer" => RustAnalyzer { compilers: rustc_private_compilers, target });
        add_component!("trust-llvm-tools" => LlvmTools { target });
        add_component!("tippy" => Clippy { compilers: rustc_private_compilers, target });
        add_component!("trust-miri" => Miri { compilers: rustc_private_compilers, target });
        add_component!("trust-analysis" => Analysis { build_compiler, target });
        add_component!("llvm-bitcode-linker" => LlvmBitcodeLinker {
            build_compiler,
            target
        });

        let etc = builder.src.join("src/etc/installer");

        // Avoid producing tarballs during a dry run.
        if builder.config.dry_run() {
            return;
        }

        let tarball = Tarball::new(builder, "trust", &target.triple);
        let generated = tarball.combine(&tarballs);

        let tmp = tmpdir(builder).join("combined-tarball");
        let work = generated.work_dir();

        let mut license = String::new();
        license += &builder.read(&builder.src.join("COPYRIGHT"));
        license += &builder.read(&builder.src.join("LICENSE-APACHE"));
        license += &builder.read(&builder.src.join("LICENSE-MIT"));
        license.push('\n');
        license.push('\n');

        let rtf = r"{\rtf1\ansi\deff0{\fonttbl{\f0\fnil\fcharset0 Arial;}}\nowwrap\fs18";
        let mut rtf = rtf.to_string();
        rtf.push('\n');
        for line in license.lines() {
            rtf.push_str(line);
            rtf.push_str("\\line ");
        }
        rtf.push('}');

        fn filter(contents: &str, marker: &str) -> String {
            let start = format!("tool-{marker}-start");
            let end = format!("tool-{marker}-end");
            let mut lines = Vec::new();
            let mut omitted = false;
            for line in contents.lines() {
                if line.contains(&start) {
                    omitted = true;
                } else if line.contains(&end) {
                    omitted = false;
                } else if !omitted {
                    lines.push(line);
                }
            }

            lines.join("\n")
        }

        let xform = |p: &Path| {
            let mut contents = t!(fs::read_to_string(p));
            for tool in &["targo-trust", "trust-miri", "trust-docs"] {
                if !built_tools.contains(tool) {
                    contents = filter(&contents, tool);
                }
            }
            let ret = tmp.join(p.file_name().unwrap());
            t!(fs::write(&ret, &contents));
            ret
        };

        if target.contains("apple-darwin") {
            builder.info("building pkg installer");
            let pkg = tmp.join("pkg");
            let _ = fs::remove_dir_all(&pkg);

            let pkgbuild = |component: &str| {
                let mut cmd = command("pkgbuild");
                cmd.arg("--identifier")
                    .arg(format!("org.trust-lang.{component}"))
                    .arg("--scripts")
                    .arg(pkg.join(component))
                    .arg("--nopayload")
                    .arg(pkg.join(component).with_extension("pkg"));
                cmd.run(builder);
            };

            let prepare = |name: &str| {
                builder.create_dir(&pkg.join(name));
                builder.cp_link_r(
                    &work.join(format!("{}-{}", pkgname(builder, name), target.triple)),
                    &pkg.join(name),
                );
                builder.install(&etc.join("pkg/postinstall"), &pkg.join(name), FileType::Script);
                pkgbuild(name);
            };
            prepare("trustc");
            prepare("targo");
            prepare("trust-std");
            if built_tools.contains("trust-analysis") {
                prepare("trust-analysis");
            }

            for tool in &[
                "targo-trust",
                "tippy",
                "trustfmt",
                "trust-analyzer",
                "trust-docs",
                "trust-miri",
            ] {
                if built_tools.contains(tool) {
                    prepare(tool);
                }
            }
            // create an 'uninstall' package
            builder.install(&etc.join("pkg/postinstall"), &pkg.join("uninstall"), FileType::Script);
            pkgbuild("uninstall");

            builder.create_dir(&pkg.join("res"));
            builder.create(&pkg.join("res/LICENSE.txt"), &license);
            builder.install(&etc.join("gfx/rust-logo.png"), &pkg.join("res"), FileType::Regular);
            let mut cmd = command("productbuild");
            cmd.arg("--distribution")
                .arg(xform(&etc.join("pkg/Distribution.xml")))
                .arg("--resources")
                .arg(pkg.join("res"))
                .arg(distdir(builder).join(format!(
                    "{}-{}.pkg",
                    pkgname(builder, "trust"),
                    target.triple
                )))
                .arg("--package-path")
                .arg(&pkg);
            let _time = timeit(builder);
            cmd.run(builder);
        }

        if target.is_windows() {
            let exe = tmp.join("exe");
            let _ = fs::remove_dir_all(&exe);

            let prepare = |name: &str| {
                builder.create_dir(&exe.join(name));
                let dir = if name == "trust-std" || name == "trust-analysis" {
                    format!("{}-{}", name, target.triple)
                } else if name == "trust-analyzer" {
                    "trust-analyzer-preview".to_string()
                } else if name == "tippy" {
                    "tippy-preview".to_string()
                } else if name == "trustfmt" {
                    "trustfmt-preview".to_string()
                } else if name == "trust-miri" {
                    "trust-miri-preview".to_string()
                } else {
                    name.to_string()
                };
                builder.cp_link_r(
                    &work.join(format!("{}-{}", pkgname(builder, name), target.triple)).join(dir),
                    &exe.join(name),
                );
                builder.remove(&exe.join(name).join("manifest.in"));
            };
            prepare("trustc");
            prepare("targo");
            if built_tools.contains("trust-analysis") {
                prepare("trust-analysis");
            }
            prepare("trust-std");
            for tool in
                &["targo-trust", "tippy", "trustfmt", "trust-analyzer", "trust-docs", "trust-miri"]
            {
                if built_tools.contains(tool) {
                    prepare(tool);
                }
            }
            if target.is_windows_gnu() || target.is_windows_gnullvm() {
                prepare("trust-mingw");
            }

            builder.install(&etc.join("gfx/rust-logo.ico"), &exe, FileType::Regular);

            // Generate msi installer
            let wix_path = env::var_os("WIX")
                .expect("`WIX` environment variable must be set for generating MSI installer(s).");
            let wix = PathBuf::from(wix_path);
            let heat = wix.join("bin/heat.exe");
            let candle = wix.join("bin/candle.exe");
            let light = wix.join("bin/light.exe");

            let heat_flags = ["-nologo", "-gg", "-sfrag", "-srd", "-sreg"];
            command(&heat)
                .current_dir(&exe)
                .arg("dir")
                .arg("trustc")
                .args(heat_flags)
                .arg("-cg")
                .arg("RustcGroup")
                .arg("-dr")
                .arg("Rustc")
                .arg("-var")
                .arg("var.RustcDir")
                .arg("-out")
                .arg(exe.join("RustcGroup.wxs"))
                .run(builder);
            if built_tools.contains("trust-docs") {
                command(&heat)
                    .current_dir(&exe)
                    .arg("dir")
                    .arg("trust-docs")
                    .args(heat_flags)
                    .arg("-cg")
                    .arg("DocsGroup")
                    .arg("-dr")
                    .arg("Docs")
                    .arg("-var")
                    .arg("var.DocsDir")
                    .arg("-out")
                    .arg(exe.join("DocsGroup.wxs"))
                    .arg("-t")
                    .arg(etc.join("msi/squash-components.xsl"))
                    .run(builder);
            }
            command(&heat)
                .current_dir(&exe)
                .arg("dir")
                .arg("targo")
                .args(heat_flags)
                .arg("-cg")
                .arg("CargoGroup")
                .arg("-dr")
                .arg("Cargo")
                .arg("-var")
                .arg("var.CargoDir")
                .arg("-out")
                .arg(exe.join("CargoGroup.wxs"))
                .arg("-t")
                .arg(etc.join("msi/remove-duplicates.xsl"))
                .run(builder);
            if built_tools.contains("targo-trust") {
                command(&heat)
                    .current_dir(&exe)
                    .arg("dir")
                    .arg("targo-trust")
                    .args(heat_flags)
                    .arg("-cg")
                    .arg("TCargoTrustGroup")
                    .arg("-dr")
                    .arg("TCargoTrust")
                    .arg("-var")
                    .arg("var.TCargoTrustDir")
                    .arg("-out")
                    .arg(exe.join("TCargoTrustGroup.wxs"))
                    .arg("-t")
                    .arg(etc.join("msi/remove-duplicates.xsl"))
                    .run(builder);
            }
            command(&heat)
                .current_dir(&exe)
                .arg("dir")
                .arg("trust-std")
                .args(heat_flags)
                .arg("-cg")
                .arg("StdGroup")
                .arg("-dr")
                .arg("Std")
                .arg("-var")
                .arg("var.StdDir")
                .arg("-out")
                .arg(exe.join("StdGroup.wxs"))
                .run(builder);
            if built_tools.contains("trust-analyzer") {
                command(&heat)
                    .current_dir(&exe)
                    .arg("dir")
                    .arg("trust-analyzer")
                    .args(heat_flags)
                    .arg("-cg")
                    .arg("RustAnalyzerGroup")
                    .arg("-dr")
                    .arg("RustAnalyzer")
                    .arg("-var")
                    .arg("var.RustAnalyzerDir")
                    .arg("-out")
                    .arg(exe.join("RustAnalyzerGroup.wxs"))
                    .arg("-t")
                    .arg(etc.join("msi/remove-duplicates.xsl"))
                    .run(builder);
            }
            if built_tools.contains("tippy") {
                command(&heat)
                    .current_dir(&exe)
                    .arg("dir")
                    .arg("tippy")
                    .args(heat_flags)
                    .arg("-cg")
                    .arg("ClippyGroup")
                    .arg("-dr")
                    .arg("Clippy")
                    .arg("-var")
                    .arg("var.ClippyDir")
                    .arg("-out")
                    .arg(exe.join("ClippyGroup.wxs"))
                    .arg("-t")
                    .arg(etc.join("msi/remove-duplicates.xsl"))
                    .run(builder);
            }
            if built_tools.contains("trustfmt") {
                command(&heat)
                    .current_dir(&exe)
                    .arg("dir")
                    .arg("trustfmt")
                    .args(heat_flags)
                    .arg("-cg")
                    .arg("RustFmtGroup")
                    .arg("-dr")
                    .arg("RustFmt")
                    .arg("-var")
                    .arg("var.RustFmtDir")
                    .arg("-out")
                    .arg(exe.join("RustFmtGroup.wxs"))
                    .arg("-t")
                    .arg(etc.join("msi/remove-duplicates.xsl"))
                    .run(builder);
            }
            if built_tools.contains("trust-miri") {
                command(&heat)
                    .current_dir(&exe)
                    .arg("dir")
                    .arg("trust-miri")
                    .args(heat_flags)
                    .arg("-cg")
                    .arg("MiriGroup")
                    .arg("-dr")
                    .arg("Miri")
                    .arg("-var")
                    .arg("var.MiriDir")
                    .arg("-out")
                    .arg(exe.join("MiriGroup.wxs"))
                    .arg("-t")
                    .arg(etc.join("msi/remove-duplicates.xsl"))
                    .run(builder);
            }
            command(&heat)
                .current_dir(&exe)
                .arg("dir")
                .arg("trust-analysis")
                .args(heat_flags)
                .arg("-cg")
                .arg("AnalysisGroup")
                .arg("-dr")
                .arg("Analysis")
                .arg("-var")
                .arg("var.AnalysisDir")
                .arg("-out")
                .arg(exe.join("AnalysisGroup.wxs"))
                .arg("-t")
                .arg(etc.join("msi/remove-duplicates.xsl"))
                .run(builder);
            if target.is_windows_gnu() || target.is_windows_gnullvm() {
                command(&heat)
                    .current_dir(&exe)
                    .arg("dir")
                    .arg("trust-mingw")
                    .args(heat_flags)
                    .arg("-cg")
                    .arg("GccGroup")
                    .arg("-dr")
                    .arg("Gcc")
                    .arg("-var")
                    .arg("var.GccDir")
                    .arg("-out")
                    .arg(exe.join("GccGroup.wxs"))
                    .run(builder);
            }

            let candle = |input: &Path| {
                let output = exe.join(input.file_stem().unwrap()).with_extension("wixobj");
                let arch = if target.contains("x86_64") { "x64" } else { "x86" };
                let mut cmd = command(&candle);
                cmd.current_dir(&exe)
                    .arg("-nologo")
                    .arg("-dRustcDir=trustc")
                    .arg("-dCargoDir=targo")
                    .arg("-dStdDir=trust-std")
                    .arg("-dAnalysisDir=trust-analysis")
                    .arg("-arch")
                    .arg(arch)
                    .arg("-out")
                    .arg(&output)
                    .arg(input);
                add_env(builder, &mut cmd, target, &built_tools);

                if built_tools.contains("tippy") {
                    cmd.arg("-dClippyDir=tippy");
                }
                if built_tools.contains("trustfmt") {
                    cmd.arg("-dRustFmtDir=trustfmt");
                }
                if built_tools.contains("targo-trust") {
                    cmd.arg("-dTCargoTrustDir=targo-trust");
                }
                if built_tools.contains("trust-docs") {
                    cmd.arg("-dDocsDir=trust-docs");
                }
                if built_tools.contains("trust-analyzer") {
                    cmd.arg("-dRustAnalyzerDir=trust-analyzer");
                }
                if built_tools.contains("trust-miri") {
                    cmd.arg("-dMiriDir=trust-miri");
                }
                if target.is_windows_gnu() || target.is_windows_gnullvm() {
                    cmd.arg("-dGccDir=trust-mingw");
                }
                cmd.run(builder);
            };
            candle(&xform(&etc.join("msi/rust.wxs")));
            candle(&etc.join("msi/ui.wxs"));
            candle(&etc.join("msi/rustwelcomedlg.wxs"));
            candle("RustcGroup.wxs".as_ref());
            if built_tools.contains("trust-docs") {
                candle("DocsGroup.wxs".as_ref());
            }
            candle("CargoGroup.wxs".as_ref());
            if built_tools.contains("targo-trust") {
                candle("TCargoTrustGroup.wxs".as_ref());
            }
            candle("StdGroup.wxs".as_ref());
            if built_tools.contains("tippy") {
                candle("ClippyGroup.wxs".as_ref());
            }
            if built_tools.contains("trustfmt") {
                candle("RustFmtGroup.wxs".as_ref());
            }
            if built_tools.contains("trust-miri") {
                candle("MiriGroup.wxs".as_ref());
            }
            if built_tools.contains("trust-analyzer") {
                candle("RustAnalyzerGroup.wxs".as_ref());
            }
            candle("AnalysisGroup.wxs".as_ref());

            if target.is_windows_gnu() || target.is_windows_gnullvm() {
                candle("GccGroup.wxs".as_ref());
            }

            builder.create(&exe.join("LICENSE.rtf"), &rtf);
            builder.install(&etc.join("gfx/banner.bmp"), &exe, FileType::Regular);
            builder.install(&etc.join("gfx/dialogbg.bmp"), &exe, FileType::Regular);

            builder.info(&format!("building `msi` installer with {light:?}"));
            let filename = format!("{}-{}.msi", pkgname(builder, "trust"), target.triple);
            let mut cmd = command(&light);
            cmd.arg("-nologo")
                .arg("-ext")
                .arg("WixUIExtension")
                .arg("-ext")
                .arg("WixUtilExtension")
                .arg("-out")
                .arg(exe.join(&filename))
                .arg("rust.wixobj")
                .arg("ui.wixobj")
                .arg("rustwelcomedlg.wixobj")
                .arg("RustcGroup.wixobj")
                .arg("CargoGroup.wixobj")
                .arg("StdGroup.wixobj")
                .arg("AnalysisGroup.wixobj")
                .current_dir(&exe);

            if built_tools.contains("targo-trust") {
                cmd.arg("TCargoTrustGroup.wixobj");
            }
            if built_tools.contains("tippy") {
                cmd.arg("ClippyGroup.wixobj");
            }
            if built_tools.contains("trustfmt") {
                cmd.arg("RustFmtGroup.wixobj");
            }
            if built_tools.contains("trust-miri") {
                cmd.arg("MiriGroup.wixobj");
            }
            if built_tools.contains("trust-analyzer") {
                cmd.arg("RustAnalyzerGroup.wixobj");
            }
            if built_tools.contains("trust-docs") {
                cmd.arg("DocsGroup.wixobj");
            }

            if target.is_windows_gnu() || target.is_windows_gnullvm() {
                cmd.arg("GccGroup.wixobj");
            }
            // ICE57 wrongly complains about the shortcuts
            cmd.arg("-sice:ICE57");

            let _time = timeit(builder);
            cmd.run(builder);

            if !builder.config.dry_run() {
                t!(move_file(exe.join(&filename), distdir(builder).join(&filename)));
            }
        }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("extended", self.target).built_by(self.build_compiler))
    }
}

fn add_env(
    builder: &Builder<'_>,
    cmd: &mut BootstrapCommand,
    target: TargetSelection,
    built_tools: &HashSet<&'static str>,
) {
    let mut parts = builder.version.split('.');
    cmd.env("CFG_RELEASE_INFO", builder.rust_version())
        .env("CFG_RELEASE_NUM", &builder.version)
        .env("CFG_RELEASE", builder.rust_release())
        .env("CFG_VER_MAJOR", parts.next().unwrap())
        .env("CFG_VER_MINOR", parts.next().unwrap())
        .env("CFG_VER_PATCH", parts.next().unwrap())
        .env("CFG_VER_BUILD", "0") // just needed to build
        .env("CFG_PACKAGE_VERS", builder.rust_package_vers())
        .env("CFG_PACKAGE_NAME", pkgname(builder, "trust"))
        .env("CFG_BUILD", target.triple)
        .env("CFG_CHANNEL", &builder.config.channel);

    if target.is_windows_gnullvm() {
        cmd.env("CFG_MINGW", "1").env("CFG_ABI", "LLVM");
    } else if target.is_windows_gnu() {
        cmd.env("CFG_MINGW", "1").env("CFG_ABI", "GNU");
    } else {
        cmd.env("CFG_MINGW", "0").env("CFG_ABI", "MSVC");
    }

    // ensure these variables are defined
    let mut define_optional_tool = |tool_name: &str, env_name: &str| {
        cmd.env(env_name, if built_tools.contains(tool_name) { "1" } else { "0" });
    };
    define_optional_tool("trustfmt", "CFG_RUSTFMT");
    define_optional_tool("tippy", "CFG_CLIPPY");
    define_optional_tool("targo-trust", "CFG_CARGO_TRUST");
    define_optional_tool("trust-miri", "CFG_MIRI");
    define_optional_tool("trust-analyzer", "CFG_RA");
}

fn install_llvm_file(
    builder: &Builder<'_>,
    source: &Path,
    destination: &Path,
    install_symlink: bool,
) {
    if builder.config.dry_run() {
        return;
    }

    if source.is_symlink() {
        // If we have a symlink like libLLVM-18.so -> libLLVM.so.18.1, install the target of the
        // symlink, which is what will actually get loaded at runtime.
        builder.install(&t!(fs::canonicalize(source)), destination, FileType::NativeLibrary);

        let full_dest = destination.join(source.file_name().unwrap());
        if install_symlink {
            // For download-ci-llvm, also install the symlink, to match what LLVM does. Using a
            // symlink is fine here, as this is not a rustup component.
            builder.copy_link(source, &full_dest, FileType::NativeLibrary);
        } else {
            // Otherwise, replace the symlink with an equivalent linker script. This is used when
            // projects like miri link against librustc_driver.so. We don't use a symlink, as
            // these are not allowed inside rustup components.
            let link = t!(fs::read_link(source));
            let mut linker_script = t!(fs::File::create(full_dest));
            t!(write!(linker_script, "INPUT({})\n", link.display()));

            // We also want the linker script to have the same mtime as the source, otherwise it
            // can trigger rebuilds.
            let meta = t!(fs::metadata(source));
            if let Ok(mtime) = meta.modified() {
                t!(linker_script.set_modified(mtime));
            }
        }
    } else {
        builder.install(source, destination, FileType::NativeLibrary);
    }
}

/// Maybe add LLVM object files to the given destination lib-dir. Allows either static or dynamic linking.
///
/// Returns whether the files were actually copied.
#[cfg_attr(
    feature = "tracing",
    instrument(
        level = "trace",
        name = "maybe_install_llvm",
        skip_all,
        fields(target = ?target, dst_libdir = ?dst_libdir, install_symlink = install_symlink),
    ),
)]
fn maybe_install_llvm(
    builder: &Builder<'_>,
    target: TargetSelection,
    dst_libdir: &Path,
    install_symlink: bool,
) -> bool {
    // If the LLVM was externally provided, then we don't currently copy
    // artifacts into the sysroot. This is not necessarily the right
    // choice (in particular, it will require the LLVM dylib to be in
    // the linker's load path at runtime), but the common use case for
    // external LLVMs is distribution provided LLVMs, and in that case
    // they're usually in the standard search path (e.g., /usr/lib) and
    // copying them here is going to cause problems as we may end up
    // with the wrong files and isn't what distributions want.
    //
    // This behavior may be revisited in the future though.
    //
    // NOTE: this intentionally doesn't use `is_rust_llvm`; whether this is patched or not doesn't matter,
    // we only care if the shared object itself is managed by bootstrap.
    //
    // If the LLVM is coming from ourselves (just from CI) though, we
    // still want to install it, as it otherwise won't be available.
    if builder.config.is_system_llvm(target) {
        trace!("system LLVM requested, no install");
        return false;
    }

    // On macOS, rustc (and LLVM tools) link to an unversioned libLLVM.dylib
    // instead of libLLVM-11-rust-....dylib, as on linux. It's not entirely
    // clear why this is the case, though. llvm-config will emit the versioned
    // paths and we don't want those in the sysroot (as we're expecting
    // unversioned paths).
    if target.contains("apple-darwin") && builder.llvm_link_shared() {
        let src_libdir = builder.llvm_out(target).join("lib");
        let llvm_dylib_path = src_libdir.join("libLLVM.dylib");
        if llvm_dylib_path.exists() {
            builder.install(&llvm_dylib_path, dst_libdir, FileType::NativeLibrary);

            if install_symlink && let Some(llvm_config_path) = &builder.llvm_config(target) {
                let major = llvm::get_llvm_version_major(builder, llvm_config_path);
                let versioned_name = match &builder.config.llvm_version_suffix {
                    Some(version_suffix) => format!("libLLVM-{major}{version_suffix}.dylib"),
                    None => {
                        // dev builds use `-rust-dev`, while release-channel builds include the Rust version.
                        if builder.config.channel == "dev" {
                            format!("libLLVM-{major}-rust-dev.dylib")
                        } else {
                            format!(
                                "libLLVM-{major}-rust-{}-{}.dylib",
                                builder.version, builder.config.channel
                            )
                        }
                    }
                };
                t!(builder.symlink_file("libLLVM.dylib", dst_libdir.join(versioned_name)));
            }
        }
        !builder.config.dry_run()
    } else if let llvm::LlvmBuildStatus::AlreadyBuilt(llvm::LlvmResult {
        host_llvm_config, ..
    }) = llvm::prebuilt_llvm_config(builder, target, true)
    {
        trace!("LLVM already built, installing LLVM files");
        let mut cmd = command(host_llvm_config);
        cmd.cached();
        cmd.arg("--libfiles");
        builder.do_if_verbose(|| println!("running {cmd:?}"));
        let files = cmd.run_capture_stdout(builder).stdout();
        let build_llvm_out = &builder.llvm_out(builder.config.host_target);
        let target_llvm_out = &builder.llvm_out(target);
        for file in files.trim_end().split(' ') {
            // If we're not using a custom LLVM, make sure we package for the target.
            let file = if let Ok(relative_path) = Path::new(file).strip_prefix(build_llvm_out) {
                target_llvm_out.join(relative_path)
            } else {
                PathBuf::from(file)
            };
            install_llvm_file(builder, &file, dst_libdir, install_symlink);
        }
        !builder.config.dry_run()
    } else {
        false
    }
}

/// Maybe add libLLVM.so to the target lib-dir for linking.
#[cfg_attr(
    feature = "tracing",
    instrument(
        level = "trace",
        name = "maybe_install_llvm_target",
        skip_all,
        fields(
            llvm_link_shared = ?builder.llvm_link_shared(),
            target = ?target,
            sysroot = ?sysroot,
        ),
    ),
)]
pub fn maybe_install_llvm_target(builder: &Builder<'_>, target: TargetSelection, sysroot: &Path) {
    let dst_libdir = sysroot.join("lib/rustlib").join(target).join("lib");
    // We do not need to copy LLVM files into the sysroot if it is not
    // dynamically linked; it is already included into librustc_llvm
    // statically.
    if builder.llvm_link_shared() {
        maybe_install_llvm(builder, target, &dst_libdir, false);
    }
}

/// Maybe add libLLVM.so to the runtime lib-dir for rustc itself.
#[cfg_attr(
    feature = "tracing",
    instrument(
        level = "trace",
        name = "maybe_install_llvm_runtime",
        skip_all,
        fields(
            llvm_link_shared = ?builder.llvm_link_shared(),
            target = ?target,
            sysroot = ?sysroot,
        ),
    ),
)]
pub fn maybe_install_llvm_runtime(builder: &Builder<'_>, target: TargetSelection, sysroot: &Path) {
    let dst_libdir = sysroot.join(builder.libdir_relative(Compiler::new(1, target)));
    // We do not need to copy LLVM files into the sysroot if it is not
    // dynamically linked; it is already included into librustc_llvm
    // statically.
    if builder.llvm_link_shared() {
        maybe_install_llvm(builder, target, &dst_libdir, false);

        // To workaround lack of rpath on Windows, we bundle another copy of
        // the LLVM DLL to make rust-lld and llvm-tools work when `sysroot/bin`
        //  is missing from PATH, i.e. when they not launched by rustc.
        if target.triple.contains("windows") {
            let dst_libdir = sysroot.join("lib/rustlib").join(target).join("bin");
            maybe_install_llvm(builder, target, &dst_libdir, false);
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct LlvmTools {
    pub target: TargetSelection,
}

impl Step for LlvmTools {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        let mut run = run.alias("trust-llvm-tools").alias("llvm-tools");
        for tool in LLVM_TOOLS {
            run = run.alias(tool);
        }

        run
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        should_build_extended_tool(builder, "trust-llvm-tools")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(LlvmTools { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        fn tools_to_install(paths: &[PathBuf]) -> Vec<&'static str> {
            let mut tools = vec![];

            for path in paths {
                let path = path.to_str().unwrap();

                // Include all tools if the canonical Trust component or the
                // inherited Rust compatibility selector is requested.
                if path == "trust-llvm-tools" || path == "llvm-tools" {
                    return LLVM_TOOLS.to_owned();
                }

                for tool in LLVM_TOOLS {
                    if path == *tool {
                        tools.push(*tool);
                    }
                }
            }

            // If no specific tool is requested, include all tools.
            if tools.is_empty() {
                tools = LLVM_TOOLS.to_owned();
            }

            tools
        }

        let target = self.target;

        // Run only if a custom llvm-config is not used
        if let Some(config) = builder.config.target_config.get(&target)
            && !builder.config.llvm_from_ci
            && config.llvm_config.is_some()
        {
            builder.info(&format!("Skipping LlvmTools ({target}): external LLVM"));
            return None;
        }

        if !builder.config.dry_run() {
            builder.require_submodule("src/llvm-project", None);
        }

        builder.ensure(crate::core::build_steps::llvm::Llvm { target });

        let mut tarball = Tarball::new(builder, "trust-llvm-tools", &target.triple);
        tarball.set_overlay(OverlayKind::Llvm);
        tarball.is_preview(true);

        if builder.config.llvm_tools_enabled {
            // Prepare the image directory
            let src_bindir = builder.llvm_out(target).join("bin");
            let dst_bindir = format!("lib/rustlib/{}/bin", target.triple);
            for tool in tools_to_install(&builder.paths) {
                let exe = src_bindir.join(exe(tool, target));
                // When using `download-ci-llvm`, some of the tools may not exist, so skip trying to copy them.
                if !exe.exists() && builder.config.llvm_from_ci {
                    eprintln!("{} does not exist; skipping copy", exe.display());
                    continue;
                }

                tarball.add_file(&exe, &dst_bindir, FileType::Executable);
            }
        }

        // Copy libLLVM.so to the target lib dir as well, so the RPATH like
        // `$ORIGIN/../lib` can find it. It may also be used as a dependency
        // of `trustc-dev` to support the inherited `-lLLVM` when using the
        // compiler libraries.
        maybe_install_llvm_target(builder, target, tarball.image_dir());

        Some(tarball.generate())
    }
}

/// Distributes the `llvm-bitcode-linker` tool so that it can be used by a compiler whose host
/// is `target`.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct LlvmBitcodeLinker {
    /// The linker will be compiled by this compiler.
    pub build_compiler: Compiler,
    /// The linker will by usable by rustc on this host.
    pub target: TargetSelection,
}

impl Step for LlvmBitcodeLinker {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("llvm-bitcode-linker")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        should_build_extended_tool(builder, "llvm-bitcode-linker")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(LlvmBitcodeLinker {
            build_compiler: tool::LlvmBitcodeLinker::get_build_compiler_for_target(
                run.builder,
                run.target,
            ),
            target: run.target,
        });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let target = self.target;

        let llbc_linker = builder
            .ensure(tool::LlvmBitcodeLinker::from_build_compiler(self.build_compiler, target));

        let self_contained_bin_dir = format!("lib/rustlib/{}/bin/self-contained", target.triple);

        // Prepare the image directory
        let mut tarball = Tarball::new(builder, "llvm-bitcode-linker", &target.triple);
        tarball.set_overlay(OverlayKind::LlvmBitcodeLinker);
        tarball.is_preview(true);

        tarball.add_file(&llbc_linker.tool_path, self_contained_bin_dir, FileType::Executable);

        Some(tarball.generate())
    }
}

/// Distributes the `enzyme` library so that it can be used by a compiler whose host
/// is `target`.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Enzyme {
    /// Enzyme will by usable by rustc on this host.
    pub target: TargetSelection,
}

impl Step for Enzyme {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("enzyme")
    }

    fn is_default_step(builder: &Builder<'_>) -> bool {
        builder.config.llvm_enzyme
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Enzyme { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        // This prevents Enzyme from being built for "dist"
        // or "install" on the stable/beta channels. It is not yet stable and
        // should not be included.
        if !builder.build.unstable_features() {
            return None;
        }

        let target = self.target;

        let enzyme = builder.ensure(llvm::Enzyme { target });

        let target_libdir = format!("lib/rustlib/{}/lib", target.triple);

        // Prepare the image directory
        let mut tarball = Tarball::new(builder, "enzyme", &target.triple);
        tarball.set_overlay(OverlayKind::Enzyme);
        tarball.is_preview(true);

        tarball.add_file(enzyme.enzyme_path(), target_libdir, FileType::NativeLibrary);

        Some(tarball.generate())
    }
}

/// Tarball intended for internal consumption to ease rustc/std development.
///
/// Should not be considered stable by end users.
///
/// In practice, this is the tarball that gets downloaded and used by
/// `llvm.download-ci-llvm`.
///
/// (Don't confuse this with [`RustcDev`], with a `c`!)
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RustDev {
    pub target: TargetSelection,
}

impl Step for RustDev {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("rust-dev")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(RustDev { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let target = self.target;

        /* run only if llvm-config isn't used */
        if let Some(config) = builder.config.target_config.get(&target)
            && let Some(ref _s) = config.llvm_config
        {
            builder.info(&format!("Skipping RustDev ({target}): external LLVM"));
            return None;
        }

        if !builder.config.dry_run() {
            builder.require_submodule("src/llvm-project", None);
        }

        let mut tarball = Tarball::new(builder, "rust-dev", &target.triple);
        tarball.set_overlay(OverlayKind::Llvm);
        // LLVM requires a shared object symlink to exist on some platforms.
        tarball.permit_symlinks(true);

        builder.ensure(crate::core::build_steps::llvm::Llvm { target });

        let src_bindir = builder.llvm_out(target).join("bin");
        // If updating this, you likely want to change
        // src/bootstrap/download-ci-llvm-stamp as well, otherwise local users
        // will not pick up the extra file until LLVM gets bumped.
        // We should include all the build artifacts obtained from a source build,
        // so that you can use the downloadable LLVM as if you’ve just run a full source build.
        if src_bindir.exists() {
            for entry in walkdir::WalkDir::new(&src_bindir) {
                let entry = t!(entry);
                if entry.file_type().is_file() && !entry.path_is_symlink() {
                    let name = entry.file_name().to_str().unwrap();
                    tarball.add_file(src_bindir.join(name), "bin", FileType::Executable);
                }
            }
        }

        if builder.config.lld_enabled {
            // We want to package `lld` to use it with `download-ci-llvm`.
            let lld_out = builder.ensure(crate::core::build_steps::llvm::Lld { target });

            // We don't build LLD on some platforms, so only add it if it exists
            let lld_path = lld_out.join("bin").join(exe("lld", target));
            if lld_path.exists() {
                tarball.add_file(&lld_path, "bin", FileType::Executable);
            }
        }

        tarball.add_file(builder.llvm_filecheck(target), "bin", FileType::Executable);

        // Copy the include directory as well; needed mostly to build
        // librustc_llvm properly (e.g., llvm-config.h is in here). But also
        // just broadly useful to be able to link against the bundled LLVM.
        tarball.add_dir(builder.llvm_out(target).join("include"), "include");

        // Copy libLLVM.so to the target lib dir as well, so the RPATH like
        // `$ORIGIN/../lib` can find it. It may also be used as a dependency
        // of `trustc-dev` to support the inherited `-lLLVM` when using the
        // compiler libraries.
        let dst_libdir = tarball.image_dir().join("lib");
        maybe_install_llvm(builder, target, &dst_libdir, true);
        let link_type = if builder.llvm_link_shared() { "dynamic" } else { "static" };
        t!(std::fs::write(tarball.image_dir().join("link-type.txt"), link_type), dst_libdir);

        // Copy the `compiler-rt` source, so that `library/profiler_builtins`
        // can potentially use it to build the profiler runtime without needing
        // to check out the LLVM submodule.
        copy_src_dirs(
            builder,
            &builder.src.join("src").join("llvm-project"),
            &["compiler-rt"],
            // The test subdirectory is much larger than the rest of the source,
            // and we currently don't use these test files anyway.
            &["compiler-rt/test"],
            tarball.image_dir(),
        );

        Some(tarball.generate())
    }
}

/// Tarball intended for internal consumption to ease rustc/std development.
///
/// It only packages the binaries that were already compiled when bootstrap itself was built.
///
/// Should not be considered stable by end users.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Bootstrap {
    target: TargetSelection,
}

impl Step for Bootstrap {
    type Output = Option<GeneratedTarball>;

    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.path("bootstrap")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Bootstrap { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> Option<GeneratedTarball> {
        let target = self.target;

        let tarball = Tarball::new(builder, "bootstrap", &target.triple);

        let bootstrap_outdir = &builder.bootstrap_out;
        for file in &["bootstrap", "rustc", "rustdoc"] {
            tarball.add_file(
                bootstrap_outdir.join(exe(file, target)),
                "bootstrap/bin",
                FileType::Executable,
            );
        }

        Some(tarball.generate())
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("bootstrap", self.target))
    }
}

/// Tarball containing a prebuilt version of the build-manifest tool, intended to be used by the
/// release process to avoid cloning the monorepo and building stuff.
///
/// Should not be considered stable by end users.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct BuildManifest {
    target: TargetSelection,
}

impl Step for BuildManifest {
    type Output = GeneratedTarball;

    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("build-manifest")
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(BuildManifest { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> GeneratedTarball {
        // FIXME: Should BuildManifest actually be built for `self.target`?
        // Today CI only builds this step where that matches the host_target so it doesn't matter
        // today.
        let build_manifest =
            builder.ensure(tool::BuildManifest::new(builder, builder.config.host_target));

        let tarball = Tarball::new(builder, "build-manifest", &self.target.triple);
        tarball.add_file(&build_manifest.tool_path, "bin", FileType::Executable);
        tarball.generate()
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("build-manifest", self.target))
    }
}

/// Tarball containing artifacts necessary to reproduce the build of rustc.
///
/// Currently this is the PGO (and possibly BOLT) profile data.
///
/// Should not be considered stable by end users.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ReproducibleArtifacts {
    target: TargetSelection,
}

impl Step for ReproducibleArtifacts {
    type Output = Option<GeneratedTarball>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias("reproducible-artifacts")
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        true
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(ReproducibleArtifacts { target: run.target });
    }

    fn run(self, builder: &Builder<'_>) -> Self::Output {
        let mut added_anything = false;
        let tarball = Tarball::new(builder, "reproducible-artifacts", &self.target.triple);
        if let Some(path) = builder.config.rust_profile_use.as_ref() {
            tarball.add_file(path, ".", FileType::Regular);
            added_anything = true;
        }
        if let Some(path) = builder.config.llvm_profile_use.as_ref() {
            tarball.add_file(path, ".", FileType::Regular);
            added_anything = true;
        }
        for profile in &builder.config.reproducible_artifacts {
            tarball.add_file(profile, ".", FileType::Regular);
            added_anything = true;
        }
        if added_anything { Some(tarball.generate()) } else { None }
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::dist("reproducible-artifacts", self.target))
    }
}
