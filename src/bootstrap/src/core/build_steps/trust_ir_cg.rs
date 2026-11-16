//! Trust: the trust-ir → trust-cg rustc backend (`-Zcodegen-backend=trust-ir-cg`).
//!
//! This is the SELF-HOST codegen lane of the "one program, two languages"
//! design: rustc MIR is lowered per monomorphized instance into a
//! `trust_ir::Module` and compiled to native code by trust-cg's own
//! `Compiler`. The backend's source lives in the `first-party/trust-cg`
//! sibling (`crates/rustc-codegen-trust-cg`), pinned by that gitlink, and is
//! built HERE, by the Trust stage compiler it will be loaded into, as a
//! `dylib` plugin — exactly the way upstream ships `rustc_codegen_cranelift`.
//!
//! # Why a dylib, and why it is not the builtin `trust-cg`
//!
//! The builtin `trust-cg` backend (`compiler/rustc_codegen_trust_cg`, over
//! `crates/trust-cg-bridge`) is an rlib-only, statics-free adapter with the
//! M-POS proven-output gate; bootstrap refuses to self-host through it
//! (`compile::staged_narrow_trust_cg_cannot_self_host`). The sibling backend
//! emits executables, statics with relocations, thread-locals, vtables and
//! real unwinding, and reports every refusal crate-wide — the shape a
//! self-host needs. The two are distinct products of the same trust-cg core
//! and are shipped under distinct names so neither shadows the other.
//!
//! A plugin is loaded through `dlopen` and must share ONE copy of
//! `librustc_driver` (and `libstd`) with the compiler that loads it, or two
//! copies of `rustc_span`'s scoped thread-locals coexist and the first symbol
//! interning panics. That is guaranteed the same way every rustc-private tool
//! in this tree guarantees it: `Mode::ToolRustcPrivate` links against the
//! target compiler's own rustc rmetas and runtime dylibs
//! (`tool::add_rustc_private_tool_metadata_search_path`), and the crate is
//! compiled with `-Cprefer-dynamic` so nothing that already lives in
//! `librustc_driver` is duplicated into the plugin.
//!
//! # Pairing
//!
//! The dylib installed into stage N's sysroot is compiled BY stage N-1 (the
//! compiler that built stage N's rustc crates, so it can read their rmetas)
//! and links AGAINST stage N's `librustc_driver`. `Assemble` installs it as
//! part of assembling stage N, before the std that `Assemble` itself builds
//! with the stage-N compiler — so a stage-N compiler whose default backend is
//! `trust-ir-cg` finds it before it compiles a single unit with it, its own
//! std included.
//!
//! That last clause is the correction of a measured defect, not a restatement.
//! This paragraph used to say "before it compiles a single unit of stage N+1",
//! and the install sat at the END of `Assemble` accordingly. Stage N does not
//! wait for stage N+1 to use its backend: it compiles its OWN std inside
//! `Assemble`, several steps before that. See the ordering comment at the call
//! site in `compile.rs`.
//!
//! # Naming
//!
//! `rustc_interface::util::find_codegen_backend_in_sysroot` looks in
//! `<sysroot>/lib/rustlib/<host>/codegen-backends/` for
//! `<DLL_PREFIX>rustc_codegen_<name>-<CFG_RELEASE><DLL_SUFFIX>`, with `<name>`
//! taken verbatim from `-Zcodegen-backend`. The crate itself is still named
//! `rustc_codegen_trust_cg`; the artifact is renamed on install.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::env::consts::{DLL_PREFIX, DLL_SUFFIX};
use std::fs;
use std::path::{Path, PathBuf};

use crate::core::backend::CodegenBackendKind;
use crate::core::build_steps::compile::{self, CargoMessage};
use crate::core::build_steps::tool::{self, SourceType};
use crate::core::builder::{
    Builder, CommandLineStep, Kind, RunConfig, ShouldRun, Step, StepMetadata,
};
use crate::core::compiler::Compiler;
use crate::core::config::TargetSelection;
use crate::core::session::{FileType, Mode};
use crate::utils::helpers::t;

/// The backend name as written in `rust.codegen-backends` and
/// `-Zcodegen-backend`.
pub(crate) const BACKEND_NAME: &str = "trust-ir-cg";

/// Path of the backend crate, relative to the source root.
pub(crate) const CRATE_PATH: &str = "first-party/trust-cg/crates/rustc-codegen-trust-cg";

/// The crate's own name, which is what cargo names the built dylib after.
const CRATE_NAME: &str = "rustc_codegen_trust_cg";

/// Whether `rust.codegen-backends` (or the host's target override) enables
/// the trust-ir-cg backend for `host`.
pub(crate) fn enabled_for(builder: &Builder<'_>, host: TargetSelection) -> bool {
    builder.config.enabled_codegen_backends(host).iter().any(CodegenBackendKind::is_trust_ir_cg)
}

/// The file name `rustc_interface` resolves `-Zcodegen-backend=trust-ir-cg`
/// to inside `codegen-backends/`.
pub(crate) fn sysroot_dylib_name(release: &str) -> String {
    format!("{DLL_PREFIX}rustc_codegen_{BACKEND_NAME}-{release}{DLL_SUFFIX}")
}

/// The file name cargo gives the top-level dylib artifact of the crate.
fn cargo_dylib_name() -> String {
    format!("{DLL_PREFIX}{CRATE_NAME}{DLL_SUFFIX}")
}

/// Where the installed backend lives for `target_compiler`.
pub(crate) fn installed_path(builder: &Builder<'_>, target_compiler: Compiler) -> PathBuf {
    builder
        .sysroot_codegen_backends(target_compiler)
        .join(sysroot_dylib_name(&builder.rust_release()))
}

/// Build the backend for `target_compiler` and install it into that
/// compiler's `codegen-backends/`. Called from `Assemble`, after the target
/// compiler's `librustc_driver` runtime dylibs are in place and BEFORE the std
/// that `Assemble` builds with the target compiler. Returns the installed
/// path, or `None` when the backend is not enabled for this host or there is
/// nothing to build at stage 0.
pub(crate) fn install_into_sysroot(
    builder: &Builder<'_>,
    build_compiler: Compiler,
    target_compiler: Compiler,
) -> Option<PathBuf> {
    let host = target_compiler.host;
    if target_compiler.stage == 0 || !enabled_for(builder, host) {
        return None;
    }
    if builder.config.dry_run() {
        return Some(installed_path(builder, target_compiler));
    }
    // SELF-HOST ONLY. `DLL_PREFIX`/`DLL_SUFFIX` are the build machine's, the
    // runtime-dylib identity check binds to the build machine's `dlopen`, and
    // the sibling backend's TLS lowering is Darwin-TLV shaped. A cross-host
    // trust-ir-cg is a separate, unmeasured lane; refuse rather than ship a
    // plugin the assembled compiler cannot load.
    assert!(
        build_compiler.host == host,
        "the trust-ir-cg backend is built for the compiler that loads it; a cross-host build \
         ({} -> {host}) is not supported — drop `trust-ir-cg` from \
         `target.{host}.codegen-backends`",
        build_compiler.host,
    );

    let built = builder.ensure(BuildTrustIrCgDylib { build_compiler, target_compiler });
    let dst_dir = builder.sysroot_codegen_backends(target_compiler);
    t!(fs::create_dir_all(&dst_dir));
    let dst = dst_dir.join(sysroot_dylib_name(&builder.rust_release()));
    builder.copy_link(&built, &dst, FileType::NativeLibrary);
    Some(dst)
}

/// The cargo build of the backend dylib. One step per (build, target)
/// compiler pair so an `x.py build` that assembles several stages compiles
/// each pairing exactly once.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct BuildTrustIrCgDylib {
    build_compiler: Compiler,
    target_compiler: Compiler,
}

// Plain `Step` (not command-line selectable): only ever ensured by
// `install_into_sysroot`/the user-facing backend step below.
impl Step for BuildTrustIrCgDylib {
    type Output = PathBuf;

    fn run(self, builder: &Builder<'_>) -> PathBuf {
        let host = self.target_compiler.host;
        let mut cargo = tool::prepare_tool_cargo(
            builder,
            self.build_compiler,
            Mode::ToolRustcPrivate,
            host,
            Kind::Build,
            CRATE_PATH,
            SourceType::Submodule,
            &[],
        );
        // Link against the TARGET compiler's rustc rmetas and bind the runtime
        // identity to its `librustc_driver`, exactly as tippy-driver does.
        tool::add_rustc_private_tool_metadata_search_path(
            builder,
            &mut cargo,
            self.target_compiler,
            host,
        );
        // A backend dylib must borrow std and every rustc crate from the
        // loading compiler's `librustc_driver`, never carry its own copy.
        cargo.rustflag("-Cprefer-dynamic");
        // Trust: the backend's operator knobs (`-Ztrust-ir-cg-args`) are gated on a
        // `cfg` its `build.rs` sets from a CAPABILITY PROBE, for the out-of-tree case
        // where the crate is built against a compiler predating the option. In THIS
        // build there is nothing to probe: the option is declared in this tree's
        // `rustc_session::config::Options`, and the crate is compiled against that very
        // compiler's rmetas.
        //
        // The probe is not merely redundant here, it is WRONG here. It runs from a build
        // script, where `$RUSTC` is not the compiler the crate is compiled with, and it
        // fails for reasons unrelated to the option. Measured 2026-09-14 on this tree:
        // the stage1 build wrote `probe_verify_off.rmeta` and NO
        // `probe_trust_ir_cg_args.rmeta`, in a stage whose compiler accepts
        // `-Ztrust-ir-cg-args` perfectly well — so every knob was silently inert
        // (`no-proof-certs=1` ignored, `time-codegen` printing nothing) while the same
        // sibling built for stage2 had the cfg set and honoured them. An A/B across
        // those two stages would have compared two different lanes and read as "no
        // difference".
        //
        // Stating it here is also FAIL-CLOSED: if the option is ever removed from
        // `rustc_session`, the `#[cfg(trust_ir_cg_args)]` arm stops compiling and this
        // build breaks loudly, rather than the knobs going quiet again.
        cargo.rustflag("--cfg=trust_ir_cg_args");
        cargo.arg("--lib");

        let _guard = builder.msg(
            Kind::Build,
            "trust-ir-cg backend",
            Mode::ToolRustcPrivate,
            self.build_compiler,
            host,
        );

        let wanted = cargo_dylib_name();
        let mut produced: Option<PathBuf> = None;
        let ok = compile::stream_cargo(builder, cargo, vec![], &mut |msg| {
            let CargoMessage::CompilerArtifact { filenames, .. } = msg else { return };
            for filename in filenames {
                let path = Path::new(&*filename);
                // Cargo reports the hashed `deps/` copy and the top-level
                // artifact; the top-level one is the stable name.
                if path.file_name().and_then(|n| n.to_str()) == Some(wanted.as_str()) {
                    produced = Some(path.to_path_buf());
                }
            }
        });
        if !ok {
            crate::exit!(1);
        }
        let expected =
            builder.cargo_out(self.build_compiler, Mode::ToolRustcPrivate, host).join(&wanted);
        let built = produced.unwrap_or(expected);
        assert!(
            built.is_file(),
            "cargo reported success building the trust-ir-cg backend but `{}` is not a file",
            built.display()
        );
        built
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("trust-ir-cg backend", self.target_compiler.host))
    }
}

/// User-facing step: `x.py build trust-ir-cg` (or the crate path). The
/// backend is installed by `Assemble` as a side effect of assembling the
/// target compiler, so this step ensures that compiler and reports where the
/// dylib landed.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TrustIrCgBackend {
    pub target_compiler: Compiler,
}

impl CommandLineStep for TrustIrCgBackend {
    type Output = Option<PathBuf>;
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        // Upstream 1.101: every command-line step must register a pathset
        // (the old `run.never()` opt-out is gone). Registration is harmless
        // while disabled: `make_run` below still refuses to ensure the step
        // unless the backend is enabled for the target.
        run.path(CRATE_PATH).alias(BACKEND_NAME).alias("rustc_codegen_trust_ir_cg")
    }

    fn make_run(run: RunConfig<'_>) {
        if !enabled_for(run.builder, run.target) {
            return;
        }
        run.builder.ensure(TrustIrCgBackend {
            target_compiler: Compiler::new(run.builder.top_stage, run.target),
        });
    }

    fn run(self, builder: &Builder<'_>) -> Option<PathBuf> {
        if self.target_compiler.stage == 0 || !enabled_for(builder, self.target_compiler.host) {
            return None;
        }
        // Assembling the compiler installs the backend (see `install_into_sysroot`).
        let assembled = builder.compiler(self.target_compiler.stage, self.target_compiler.host);
        let path = installed_path(builder, assembled);
        if !builder.config.dry_run() {
            assert!(
                path.is_file(),
                "stage{} compiler was assembled with `trust-ir-cg` enabled but `{}` is missing",
                assembled.stage,
                path.display()
            );
        }
        Some(path)
    }

    fn metadata(&self) -> Option<StepMetadata> {
        Some(StepMetadata::build("trust-ir-cg", self.target_compiler.host))
    }
}

#[cfg(test)]
mod tests;
