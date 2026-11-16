use std::any::Any;
use std::hash::Hash;

use rustc_ast::expand::allocator::AllocatorMethod;
use rustc_data_structures::sync::{DynSend, DynSync};
use rustc_metadata::EncodedMetadata;
use rustc_metadata::creader::MetadataLoaderDyn;
use rustc_middle::dep_graph::WorkProductMap;
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::config::{OutputFilenames, PrintRequest};
use rustc_session::{CodegenBackendInit, EarlySession, IncrCompSession, Session};
use rustc_span::Symbol;
use rustc_structures::CrateType;

use super::CodegenObject;
use crate::back::archive::ArArchiveBuilderBuilder;
use crate::back::link::link_binary;
use crate::{CompiledModules, CrateInfo, ModuleCodegen, TargetConfig};

pub trait BackendTypes {
    type Function: CodegenObject;
    type BasicBlock: Copy;
    type Funclet;

    type Value: CodegenObject + PartialEq;
    type Type: CodegenObject + PartialEq;
    type FunctionSignature: CodegenObject + PartialEq;

    // FIXME(eddyb) find a common convention for all of the debuginfo-related
    // names (choose between `Dbg`, `Debug`, `DebugInfo`, `DI` etc.).
    type DIScope: Copy + Hash + PartialEq + Eq;
    type DILocation: Copy;
    type DIVariable: Copy;
}

pub trait CodegenBackend {
    fn name(&self) -> &'static str;

    fn init(&mut self, _sess: &EarlySession) -> CodegenBackendInit {
        Default::default()
    }

    /// Answer a backend-owned `--print` request.
    ///
    /// A silent empty default is unsafe: callers cannot distinguish a backend
    /// with an empty capability set from one that never wired the query. Make
    /// unsupported queries explicit; a backend must override this method to
    /// advertise concrete values.
    fn print(&self, req: &PrintRequest, _out: &mut String, sess: &Session) {
        sess.dcx().fatal(format!(
            "codegen backend `{}` does not support `--print={}`",
            self.name(),
            req.kind
        ));
    }

    /// Collect target-specific options that should be set in `cfg(...)`, including
    /// `target_feature` and support for unstable float types.
    fn target_config(&self, _sess: &EarlySession) -> TargetConfig {
        TargetConfig {
            internal_target_features: Default::default(),
            // `true` is used as a default so backends need to acknowledge when they do not
            // support the float types, rather than accidentally quietly skipping all tests.
            has_reliable_f16: true,
            has_reliable_f16_math: true,
            has_reliable_f16b: true,
            has_reliable_f128: true,
            has_reliable_f128_math: true,
        }
    }

    fn supported_crate_types(&self, _sess: &Session) -> Vec<CrateType> {
        vec![
            CrateType::Executable,
            CrateType::Dylib,
            CrateType::Rlib,
            CrateType::StaticLib,
            CrateType::Cdylib,
            CrateType::ProcMacro,
            CrateType::Sdylib,
        ]
    }

    /// Trust (WS7.10 / F-114): whether a requested crate type that
    /// `supported_crate_types` does not advertise is a hard ERROR for this
    /// session rather than rustc's default "dropping unsupported crate type"
    /// warning.
    ///
    /// The default (`false`) keeps the upstream behaviour for every backend
    /// that does not opt in. A backend returns `true` when dropping the type
    /// would make a real compilation exit 0 without the artifact it was asked
    /// for. It must return `false` for a print-only invocation that the driver
    /// answers before codegen (Cargo's `--print=file-names --crate-type …`
    /// capability probe reads a missing line as "unsupported"; an error there
    /// would fail every Cargo build, including ones that need only supported
    /// crate types), and for a driver mode that exits before codegen and link
    /// (`-Zunpretty=<mode>`, `-Zno-analysis`), which emits no artifact at all.
    fn unsupported_crate_type_is_fatal(&self, _sess: &Session) -> bool {
        false
    }

    /// Returns crate types for which this backend can produce the complete
    /// linked artifact. This is distinct from `supported_crate_types`: a
    /// backend may accept additional crate types for frontend-only output such
    /// as metadata or MIR without supporting their final link contracts.
    fn supported_link_crate_types(&self, sess: &Session) -> Vec<CrateType> {
        self.supported_crate_types(sess)
    }

    /// Answer `-Cpasses=list`. Backends without a configurable pass surface
    /// must say so explicitly; an empty successful response is indistinguishable
    /// from a missing implementation to scripts and users.
    fn print_passes(&self) {
        println!("Codegen backend `{}` has no configurable passes.", self.name());
    }

    fn print_version(&self) {}

    /// Value printed by `--print=backend-has-zstd`.
    ///
    /// Used by compiletest to determine whether tests involving zstd compression
    /// (e.g. `-Zdebuginfo-compression=zstd`) should be executed or skipped.
    fn has_zstd(&self) -> bool {
        false
    }

    /// Value printed by `--print=backend-has-mnemonic:...`.
    ///
    /// Used by compiletest to determine whether tests involving `asm!()` should
    /// be executed or skipped.
    fn has_mnemonic(&self, _sess: &Session, _mnemonic: &str) -> bool {
        false
    }

    /// The metadata loader used to load rlib and dylib metadata.
    ///
    /// Alternative codegen backends may want to use different rlib or dylib formats than the
    /// default native static archives and dynamic libraries.
    fn metadata_loader(&self) -> Box<MetadataLoaderDyn> {
        Box::new(crate::back::metadata::DefaultMetadataLoader)
    }

    /// Allows queries to be overridden. Not used by any in-tree backends, but rustc_codegen_spirv
    /// and rustc_codegen_nvvm use it.
    fn provide(&self, _providers: &mut Providers) {}

    fn target_cpu(&self, sess: &Session) -> String;

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Box<dyn Any>;

    /// This is called on the returned `Box<dyn Any>` from [`codegen_crate`](Self::codegen_crate)
    ///
    /// # Panics
    ///
    /// Panics when the passed `Box<dyn Any>` was not returned by [`codegen_crate`](Self::codegen_crate).
    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        sess: &Session,
        incr_comp_session: Option<&IncrCompSession>,
        outputs: &OutputFilenames,
        crate_info: &CrateInfo,
    ) -> (CompiledModules, WorkProductMap);

    /// This is called on the returned [`CompiledModules`] from [`join_codegen`](Self::join_codegen).
    fn link(
        &self,
        sess: &Session,
        compiled_modules: CompiledModules,
        crate_info: CrateInfo,
        metadata: EncodedMetadata,
        outputs: &OutputFilenames,
    ) {
        link_binary(
            sess,
            &ArArchiveBuilderBuilder,
            compiled_modules,
            crate_info,
            metadata,
            outputs,
            self.name(),
        );
    }
}

pub trait ExtraBackendMethods: Send + Sync + DynSend + DynSync {
    type Module;

    fn codegen_allocator<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        module_name: &str,
        methods: &[AllocatorMethod],
    ) -> Self::Module;

    /// This generates the codegen unit and returns it along with
    /// a `u64` giving an estimate of the unit's processing cost.
    fn compile_codegen_unit(
        &self,
        tcx: TyCtxt<'_>,
        cgu_name: Symbol,
        bitcode_needed: bool,
    ) -> (ModuleCodegen<Self::Module>, u64);
}
