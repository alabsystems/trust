use std::io;
use std::path::Path;

use rustc_macros::Diagnostic;
use rustc_span::{Span, Symbol};
use rustc_structures::CrateType;
use rustc_target::spec::TargetTuple;

#[derive(Diagnostic)]
#[diag(
    "`--crate-name` and `#[crate_name]` are required to match, but `{$crate_name}` != `{$attr_crate_name}`"
)]
pub(crate) struct CrateNameDoesNotMatch {
    #[primary_span]
    pub(crate) span: Span,
    pub(crate) crate_name: Symbol,
    pub(crate) attr_crate_name: Symbol,
}

#[derive(Diagnostic)]
#[diag("crate names cannot start with a `-`, but `{$crate_name}` has a leading hyphen")]
pub(crate) struct CrateNameInvalid<'a> {
    pub(crate) crate_name: &'a str,
}

#[derive(Diagnostic)]
#[diag("Ferris cannot be used as an identifier")]
pub(crate) struct FerrisIdentifier {
    #[primary_span]
    pub spans: Vec<Span>,
    #[suggestion(
        "try using their name instead",
        code = "{ferris_fix}",
        applicability = "maybe-incorrect"
    )]
    pub first_span: Span,
    pub ferris_fix: &'static str,
}

#[derive(Diagnostic)]
#[diag("identifiers cannot contain emoji: `{$ident}`")]
pub(crate) struct EmojiIdentifier {
    #[primary_span]
    pub spans: Vec<Span>,
    pub ident: Symbol,
}

#[derive(Diagnostic)]
#[diag("cannot mix `bin` crate type with others")]
pub(crate) struct MixedBinCrate;

#[derive(Diagnostic)]
#[diag("cannot mix `proc-macro` crate type with others")]
pub(crate) struct MixedProcMacroCrate;

#[derive(Diagnostic)]
#[diag("cannot compile `proc-macro` crate to wasm targets without -Zwasm-proc-macros")]
pub(crate) struct UnstableWasmProcMacro;

#[derive(Diagnostic)]
#[diag("error writing dependencies to `{$path}`: {$error}")]
pub(crate) struct ErrorWritingDependencies<'a> {
    pub path: &'a Path,
    pub error: io::Error,
}

#[derive(Diagnostic)]
#[diag("the input file \"{$path}\" would be overwritten by the generated executable")]
pub(crate) struct InputFileWouldBeOverWritten<'a> {
    pub path: &'a Path,
}

#[derive(Diagnostic)]
#[diag(
    "the generated executable for the input file \"{$input_path}\" conflicts with the existing directory \"{$dir_path}\""
)]
pub(crate) struct GeneratedFileConflictsWithDirectory<'a> {
    pub input_path: &'a Path,
    pub dir_path: &'a Path,
}

#[derive(Diagnostic)]
#[diag("failed to find or create the directory specified by `--temps-dir`")]
pub(crate) struct TempsDirError;

#[derive(Diagnostic)]
#[diag("failed to find or create the directory specified by `--out-dir`")]
pub(crate) struct OutDirError;

#[derive(Diagnostic)]
#[diag("failed to write file {$path}: {$error}")]
pub(crate) struct FailedWritingFile<'a> {
    pub path: &'a Path,
    pub error: io::Error,
}

#[derive(Diagnostic)]
#[diag(
    "building proc macro crate with `panic=abort` or `panic=immediate-abort` may crash the compiler should the proc-macro panic"
)]
pub(crate) struct ProcMacroCratePanicAbort;

#[derive(Diagnostic)]
#[diag("building proc macro crate with sanitizers enabled is not supported")]
pub(crate) struct CannotSanitizeProcMacro;

#[derive(Diagnostic)]
#[diag(
    "due to multiple output types requested, the explicitly specified output file name will be adapted for each output type"
)]
pub(crate) struct MultipleOutputTypesAdaption;

#[derive(Diagnostic)]
#[diag("ignoring -C extra-filename flag due to -o flag")]
pub(crate) struct IgnoringExtraFilename;

#[derive(Diagnostic)]
#[diag("ignoring --out-dir flag due to -o flag")]
pub(crate) struct IgnoringOutDir;

#[derive(Diagnostic)]
#[diag("can't use option `-o` or `--emit` to write multiple output types to stdout")]
pub(crate) struct MultipleOutputTypesToStdout;

#[derive(Diagnostic)]
#[diag(
    "target feature `{$feature}` must be {$enabled} to ensure that the ABI of the current target can be implemented correctly"
)]
pub(crate) struct AbiRequiredTargetFeature<'a> {
    pub feature: &'a str,
    pub enabled: &'a str,
    #[note(
        "this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!"
    )]
    #[note(
        "for more information, see issue #162235 <https://github.com/rust-lang/rust/issues/162235>"
    )]
    pub fcw: bool,
}

#[derive(Diagnostic)]
#[diag("dropping unsupported crate type `{$crate_type}` for codegen backend `{$codegen_backend}`")]
pub(crate) struct UnsupportedCrateTypeForCodegenBackend {
    pub(crate) crate_type: CrateType,
    pub(crate) codegen_backend: &'static str,
}

/// Trust (WS7.10 / F-114): the fail-loud twin of
/// [`UnsupportedCrateTypeForCodegenBackend`], emitted instead of it when the
/// backend's `unsupported_crate_type_is_fatal` hook says that dropping the type
/// would make this compilation exit 0 without the artifact it was asked for.
#[derive(Diagnostic)]
#[diag("codegen backend `{$codegen_backend}` cannot emit crate type `{$crate_type}`")]
#[note(
    "this compilation requests native output, and `{$codegen_backend}` supports only the crate type(s) {$supported}"
)]
#[note(
    "the crate type is refused rather than dropped: dropping it would exit successfully without producing the requested artifact"
)]
pub(crate) struct UnsupportedCrateTypeForCodegenBackendFatal {
    pub(crate) crate_type: CrateType,
    pub(crate) codegen_backend: &'static str,
    pub(crate) supported: String,
}

#[derive(Diagnostic)]
#[diag("dropping unsupported crate type `{$crate_type}` for target `{$target_triple}`")]
pub(crate) struct UnsupportedCrateTypeForTarget<'a> {
    pub(crate) crate_type: CrateType,
    pub(crate) target_triple: &'a TargetTuple,
}
