use std::str::FromStr;

/// Represents a codegen backend.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub enum CodegenBackendKind {
    #[default]
    Llvm,
    Cranelift,
    Gcc,
    // Trust: trust-cg verified codegen backend (#829).
    TrustCg,
    // Trust: the trust-ir -> trust-cg self-host backend, built from the
    // `first-party/trust-cg` sibling as a dylib plugin (build_steps/trust_ir_cg.rs).
    TrustIrCg,
    Custom(String),
}

impl CodegenBackendKind {
    /// Name of the codegen backend, as identified in the `compiler` directory
    /// (`rustc_codegen_<name>`).
    pub(crate) fn name(&self) -> &str {
        match self {
            CodegenBackendKind::Llvm => "llvm",
            CodegenBackendKind::Cranelift => "cranelift",
            CodegenBackendKind::Gcc => "gcc",
            // Trust: trust-cg verified codegen backend (#829).
            CodegenBackendKind::TrustCg => "trust-cg",
            // Trust: the trust-ir -> trust-cg self-host backend.
            CodegenBackendKind::TrustIrCg => "trust-ir-cg",
            CodegenBackendKind::Custom(name) => name,
        }
    }

    pub(crate) fn is_llvm(&self) -> bool {
        matches!(self, Self::Llvm)
    }

    // Trust: trust-cg verified codegen backend (#829).
    pub(crate) fn is_trust_cg(&self) -> bool {
        matches!(self, Self::TrustCg)
    }

    // Trust: the trust-ir -> trust-cg self-host backend.
    pub(crate) fn is_trust_ir_cg(&self) -> bool {
        matches!(self, Self::TrustIrCg)
    }

    /// Trust: is this backend LINKED INTO `rustc_driver`, rather than `dlopen`ed
    /// from `<sysroot>/lib/rustlib/<host>/codegen-backends/`?
    ///
    /// This must stay in agreement with `rustc_interface::util::builtin_codegen_backend`,
    /// which is the authority: everything it does not answer for is a plugin that the
    /// sysroot must already carry before the compiler can start at all.
    pub(crate) fn is_linked_into_rustc(&self) -> bool {
        match self {
            Self::Llvm | Self::TrustCg => true,
            Self::TrustIrCg | Self::Cranelift | Self::Gcc | Self::Custom(_) => false,
        }
    }
}

/// FIXME(Zalathar): This is partly redundant with the parsing code in `parse_codegen_backends`.
impl FromStr for CodegenBackendKind {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "" => Err("Invalid empty backend name"),
            "gcc" => Ok(Self::Gcc),
            "llvm" => Ok(Self::Llvm),
            "cranelift" => Ok(Self::Cranelift),
            // Trust: trust-cg verified codegen backend (#829).
            "trust-cg" => Ok(Self::TrustCg),
            // Trust: the trust-ir -> trust-cg self-host backend.
            "trust-ir-cg" => Ok(Self::TrustIrCg),
            _ => Ok(Self::Custom(s.to_string())),
        }
    }
}
