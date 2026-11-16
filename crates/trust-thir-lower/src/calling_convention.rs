//! Exact source calling conventions for the direct THIR producer.
//!
//! A source ABI is not a Rust/C bit. Target canonicalization resolves aliases (notably
//! `system`), but erases unwind and rust-call's tuple adaptation. Keep the original typed
//! ABI alongside the emitted convention. A missing/unsupported mapping is a refusal, never C.
use rustc_abi::{ArmCall, CanonAbi, ExternAbi, X86Call};
use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use trust_ir::CallingConv;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdaptedAbi {
    Constructor,
    Closure,
    Coroutine,
    Clean,
    Initializer,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbiSource {
    Declared { abi: ExternAbi, c_variadic: bool },
    /// Compiler-owned signatures whose environment/tuple convention the producer adapts.
    Adapted(AdaptedAbi),
    Unknown,
    Conflict,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FunctionAbi {
    source: AbiSource,
    convention: Option<CallingConv>,
    canonical: Option<CanonAbi>,
}

impl FunctionAbi {
    pub const RUST: Self = Self {
        source: AbiSource::Declared { abi: ExternAbi::Rust, c_variadic: false },
        convention: Some(CallingConv::Rust),
        canonical: Some(CanonAbi::Rust),
    };
    pub const C: Self = Self {
        source: AbiSource::Declared { abi: ExternAbi::C { unwind: false }, c_variadic: false },
        convention: Some(CallingConv::C),
        canonical: Some(CanonAbi::C),
    };
    pub const UNKNOWN: Self = Self { source: AbiSource::Unknown, convention: None, canonical: None };
    pub const CONFLICT: Self = Self { source: AbiSource::Conflict, convention: None, canonical: None };

    pub fn adapted(kind: AdaptedAbi) -> Self {
        Self { source: AbiSource::Adapted(kind), convention: Some(CallingConv::Rust), canonical: Some(CanonAbi::Rust) }
    }

    pub fn declared(tcx: TyCtxt<'_>, abi: ExternAbi, c_variadic: bool) -> Self {
        let canonical = rustc_target::callconv::AbiMap::from_target(&tcx.sess.target)
            .canonize_abi(abi, c_variadic)
            .into_option();
        Self::from_mapping(abi, c_variadic, canonical)
    }

    fn from_mapping(abi: ExternAbi, c_variadic: bool, canonical: Option<CanonAbi>) -> Self {
        // These source ABIs have semantics beyond the canonical directive. In particular
        // `rust-call` flattens a final tuple; LLVM intrinsics are not ordinary C calls.
        let supported_source = matches!(abi,
            ExternAbi::Rust | ExternAbi::RustCold | ExternAbi::C { .. }
            | ExternAbi::System { .. } | ExternAbi::Cdecl { .. } | ExternAbi::Stdcall { .. }
            | ExternAbi::Fastcall { .. } | ExternAbi::Thiscall { .. } | ExternAbi::Vectorcall { .. }
            | ExternAbi::SysV64 { .. } | ExternAbi::Win64 { .. } | ExternAbi::Aapcs { .. }
            | ExternAbi::EfiApi | ExternAbi::Swift
        );
        let unwind = match abi {
            ExternAbi::C { unwind } | ExternAbi::System { unwind }
            | ExternAbi::Cdecl { unwind } | ExternAbi::Stdcall { unwind }
            | ExternAbi::Fastcall { unwind } | ExternAbi::Thiscall { unwind }
            | ExternAbi::Vectorcall { unwind } | ExternAbi::SysV64 { unwind }
            | ExternAbi::Win64 { unwind } | ExternAbi::Aapcs { unwind } => unwind,
            _ => false,
        };
        let convention = if !supported_source { None } else { canonical.and_then(|canonical| {
            // IR406 records C-unwind explicitly without granting modeled unwind semantics.
            // No other unwind-enabled foreign convention has an IR representation.
            if unwind {
                return (canonical == CanonAbi::C).then_some(CallingConv::CUnwind);
            }
            // Preserve named source protocols when IR406 has their exact spelling. Their
            // target-specific canonical directive is retained separately (e.g. EFI and the
            // Windows rust-cold alias); an IR consumer still owes its own ABI support/refusal.
            if abi == ExternAbi::EfiApi { return Some(CallingConv::EfiApi); }
            if abi == ExternAbi::RustCold { return Some(CallingConv::RustCold); }
            Some(match canonical {
                CanonAbi::C => CallingConv::C,
                CanonAbi::Rust => CallingConv::Rust,
                CanonAbi::RustCold => CallingConv::RustCold,
                CanonAbi::Swift => CallingConv::Swift,
                CanonAbi::Arm(ArmCall::Aapcs) => CallingConv::Aapcs,
                CanonAbi::X86(X86Call::SysV64) => CallingConv::SysV64,
                CanonAbi::X86(X86Call::Win64) => CallingConv::Win64,
                CanonAbi::X86(X86Call::Vectorcall) => CallingConv::VectorCall,
                // No invented fallback for stdcall/fastcall/thiscall, interrupts,
                // CMSE, GPU, custom or the other Rust-specific adaptation protocols.
                _ => return None,
            })
        }) };
        Self { source: AbiSource::Declared { abi, c_variadic }, convention, canonical }
    }

    pub fn of_definition(tcx: TyCtxt<'_>, def: DefId) -> Self {
        // Clean's registry owns an installed Rust signature; its generated item has no HIR
        // header. This is positive compiler-owned evidence, not `None => Rust`.
        if def.as_local().is_some_and(|local| tcx.resolutions(()).clean_origin_defs
            .iter().any(|&(clean_def, _, _)| clean_def == local)) {
            return Self::adapted(AdaptedAbi::Clean);
        }
        match tcx.def_kind(def) {
            DefKind::Ctor(..) => Self::adapted(AdaptedAbi::Constructor),
            DefKind::Closure => Self::adapted(AdaptedAbi::Closure),
            DefKind::SyntheticCoroutineBody => Self::adapted(AdaptedAbi::Coroutine),
            DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::AnonConst
            | DefKind::Static { .. } => Self::adapted(AdaptedAbi::Initializer),
            DefKind::Fn | DefKind::AssocFn => {
                if let Some(local) = def.as_local() {
                    // This runs inside mir_built. Read only already-lowered HIR here: a
                    // signature type query can demand types/consts and re-enter that query.
                    // ForeignItem's own header is Extern::None; its owning extern BLOCK
                    // supplies the real ABI, while the item's declaration owns variadicity.
                    let node = tcx.hir_node_by_def_id(local);
                    let Some(sig) = node.fn_sig() else { return Self::UNKNOWN; };
                    let abi = if tcx.is_foreign_item(def) {
                        tcx.hir_get_foreign_abi(tcx.local_def_id_to_hir_id(local))
                    } else { sig.header.abi };
                    Self::declared(tcx, abi, sig.decl.c_variadic())
                } else {
                    // Cross-crate signatures are loaded metadata and cannot demand a local body.
                    let sig = tcx.fn_sig(def).skip_binder().skip_binder();
                    Self::declared(tcx, sig.abi(), sig.c_variadic())
                }
            }
            _ => Self::UNKNOWN,
        }
    }

    #[cfg(test)]
    pub(crate) fn test_only(abi: ExternAbi, canonical: Option<CanonAbi>) -> Self {
        Self::from_mapping(abi, false, canonical)
    }

    #[cfg(test)]
    pub(crate) fn test_only_variadic(abi: ExternAbi, canonical: Option<CanonAbi>) -> Self {
        Self::from_mapping(abi, true, canonical)
    }

    pub fn source(self) -> AbiSource { self.source }
    pub fn calling_conv(self) -> Result<CallingConv, &'static str> {
        self.convention.ok_or("unsupported, absent or conflicting source calling convention")
    }
    /// The old unknown-signature Rust refusal must survive for every Rust convention.
    pub fn is_rust_convention(self) -> bool {
        matches!(self.convention, Some(CallingConv::Rust | CallingConv::RustCold))
    }
    /// Match the selected IR validator's bodyless-declaration layout boundary exactly.
    /// RustCold still carries the Rust unknown-signature refusal above, but only Rust
    /// is exempt from `is_foreign_abi_boundary`'s repr(Rust)-by-value checks. Keeping
    /// these questions separate prevents a signed RustCold declaration from turning a
    /// per-body unsupported call into a whole-module validation error.
    pub fn needs_foreign_layout_check(self) -> bool {
        self.convention != Some(CallingConv::Rust)
    }
    /// Clean/template joins admit only the existing plain-Rust protocol.
    pub fn is_plain_rust(self) -> bool {
        self.convention == Some(CallingConv::Rust) && matches!(self.source,
            AbiSource::Declared { abi: ExternAbi::Rust, c_variadic: false } | AbiSource::Adapted(_))
    }
    pub fn fn_pointer_conv(self) -> Option<CallingConv> {
        match self.source {
            // Preserve the existing fn-pointer signature boundary. FuncTy's optional ABI
            // record is a complete physical signature claim, not a free convention label;
            // this source-only producer does not invent it to widen indirect-call support.
            AbiSource::Declared { abi: ExternAbi::Rust | ExternAbi::C { unwind: false }, c_variadic: false }
                => self.convention,
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn target_mapping_preserves_distinct_conventions_and_source_aliases() {
        for (source, canonical, expected) in [
            (ExternAbi::Rust, CanonAbi::Rust, CallingConv::Rust),
            (ExternAbi::C { unwind: false }, CanonAbi::C, CallingConv::C),
            (ExternAbi::System { unwind: false }, CanonAbi::X86(X86Call::Win64), CallingConv::Win64),
            (ExternAbi::SysV64 { unwind: false }, CanonAbi::X86(X86Call::SysV64), CallingConv::SysV64),
            (ExternAbi::Win64 { unwind: false }, CanonAbi::X86(X86Call::Win64), CallingConv::Win64),
            (ExternAbi::Aapcs { unwind: false }, CanonAbi::Arm(ArmCall::Aapcs), CallingConv::Aapcs),
            (ExternAbi::EfiApi, CanonAbi::X86(X86Call::Win64), CallingConv::EfiApi),
            (ExternAbi::RustCold, CanonAbi::Rust, CallingConv::RustCold),
            (ExternAbi::Vectorcall { unwind: false }, CanonAbi::X86(X86Call::Vectorcall), CallingConv::VectorCall),
            (ExternAbi::RustCold, CanonAbi::RustCold, CallingConv::RustCold),
            (ExternAbi::Swift, CanonAbi::Swift, CallingConv::Swift),
        ] {
            let observed = FunctionAbi::from_mapping(source, false, Some(canonical));
            assert_eq!(observed.calling_conv(), Ok(expected));
            assert_eq!(observed.needs_foreign_layout_check(), expected != CallingConv::Rust);
            if expected == CallingConv::RustCold {
                assert!(observed.is_rust_convention(), "unknown signatures still refuse");
                assert!(observed.needs_foreign_layout_check(), "signed layouts match IR boundary");
            }
            assert_eq!(observed.source(), AbiSource::Declared { abi: source, c_variadic: false });
            let indirect = matches!(source, ExternAbi::Rust | ExternAbi::C { unwind: false });
            assert_eq!(observed.fn_pointer_conv(), indirect.then_some(expected));
        }
        assert_ne!(FunctionAbi::from_mapping(ExternAbi::System { unwind: false }, false, Some(CanonAbi::C)), FunctionAbi::C);
    }

    #[test]
    fn unwind_tuple_adaptation_and_unrepresentable_abis_never_fall_back() {
        assert_eq!(FunctionAbi::from_mapping(ExternAbi::C { unwind: true }, false, Some(CanonAbi::C)).calling_conv(), Ok(CallingConv::CUnwind));
        assert_eq!(FunctionAbi::from_mapping(ExternAbi::System { unwind: true }, false, Some(CanonAbi::C)).calling_conv(), Ok(CallingConv::CUnwind));
        for (source, canonical) in [
            (ExternAbi::RustCall, Some(CanonAbi::Rust)),
            (ExternAbi::LlvmIntrinsic, Some(CanonAbi::C)),
            (ExternAbi::Stdcall { unwind: false }, Some(CanonAbi::X86(X86Call::Stdcall))),
            (ExternAbi::SysV64 { unwind: true }, Some(CanonAbi::X86(X86Call::SysV64))),
            (ExternAbi::Swift, None),
        ] {
            let observed = FunctionAbi::from_mapping(source, false, canonical);
            assert!(observed.calling_conv().is_err(), "{source:?}");
            assert_eq!(observed.fn_pointer_conv(), None);
        }
        for source in [ExternAbi::RustInvalid, ExternAbi::Custom, ExternAbi::GpuKernel,
            ExternAbi::PtxKernel, ExternAbi::RustPreserveNone, ExternAbi::RustTail] {
            assert!(FunctionAbi::from_mapping(source, false, Some(CanonAbi::C)).calling_conv().is_err(),
                "a canonical C directive cannot authorize an unsupported source protocol: {source:?}");
        }
        assert!(FunctionAbi::UNKNOWN.calling_conv().is_err());
        assert!(FunctionAbi::CONFLICT.calling_conv().is_err());
        assert_eq!(FunctionAbi::adapted(AdaptedAbi::Closure).calling_conv(), Ok(CallingConv::Rust));
        assert_eq!(FunctionAbi::from_mapping(ExternAbi::C { unwind: false }, true, Some(CanonAbi::C)).fn_pointer_conv(), None);
    }
}
