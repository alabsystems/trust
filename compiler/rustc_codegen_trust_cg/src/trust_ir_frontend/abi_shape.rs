//! Trust (step 2 increment 5, sub-steps 5.4.2 and 5.4.3): rustc's `FnAbi` for one instance,
//! read ONCE into plain data — the `AbiShape` that `codegen_module.rs` legalizes and places.
//!
//! # Why a separate, plain-data shape
//!
//! `codegen_module.rs` is PURE (no `TyCtxt`, no `Session`) so that every rule it applies is a
//! unit test (`codegen_module/tests.rs`), and it is frozen at 5.4.4 (INC5.4-FREEZE). It still
//! has to read rustc's own ABI decision for every definition and every callee: the placement
//! table P the call-event gate binds producer IR to machine registers through is read from
//! rustc's `FnAbi`, never from trust-cg's classifier (design §3.1 rule 10), and so is the
//! legalization rule 9 performs (design §3.1 rule 9: "the same lowering rustc_codegen_llvm
//! performs"). This file is the one place that crosses that boundary: it asks rustc, after the
//! SAME preconditions the old lane checks (`fn_abi_preconditions` in the crate root, extracted
//! verbatim), and records each slot's pass mode, scalar width and kind, extension and `InReg`
//! bit, plus whether the slot is one the old F1 lane's audited predicates admit (`audited`,
//! `newtype`), and, for a `Pair`, which value the two halves are halves of (`PairOf`).
//!
//! NOT FROZEN (an unfrozen residual of `codegen_module.rs`, listed in
//! `scripts/frozen-files.txt` at 5.4.4). Weakening it is caught by the run-make fixtures that
//! execute compiler-lane output against LLVM's (`trust-cg-f1-abi-legalization`), by
//! `codegen_module.rs`'s own cross-checks (a `Pair`'s halves against the producer's recorded
//! field offsets and lane types), by `trust_ir_build::validate_module` over the legalized
//! module, and by the call-event gate, which checks P against the producer's signature
//! independently (`check_fixed_placement`).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_abi::{BackendRepr, CanonAbi, FieldsShape, Primitive};
use rustc_middle::mir;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_target::callconv::{ArgAbi, ArgAttribute, ArgAttributes, ArgExtension, PassMode};

/// The calling convention of an audited instance. `fn_abi_preconditions` admits only these two.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AbiConv {
    /// `extern "Rust"`.
    Rust,
    /// `extern "C"` (non-unwinding).
    C,
}

/// The kind of one scalar slot, read from rustc's layout (`BackendRepr::Scalar`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScalarKind {
    /// An integer (`bool`, `char` and a fieldless enum's tag are integers to rustc).
    Int {
        /// rustc's signedness of the integer.
        signed: bool,
    },
    /// A pointer.
    Pointer,
    /// A floating-point value.
    Float,
    /// A `Direct` slot whose layout is not one scalar.
    Other,
}

/// The extension contract rustc attaches to a slot (`ArgAttributes::arg_ext`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AbiExtension {
    /// None.
    None,
    /// Zero-extended by the writer.
    Zext,
    /// Sign-extended by the writer.
    Sext,
}

/// One scalar half of a `Pair`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ScalarShape {
    /// The scalar's size in bits.
    pub(crate) bits: u32,
    /// Its kind.
    pub(crate) kind: ScalarKind,
    /// Its extension contract.
    pub(crate) ext: AbiExtension,
    /// Whether rustc marked it `InReg`.
    pub(crate) inreg: bool,
}

/// What a `Pair`'s two scalars are the halves of (5.4.3), read from rustc's type and layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PairOf {
    /// A struct or tuple of exactly two fields, one per half. `fields[k]` is the DECLARATION
    /// index of the field half `k` carries. Half 0 is the field at offset 0: rustc's
    /// `ScalarPair`, and so the two argument registers, follow the LAYOUT order, which a
    /// `repr(Rust)` reordering can make the reverse of the declaration order.
    Fields([u32; 2]),
    /// A slice reference: half 0 is the data pointer, half 1 the length.
    SliceRef,
    /// An enum riding `(tag, payload)`.
    Enum,
    /// Anything else rustc passes as a pair (`&str`, a trait object, a niched pair, ...).
    Other,
}

/// One argument (or the result) as rustc passes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ArgShape {
    /// `PassMode::Ignore`: not passed (a zero-sized argument, a unit or never result).
    Ignore,
    /// `PassMode::Direct`: one scalar.
    Direct {
        /// The layout's size in bits.
        bits: u32,
        /// The scalar's kind.
        kind: ScalarKind,
        /// The extension contract.
        ext: AbiExtension,
        /// `InReg`.
        inreg: bool,
        /// Trust: whether actual physical register transport is supported. This
        /// is the legacy scalar predicate or the source-owned thin-pointer
        /// contract; a result additionally accepts the existing bool extension.
        /// It carries no pointee/provenance/NoUB or proof permission.
        audited: bool,
        /// Whether the slot is a single-field struct passed as that field's scalar
        /// (`direct_newtype_struct_arg_abi_supported`) whose one field is an integer, a `char`
        /// or a thin shared reference — the newtype 5.4.3 legalizes.
        newtype: bool,
    },
    /// `PassMode::Pair`: two scalars.
    Pair {
        /// The scalar at offset 0.
        first: ScalarShape,
        /// The other scalar.
        second: ScalarShape,
        /// What they are the halves of.
        of: PairOf,
        /// Whether the old F1 lane's predicate for that value admits the slot
        /// (`slice_ref_arg_abi_supported`, `pair_struct_arg_abi_supported` or the tuple twin
        /// below, `pair_enum_abi_supported`): plain attributes, a genuine `ScalarPair`, at most
        /// 16 bytes, and for a reference a SHARED one.
        audited: bool,
    },
    /// `PassMode::Indirect`: through a pointer (`on_stack` is by-value stack copy).
    Indirect {
        /// rustc's `on_stack`.
        on_stack: bool,
        /// Whether the pointer carries metadata (an unsized value).
        has_meta: bool,
        /// Whether the slot is a by-value struct the old F1 lane's predicate admits
        /// (`indirect_by_value_struct_arg_abi_supported`: plain attributes, no metadata, not on
        /// the stack, over 16 bytes). For the result this is the `sret` 5.4.3 legalizes.
        audited: bool,
    },
    /// `PassMode::Cast`.
    Cast,
}

/// rustc's `FnAbi` for one instance, as plain data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AbiShape {
    /// The calling convention.
    pub(crate) conv: AbiConv,
    /// One shape per argument, in order.
    pub(crate) params: Vec<ArgShape>,
    /// The result's shape.
    pub(crate) ret: ArgShape,
}

fn extension(ext: ArgExtension) -> AbiExtension {
    match ext {
        ArgExtension::None => AbiExtension::None,
        ArgExtension::Zext => AbiExtension::Zext,
        ArgExtension::Sext => AbiExtension::Sext,
    }
}

fn scalar_kind(primitive: Primitive) -> ScalarKind {
    match primitive {
        Primitive::Int(_, signed) => ScalarKind::Int { signed },
        Primitive::Pointer(_) => ScalarKind::Pointer,
        Primitive::Float(_) => ScalarKind::Float,
    }
}

fn bits_u32(bits: u64) -> u32 {
    u32::try_from(bits).unwrap_or(u32::MAX)
}

fn plain(attrs: &ArgAttributes) -> bool {
    !attrs.contains(ArgAttribute::InReg) && attrs.arg_ext == ArgExtension::None
}

/// A by-value TUPLE of exactly two fields riding `PassMode::Pair` — the tuple twin of the crate
/// root's `pair_struct_arg_abi_supported` (which admits only an ADT struct): plain attributes on
/// both halves, a genuine `ScalarPair`, at most 16 bytes.
fn pair_tuple_arg_abi_supported<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    let ty::Tuple(fields) = arg.layout.ty.kind() else {
        return false;
    };
    let PassMode::Pair(a, b) = &arg.mode else {
        return false;
    };
    fields.len() == 2
        && plain(a)
        && plain(b)
        && matches!(arg.layout.backend_repr, BackendRepr::ScalarPair { .. })
        && arg.layout.size.bytes() <= 16
}

/// Which value a `Pair` slot's two halves are halves of (see [`PairOf`]).
fn pair_of<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> PairOf {
    match arg.layout.ty.kind() {
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) if matches!(inner.kind(), ty::Slice(_)) => {
            PairOf::SliceRef
        }
        ty::Adt(adt, _) if adt.is_enum() => PairOf::Enum,
        ty::Adt(adt, _) if adt.is_struct() => two_field_halves(arg),
        ty::Tuple(_) => two_field_halves(arg),
        _ => PairOf::Other,
    }
}

/// The declaration index of the field each half carries, from rustc's own field offsets: the
/// field at offset 0 is half 0, the other half 1. Anything but two fields at distinct offsets,
/// one of them 0, is `Other`.
fn two_field_halves<'tcx>(arg: &ArgAbi<'tcx, Ty<'tcx>>) -> PairOf {
    let FieldsShape::Arbitrary { .. } = &arg.layout.fields else {
        return PairOf::Other;
    };
    if arg.layout.fields.count() != 2 {
        return PairOf::Other;
    }
    let (o0, o1) = (arg.layout.fields.offset(0), arg.layout.fields.offset(1));
    match (o0.bytes(), o1.bytes()) {
        (0, b) if b != 0 => PairOf::Fields([0, 1]),
        (a, 0) if a != 0 => PairOf::Fields([1, 0]),
        _ => PairOf::Other,
    }
}

/// A single-field struct passed `Direct` as its field's scalar, whose field is an integer, a
/// `char` or a thin SHARED reference (never `&mut T`, a raw pointer, a float or `bool`).
fn audited_newtype<'tcx>(tcx: TyCtxt<'tcx>, arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    if !crate::direct_newtype_struct_arg_abi_supported(arg) {
        return false;
    }
    let ty::Adt(adt, args) = arg.layout.ty.kind() else {
        return false;
    };
    let fields = &adt.non_enum_variant().fields;
    if fields.len() != 1 {
        return false;
    }
    let Some(field) = fields.iter().next() else {
        return false;
    };
    let bits = arg.layout.size.bits();
    if bits == 0 || bits > 64 {
        return false;
    }
    // Not normalized: a field whose type is still an alias (`<T as Tr>::Assoc`) is not one of the
    // kinds below, so it is refused, never guessed.
    match field.ty(tcx, *args).skip_normalization().kind() {
        ty::Int(_) | ty::Uint(_) | ty::Char => true,
        ty::Ref(_, _, mir::Mutability::Not) => bits == 64,
        _ => false,
    }
}

/// The shape of one slot. `audited` is computed by the caller, which knows the position.
fn arg_shape<'tcx>(tcx: TyCtxt<'tcx>, arg: &ArgAbi<'tcx, Ty<'tcx>>, audited: bool) -> ArgShape {
    match &arg.mode {
        PassMode::Ignore => ArgShape::Ignore,
        PassMode::Direct(attrs) => ArgShape::Direct {
            bits: bits_u32(arg.layout.size.bits()),
            kind: match arg.layout.backend_repr {
                BackendRepr::Scalar(scalar) => scalar_kind(scalar.primitive()),
                _ => ScalarKind::Other,
            },
            ext: extension(attrs.arg_ext),
            inreg: attrs.contains(ArgAttribute::InReg),
            audited,
            newtype: audited_newtype(tcx, arg),
        },
        PassMode::Pair(a, b) => {
            let (first, second) = match arg.layout.backend_repr {
                BackendRepr::ScalarPair { a: x, b: y, .. } => (
                    (bits_u32(x.size(&tcx).bits()), scalar_kind(x.primitive())),
                    (bits_u32(y.size(&tcx).bits()), scalar_kind(y.primitive())),
                ),
                _ => ((0, ScalarKind::Other), (0, ScalarKind::Other)),
            };
            let of = pair_of(arg);
            let audited = match (of, arg.layout.ty.kind()) {
                (PairOf::SliceRef, _) => crate::slice_ref_arg_abi_supported(arg),
                (PairOf::Fields(_), ty::Tuple(_)) => pair_tuple_arg_abi_supported(arg),
                (PairOf::Fields(_), _) => crate::pair_struct_arg_abi_supported(arg),
                (PairOf::Enum, _) => crate::pair_enum_abi_supported(arg),
                (PairOf::Other, _) => false,
            };
            ArgShape::Pair {
                first: ScalarShape {
                    bits: first.0,
                    kind: first.1,
                    ext: extension(a.arg_ext),
                    inreg: a.contains(ArgAttribute::InReg),
                },
                second: ScalarShape {
                    bits: second.0,
                    kind: second.1,
                    ext: extension(b.arg_ext),
                    inreg: b.contains(ArgAttribute::InReg),
                },
                of,
                audited,
            }
        }
        PassMode::Indirect { mode, .. } => ArgShape::Indirect {
            on_stack: matches!(mode, rustc_target::callconv::IndirectMode::OnStack),
            has_meta: false,
            audited: crate::indirect_by_value_struct_arg_abi_supported(arg),
        },
        PassMode::IndirectUnsized { .. } => ArgShape::Indirect {
            on_stack: false,
            has_meta: true,
            audited: crate::indirect_by_value_struct_arg_abi_supported(arg),
        },
        PassMode::Cast { .. } => ArgShape::Cast,
    }
}

// Trust: physical transport and the old MIR proof fragment are distinct.
// Keep the legacy predicate unchanged, and add only the source-owned native
// pointer contract; the pure legalizer still checks its actual width/kind/attrs.
fn direct_register_abi_supported<'tcx>(tcx: TyCtxt<'tcx>, arg: &ArgAbi<'tcx, Ty<'tcx>>) -> bool {
    crate::scalar_register_abi_ty_supported(arg, crate::EnumAbi::Admit)
        || crate::source_abi::direct_thin_pointer_transport_supported(tcx, arg)
}

/// rustc's `FnAbi` for `instance`, after the old lane's preconditions (`fn_abi_preconditions`:
/// codegen attributes, the audited Rust/C convention, convention drift, no variadic or
/// implicit argument, no unwinding, and `ir_param_count` arguments). The precondition's message
/// is returned unchanged on refusal, so a refusal reads the same on both lanes.
///
/// The compiler lane imposes NO register cap here: P gives a function with an argument past
/// the register file no entry, so the call-event gate grades it Unknown (design §5 O5).
pub(crate) fn abi_shape_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    ir_param_count: usize,
) -> Result<AbiShape, String> {
    let fn_abi = crate::fn_abi_preconditions(tcx, instance, ir_param_count)?;
    let conv = match fn_abi.conv {
        CanonAbi::Rust => AbiConv::Rust,
        CanonAbi::C => AbiConv::C,
        other => {
            return Err(format!(
                "calling convention `{other}` is not in the audited Rust/C ABI lane"
            ));
        }
    };
    let params = fn_abi
        .args
        .iter()
        .map(|arg| {
            arg_shape(tcx, arg, direct_register_abi_supported(tcx, arg))
        })
        .collect();
    let ret_audited = direct_register_abi_supported(tcx, &fn_abi.ret)
        || crate::zext_bool_return_abi_supported(&fn_abi.ret);
    let ret = arg_shape(tcx, &fn_abi.ret, ret_audited);
    Ok(AbiShape { conv, params, ret })
}
