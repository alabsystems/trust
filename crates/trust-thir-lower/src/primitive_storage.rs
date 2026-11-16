//! Exact source/image admission for owned primitive transport, not arithmetic,
//! aggregate storage, reference-valued slots, or a layout permission.
use rustc_middle::ty::{self, Ty as RustcTy};
use super::Ty;
pub(super) fn image(source: RustcTy<'_>) -> Option<Ty> {
    Some(match source.kind() {
        ty::Bool => Ty::Bool,
        ty::Char => Ty::Char,
        ty::Int(ty::IntTy::I8) => Ty::I8,
        ty::Int(ty::IntTy::I16) => Ty::I16,
        ty::Int(ty::IntTy::I32) => Ty::I32,
        ty::Int(ty::IntTy::I64) => Ty::I64,
        ty::Int(ty::IntTy::I128) => Ty::I128,
        ty::Int(ty::IntTy::Isize) => Ty::Isize,
        ty::Uint(ty::UintTy::U8) => Ty::U8,
        ty::Uint(ty::UintTy::U16) => Ty::U16,
        ty::Uint(ty::UintTy::U32) => Ty::U32,
        ty::Uint(ty::UintTy::U64) => Ty::U64,
        ty::Uint(ty::UintTy::U128) => Ty::U128,
        ty::Uint(ty::UintTy::Usize) => Ty::Usize,
        ty::Float(ty::FloatTy::F32) => Ty::F32,
        ty::Float(ty::FloatTy::F64) => Ty::F64,
        // Only real Rust unit, never a Unit image used for an opaque source.
        ty::Tuple(fields) if fields.is_empty() => Ty::Unit,
        _ => return None,
    })
}
pub(super) fn admits(source: RustcTy<'_>, mapped: &Ty) -> bool {
    image(source).as_ref() == Some(mapped)
}
