//! Primitive IEEE values can occupy the same owned slots used by integer locals.
//! This is a memory transport decision, never an integer arithmetic permission.

use super::Ty;

pub(super) fn admits(ty: &Ty) -> bool {
    matches!(ty, Ty::F32 | Ty::F64)
}
