//! Trust: exact registered-struct dependency bounds for zero-length array fields.
//!
//! This is only a dependency bound, never declaration validation. The splice
//! still checks every positional definition and all its fields before admitting
//! any body, then remaps through the existing cycle-checked definition DAG.

use trust_ir::{StructDef, Ty, TyId};

/// The nested-first bound for an exact registered struct before `frontier`.
/// No other table-indexed element is admitted by this additional zero-array lane.
pub(super) fn element_bound(
    types: &[Ty],
    structs: &[StructDef],
    element: TyId,
    frontier: usize,
) -> Option<usize> {
    let Ty::Struct(id) = types.get(element.as_usize())? else { return None };
    let index = id.as_usize();
    let definition = structs.get(index)?;
    if definition.id != *id || index >= frontier {
        return None;
    }
    index.checked_add(1)
}

#[cfg(test)]
#[path = "zero_array_struct/tests.rs"]
mod tests;
