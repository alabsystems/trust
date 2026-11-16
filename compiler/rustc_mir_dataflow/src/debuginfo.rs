use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::*;

/// Return the set of locals that appear in debuginfo.
pub fn debuginfo_locals(body: &Body<'_>) -> DenseBitSet<Local> {
    let mut locals = DenseBitSet::new_empty(body.local_decls.len());
    for debuginfo in body.var_debug_info.iter() {
        if let VarDebugInfoContents::Place(place) = debuginfo.value {
            locals.insert(place.local);
            for elem in place.projection {
                if let ProjectionElem::Index(local) = elem {
                    locals.insert(local);
                }
            }
        }
    }
    locals
}
