// RANK 2 (soundness): a monomorphic AssocFn pick inside an inline-const block.
// `const { C.n() }` is a typeck CHILD body sharing the root's TypeckResults, so
// the pick folds into the root's type_dependent_defs — but the checker walks
// only the ROOT body, so `try_resolve` never re-derived it, and the root wrongly
// ACCEPTed with an un-re-derived pick. Expected post-fix: the coverage guard
// (picks_all_in_root_body) sees a pick keyed to a child body and rejects the
// witness; warm replay is a clean MISS, output byte-identical to a no-flag build.
pub struct C;

impl C {
    pub const fn n(&self) -> usize {
        7
    }
}

pub fn f() -> usize {
    const {
        let c = C;
        c.n()
    }
}
