//! Preserve the existing Clean folder's changed child Arcs in the untrusted
//! constant-only advice maps. No expression schema or reduction is added.

use std::collections::HashMap;
use std::sync::Arc;

use clean_kernel::{Expr, ExprFolderOpt};

#[derive(Default)]
pub(super) struct Memo {
    // Retain every input Arc as well as its result: no input address can be
    // recycled while this fixed-map folder still has a corresponding entry.
    children: HashMap<usize, (Arc<Expr>, Option<Arc<Expr>>)>,
}

/// Only the two fixed, context-independent Const mappings implement this.
/// Neither observes binder depth; FVar abstraction remains Clean's existing
/// separately scoped operation after the entire transport is complete.
pub(super) trait SharedConstFolder: ExprFolderOpt {
    fn child_memo(&mut self) -> &mut Memo;

    fn fold_shared(&mut self, input: &Arc<Expr>) -> Option<Arc<Expr>> {
        let key = Arc::as_ptr(input) as usize;
        if let Some((_, result)) = self.child_memo().children.get(&key) {
            return result.clone();
        }
        // Use the existing default dispatch and work charge on each miss.
        let result = self.fold_expr_opt(input).map(Arc::new);
        self.child_memo().children.insert(key, (input.clone(), result.clone()));
        result
    }
}
