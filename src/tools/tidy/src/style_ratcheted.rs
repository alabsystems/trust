//! Trust: the style rules of [`crate::style`], applied to a root that is not
//! clean yet.
//!
//! `crates/` and `targo-trust/` were written entirely outside any mechanical
//! style gate. Turning that gate on as a hard failure would report a backlog
//! that belongs to no current change, and the predictable response to a gate
//! that cannot be got green is to stop running it. So the same rules run, the
//! findings are still printed, and the verdict is a count compared against
//! `src/tools/tidy/trust-style-ratchet.txt`: a rise fails, a fall is what
//! `--bless` records. There is no path that raises the number silently.

use std::path::Path;

use crate::diagnostics::TidyCtx;

pub fn check(root_path: &Path, path: &Path, tidy_ctx: TidyCtx) {
    crate::style::check_ratcheted(root_path, path, tidy_ctx);
}
