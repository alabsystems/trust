//@ check-pass
//@ proc-macro: qualified-path-one-span.rs

// Trust: regression test. `unused_qualifications` computed its removal span as
// `path[0].ident.span.until(seg.ident.span)`, which is EMPTY when a path's
// segments all share one span. A suggestion on an empty span trips
//   "Span ... must not be empty and have no suggestion"
// in rustc_errors, aborting the compiler rather than emitting a lint.
//
// Found via clean's kernel_lint_ratchet: `--force-warn unused_qualifications` on
// clean-kernel ICEd on `Const(Name, #[serde(with = "...")] LevelVec)`, where
// serde_derive rebuilds the path from a string literal and every segment inherits
// that literal's span. The ratchet had been scoring the aborted build as ZERO
// warnings — its best possible score — so nothing reported it.
//
// The lint must simply not fire when it has no text to remove.

#![forbid(unused_qualifications)]

extern crate qualified_path_one_span;

pub mod inner {
    pub fn helper() -> u32 {
        1
    }
}

use inner::helper;

pub fn exercised() -> u32 {
    // Expands to `inner::helper()` with one span — the caller's `anchor`
    // token — across every segment, so it is NOT `from_expansion()`.
    qualified_path_one_span::call_via_one_span_path!(anchor) + helper()
}

fn main() {
    let _ = exercised();
}
