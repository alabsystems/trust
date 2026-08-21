//! Reject compiletest expectation markers written into Trust fixture prose.
//!
//! Compiletest searches every source line for its expectation marker. A Trust
//! fixture that spells that marker while explaining an annotation in a `//!` or
//! `///` comment therefore creates another expectation that no diagnostic can
//! satisfy. Keep this check scoped to `tests/ui/trust`: rustdoc and upstream UI
//! tests legitimately attach expectations to documentation comments.

use std::ffi::OsStr;
use std::path::Path;

use crate::diagnostics::{CheckId, TidyCtx};
use crate::walk::{filter_dirs, walk};

const TRUST_UI_SUBDIR: &str = "ui/trust";
const COMPILETEST_MARKER: &str = concat!("//", "~");

/// Whether a line is Rust line-doc prose containing a compiletest expectation
/// marker. Four or more leading slashes form an ordinary comment, not `///`.
fn line_is_doc_comment_with_marker(line: &str) -> bool {
    let trimmed = line.trim_start();
    let is_inner_doc = trimmed.starts_with("//!");
    let is_outer_doc = trimmed.starts_with("///") && !trimmed.starts_with("////");
    (is_inner_doc || is_outer_doc) && line.contains(COMPILETEST_MARKER)
}

fn marker_lines(contents: &str) -> impl Iterator<Item = usize> + '_ {
    contents
        .lines()
        .enumerate()
        .filter_map(|(index, line)| line_is_doc_comment_with_marker(line).then_some(index + 1))
}

pub fn check(tests_path: &Path, tidy_ctx: TidyCtx) {
    // Construct the Trust-owned subtree here instead of relying on the caller
    // to pass a narrow path. Walking all of `tests` would reject legitimate
    // rustdoc fixtures whose diagnostic annotations belong on doc comments.
    let trust_ui_path = tests_path.join(TRUST_UI_SUBDIR);
    let mut check =
        tidy_ctx.start_check(CheckId::new("trust_prose_annotations").path(&trust_ui_path));

    walk(
        &trust_ui_path,
        |path, is_dir| {
            filter_dirs(path)
                || (!is_dir && path.extension().is_none_or(|ext| ext != OsStr::new("rs")))
        },
        &mut |entry, contents| {
            for line in marker_lines(contents) {
                check.error(format!(
                    "{}:{line}: compiletest expectation marker appears in Trust doc-comment \
                     prose; describe the annotation without spelling its raw marker",
                    entry.path().display(),
                ));
            }
        },
    );
}

#[cfg(test)]
mod tests {
    use super::{line_is_doc_comment_with_marker, marker_lines};

    #[test]
    fn rejects_markers_in_inner_and_outer_doc_prose() {
        assert!(line_is_doc_comment_with_marker("//! quote: //~ ERROR message"));
        assert!(line_is_doc_comment_with_marker("  /// quote: //~^ ERROR message"));
        assert!(line_is_doc_comment_with_marker("\t//! quote: //~| HELP message"));
    }

    #[test]
    fn allows_real_annotations_and_non_doc_prose() {
        assert!(!line_is_doc_comment_with_marker("let value = missing; //~ ERROR not found"));
        assert!(!line_is_doc_comment_with_marker("// prose without the raw marker"));
        assert!(!line_is_doc_comment_with_marker("//// ordinary comment //~ ERROR example"));
        assert!(!line_is_doc_comment_with_marker("//! says `tilde annotation`"));
    }

    #[test]
    fn should_fail_directive_does_not_exempt_doc_prose() {
        let contents = "//@ should-fail\n//! prose quotes //~ ERROR\nfn main() {}\n";
        assert_eq!(marker_lines(contents).collect::<Vec<_>>(), vec![2]);
    }
}
