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
