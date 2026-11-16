use crate::Config;

/// Returns `true` if the given span is a part of generated files.
pub(super) fn is_generated_file(original_snippet: &str, config: &Config) -> bool {
    has_generated_marker(
        original_snippet,
        config.generated_marker_line_search_limit(),
    )
}

// Trust (T14d): the marker test alone, for the module resolver, which skips
// an `include!`d generated file before any configuration applies to it.
pub(crate) fn has_generated_marker(original_snippet: &str, search_limit: usize) -> bool {
    original_snippet
        .lines()
        // looking for marker only in the beginning of the file
        .take(search_limit)
        .any(|line| line.contains("@generated"))
}
