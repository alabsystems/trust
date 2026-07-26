use std::path::Path;

pub(crate) fn discarded_error_boundary(path: &Path) {
    let _ = std::fs::remove_file(path);
    std::fs::canonicalize(path).ok();
    let _bytes = std::fs::read(path).unwrap_or_default();
}
