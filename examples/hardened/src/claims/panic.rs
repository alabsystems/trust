use std::fs;
use std::path::Path;

pub(crate) fn panic_boundary(path: &Path, bytes: &[u8]) {
    let _ = fs::metadata(path).expect("fixture intentionally models panic-on-error");
    let _ = String::from_utf8(bytes.to_vec()).unwrap();
    assert!(!bytes.is_empty());
    if path == Path::new("") {
        panic!("empty path is not accepted by this fixture");
    }
    if bytes == b"todo" {
        todo!("fixture intentionally models an unfinished public edge");
    }
    if bytes == b"unreachable" {
        unreachable!("fixture intentionally models an impossible branch");
    }
}
