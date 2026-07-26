use std::ffi::OsStr;
use std::path::Path;

mod claims;

#[allow(dead_code)]
extern "C" {
    fn getenv(name: *const std::os::raw::c_char) -> *mut std::os::raw::c_char;
}

fn main() {
    let path = Path::new("target/hardened-fixture.tmp");
    let replacement = Path::new("target/hardened-fixture.renamed");
    let dir = Path::new("target/hardened-fixture-dir");
    let _ = claims::paths::raw_path_toctou_boundary(path, replacement);
    let _ = claims::paths::path_identity_boundary(path);
    let _ = claims::permissions::permission_create_boundary(dir);
    let _ = claims::permissions::permission_window_boundary(path);
    let _ = claims::bytes::byte_exact_boundary(path, b"fixture");
    claims::panic::panic_boundary(path, b"fixture");
    claims::errors::discarded_error_boundary(path);
    let _ = claims::compatibility::compatibility_observable_boundary();
    let _ = claims::process::process_signal_semantics_boundary();
    claims::trust_domain::trust_domain_ordering_boundary(
        OsStr::new("/"),
        OsStr::new("root"),
        OsStr::new("wheel"),
        OsStr::new("plugin"),
    );
    claims::unsafe_ffi::unsafe_ffi_boundary();
}
