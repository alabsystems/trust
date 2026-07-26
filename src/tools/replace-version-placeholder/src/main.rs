use std::path::PathBuf;

use tidy::{t, walk};

pub const VERSION_PLACEHOLDER: &str = "CURRENT_RUSTC_VERSION";

fn main() {
    let root_path: PathBuf = std::env::args_os().nth(1).expect("need path to root of repo").into();
    // Trust: the placeholder this expands is CURRENT_RUSTC_VERSION, sitting in
    // `#[stable(since = ...)]` attributes that record the RUST release an item
    // stabilized in. That is Rust's version line, so it expands from
    // `src/rust-compat-version`; Trust's own `major.minor.dev` version in
    // `src/version` would stamp the stdlib with a number from another scheme.
    let version_path = root_path.join("src").join("rust-compat-version");
    let version_str = t!(std::fs::read_to_string(&version_path), version_path);
    let version_str = version_str.trim();
    walk::walk_many(
        &[
            &root_path.join("compiler"),
            &root_path.join("library"),
            &root_path.join("src/doc/rustc"),
            &root_path.join("src/doc/rustdoc"),
            &root_path.join("src/tools/tippy"),
        ],
        |path, _is_dir| filter_dirs(path),
        &mut |entry, contents| {
            if !contents.contains(VERSION_PLACEHOLDER) {
                return;
            }
            let new_contents = contents.replace(VERSION_PLACEHOLDER, version_str);
            let path = entry.path();
            t!(std::fs::write(&path, new_contents), path);
        },
    );
}

fn filter_dirs(path: &std::path::Path) -> bool {
    // tidy would skip some paths that we do want to process
    let allow = ["library/stdarch"];
    walk::filter_dirs(path) && !allow.iter().any(|p| path.ends_with(p))
}
