// Trust: outlined FileSearch API regressions; the parent module is cfg(test).
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use rustc_target::spec::TargetTuple;

use super::*;

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let unique = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let root = env::temp_dir().join(format!(
            "trust-file-search-{}-{unique}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        fs::create_dir(root.join("rustc-dependencies")).unwrap();
        fs::write(root.join("libhashbrown-std.rmeta"), b"public std helper").unwrap();
        fs::write(root.join("rustc-dependencies/libhashbrown-compiler.rmeta"), b"compiler helper")
            .unwrap();
        Self(root)
    }

    fn search(&self, implicit: bool) -> FileSearch {
        let target = Target::expect_builtin(&TargetTuple::from_tuple("aarch64-apple-darwin"));
        let tlib = SearchPath { kind: PathKind::All, dir: self.0.clone().into() };
        FileSearch::new(&[], &tlib, &target, implicit)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn direct_imports_see_std_while_dependencies_see_both_versions() {
    let fixture = Fixture::new();
    let search = fixture.search(true);
    let direct: Vec<_> = search
        .get_library_candidates("libhashbrown-", ".rmeta", PathKind::Crate)
        .map(|(_, path)| path)
        .collect();
    assert_eq!(direct, [fixture.0.join("libhashbrown-std.rmeta")]);
    let dependencies: Vec<_> = search
        .get_library_candidates("libhashbrown-", ".rmeta", PathKind::Dependency)
        .map(|(_, path)| path)
        .collect();
    assert_eq!(
        dependencies,
        [
            fixture.0.join("rustc-dependencies/libhashbrown-compiler.rmeta"),
            fixture.0.join("libhashbrown-std.rmeta"),
        ]
    );
    assert_eq!(search.search_paths(PathKind::Crate).count(), 1);
    assert_eq!(search.search_paths(PathKind::Dependency).count(), 2);
    assert_eq!(search.cli_search_paths(PathKind::All).count(), 0);
}

#[test]
fn disabling_implicit_roots_does_not_expose_private_helpers_as_roots() {
    let fixture = Fixture::new();
    let search = fixture.search(false);
    assert_eq!(
        search.get_library_candidates("libhashbrown-", ".rmeta", PathKind::Crate).count(),
        0
    );
    assert_eq!(search.search_paths(PathKind::Crate).count(), 0);
    assert_eq!(
        search.get_library_candidates("libhashbrown-", ".rmeta", PathKind::Dependency).count(),
        2
    );
    assert_eq!(search.search_paths(PathKind::Native).count(), 1);
}

#[test]
fn absent_dependency_directory_preserves_the_original_search_paths() {
    let fixture = Fixture::new();
    fs::remove_dir_all(fixture.0.join("rustc-dependencies")).unwrap();
    let search = fixture.search(true);
    assert_eq!(search.search_paths(PathKind::All).count(), 1);
    assert_eq!(
        search.get_library_candidates("libhashbrown-", ".rmeta", PathKind::Dependency).count(),
        1
    );
}

// Trust (TG6): the kernel's account of the file the compiler's code is mapped
// from, which names a local kernel fact's compiler identity.
#[test]
fn proc_maps_names_the_file_mapped_at_an_address() {
    let maps = "\
55d0c0a00000-55d0c0a21000 r--p 00000000 103:02 1311                      /usr/bin/rustc
7f1c00000000-7f1c00400000 r-xp 00012000 fd:01 98765                      /opt/sys root/lib/librustc_driver-1.so
7f1c00400000-7f1c00500000 rw-p 00000000 00:00 0
";
    assert_eq!(proc_maps_file(maps, 0x7f1c0000_1234), Some((0xfd, 0x01, 98765)));
    assert_eq!(proc_maps_file(maps, 0x55d0c0a00000), Some((0x103, 0x02, 1311)));
    // NEGATIVE CONTROLS: an anonymous mapping, an end bound, and no mapping.
    assert_eq!(proc_maps_file(maps, 0x7f1c0040_0010), None);
    assert_eq!(proc_maps_file(maps, 0x55d0c0a21000), None);
    assert_eq!(proc_maps_file(maps, 0x10), None);
}

#[cfg(any(target_os = "macos", target_os = "linux", target_os = "android"))]
#[test]
fn the_compiler_mapping_is_the_file_its_path_names() {
    use std::os::unix::fs::MetadataExt;
    let (path, mapped) = current_dll_mapping().unwrap();
    let metadata = fs::metadata(&path).unwrap();
    assert_eq!(MappedFile { device: metadata.dev(), inode: metadata.ino() }, mapped);
}
