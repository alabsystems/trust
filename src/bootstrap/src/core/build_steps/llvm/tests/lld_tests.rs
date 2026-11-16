use super::*;

#[test]
fn paired_lld_requires_exports_from_the_selected_llvm_only() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap().join("selected llvm");
    let directory = root.join("lib/cmake/llvm");
    let provider = LlvmOutput {
        llvm_config: root.join("bin/llvm-config"),
        link_shared: false,
        llvm_root_dir: root,
        kind: LlvmKind::External,
    };
    assert!(lld_cmake_inputs(&provider).is_err());
    fs::create_dir_all(&directory).unwrap();
    fs::write(directory.join("LLVMConfig.cmake"), b"selected config").unwrap();
    assert!(lld_cmake_inputs(&provider).is_err());
    fs::write(directory.join("LLVMExports.cmake"), b"selected exports").unwrap();
    assert_eq!(lld_cmake_inputs(&provider).unwrap(), directory);
    fs::remove_file(directory.join("LLVMExports.cmake")).unwrap();
    fs::create_dir(directory.join("LLVMExports.cmake")).unwrap();
    assert_eq!(lld_cmake_inputs(&provider).unwrap_err().kind(), std::io::ErrorKind::InvalidData);
}

#[test]
fn paired_lld_cache_cannot_hide_a_changed_or_ambiguous_provider() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap();
    let selected = root.join("selected provider");
    let other = root.join("another provider");
    fs::create_dir(&selected).unwrap();
    fs::create_dir(&other).unwrap();
    let out = root.join("lld");
    fs::create_dir_all(out.join("build")).unwrap();
    let cache = out.join("build/CMakeCache.txt");
    assert!(!lld_cached_provider(&out, &selected));
    fs::write(&cache, format!("LLVM_DIR:UNINITIALIZED={}\n", selected.display())).unwrap();
    assert!(!lld_cached_provider(&out, &selected), "an untyped same-provider hint is not binding");
    fs::write(&cache, format!("LLVM_DIR:PATH={}\n", selected.display())).unwrap();
    assert!(lld_cached_provider(&out, &selected));
    assert!(!lld_cached_provider(&out, &other));
    fs::write(
        &cache,
        format!("LLVM_DIR:PATH={}\nLLVM_DIR:PATH={}\n", selected.display(), other.display()),
    )
    .unwrap();
    assert!(!lld_cached_provider(&out, &selected));
    fs::write(&cache, "LLVM_CMAKE_DIR:UNINITIALIZED=/unverified/hint\n").unwrap();
    assert!(!lld_cached_provider(&out, &selected));
}
