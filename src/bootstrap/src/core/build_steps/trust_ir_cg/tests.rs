use super::*;

#[test]
fn sysroot_dylib_name_matches_rustc_interface_lookup() {
    // `find_codegen_backend_in_sysroot` accepts
    // `rustc_codegen_<backend>-<CFG_RELEASE>` between the platform prefix
    // and suffix, with the backend name verbatim (hyphens kept).
    let name = sysroot_dylib_name("1.99.0-dev");
    assert!(name.starts_with(DLL_PREFIX));
    assert!(name.ends_with(DLL_SUFFIX));
    let stem = &name[DLL_PREFIX.len()..name.len() - DLL_SUFFIX.len()];
    assert_eq!(stem, "rustc_codegen_trust-ir-cg-1.99.0-dev");
}

#[test]
fn cargo_dylib_name_is_the_crate_name() {
    let name = cargo_dylib_name();
    let stem = &name[DLL_PREFIX.len()..name.len() - DLL_SUFFIX.len()];
    assert_eq!(stem, "rustc_codegen_trust_cg");
    assert_ne!(
        name,
        sysroot_dylib_name("1.99.0-dev"),
        "the built and installed names must differ: the builtin `trust-cg` would \
         otherwise be shadowed by, or shadow, the plugin"
    );
}
