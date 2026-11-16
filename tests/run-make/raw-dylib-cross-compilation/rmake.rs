// When cross-compiling using `raw-dylib`, rustc would try to fetch some
// very specific `dlltool` to complete the cross-compilation (such as `i686-w64-mingw32-dlltool`)
// when Windows only calls it `dlltool`. This test performs some cross-compilation in a
// way that previously failed due to this bug, and checks that it succeeds.
// See https://github.com/rust-lang/rust/pull/108355

//@ ignore-i686-pc-windows-gnu
// Reason: dlltool on this distribution is unable to produce x64 binaries
//@ needs-dlltool
// Reason: this is the utility being checked by this test

use run_make_support::{llvm_objdump, rust_lib_name, rustc};

fn main() {
    // Build as x86 and make sure that we have x86 objects only.
    rustc()
        .crate_type("lib")
        .crate_name("i686_raw_dylib_test")
        .target("i686-pc-windows-gnu")
        .input("lib.rs")
        // Trust: execute the real cross-target helper, without a target std,
        // and require the unsupported direct-tool boundary to withhold facts.
        .arg("-Ztrust-tool-inputs")
        .emit("dep-info,link")
        .run();
    assert_unavailable_tools("i686_raw_dylib_test.d");
    llvm_objdump()
        .arg("-a")
        .input(rust_lib_name("i686_raw_dylib_test"))
        .run()
        .assert_stdout_contains("file format coff-i386")
        .assert_stdout_not_contains("file format coff-x86-64");
    // Build as x64 and make sure that we have x64 objects only.
    rustc()
        .crate_type("lib")
        .crate_name("x64_raw_dylib_test")
        .target("x86_64-pc-windows-gnu")
        .input("lib.rs")
        // Trust: both native-host dlltool architecture selections stay valid
        // compilation, but neither may mint a completed empty tool inventory.
        .arg("-Ztrust-tool-inputs")
        .emit("dep-info,link")
        .run();
    assert_unavailable_tools("x64_raw_dylib_test.d");
    llvm_objdump()
        .arg("-a")
        .input(rust_lib_name("x64_raw_dylib_test"))
        .run()
        .assert_stdout_not_contains("file format coff-i386")
        .assert_stdout_contains("file format coff-x86-64");
}

// Trust: inspect the actual compiler's terminal dep-info, not a model row.
fn assert_unavailable_tools(path: &str) {
    let dep_info = std::fs::read_to_string(path).unwrap();
    let terminal: Vec<_> =
        dep_info.lines().filter_map(|line| line.strip_prefix("# trust-tool-inputs-v1:")).collect();
    assert_eq!(terminal, ["unavailable"], "{dep_info}");
}
