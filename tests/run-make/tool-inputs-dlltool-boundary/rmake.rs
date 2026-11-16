// Trust: a real compiler-owned native helper must not disappear into an empty
// terminal inventory. Cross codegen uses no target std or executable runner.
//@ only-unix
//@ needs-llvm-components: x86

use std::path::Path;

use run_make_support::{env_var, llvm_objdump, rust_lib_name, rustc};

fn main() {
    // Reuse the maintained raw-dylib subject, including its no_core lang items.
    std::fs::write("subject.rs", include_str!("../raw-dylib-cross-compilation/lib.rs")).unwrap();
    let dlltool = Path::new(&env_var("LLVM_BIN_DIR")).join("llvm-dlltool");
    assert!(dlltool.is_file(), "the selected LLVM must provide its actual llvm-dlltool");
    // Trust: the GNU-tool probe is unavailable on native Darwin. Exercise both
    // original Windows GNU architectures with the same genuine LLVM helper.
    for (target, name, object_format, other_format) in [
        (
            "i686-pc-windows-gnu",
            "tool_inputs_dlltool_i686",
            "file format coff-i386",
            "file format coff-x86-64",
        ),
        (
            "x86_64-pc-windows-gnu",
            "tool_inputs_dlltool_x64",
            "file format coff-x86-64",
            "file format coff-i386",
        ),
    ] {
        rustc()
            .crate_type("lib")
            .crate_name(name)
            .target(target)
            .input("subject.rs")
            .arg(format!("-Cdlltool={}", dlltool.display()))
            .arg("-Ztrust-tool-inputs")
            .emit("dep-info,link")
            .run();
        let dep_info = std::fs::read_to_string(format!("{name}.d")).unwrap();
        let terminal: Vec<_> = dep_info
            .lines()
            .filter_map(|line| line.strip_prefix("# trust-tool-inputs-v1:"))
            .collect();
        assert_eq!(terminal, ["unavailable"], "target={target} {dep_info}");
        llvm_objdump()
            .arg("-a")
            .input(rust_lib_name(name))
            .run()
            .assert_stdout_contains(object_format)
            .assert_stdout_not_contains(other_format);
    }
}
