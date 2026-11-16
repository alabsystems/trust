//! Tests for the `cargo rustdoc` command.

use std::fs;

use crate::prelude::*;
use cargo_test_support::str;
use cargo_test_support::{basic_manifest, cross_compile, project};

use crate::utils::cross_compile::disabled as cross_compile_disabled;

/// A native proxy observes the actual inherited FIFO pair, rather than trusting
/// MAKEFLAGS text. The post-build doctest must use the same scheduler as the
/// fixture's compiler; a lost handoff or a fresh replacement pool fails here.
#[cfg(unix)]
#[cargo_test]
fn doctests_retain_the_original_compiler_scheduler() {
    let proxy = project()
        .at("doc-gnu-proxy")
        .file("Cargo.toml", &basic_manifest("doc-gnu-proxy", "0.0.1"))
        .file("src/main.rs", r#"
use std::ffi::{CString, OsString};
use std::mem::ManuallyDrop;
use std::os::fd::FromRawFd;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::path::Path;

unsafe extern "C" {
    fn execvp(program: *const std::ffi::c_char, args: *const *const std::ffi::c_char) -> i32;
}

fn main() {
    let mut args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let rustc = args.first().is_some_and(|arg| {
        matches!(Path::new(arg).file_name().and_then(|s| s.to_str()), Some("rustc" | "trustc"))
    });
    let program = if rustc { args.remove(0) }
        else { std::env::var_os("DOC_GNU_REAL_RUSTDOC").expect("real rustdoc") };
    let compiler_work = rustc && args.windows(2).any(|a| a[0] == "--crate-name" && a[1] == "foo");
    let doctest_work = !rustc && args.iter().any(|a| a == "--test");
    if compiler_work || doctest_work {
        let flags = std::env::var("CARGO_MAKEFLAGS").expect("compiler scheduler was not retained");
        let auth = flags.split_whitespace().find_map(|s| s.strip_prefix("--jobserver-auth="))
            .expect("GNU pipe handoff");
        let (read, write) = auth.split_once(',').expect("GNU pipe pair");
        let read = ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(read.parse().unwrap()) });
        let write = ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(write.parse().unwrap()) });
        let r = read.metadata().expect("live original GNU read endpoint");
        let w = write.metadata().expect("live original GNU write endpoint");
        assert!(r.file_type().is_fifo() && w.file_type().is_fifo());
        let identity = format!("{}:{}:{}:{}", r.dev(), r.ino(), w.dev(), w.ino());
        let record = std::env::var_os("DOC_GNU_RECORD").expect("identity record");
        if compiler_work { std::fs::write(record, identity).unwrap(); }
        else {
            assert_eq!(std::fs::read_to_string(record).unwrap(), identity, "doctest replaced the compiler's original pool");
            std::fs::write(std::env::var_os("DOC_GNU_DOCTEST_RECORD").expect("doctest identity record"), identity).unwrap();
        }
    }
    let program = CString::new(program.as_os_str().as_bytes()).unwrap();
    let args: Vec<CString> = std::iter::once(program.clone()).chain(
        args.iter().map(|a| CString::new(a.as_os_str().as_bytes()).unwrap())
    ).collect();
    let mut pointers: Vec<_> = args.iter().map(|a| a.as_ptr()).collect();
    pointers.push(std::ptr::null());
    unsafe { execvp(program.as_ptr(), pointers.as_ptr()); }
    panic!("exec compiler: {}", std::io::Error::last_os_error());
}
"#)
        .build();
    proxy.cargo("build").run();
    let p = project()
        .at("doc-gnu-subject")
        .file(
            "src/lib.rs",
            r#"
/// ```
/// assert_eq!(foo::answer(), 42);
/// ```
pub fn answer() -> u32 { 42 }
/// ```compile_fail,E0451
/// let _ = foo::Sealed { private: () };
/// ```
pub struct Sealed { private: () }
"#,
        )
        .build();
    p.cargo("test --doc")
        .env("RUSTC_WRAPPER", proxy.bin("doc-gnu-proxy"))
        .env("RUSTDOC", proxy.bin("doc-gnu-proxy"))
        .env("DOC_GNU_REAL_RUSTDOC", "rustdoc")
        .env("DOC_GNU_RECORD", p.root().join("compiler-gnu.identity"))
        .env("DOC_GNU_DOCTEST_RECORD", p.root().join("doctest-gnu.identity"))
        .with_stdout_contains("test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;[..]")
        .run();
    // Trust: require both actual events. A successful library build alone must
    // not count as evidence that the post-build doctest used the original pool.
    let compiler_identity = fs::read(p.root().join("compiler-gnu.identity")).unwrap();
    let doctest_identity = fs::read(p.root().join("doctest-gnu.identity")).unwrap();
    assert_eq!(compiler_identity, doctest_identity);
}

#[cargo_test]
fn rustdoc_simple() {
    let p = project().file("src/lib.rs", "").build();

    p.cargo("rustdoc -v")
        .with_stderr_data(str![[r#"
[DOCUMENTING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustdoc [..] --crate-name foo src/lib.rs -o [ROOT]/foo/target/doc [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[GENERATED] [ROOT]/foo/target/doc/foo/index.html

"#]])
        .run();
}

#[cargo_test]
fn rustdoc_simple_html() {
    // Trust: retain the channel refusal and exact current Trust guidance.
    let p = project().file("src/lib.rs", "").build();

    p.cargo("rustdoc --output-format html --open -v")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] the `--output-format` flag is unstable, and only available on Trust/nightly-capable Cargo channels, but this is the `stable` channel
Use the Trust `trust` channel, or another Cargo channel with explicit unstable-feature support, for these flags.
See https://github.com/alabsystems/Trust/issues for more information about the `--output-format` flag.

"#]])
        .run();
}

#[cargo_test(nightly, reason = "--output-format is unstable")]
fn rustdoc_simple_json() {
    let p = project().file("src/lib.rs", "").build();

    p.cargo("rustdoc --output-format json -v")
        .arg("-Zunstable-options")
        .masquerade_as_nightly_cargo(&["rustdoc-output-format"])
        .with_stderr_data(str![[r#"
[DOCUMENTING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustdoc [..] --crate-name foo [..]-o [ROOT]/foo/target/debug/build/foo/[HASH]/out [..] --output-format=json[..]
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[GENERATED] [ROOT]/foo/target/doc/foo.json

"#]])
        .run();
    assert!(p.root().join("target/doc/foo.json").is_file());
}

#[cargo_test]
fn rustdoc_invalid_output_format() {
    let p = project().file("src/lib.rs", "").build();

    p.cargo("rustdoc --output-format pdf -v")
        .arg("-Zunstable-options")
        .masquerade_as_nightly_cargo(&["rustdoc-output-format"])
        .with_status(1)
        .with_stderr_data(str![[r#"
[ERROR] invalid value 'pdf' for '--output-format <FMT>'
  [possible values: html, json]

For more information, try '--help'.

"#]])
        .run();
}

#[cargo_test]
fn rustdoc_json_stable() {
    // Trust: retain the channel refusal and exact current Trust guidance.
    let p = project().file("src/lib.rs", "").build();

    p.cargo("rustdoc --output-format json -v")
        .arg("-Zunstable-options")
        .with_status(101)
        .with_stderr_data(
            str![[r#"
[ERROR] the `-Z` flag is only accepted on Trust/nightly-capable Cargo channels, but this is the `stable` channel
Use the Trust `trust` channel, or another Cargo channel with explicit unstable-feature support, for these flags.

"#]]
	    )
        .run();
}

#[cargo_test]
fn rustdoc_json_without_unstable_options() {
    // Trust: retain the channel refusal and exact current Trust guidance.
    let p = project().file("src/lib.rs", "").build();

    p.cargo("rustdoc --output-format json -v")
        .masquerade_as_nightly_cargo(&["rustdoc-output-format"])
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] the `--output-format` flag is unstable, pass `-Z unstable-options` to enable it
See https://github.com/alabsystems/Trust/issues for more information about the `--output-format` flag.

"#]])
        .run();
}

#[cargo_test]
fn rustdoc_args() {
    let p = project().file("src/lib.rs", "").build();

    p.cargo("rustdoc -v -- --cfg=foo")
        .with_stderr_data(str![[r#"
[DOCUMENTING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustdoc [..] --crate-name foo src/lib.rs -o [ROOT]/foo/target/doc [..]-C metadata=[..]--cfg=foo[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[GENERATED] [ROOT]/foo/target/doc/foo/index.html

"#]])
        .run();
}

#[cargo_test]
fn rustdoc_binary_args_passed() {
    let p = project().file("src/main.rs", "").build();

    p.cargo("rustdoc -v")
        .arg("--")
        .arg("--markdown-no-toc")
        .with_stderr_data(str![[r#"
...
[RUNNING] `rustdoc [..] --markdown-no-toc[..]`
...
"#]])
        .run();
}

#[cargo_test]
fn rustdoc_foo_with_bar_dependency() {
    let foo = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [dependencies.bar]
                path = "../bar"
            "#,
        )
        .file("src/lib.rs", "extern crate bar; pub fn foo() {}")
        .build();
    let _bar = project()
        .at("bar")
        .file("Cargo.toml", &basic_manifest("bar", "0.0.1"))
        .file("src/lib.rs", "pub fn baz() {}")
        .build();

    foo.cargo("rustdoc -v -- --cfg=foo")
        .with_stderr_data(str![[r#"
[LOCKING] 1 package to highest compatible version
[CHECKING] bar v0.0.1 ([ROOT]/bar)
[RUNNING] `rustc [..] [ROOT]/bar/src/lib.rs [..]`
[DOCUMENTING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustdoc [..] --crate-name foo src/lib.rs -o [ROOT]/foo/target/doc [..]-C metadata=[..] --extern [..]--cfg=foo[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[GENERATED] [ROOT]/foo/target/doc/foo/index.html

"#]])
        .run();
}

#[cargo_test]
fn rustdoc_only_bar_dependency() {
    let foo = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [dependencies.bar]
                path = "../bar"
            "#,
        )
        .file("src/main.rs", "extern crate bar; fn main() { bar::baz() }")
        .build();
    let _bar = project()
        .at("bar")
        .file("Cargo.toml", &basic_manifest("bar", "0.0.1"))
        .file("src/lib.rs", "pub fn baz() {}")
        .build();

    foo.cargo("rustdoc -v -p bar -- --cfg=foo")
        .with_stderr_data(str![[r#"
[LOCKING] 1 package to highest compatible version
[DOCUMENTING] bar v0.0.1 ([ROOT]/bar)
[RUNNING] `rustdoc [..] --crate-name bar [ROOT]/bar/src/lib.rs -o [ROOT]/foo/target/doc [..]-C metadata=[..]--cfg=foo[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[GENERATED] [ROOT]/foo/target/doc/bar/index.html

"#]])
        .run();
}

#[cargo_test]
fn rustdoc_same_name_documents_lib() {
    let p = project()
        .file("src/main.rs", "fn main() {}")
        .file("src/lib.rs", r#" "#)
        .build();

    p.cargo("rustdoc -v -- --cfg=foo")
        .with_stderr_data(str![[r#"
[DOCUMENTING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustdoc [..] --crate-name foo src/lib.rs -o [ROOT]/foo/target/doc [..]-C metadata=[..]--cfg=foo[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[GENERATED] [ROOT]/foo/target/doc/foo/index.html

"#]])
        .run();
}

#[cargo_test]
fn features() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [features]
                quux = []
            "#,
        )
        .file("src/lib.rs", "")
        .build();

    p.cargo("rustdoc --verbose --features quux")
        .with_stderr_data(str![[r#"
...
[RUNNING] `rustdoc [..]feature=[..]quux[..]`
...
"#]])
        .run();
}

#[cargo_test]
fn proc_macro_crate_type() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [lib]
                proc-macro = true

            "#,
        )
        .file("src/lib.rs", "")
        .build();

    p.cargo("rustdoc --verbose")
        .with_stderr_data(str![[r#"
...
[RUNNING] `rustdoc --edition=2015 --crate-type proc-macro [..]`
...
"#]])
        .run();
}

#[cargo_test]
fn rustdoc_target() {
    if cross_compile_disabled() {
        return;
    }

    let p = project().file("src/lib.rs", "").build();

    p.cargo("rustdoc --verbose --target")
        .arg(cross_compile::alternate())
        .with_stderr_data(str![[r#"
[DOCUMENTING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustdoc [..]--crate-name foo src/lib.rs [..]--target [ALT_TARGET] -o [ROOT]/foo/target/[ALT_TARGET]/doc [..] -L dependency=[ROOT]/foo/target/debug/build/foo/[HASH]/out[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[GENERATED] [ROOT]/foo/target/[..]/doc/foo/index.html

"#]])
        .run();
}

#[cargo_test]
fn fail_with_glob() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [workspace]
                members = ["bar"]
            "#,
        )
        .file("bar/Cargo.toml", &basic_manifest("bar", "0.1.0"))
        .file("bar/src/lib.rs", "pub fn bar() {  break_the_build(); }")
        .build();

    p.cargo("rustdoc -p '*z'")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] glob patterns on package selection are not supported.

"#]])
        .run();
}

#[cargo_test(nightly, reason = "--output-format is unstable")]
fn rustdoc_json_same_crate_different_version() {
    let entry = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "entry"
                version = "0.1.0"
                edition = "2021"

                [dependencies]
                dep_v1 = { path = "../dep_v1", package = "dep" }
                dep_v2 = { path = "../dep_v2", package = "dep" }
            "#,
        )
        .file("src/lib.rs", "pub fn entry() {}")
        .build();

    let _dep_v1 = project()
        .at("dep_v1")
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "dep"
                version = "1.0.0"
                edition = "2021"
            "#,
        )
        .file("src/lib.rs", "pub fn dep_v1_fn() {}")
        .build();

    let _dep_v2 = project()
        .at("dep_v2")
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "dep"
                version = "2.0.0"
                edition = "2021"
            "#,
        )
        .file("src/lib.rs", "pub fn dep_v2_fn() {}")
        .build();

    entry
        .cargo("rustdoc -v --output-format json -p dep@1.0.0")
        .arg("-Zunstable-options")
        .masquerade_as_nightly_cargo(&["rustdoc-output-format"])
        .with_stderr_data(str![[r#"
[LOCKING] 2 packages to highest compatible versions
[DOCUMENTING] dep v1.0.0 ([ROOT]/dep_v1)
[RUNNING] `rustdoc [..] --crate-name dep [ROOT]/dep_v1/src/lib.rs [..] --output-format=json[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[GENERATED] [ROOT]/foo/target/doc/dep.json

"#]])
        .run();

    let dep_json = fs::read_to_string(entry.root().join("target/doc/dep.json")).unwrap();
    assert!(dep_json.contains("dep_v1_fn"));
    assert!(!dep_json.contains("dep_v2_fn"));

    entry
        .cargo("rustdoc -v --output-format json -p dep@2.0.0")
        .arg("-Zunstable-options")
        .masquerade_as_nightly_cargo(&["rustdoc-output-format"])
        .with_stderr_data(str![[r#"
[DOCUMENTING] dep v2.0.0 ([ROOT]/dep_v2)
[RUNNING] `rustdoc [..] --crate-name dep [ROOT]/dep_v2/src/lib.rs [..] --output-format=json[..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[GENERATED] [ROOT]/foo/target/doc/dep.json

"#]])
        .run();

    let dep_json = fs::read_to_string(entry.root().join("target/doc/dep.json")).unwrap();
    assert!(!dep_json.contains("dep_v1_fn"));
    assert!(dep_json.contains("dep_v2_fn"));

    entry
        .cargo("rustdoc -v --output-format json -p dep@1.0.0")
        .arg("-Zunstable-options")
        .masquerade_as_nightly_cargo(&["rustdoc-output-format"])
        .with_stderr_data(str![[r#"
[FRESH] dep v1.0.0 ([ROOT]/dep_v1)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s
[GENERATED] [ROOT]/foo/target/doc/dep.json

"#]])
        .run();

    let dep_json = fs::read_to_string(entry.root().join("target/doc/dep.json")).unwrap();
    assert!(dep_json.contains("dep_v1_fn"));
    assert!(!dep_json.contains("dep_v2_fn"));
}
