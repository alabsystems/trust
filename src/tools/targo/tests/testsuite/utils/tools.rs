//! Common executables that can be reused by various tests.
// Trust: transparent proxy fixture adapters for SP-1; exact changed coverage
// is ledgered in tests/upstream-rust/divergence-audit.toml.

use crate::prelude::*;
use cargo_test_support::{Project, basic_manifest, paths, project};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::OnceLock;

// Trust: the exact transparent Unix proxy adapter is independently exercised
// before fixture changes. Its changed coverage and expiry are ledgered in
// tests/upstream-rust/divergence-audit.toml; default plain-spawn negatives stay.
pub fn with_transparent_proxy(source: &str) -> String {
    format!(
        "{source}\nmod transparent_proxy {{\n{}\n}}",
        include_str!("fixtures/transparent_proxy.rs"),
    )
}

static ECHO_WRAPPER: OnceLock<Mutex<Option<PathBuf>>> = OnceLock::new();
static ECHO: OnceLock<Mutex<Option<PathBuf>>> = OnceLock::new();
static CLIPPY_DRIVER: OnceLock<Mutex<Option<PathBuf>>> = OnceLock::new();

/// Trust: fixture-authored proxies must target the same compiler as ordinary
/// fixture commands, not the bootstrap compiler that built the test binary.
pub fn rustc_executable() -> PathBuf {
    fixture_executable("rustc").unwrap_or_else(|| {
        std::env::var_os("RUSTC")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("rustc"))
    })
}

/// Trust: documentation proxies use the same dedicated fixture bundle too.
pub fn rustdoc_executable() -> PathBuf {
    fixture_executable("rustdoc").unwrap_or_else(|| {
        std::env::var_os("RUSTDOC")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("rustdoc"))
    })
}

fn fixture_executable(tool: &str) -> Option<PathBuf> {
    // Trust: use the same exact, paired fixture request as direct compiler commands.
    let directory = match (
        std::env::var_os("TRUST_TARGO_TEST_NO_VERIFY"),
        std::env::var_os("TEST_TRUST_SHIM_DIR"),
    ) {
        (None, None) => return None,
        (Some(marker), Some(directory)) if marker == "1" && !directory.is_empty() => directory,
        _ => panic!("TEST_TRUST_SHIM_DIR and exact TRUST_TARGO_TEST_NO_VERIFY=1 must accompany each other"),
    };
    let executable = PathBuf::from(directory).join(format!("{tool}{}", std::env::consts::EXE_SUFFIX));
    assert!(executable.is_file(), "fixture {tool} is missing: {}", executable.display());
    Some(executable)
}

/// Trust: use the existing checked transport for a fixture which must wait
/// for a child instead of transparently replacing itself.
pub fn jobserver_build_dependency() -> String {
    format!(
        "\n[build-dependencies]\njobserver_utils = {{ path = {:?} }}\n",
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../jobserver_utils")
    )
}

/// Returns the path to an executable that works as a wrapper around rustc.
///
/// The wrapper will echo the command line it was called with to stderr.
pub fn echo_wrapper() -> PathBuf {
    let mut lock = ECHO_WRAPPER
        .get_or_init(|| Default::default())
        .lock()
        .unwrap();
    if let Some(path) = &*lock {
        return path.clone();
    }
    let p = project()
        .at(paths::global_root().join("rustc-echo-wrapper"))
        .file("Cargo.toml", &basic_manifest("rustc-echo-wrapper", "1.0.0"))
        .file(
            "src/main.rs",
            &with_transparent_proxy(
                r#"
            use std::fs::read_to_string;
            use std::path::PathBuf;
            fn main() {
                // Handle args from `@path` argfile for rustc
                let args = std::env::args()
                    .flat_map(|p| if let Some(p) = p.strip_prefix("@") {
                        read_to_string(p).unwrap().lines().map(String::from).collect()
                    } else {
                        vec![p]
                    })
                    .collect::<Vec<_>>();
                eprintln!("WRAPPER CALLED: {}", args[1..].join(" "));
                let status = transparent_proxy::status(std::process::Command::new(&args[1])
                    .args(&args[2..])).unwrap();
                std::process::exit(status.code().unwrap_or(1));
            }
            "#,
            ),
        )
        .build();
    p.cargo("build").run();
    let path = p.bin("rustc-echo-wrapper");
    *lock = Some(path.clone());
    path
}

/// Returns the path to an executable that prints its arguments.
///
/// Do not expect this to be anything fancy.
pub fn echo() -> PathBuf {
    let mut lock = ECHO.get_or_init(|| Default::default()).lock().unwrap();
    if let Some(path) = &*lock {
        return path.clone();
    }
    if let Ok(path) = cargo_util::paths::resolve_executable(Path::new("echo")) {
        *lock = Some(path.clone());
        return path;
    }
    // Often on Windows, `echo` is not available.
    let p = project()
        .at(paths::global_root().join("basic-echo"))
        .file("Cargo.toml", &basic_manifest("basic-echo", "1.0.0"))
        .file(
            "src/main.rs",
            r#"
                fn main() {
                    let mut s = String::new();
                    let mut it = std::env::args().skip(1).peekable();
                    while let Some(n) = it.next() {
                        s.push_str(&n);
                        if it.peek().is_some() {
                            s.push(' ');
                        }
                    }
                    println!("{}", s);
                }
            "#,
        )
        .build();
    p.cargo("build").run();
    let path = p.bin("basic-echo");
    *lock = Some(path.clone());
    path
}

/// Returns a project which builds a cargo-echo simple subcommand
pub fn echo_subcommand() -> Project {
    let p = project()
        .at("cargo-echo")
        .file("Cargo.toml", &basic_manifest("cargo-echo", "0.0.1"))
        .file(
            "src/main.rs",
            r#"
                fn main() {
                    let args: Vec<_> = ::std::env::args().skip(1).collect();
                    println!("{}", args.join(" "));
                }
            "#,
        )
        .build();
    p.cargo("build").run();
    p
}

/// A wrapper around `rustc` instead of calling `clippy`.
pub fn wrapped_clippy_driver() -> PathBuf {
    let mut lock = CLIPPY_DRIVER
        .get_or_init(|| Default::default())
        .lock()
        .unwrap();
    if let Some(path) = &*lock {
        return path.clone();
    }
    let clippy_driver = project()
        .at(paths::global_root().join("clippy-driver"))
        .file("Cargo.toml", &basic_manifest("clippy-driver", "0.0.1"))
        .file(
            "src/main.rs",
            &with_transparent_proxy(r#"
            fn main() {
                let mut args = std::env::args_os();
                let _me = args.next().unwrap();
                let rustc = args.next().unwrap();
                let status = transparent_proxy::status(std::process::Command::new(rustc).args(args)).unwrap();
                std::process::exit(status.code().unwrap_or(1));
            }
            "#),
        )
        .build();
    clippy_driver.cargo("build").run();
    let path = clippy_driver.bin("clippy-driver");
    *lock = Some(path.clone());
    path
}
