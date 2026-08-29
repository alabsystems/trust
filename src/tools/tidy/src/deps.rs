//! Checks the licenses of third-party dependencies.

use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::fs::{File, read_dir};
use std::io::Write;
use std::path::Path;

use cargo_metadata::semver::Version;
use cargo_metadata::{Metadata, Package, PackageId};

use crate::diagnostics::{RunningCheck, TidyCtx};

#[path = "../../../bootstrap/src/utils/proc_macro_deps.rs"]
mod proc_macro_deps;

#[derive(Clone, Copy)]
struct ListLocation {
    path: &'static str,
    line: u32,
}

impl Display for ListLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.path, self.line)
    }
}

/// Creates a [`ListLocation`] for the current location (with an additional offset to the actual list start);
macro_rules! location {
    (+ $offset:literal) => {
        ListLocation { path: file!(), line: line!() + $offset }
    };
}

/// These are licenses that are allowed for all crates, including the runtime,
/// rustc, tools, etc.
#[rustfmt::skip]
const LICENSES: &[&str] = &[
    // tidy-alphabetical-start
    "0BSD OR MIT OR Apache-2.0",                           // adler2 license
    "Apache-2.0 / MIT",
    "Apache-2.0 OR ISC OR MIT",
    "Apache-2.0 OR MIT",
    "Apache-2.0 WITH LLVM-exception OR Apache-2.0 OR MIT", // wasi license
    "Apache-2.0/MIT",
    "BSD-2-Clause OR Apache-2.0 OR MIT",                   // zerocopy
    "BSD-2-Clause OR MIT OR Apache-2.0",
    "BSD-3-Clause/MIT",
    "CC0-1.0 OR MIT-0 OR Apache-2.0",
    "ISC",
    "MIT / Apache-2.0",
    "MIT AND (MIT OR Apache-2.0)",
    "MIT AND Apache-2.0 WITH LLVM-exception AND (MIT OR Apache-2.0)", // compiler-builtins
    "MIT OR Apache-2.0 OR BSD-1-Clause",
    "MIT OR Apache-2.0 OR LGPL-2.1-or-later",              // r-efi, r-efi-alloc; LGPL is not acceptable, but we use it under MIT OR Apache-2.0
    "MIT OR Apache-2.0 OR Zlib",                           // tinyvec_macros
    "MIT OR Apache-2.0",
    "MIT OR Zlib OR Apache-2.0",                           // miniz_oxide
    "MIT",
    "MIT/Apache-2.0",
    "Unlicense OR MIT",
    "Unlicense/MIT",
    "Zlib",                                                // foldhash (FIXME: see PERMITTED_STDLIB_DEPENDENCIES)
    // tidy-alphabetical-end
];

/// These are licenses that are allowed for rustc, tools, etc. But not for the runtime!
#[rustfmt::skip]
const LICENSES_TOOLS: &[&str] = &[
    // tidy-alphabetical-start
    "(Apache-2.0 OR MIT) AND BSD-3-Clause",
    "(MIT OR Apache-2.0) AND Unicode-3.0",                 // unicode_ident (1.0.14)
    "(MIT OR Apache-2.0) AND Unicode-DFS-2016",            // unicode_ident (1.0.12)
    "0BSD",
    "Apache-2.0 AND ISC",
    "Apache-2.0 OR BSL-1.0",  // BSL is not acceptable, but we use it under Apache-2.0
    "Apache-2.0 OR GPL-2.0-only",
    "Apache-2.0 WITH LLVM-exception",
    "Apache-2.0",
    "BSD-2-Clause",
    "BSD-3-Clause",
    "CC0-1.0 OR Apache-2.0 OR Apache-2.0 WITH LLVM-exception",
    "CC0-1.0",
    "Unicode-3.0",                                         // icu4x
    "Unicode-DFS-2016",                                    // tinystr
    "Zlib OR Apache-2.0 OR MIT",                           // tinyvec
    "Zlib",
    // tidy-alphabetical-end
];

type ExceptionList = &'static [(&'static str, &'static str)];

#[derive(Clone, Copy)]
pub(crate) struct WorkspaceInfo<'a> {
    /// Path to the directory containing the workspace root Cargo.toml file.
    pub(crate) path: &'a str,
    /// The list of license exceptions.
    pub(crate) exceptions: ExceptionList,
    /// Optionally:
    /// * A list of crates for which dependencies need to be explicitly allowed.
    /// * The list of allowed dependencies.
    /// * The source code location of the allowed dependencies list
    crates_and_deps: Option<(&'a [&'a str], &'a [&'a str], ListLocation)>,
    /// Submodules required for the workspace
    pub(crate) submodules: &'a [&'a str],
}

const WORKSPACE_LOCATION: ListLocation = location!(+4);

/// The workspaces to check for licensing and optionally permitted dependencies.
// FIXME auto detect all cargo workspaces
pub(crate) const WORKSPACES: &[WorkspaceInfo<'static>] = &[
    // The root workspace has to be first for check_rustfix to work.
    WorkspaceInfo {
        path: ".",
        exceptions: EXCEPTIONS,
        crates_and_deps: Some((
            &["rustc-main"],
            PERMITTED_RUSTC_DEPENDENCIES,
            PERMITTED_RUSTC_DEPS_LOCATION,
        )),
        submodules: &[],
    },
    WorkspaceInfo {
        path: "library",
        exceptions: EXCEPTIONS_STDLIB,
        crates_and_deps: Some((
            &["sysroot"],
            PERMITTED_STDLIB_DEPENDENCIES,
            PERMITTED_STDLIB_DEPS_LOCATION,
        )),
        submodules: &[],
    },
    WorkspaceInfo {
        path: "library/stdarch",
        exceptions: EXCEPTIONS_STDARCH,
        crates_and_deps: None,
        submodules: &[],
    },
    WorkspaceInfo {
        path: "src/bootstrap",
        exceptions: EXCEPTIONS_BOOTSTRAP,
        crates_and_deps: None,
        submodules: &[],
    },
    WorkspaceInfo {
        path: "src/tools/targo",
        exceptions: EXCEPTIONS_CARGO,
        crates_and_deps: None,
        submodules: &["src/tools/targo"],
    },
    // FIXME uncomment once all deps are vendored
    //  WorkspaceInfo {
    //      path: "src/tools/miri/test-cargo-miri",
    //      crates_and_deps: None
    //      submodules: &[],
    //  },
    // WorkspaceInfo {
    //      path: "src/tools/miri/test_dependencies",
    //      crates_and_deps: None,
    //      submodules: &[],
    //  }
    WorkspaceInfo {
        path: "src/tools/rust-analyzer",
        exceptions: EXCEPTIONS_RUST_ANALYZER,
        crates_and_deps: None,
        submodules: &[],
    },
    WorkspaceInfo {
        path: "src/tools/rustbook",
        exceptions: EXCEPTIONS_RUSTBOOK,
        crates_and_deps: None,
        submodules: &[],
    },
    WorkspaceInfo {
        path: "tests/run-make-cargo/uefi-qemu/uefi_qemu_test",
        exceptions: EXCEPTIONS_UEFI_QEMU_TEST,
        crates_and_deps: None,
        submodules: &[],
    },
];

/// These are exceptions to Rust's permissive licensing policy, and
/// should be considered bugs. Exceptions are only allowed in Rust
/// tooling. It is _crucial_ that no exception crates be dependencies
/// of the Rust runtime (std/test).
#[rustfmt::skip]
const EXCEPTIONS: ExceptionList = &[
    // tidy-alphabetical-start
    ("colored", "MPL-2.0"),                                  // rustfmt
    ("gmp-mpfr-sys", "LGPL-3.0+"),                           // Trust verifier stack via ay/rug
    ("option-ext", "MPL-2.0"),                               // cargo-miri (via `directories`)
    ("rug", "LGPL-3.0+"),                                    // Trust verifier stack via ay
    // tidy-alphabetical-end
];

/// These are exceptions to Rust's permissive licensing policy, and
/// should be considered bugs. Exceptions are only allowed in Rust
/// tooling. It is _crucial_ that no exception crates be dependencies
/// of the Rust runtime (std/test).
#[rustfmt::skip]
const EXCEPTIONS_STDLIB: ExceptionList = &[
    // tidy-alphabetical-start
    ("fortanix-sgx-abi", "MPL-2.0"), // libstd but only for `sgx` target. FIXME: this dependency violates the documentation comment above.
    // tidy-alphabetical-end
];

const EXCEPTIONS_CARGO: ExceptionList = &[
    // tidy-alphabetical-start
    ("bitmaps", "MPL-2.0+"),
    ("im-rc", "MPL-2.0+"),
    ("sized-chunks", "MPL-2.0+"),
    // tidy-alphabetical-end
];

const EXCEPTIONS_RUST_ANALYZER: ExceptionList = &[
    // tidy-alphabetical-start
    ("option-ext", "MPL-2.0"),
    // tidy-alphabetical-end
];

const EXCEPTIONS_RUSTBOOK: ExceptionList = &[
    // tidy-alphabetical-start
    ("font-awesome-as-a-crate", "CC-BY-4.0 AND MIT"),
    ("mdbook-core", "MPL-2.0"),
    ("mdbook-driver", "MPL-2.0"),
    ("mdbook-html", "MPL-2.0"),
    ("mdbook-markdown", "MPL-2.0"),
    ("mdbook-preprocessor", "MPL-2.0"),
    ("mdbook-renderer", "MPL-2.0"),
    ("mdbook-summary", "MPL-2.0"),
    // tidy-alphabetical-end
];

const EXCEPTIONS_STDARCH: ExceptionList = &[];

const EXCEPTIONS_BOOTSTRAP: ExceptionList = &[];

const EXCEPTIONS_UEFI_QEMU_TEST: ExceptionList = &[];

const PERMITTED_RUSTC_DEPS_LOCATION: ListLocation = location!(+6);

/// Crates rustc is allowed to depend on. Avoid adding to the list if possible.
///
/// This list is here to provide a speed-bump to adding a new dependency to
/// rustc. Please check with the compiler team before adding an entry.
const PERMITTED_RUSTC_DEPENDENCIES: &[&str] = &[
    // tidy-alphabetical-start
    "adler2",
    "aho-corasick",
    "allocator-api2", // FIXME: only appears in Cargo.lock due to https://github.com/rust-lang/cargo/issues/10801
    "annotate-snippets",
    "anstream",
    "anstyle",
    "anstyle-parse",
    "anstyle-query",
    "anstyle-wincon",
    "ar_archive_writer",
    "arrayref",
    "arrayvec",
    "bitflags",
    "blake3",
    "block-buffer",
    "block2",
    "bstr",
    "cc",
    "cfg-if",
    "cfg_aliases",
    "colorchoice",
    "constant_time_eq",
    "cpufeatures",
    "crc32fast",
    "crossbeam-deque",
    "crossbeam-epoch",
    "crossbeam-utils",
    "crypto-common",
    "ctrlc",
    "darling",
    "darling_core",
    "darling_macro",
    "datafrog",
    "derive-where",
    "derive_setters",
    "digest",
    "dispatch2",
    "displaydoc",
    "dissimilar",
    "dyn-clone",
    "either",
    "elsa",
    "ena",
    "equivalent",
    "errno",
    "expect-test",
    "fallible-iterator", // dependency of `thorin`
    "fastrand",
    "find-msvc-tools",
    "flate2",
    "fluent-bundle",
    "fluent-langneg",
    "fluent-syntax",
    "fnv",
    "foldhash",
    "generic-array",
    "getopts",
    "getrandom",
    "gimli",
    "gsgdt",
    "hashbrown",
    "icu_collections",
    "icu_list",
    "icu_locale",
    "icu_locale_core",
    "icu_locale_data",
    "icu_provider",
    "ident_case",
    "indexmap",
    "intl-memoizer",
    "intl_pluralrules",
    "is_terminal_polyfill",
    "itertools",
    "itoa",
    "jiff",
    "jiff-static",
    "jobserver",
    "lazy_static",
    "leb128",
    "libc",
    "libloading",
    "linux-raw-sys",
    "litemap",
    "lock_api",
    "log",
    "matchers",
    "md-5",
    "measureme",
    "memchr",
    "memmap2",
    "miniz_oxide",
    "nix",
    "nu-ansi-term",
    "objc2",
    "objc2-encode",
    "object",
    "odht",
    "once_cell",
    "once_cell_polyfill",
    "parking_lot",
    "parking_lot_core",
    "pathdiff",
    "perf-event-open-sys",
    "pin-project-lite",
    "polonius-engine",
    "portable-atomic", // dependency for platforms doesn't support `AtomicU64` in std
    "portable-atomic-util",
    "potential_utf",
    "ppv-lite86",
    "proc-macro-hack",
    "proc-macro2",
    "psm",
    "pulldown-cmark",
    "pulldown-cmark-escape",
    "punycode",
    "quote",
    "r-efi",
    "rand",
    "rand_chacha",
    "rand_core",
    "rand_xorshift", // dependency for doc-tests in rustc_thread_pool
    "rand_xoshiro",
    "redox_syscall",
    "ref-cast",
    "ref-cast-impl",
    "regex",
    "regex-automata",
    "regex-syntax",
    "rustc-demangle",
    "rustc-hash",
    "rustc-literal-escaper",
    "rustc-stable-hash",
    "rustc_apfloat",
    "rustix",
    "ruzstd", // via object in thorin-dwp
    "schemars",
    "schemars_derive",
    "scoped-tls",
    "scopeguard",
    "self_cell",
    "serde",
    "serde_core",
    "serde_derive",
    "serde_derive_internals",
    "serde_json",
    "serde_path_to_error",
    "sha1",
    "sha2",
    "sharded-slab",
    "shlex",
    "simd-adler32",
    "smallvec",
    "stable_deref_trait",
    "stacker",
    "static_assertions",
    "strsim",
    "syn",
    "synstructure",
    "tempfile",
    "termize",
    "thin-vec",
    "thiserror",
    "thiserror-impl",
    "thorin-dwp",
    "thread_local",
    "tikv-jemalloc-sys",
    "tinystr",
    "tinyvec",
    "tinyvec_macros",
    "tracing",
    "tracing-attributes",
    "tracing-core",
    "tracing-log",
    "tracing-serde",
    "tracing-subscriber",
    "tracing-tree",
    "twox-hash",
    "type-map",
    "typenum",
    "unic-langid",
    "unic-langid-impl",
    "unic-langid-macros",
    "unic-langid-macros-impl",
    "unicase",
    "unicode-ident",
    "unicode-normalization",
    "unicode-properties",
    "unicode-script",
    "unicode-security",
    "unicode-width",
    "utf8_iter",
    "utf8parse",
    "valuable",
    "version_check",
    "wasi",
    "wasm-encoder",
    "wasmparser",
    "windows",
    "windows-collections",
    "windows-core",
    "windows-future",
    "windows-implement",
    "windows-interface",
    "windows-link",
    "windows-numerics",
    "windows-result",
    "windows-strings",
    "windows-sys",
    "windows-threading",
    "wit-bindgen-rt@0.39.0", // pinned to a specific version due to using a binary blob: <https://github.com/rust-lang/rust/pull/136395#issuecomment-2692769062>
    "writeable",
    "yoke",
    "yoke-derive",
    "zerocopy",
    "zerocopy-derive",
    "zerofrom",
    "zerofrom-derive",
    "zerotrie",
    "zerovec",
    "zerovec-derive",
    "zlib-rs",
    // tidy-alphabetical-end
];

/// Trust: entries of upstream's `PERMITTED_RUSTC_DEPENDENCIES` that Trust's own
/// resolution no longer reaches, listed here instead of being deleted from the
/// upstream array.
///
/// Deleting from `PERMITTED_RUSTC_DEPENDENCIES` would edit a merge-hot upstream
/// list — a conflict on every sync, forever, over a divergence that is entirely
/// ours. Listing the retirement here keeps upstream's array byte-identical and
/// makes the divergence reviewable: one row, one reason, and it fails closed
/// (see the re-introduction check in `check_permitted_dependencies`).
///
/// MEASURED 2026-08-22, and the measurement matters because the previously
/// recorded reason for this whole lane was wrong. `docs/audits/2026-08-21-tidy-
/// debt-ledger.md` held that the missing entries were platform-specific — absent
/// from a macOS resolution, present on Windows/wasm hosts — and that pruning was
/// therefore a trap. A `Cargo.lock` is host-independent, and this one proves it:
/// `windows-sys`, `windows-core`, `windows-link`, `windows-result`,
/// `windows-strings` and two `wasi` versions are all present in the root lock as
/// resolved on macOS. The real mechanism is a version move — `windows-sys
/// 0.61.2` depends on `windows-link`, not on the `windows-targets` +
/// `windows_*_{msvc,gnu,gnullvm}` family it used to — and `blake3 1.8.7` dropped
/// `arrayref` in favour of `arrayvec`. Those crates are gone from the graph, on
/// every host, and the allowlist rows for them were dead.
///
/// The `windows_*`, `wasip2`/`wasip3`, `wit-bindgen*` and `prettyplease` rows
/// removed at the same time were in `TRUST_PERMITTED_RUSTC_DEPENDENCIES` below —
/// Trust-owned, so deleting them costs no merge tax. `wasip2`/`wasip3`/
/// `wit-bindgen` remain correctly listed in `PERMITTED_STDLIB_DEPENDENCIES`,
/// which is where the `library` workspace actually reaches them.
#[rustfmt::skip]
const TRUST_RETIRED_UPSTREAM_RUSTC_DEPENDENCIES: &[&str] = &[
    // tidy-alphabetical-start
    "arrayref",   // blake3 1.8.7 replaced it with arrayvec
    // tidy-alphabetical-end
];

/// Trust: the mirror image of the list above — crates the rustc graph reaches
/// that upstream's list does not yet name, because Trust's lock is AHEAD of the
/// merge base rather than behind it.
///
/// These are not Trust dependencies. Every row is an upstream crate that split
/// or gained an optional feature in a version newer than the one upstream's
/// allowlist was written against, so it is kept out of
/// `TRUST_PERMITTED_RUSTC_DEPENDENCIES` — that list's whole point is that
/// verifier-stack drift is auditable on its own, and mixing upstream drift into
/// it would destroy exactly that.
///
/// Each row carries the edge that introduces it, traced 2026-08-22 through
/// `cargo metadata --all-features` (which is the configuration tidy itself
/// resolves, so an optional feature that upstream never activates still counts
/// here). When a merge brings upstream's own list forward past these, the rows
/// become duplicates and should be deleted, not left to accumulate.
#[rustfmt::skip]
const TRUST_UPSTREAM_DRIFT_RUSTC_DEPENDENCIES: &[&str] = &[
    // tidy-alphabetical-start
    "defmt",                     // rustc_driver_impl <- jiff <- jiff-static <- jiff-core <- defmt
    "defmt-macros",              //   "  <- defmt <- defmt-macros
    "defmt-parser",              //   "  <- defmt-macros <- defmt-parser
    "icu_locale_fallback",       // rustc_error_messages <- icu_locale <- icu_locale_fallback
    "icu_locale_fallback_data",  //   "  <- icu_locale_fallback <- icu_locale_fallback_data
    "jiff-core",                 // rustc_driver_impl <- jiff <- jiff-static <- jiff-core
    // tidy-alphabetical-end
];

/// Additional crates pulled into rustc by Trust's default native verifier stack.
///
/// Keep this separate from `PERMITTED_RUSTC_DEPENDENCIES` so upstream Rust
/// dependency drift and Trust-introduced verifier dependency drift are audited
/// independently.
///
// Trust: THIS LIST IS DEP-KIND-BLIND, AND THAT IS WHY THE `ed25519` ROWS ARE STILL HERE.
//
// `check_permitted_dependencies` walks `metadata.resolve.nodes[].deps` via `deps_of`
// without inspecting `dep_kinds`, so a package reachable from `rustc-main` through a
// *dev*-dependency is indistinguishable here from one the compiler actually links.
// `proptest` is the long-standing example; the `ed25519` family is the new one.
//
// Phase 1d moved `trust-proof-cert` off crates.io `ed25519-dalek` onto the Trust-owned
// `trust-ed25519` (a `package = ` rename in both workspace manifests). Measured on the
// resolve graph after that change, `ed25519-dalek 2.2.0` and its closure are reachable
// from `rustc-main` by exactly one path, and every edge in its tail is dev:
//
//     rustc_mir_transform -> trust-router -[dev]-> trust-proof-cert
//                                         -> trust-ed25519 -[dev]-> ed25519-dalek -> ...
//
// That dev-dependency is the differential acceptance gate
// (`crates/trust-ed25519/tests/differential_ed25519.rs`), which compares the Trust
// implementation against the incumbent and must keep naming it by explicit version.
//
// So: DO NOT DELETE these six as "retired by phase 1d". Measured — removing
// curve25519-dalek, curve25519-dalek-derive, der, ed25519, ed25519-dalek and
// fiat-crypto produces six *new* `Dependency for rustc-main not explicitly permitted`
// errors, because the deleted names are still in the kind-blind closure. (`der` is
// doubly wrong to remove: it arrives via `pkcs8`/`spki`, not directly.)
//
// They may be deleted only when the differential gate no longer dev-depends on the
// incumbent — i.e. when the incumbent leaves the tree entirely — or if `deps_of` is
// first taught to filter `dep_kinds`, which is a change to a shared upstream check
// with a far wider blast radius than this list.
#[rustfmt::skip]
const TRUST_PERMITTED_RUSTC_DEPENDENCIES: &[&str] = &[
    // tidy-alphabetical-start
    "ahash",
    "android_system_properties",
    "anyhow",
    "autocfg",
    "az",
    "base64ct",
    "beef",
    "bincode",
    "bincode_derive",
    "bit-set",
    "bit-vec",
    "bytemuck",
    "bytemuck_derive",
    "bytes",
    "camino",
    "carcara",
    "cargo-manifest",
    "cargo-platform",
    "cargo_metadata",
    "clap",
    "clap_builder",
    "clap_derive",
    "clap_lex",
    "const-oid",
    "crossbeam-channel",
    "crossbeam-queue",
    "curve25519-dalek",       // Trust: dev-only after phase 1d: kept because deps_of ignores dep_kinds (see note above)
    "curve25519-dalek-derive",// Trust: dev-only after phase 1d: kept because deps_of ignores dep_kinds (see note above)
    "der",                    // Trust: dev-only after phase 1d: kept because deps_of ignores dep_kinds (see note above); arrives via pkcs8/spki
    "ed25519",                // Trust: dev-only after phase 1d: kept because deps_of ignores dep_kinds (see note above)
    "ed25519-dalek",          // Trust: dev-only after phase 1d: kept because deps_of ignores dep_kinds (see note above)
    "fiat-crypto",            // Trust: dev-only after phase 1d: kept because deps_of ignores dep_kinds (see note above)
    "fixedbitset",
    "fs2",
    "gmp-mpfr-sys",
    "heck",
    "hmac",
    "home",
    "httparse",
    "hybrid-array",
    "inventory",
    "libm",
    "logos",
    "logos-codegen",
    "logos-derive",
    "lz4_flex",
    "mio",
    "num-bigint",
    "num-integer",
    "num-rational",
    "num-traits",
    "objc2-cloud-kit",
    "objc2-core-data",
    "objc2-core-foundation",
    "objc2-core-graphics",
    "objc2-core-image",
    "objc2-core-location",
    "objc2-core-text",
    "objc2-foundation",
    "objc2-io-surface",
    "objc2-quartz-core",
    "objc2-ui-kit",
    "objc2-user-notifications",
    "os_info",
    "percent-encoding",
    "pkcs8",
    "pkg-config",
    "proc-macro-crate",
    "proptest",
    "quick-error",
    "rayon",
    "rayon-core",
    "rmp",
    "rmp-serde",
    "rug",
    "rustc-std-workspace-core",
    "rustdoc-json-stable",
    "rustdoc-types",
    "rustversion",
    "rusty-fork",
    "semver",
    "serde_spanned",
    "sha1-checked",
    "sha2-asm",
    "signal-hook",
    "signal-hook-registry",
    "signature",
    "socket2",
    "spki",
    "strum",
    "strum_macros",
    "subtle",
    "tokio",
    "tokio-macros",
    "toml",
    "toml_datetime",
    "toml_edit",
    "toml_parser",
    "toml_write",
    "unarray",
    "unty",
    "utf8_iter",
    "virtue",
    "wait-timeout",
    "winapi",
    "winapi-i686-pc-windows-gnu",
    "winapi-x86_64-pc-windows-gnu",
    "winnow",
    "zeroize",
    "zmij",
    "zstd",
    "zstd-safe",
    "zstd-sys",
    // tidy-alphabetical-end
];

const PERMITTED_STDLIB_DEPS_LOCATION: ListLocation = location!(+2);

const PERMITTED_STDLIB_DEPENDENCIES: &[&str] = &[
    // tidy-alphabetical-start
    "addr2line",
    "adler2",
    "cc",
    "cfg-if",
    "compiler_builtins",
    "dlmalloc",
    "foldhash", // FIXME: only appears in Cargo.lock due to https://github.com/rust-lang/cargo/issues/10801
    "fortanix-sgx-abi",
    "getopts",
    "gimli",
    "hashbrown",
    "hermit-abi",
    "libc",
    "memchr",
    "miniz_oxide",
    "moto-rt",
    "object",
    "r-efi",
    "r-efi-alloc",
    "rand",
    "rand_core",
    "rand_xorshift",
    "rustc-demangle",
    "rustc-literal-escaper",
    "shlex",
    "trust-bignum", // Trust (I6): the bignum carrier runtime, shipped into the sysroot via library/sysroot
    "unwinding",
    "vex-sdk",
    "wasip1",
    "wasip2",
    "wasip3",
    "windows-link",
    "windows-sys@0.61.100", // Enforce the usage of our dummy windows-sys patch. Keep version in sync.
    "wit-bindgen",
    // tidy-alphabetical-end
];

/// Dependency checks.
///
/// `root` is path to the directory with the root `Cargo.toml` (for the workspace). `cargo` is path
/// to the cargo executable.
pub fn check(root: &Path, cargo: &Path, tidy_ctx: TidyCtx) {
    let mut check = tidy_ctx.start_check("deps");
    let bless = tidy_ctx.is_bless_enabled();

    let mut checked_runtime_licenses = false;

    check_proc_macro_dep_list(root, cargo, bless, &mut check);

    for &WorkspaceInfo { path, exceptions, crates_and_deps, submodules } in WORKSPACES {
        if has_missing_submodule(root, submodules, tidy_ctx.is_running_on_ci()) {
            continue;
        }

        if !root.join(path).join("Cargo.lock").exists() {
            check.error(format!("the `{path}` workspace doesn't have a Cargo.lock"));
            continue;
        }

        let mut cmd = cargo_metadata::MetadataCommand::new();
        cmd.cargo_path(cargo)
            .manifest_path(root.join(path).join("Cargo.toml"))
            .features(cargo_metadata::CargoOpt::AllFeatures)
            .other_options(vec!["--locked".to_owned()]);
        let metadata = t!(cmd.exec());

        // Check for packages which have been moved into a different workspace and not updated
        let absolute_root =
            if path == "." { root.to_path_buf() } else { t!(std::path::absolute(root.join(path))) };
        let absolute_root_real = t!(std::path::absolute(&metadata.workspace_root));
        if absolute_root_real != absolute_root {
            check.error(format!("{path} is part of another workspace ({} != {}), remove from `WORKSPACES` ({WORKSPACE_LOCATION})", absolute_root.display(), absolute_root_real.display()));
        }
        check_license_exceptions(&metadata, path, exceptions, &mut check);
        if let Some((crates, permitted_deps, location)) = crates_and_deps {
            let descr = crates.get(0).unwrap_or(&path);
            check_permitted_dependencies(
                &metadata,
                descr,
                permitted_deps,
                crates,
                location,
                &mut check,
            );
        }

        if path == "library" {
            check_runtime_license_exceptions(&metadata, &mut check);
            check_runtime_no_duplicate_dependencies(&metadata, &mut check);
            check_runtime_no_proc_macros(&metadata, &mut check);
            checked_runtime_licenses = true;
        }
    }

    // Sanity check to ensure we don't accidentally remove the workspace containing the runtime
    // crates.
    assert!(checked_runtime_licenses);
}

/// Ensure the list of proc-macro crate transitive dependencies is up to date
fn check_proc_macro_dep_list(root: &Path, cargo: &Path, bless: bool, check: &mut RunningCheck) {
    if std::env::var("RUSTC").is_err() {
        panic!("tidy must be run under bootstrap (./x test tidy), not as a standalone command");
    }
    let mut cmd = cargo_metadata::MetadataCommand::new();
    cmd.cargo_path(cargo)
        .manifest_path(root.join("Cargo.toml"))
        .features(cargo_metadata::CargoOpt::AllFeatures)
        .other_options(vec!["--locked".to_owned()]);
    let metadata = t!(cmd.exec());
    let is_proc_macro_pkg = |pkg: &Package| pkg.targets.iter().any(|target| target.is_proc_macro());

    let mut proc_macro_deps = HashSet::new();
    for pkg in metadata.packages.iter().filter(|pkg| is_proc_macro_pkg(pkg)) {
        deps_of(&metadata, &pkg.id, &mut proc_macro_deps);
    }
    // Remove the proc-macro crates themselves
    proc_macro_deps.retain(|pkg| !is_proc_macro_pkg(&metadata[pkg]));

    let proc_macro_deps: HashSet<_> =
        proc_macro_deps.into_iter().map(|dep| metadata[dep].name.as_ref()).collect();
    let expected = proc_macro_deps::CRATES.iter().copied().collect::<HashSet<_>>();

    let needs_blessing = proc_macro_deps.difference(&expected).next().is_some()
        || expected.difference(&proc_macro_deps).next().is_some();

    if needs_blessing && bless {
        let mut proc_macro_deps: Vec<_> = proc_macro_deps.into_iter().collect();
        proc_macro_deps.sort();
        let mut file = File::create(root.join("src/bootstrap/src/utils/proc_macro_deps.rs"))
            .expect("`proc_macro_deps` should exist");
        writeln!(
            &mut file,
            "/// Do not update manually - use `./x.py test tidy --bless`
/// Holds all direct and indirect dependencies of proc-macro crates in tree.
/// See <https://github.com/rust-lang/rust/issues/134863>
pub static CRATES: &[&str] = &[
    // tidy-alphabetical-start"
        )
        .unwrap();
        for dep in proc_macro_deps {
            writeln!(&mut file, "    {dep:?},").unwrap();
        }
        writeln!(
            &mut file,
            "    // tidy-alphabetical-end
];"
        )
        .unwrap();
    } else {
        let mut error_found = false;

        for missing in proc_macro_deps.difference(&expected) {
            error_found = true;
            check.error(format!(
                "proc-macro crate dependency `{missing}` is not registered in `src/bootstrap/src/utils/proc_macro_deps.rs`",
            ));
        }
        for extra in expected.difference(&proc_macro_deps) {
            error_found = true;
            check.error(format!(
                "`{extra}` is registered in `src/bootstrap/src/utils/proc_macro_deps.rs`, but is not a proc-macro crate dependency",
            ));
        }
        if error_found {
            check.message("Run `./x.py test tidy --bless` to regenerate the list");
        }
    }
}

/// Used to skip a check if a submodule is not checked out, and not in a CI environment.
///
/// This helps prevent enforcing developers to fetch submodules for tidy.
pub fn has_missing_submodule(root: &Path, submodules: &[&str], is_ci: bool) -> bool {
    !is_ci
        && submodules.iter().any(|submodule| {
            let path = root.join(submodule);
            !path.exists()
            // If the directory is empty, we can consider it as an uninitialized submodule.
            || read_dir(path).unwrap().next().is_none()
        })
}

/// Check that all licenses of runtime dependencies are in the valid list in `LICENSES`.
///
/// Unlike for tools we don't allow exceptions to the `LICENSES` list for the runtime with the sole
/// exception of `fortanix-sgx-abi` which is only used on x86_64-fortanix-unknown-sgx.
fn check_runtime_license_exceptions(metadata: &Metadata, check: &mut RunningCheck) {
    for pkg in &metadata.packages {
        if pkg.source.is_none() {
            // No need to check local packages.
            continue;
        }
        let license = match &pkg.license {
            Some(license) => license,
            None => {
                check
                    .error(format!("dependency `{}` does not define a license expression", pkg.id));
                continue;
            }
        };
        if !LICENSES.contains(&license.as_str()) {
            // This is a specific exception because SGX is considered "third party".
            // See https://github.com/rust-lang/rust/issues/62620 for more.
            // In general, these should never be added and this exception
            // should not be taken as precedent for any new target.
            if *pkg.name == "fortanix-sgx-abi" && pkg.license.as_deref() == Some("MPL-2.0") {
                continue;
            }

            check.error(format!("invalid license `{}` in `{}`", license, pkg.id));
        }
    }
}

/// Check that all licenses of tool dependencies are in the valid list in `LICENSES`.
///
/// Packages listed in `exceptions` are allowed for tools.
fn check_license_exceptions(
    metadata: &Metadata,
    workspace: &str,
    exceptions: &[(&str, &str)],
    check: &mut RunningCheck,
) {
    // Validate the EXCEPTIONS list hasn't changed.
    for (name, license) in exceptions {
        // Check that the package actually exists.
        if !metadata.packages.iter().any(|p| *p.name == *name) {
            check.error(format!(
                "could not find exception package `{name}` in workspace `{workspace}`\n\
                Remove from EXCEPTIONS list if it is no longer used.",
            ));
        }
        // Check that the license hasn't changed.
        for pkg in metadata.packages.iter().filter(|p| *p.name == *name) {
            match &pkg.license {
                None => {
                    check.error(format!(
                        "dependency exception `{}` in workspace `{workspace}` does not declare a license expression",
                        pkg.id
                    ));
                }
                Some(pkg_license) => {
                    if pkg_license.as_str() != *license {
                        check.error(format!(r#"dependency exception `{name}` license in workspace `{workspace}` has changed
    previously `{license}` now `{pkg_license}`
    update EXCEPTIONS for the new license
"#));
                    }
                }
            }
        }
        if LICENSES.contains(license) || LICENSES_TOOLS.contains(license) {
            check.error(format!(
                "dependency exception `{name}` is not necessary. `{license}` is an allowed license"
            ));
        }
    }

    let exception_names: Vec<_> = exceptions.iter().map(|(name, _license)| *name).collect();

    // Check if any package does not have a valid license.
    for pkg in &metadata.packages {
        if pkg.source.is_none() {
            // No need to check local packages.
            continue;
        }
        if exception_names.contains(&pkg.name.as_str()) {
            continue;
        }
        let license = match &pkg.license {
            Some(license) => license,
            None => {
                check.error(format!(
                    "dependency `{}` in workspace `{workspace}` does not define a license expression",
                    pkg.id
                ));
                continue;
            }
        };
        if !LICENSES.contains(&license.as_str()) && !LICENSES_TOOLS.contains(&license.as_str()) {
            check.error(format!(
                "invalid license `{}` for package `{}` in workspace `{workspace}`",
                license, pkg.id
            ));
        }
    }
}

fn check_runtime_no_duplicate_dependencies(metadata: &Metadata, check: &mut RunningCheck) {
    let mut seen_pkgs = HashSet::new();
    for pkg in &metadata.packages {
        if pkg.source.is_none() {
            continue;
        }

        if !seen_pkgs.insert(&*pkg.name) {
            check.error(format!(
                "duplicate package `{}` is not allowed for the standard library",
                pkg.name
            ));
        }
    }
}

fn check_runtime_no_proc_macros(metadata: &Metadata, check: &mut RunningCheck) {
    for pkg in &metadata.packages {
        if pkg.targets.iter().any(|target| target.is_proc_macro()) {
            check.error(format!(
                "proc macro `{}` is not allowed as standard library dependency.\n\
                Using proc macros in the standard library would break cross-compilation \
                as proc-macros don't get shipped for the host tuple.",
                pkg.name
            ));
        }
    }
}

/// Checks the dependency of `restricted_dependency_crates` at the given path. Changes `bad` to
/// `true` if a check failed.
///
/// Specifically, this checks that the dependencies are on the `permitted_dependencies`.
fn check_permitted_dependencies(
    metadata: &Metadata,
    descr: &str,
    permitted_dependencies: &[&'static str],
    restricted_dependency_crates: &[&'static str],
    permitted_location: ListLocation,
    check: &mut RunningCheck,
) {
    let mut has_permitted_dep_error = false;
    // Trust: two additive lists, kept apart on purpose — verifier-stack drift
    // (ours) and upstream drift ahead of the merge base (not ours).
    let trust_permitted_dependencies: Vec<&'static str> = if descr == "rustc-main" {
        TRUST_PERMITTED_RUSTC_DEPENDENCIES
            .iter()
            .chain(TRUST_UPSTREAM_DRIFT_RUSTC_DEPENDENCIES.iter())
            .copied()
            .collect()
    } else {
        Vec::new()
    };
    let mut deps = HashSet::new();
    for to_check in restricted_dependency_crates {
        let to_check = pkg_from_name(metadata, to_check);
        deps_of(metadata, &to_check.id, &mut deps);
    }

    fn compare(pkg: &Package, permitted: &str) -> bool {
        if let Some((name, version)) = permitted.split_once("@") {
            let Ok(version) = Version::parse(version) else {
                return false;
            };
            *pkg.name == name && pkg.version == version
        } else {
            *pkg.name == permitted
        }
    }
    // Trust: entries upstream still lists that Trust's own resolution has moved
    // past. See `TRUST_RETIRED_UPSTREAM_RUSTC_DEPENDENCIES` for why this is a
    // separate list rather than a deletion from the upstream array.
    let trust_retired = if descr == "rustc-main" {
        TRUST_RETIRED_UPSTREAM_RUSTC_DEPENDENCIES
    } else {
        &[] as &[&'static str]
    };

    // Check that the PERMITTED_DEPENDENCIES does not have unused entries.
    for permitted in permitted_dependencies.iter().chain(trust_permitted_dependencies.iter()) {
        if !deps.iter().any(|dep_id| compare(pkg_from_id(metadata, dep_id), permitted)) {
            // Trust: a retired entry is EXPECTED to be absent, so it is not an
            // error — but it is still reported below if it comes back, so a
            // retirement can never quietly outlive its reason.
            if trust_retired.contains(permitted) {
                continue;
            }
            check.error(format!(
                "could not find allowed package `{permitted}`\n\
                Remove from PERMITTED_DEPENDENCIES list if it is no longer used.",
            ));
            has_permitted_dep_error = true;
        }
    }

    // Trust: the retirement list is itself gated. If a retired dependency is
    // back in the graph, the upstream row is live again and the retirement is
    // stale — that must fail, exactly as an expired pin waiver does, or the
    // list becomes a place where a real re-introduced dependency hides.
    for retired in trust_retired {
        if deps.iter().any(|dep_id| compare(pkg_from_id(metadata, dep_id), retired)) {
            check.error(format!(
                "`{retired}` is in the dependency graph again, but it is still listed in \
                 TRUST_RETIRED_UPSTREAM_RUSTC_DEPENDENCIES.\n\
                Delete that row: upstream's PERMITTED_RUSTC_DEPENDENCIES entry covers it once more.",
            ));
            has_permitted_dep_error = true;
        }
    }

    // Get in a convenient form.
    let permitted_dependencies: HashMap<_, _> = permitted_dependencies
        .iter()
        .chain(trust_permitted_dependencies.iter())
        .map(|s| {
            if let Some((name, version)) = s.split_once('@') {
                (name, Version::parse(version).ok())
            } else {
                (*s, None)
            }
        })
        .collect();

    for dep in deps {
        let dep = pkg_from_id(metadata, dep);
        // If this path is in-tree, we don't require it to be explicitly permitted.
        if dep.source.is_some() {
            let is_eq = if let Some(version) = permitted_dependencies.get(dep.name.as_str()) {
                if let Some(version) = version { version == &dep.version } else { true }
            } else {
                false
            };
            if !is_eq {
                check.error(format!("Dependency for {descr} not explicitly permitted: {}", dep.id));
                has_permitted_dep_error = true;
            }
        }
    }

    if has_permitted_dep_error {
        eprintln!("Go to `{}:{}` for the list.", permitted_location.path, permitted_location.line);
    }
}

/// Finds a package with the given name.
fn pkg_from_name<'a>(metadata: &'a Metadata, name: &'static str) -> &'a Package {
    let mut i = metadata.packages.iter().filter(|p| *p.name == name);
    let result =
        i.next().unwrap_or_else(|| panic!("could not find package `{name}` in package list"));
    assert!(i.next().is_none(), "more than one package found for `{name}`");
    result
}

fn pkg_from_id<'a>(metadata: &'a Metadata, id: &PackageId) -> &'a Package {
    metadata.packages.iter().find(|p| &p.id == id).unwrap()
}

/// Recursively find all dependencies.
fn deps_of<'a>(metadata: &'a Metadata, pkg_id: &'a PackageId, result: &mut HashSet<&'a PackageId>) {
    if !result.insert(pkg_id) {
        return;
    }
    let node = metadata
        .resolve
        .as_ref()
        .unwrap()
        .nodes
        .iter()
        .find(|n| &n.id == pkg_id)
        .unwrap_or_else(|| panic!("could not find `{pkg_id}` in resolve"));
    for dep in &node.deps {
        deps_of(metadata, &dep.pkg, result);
    }
}
