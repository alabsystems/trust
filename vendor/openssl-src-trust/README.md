# Maintained OpenSSL Rust driver

This is the Rust driver from `openssl-src 300.6.1+3.6.3`, with explicit owned
jobserver transport for Trust's SP-1 descriptor-stripping process spawn. The
original MIT and Apache licenses and upstream README are retained. No OpenSSL C
source is copied or changed here: `source_dir()` and `version()` delegate to the
exact registry package `openssl-src =300.6.1`, whose `.crate` SHA-256 is
`46eb8fb9fb3b61ce1c0f8a026c4c1a0714d3a9e138e7fbde78753ce2babc3846`.

The distinct package name `trust-openssl-src` avoids a registry patch depending
on itself. `openssl-sys` aliases this package as `openssl-src`, preserving the
Rust API and original feature names. The driver accepts an optional owned
`jobserver_utils::Jobserver` captured by the caller at startup. It never imports
ambient descriptor numbers. All GNU make phases (`depend`, `build_libs`, and
`install_dev`) use the same capability, with make flags derived from its newly
owned endpoints. Without an explicit capability the make commands clear all
three inherited make-flag variables and run serially. The MSVC nmake path is
unchanged. The shared transport currently requires Rust 1.85 or later.

The `test-support` feature builds a native child process fixture for the standard
Rust integration tests. It is disabled for production. The Unix tests exercise
the actual Trust std spawn behavior and the machine's GNU make, including
recursive shared-token limits, successful and failed recipe token restoration,
unrelated descriptor stripping, and malformed startup authority. They do not
establish compiler verification or product proof grades.

The native recipe boundary now copies the pinned C source through checked file
handles, hashes the exact copied bytes, and freezes the environment for each
Configure/make invocation while preserving its owned jobserver overrides.
`Build::native_recipe()` exposes a diagnostic observation of a successful build.
This observation is not cache authority and still declines whole-archive reuse.
An absent or invalid `SOURCE_DATE_EPOCH` remains a whole-invocation clock blocker;
no timestamp is silently substituted.

On the qualified native aarch64 macOS profile, the maintained producer now uses
Clang's C action cache. Configure, generators, make, dependency scanning and
preprocessing still execute. A cache hit avoids native code generation and
recreates the exact object bytes. The namespace binds the complete selected
compiler image, checked system-runtime closure and effective native environment;
Clang keys the fresh dependency tree and actual compiler flags. Foreign Rust
unit/agent metadata is removed from the actual native recipe. Custom compiler,
generator, archiver, cross configuration and unsupported native profiles keep
the original compilation path. A physically stable native cwd/install prefix
allows different Rust wrapper units to reuse identical native actions. Newly
installed outputs are completely checked and copied back into each Rust unit's
output tree; Targo's normal build-script fingerprint/output checks remain.

The initial compiler profile is the exact qualified Apple CLT Clang21 image at
its platform installation path. Other images/locations and unqualified flags
(including plugins, LTO and external assemblers) decline reuse. The system
loader image is also byte-bound. These restrictions preserve ordinary supported
compilation while additional native profiles await their own qualification.

The native store has a nonblocking exclusive lease retained by actual make and
Clang descendants. Its complete closed content tree is checked before reuse;
kernel-reported sparse zero extents are bound by logical range and all data
extent bytes are read. Corrupt, missing or redirected stores are quarantined.
The local digest assumes trusted cache writers: it is not authentication against
a same-user process that rewrites both data and digest. Runtime selection uses
the operating system's mapped cache and Apple's content-derived122-bit UUID,
with independent full SHA256 content identities. This native TCB boundary is
not Trust proof, formal compiler verification or a stronger product grade.
