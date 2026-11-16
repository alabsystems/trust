# Maintained openssl-sys caller patch

Foreign Rust source: `openssl-sys 0.9.117`, upstream registry archive SHA-256
`b47e7e6bb2c38cd930d25a23b40fa52e068c10e85f3e03a7f5ba5aaca5713695`.
The original MIT license, FFI source, feature names, optional SSL implementations,
and original manifest are retained. This directory contains no OpenSSL C bundle.

Trust changes only the vendored build-driver boundary: at `main` startup, before
probes, files or output, capture the checked inherited jobserver. Refuse invalid
advertised authority. Pass the owned optional capability through `find_openssl`
and `find_vendored` into the maintained Rust driver. `OPENSSL_NO_VENDOR` still
selects the original system-library path. Non-vendored builds have no new
scheduling dependency. The driver is a distinct package, locally aliased as
`openssl-src`; its exact registry source dependency has no patch cycle. Rust
1.85 is required by the shared owned transport, replacing upstream's 1.80 floor.

Targo's workspace applies this `openssl-sys` patch explicitly and pins its
version in the vendored feature so a later lock update cannot silently select
an unpatched newer caller. The separate
driver and caller locks support native isolated controls without changing a
live registry, using a Make launcher, or rebuilding the compiler. The `vendored`
integration test links the actual built OpenSSL 3.6.3 archive and checks SHA-256
against a known answer. These are unverified build/transport controls.
