# `trust-verify-target-spec-sha256`

The tracking issue for this feature is internal to Trust.

------------------------

This is a reserved Targo-to-compiler protocol field. Do not set it by hand.

`-Z trust-verify-target-spec-sha256=<hex>` binds a session-scoped custom JSON
target to the exact bytes `trustc` parsed. The compiler hashes the JSON it
actually read and rejects the compilation if the digest disagrees with Cargo's.

The binding closes a hole that only appears under an authenticated session:

- Supplying the digest without an explicit custom JSON `--target` is an error.
- An authenticated session **with** a custom JSON target and **without** the
  digest is also an error — Cargo must bind the target's contents.
- An authenticated session naming a non-built-in target *tuple* is rejected
  outright. Such a name is resolved after this boundary by a search over
  `RUST_TARGET_PATH` and the sysroot's `lib/rustlib/<name>/target.json`
  fallback; only rustc observes which file wins, so no proof inventory can bind
  its origin or its bytes. Pass an explicit `.json` target instead.

The option is untracked: it authenticates an input rather than selecting one.
