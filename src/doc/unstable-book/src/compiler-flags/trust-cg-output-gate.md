# `trust-cg-output-gate`

The tracking issue for this feature is internal to Trust.

------------------------

The `-Z trust-cg-output-gate=<mode>` option selects the trust-cg
output-preservation policy. It accepts exactly:

- `strict` (default): emit only output carrying an accepted machine-checked
  preservation proof.
- `allow-unknown`: reject known refutations, but let an unsupported
  output-preservation shape through and record it.
- `off`: explicitly disable the gate.

A **refuted** verdict — a detected miscompile — is fatal under `strict` and
`allow-unknown` alike. That is the gate's core guarantee, and only `off` bypasses
it.

For an in-scope strict batteries-on compilation, the compiler strengthens
`allow-unknown` to `strict` and rejects `off` outright. The strengthening happens
in two places on purpose: the driver canonicalizes the stored value before any
hash is taken, so one compilation cannot carry two tracked identities, and the
trust-cg backend independently derives the same effective mode from the session.
A custom driver that skips the first cannot bypass the second.

Strict mode also refuses output paths that cannot yet bind a machine-checked
proof to the exact shipped bytes: non-native-architecture cross-compiles, Wasm
fast-path modules, allocator shim objects, name/cardinality mismatches, and any
regular object without a matching gate result. `allow-unknown` may emit those
unsupported shapes, but never a known refutation.

This option changes whether machine code may be emitted, so it participates in
rustc dependency and crate hashing. Ambient environment is deliberately not
consulted: a policy that selects generated machine code must not be settable
through untracked process state.
