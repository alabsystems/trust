# Inclusive iterator yield regression

`loop_off_by_one.json` is the real extracted body of
`sentinel_loop_off_by_one_must_not_prove` from the unchanged Clean
`tests/trust_verify/vacuity_sentinel.rs` (source SHA-256
`857371e229881c7e607b1eec97e7290025276fe9afd0af8d6ba82f36ca0a56f8`).
The qualified Trust compiler built from
`d9f608b9188f99ab87589e5b91487321ff039b6c` captured it with
`--edition 2021 --crate-type lib -Ztrust-verify=on -Ztrust-policy=advisory
-Ztrust-dump=mir-only:<dir>`. Extraction exits zero; verification is skipped
in this diagnostic mode and supplies no proof evidence.

Raw capture SHA-256:
`f3cc785b08ee3e1771bf521d5c97bd6468bf35b1a68c7e4b421794c59e828eed`.
Only the capture directory prefix in source-span `file` values is replaced
with the sanctioned `<dump-root>/` placeholder. No body, type, identity,
contract, location, or obligation content is changed.

The original loop is `for i in 0..=a.len()` over `a: &[u8]`, with
`a[i]` at line135,column31. The inclusive endpoint must remain a possible
out-of-bounds value. The generator must retain its real recorded
`SliceBoundsCheck`; an unrecorded alarm or an unsupported row cannot
substitute for that obligation.

## Counterexample controls

`programs.rs` is the unchanged source for the four named control captures.
The same qualified D9 compiler captured them with the flags above and
`--crate-name inclusive_yield_controls`. Only span directory prefixes are
normalized. Their source SHA-256 is
`59f4beb37674d23ec704d4843a8a2f980e3a92e1e4fc07d2cc13308bae26c828`.

The first-yield and `step_by(2)` functions over a one-byte array always read
index0. The host regression executes every possible byte input. Bounds on
the original yield set do not establish which value a particular call yields;
a model choosing index1 must be withheld as an executable counterexample.
The two-byte positive control must retain its actual bounds row and prove.
The exclusive first-yield source is retained as a Rust execution control;
no change to exclusive-range counterexample semantics is claimed here.

Raw capture hashes:

- `inclusive_step_skips_past_end`: `66a5bd1827f45b50732766594967e6ec6013378ff9b263c865ac37e5d17cac41`
- `inclusive_safe_bound`: `cad04f32299f08133bcab571c27a601efa6862b179bfe24013f19f14ec0b6c46`
- `inclusive_first_yield_returns`: `5caec282a4e38a8c6803f426e1a05d31dc0117275f6aac0e2a75e4a059caceb4`
- `exclusive_first_yield_returns`: `165a5c74d83d8f0a762e942e20ae912ed364adb81b4ea3b45b447fc8124e49c5`
