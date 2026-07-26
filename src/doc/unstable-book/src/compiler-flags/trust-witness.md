# Trust typeck-witness lane

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-witness=auto|off|mint:<dir>|replay:<dir>` selects the typeck-witness
lane and the store it uses. A witness records a typeck root's result so a later
compile can replay and *check* it instead of re-elaborating from scratch.

Lane and store are one option because a store directory is meaningless without a
lane, and the managed lane owns its own store: with separate switches a caller
could name a mint directory while the managed lane silently replayed from a
different one.

## `auto` (default)

Mint and replay both run against `<out-dir>/trust-witness`, router-gated to
bodies whose fresh-typeck cost clears the fixed decode + check floor (small
bodies fall straight through to ordinary typeck). Inert without an explicit
`--out-dir`, so ad-hoc single-file compiles are unaffected, and inert under
incremental compilation, `-Z unpretty`, and `-Z validate-mir`.

## `off`

Neither lane runs. Output is byte-identical to an upstream compile.

## `mint:<dir>`

Mint every eligible root into `<dir>`; replay does not run. The router does not
apply — measurement and deterministic harnesses depend on minting every root.
The store is mandatory: defaulting it to the managed store would overwrite the
managed lane's own evidence.

## `replay:<dir>`

Replay every stored root from `<dir>`; mint does not run. A replayed candidate is
re-checked before it is used; a miss or a rejection falls back to ordinary
typeck, so a stale or corrupt store costs time, never correctness.

## Key selection

`-Z trust-witness-precise` is a separate option, not a fourth lane. It switches
mint and replay to the precise per-referenced-def key, and a replayed candidate
under it is byte-diffed against real typeck and **never trusted** — real
typeck's result is always the one returned. It exists to measure that key's
divergence rate. It is not shippable as a trusted key until the A1–A3
negative-context recorder lands; see
`docs/design/2026-07-23-a1a3-edit-loop-key-disposition.md`.
