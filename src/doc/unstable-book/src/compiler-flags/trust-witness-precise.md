# `trust-witness-precise`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-witness-precise` (default: off) is an **experimental shadow-mint
parity measurement** of the precise per-referenced-def typeck-witness key. It is
never trusted.

It is a separate option rather than a fourth `-Z trust-witness` lane because it
selects the witness *key*, not which lane runs. Mint and replay both switch to
the precise key — which hits without depending on the whole-crate SVH, and so
survives the edit loop — but a replayed candidate under it is byte-diffed
against real typeck and the result **real typeck produced is always the one
returned**. The flag exists to measure the precise key's divergence rate, not to
make compiles faster.

Folding it into the lane domain would either delete that parity harness or imply
the key is shippable. It is not: it stays an opt-in shadow-mint measurement until
the A1–A3 negative-context recorder lands. See
`docs/design/2026-07-23-a1a3-edit-loop-key-disposition.md`.

Like `-Z trust-witness`, this option is untracked, so a no-flag lane stays
byte-identical to an upstream compile.
