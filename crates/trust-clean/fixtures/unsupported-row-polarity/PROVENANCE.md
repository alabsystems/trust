# unsupported-row-polarity — provenance

One function, `vec_range_index_with_ensures`, extracted verbatim from
`unsupported_row_polarity_fx.rs` in this directory. Nothing here is
hand-written: the JSON is the compiler's own MIR extraction.

```sh
trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
       -Ztrust-dump=mir-only:<dir> unsupported_row_polarity_fx.rs
```

with the stage2 `trustc` at `build/aarch64-apple-darwin/stage2/bin/trustc`.

## Why this fixture exists

`&v[..end]` over an owned `Vec` hands `trust_vcgen`'s `panic_calls` soft-len arm
a slice length it cannot derive. That arm DECLINES the bounds obligation with an
`UnsupportedMir { kind: "SliceBoundsCheck" }` row — the honest reading is
"undecided", and on the compiler path `discharge_body_vcs` preclassifies it to
`Unknown` by kind and never dispatches it.

`trust_clean::whole_program`'s kernel gates do not preclassify by kind. They
select rows by `proof_level()`, and `UnsupportedMir::proof_level()` is
`L0Safety`, so the declined row's `formula` goes straight to
`vc_refute::check_refute_vc` and `RefutedModulo3` is read as DISCHARGED. That
made the row's violation formula load-bearing for soundness: `Bool(false)` is
UNSAT, so the gate discharged an obligation nothing had decided.

The `ensures result < 8` clause is there so the REST of the gate passes — it is
kernel-checked modulo 3 — leaving the declined safety row as the only thing the
verdict turns on.

The body PANICS for every `end > v.len()`; a stock-rustc build of the same body
faults on 33 of 54 sampled `(v.len(), end)` pairs, the first at
`(v.len(), end) = (0, 1)`. So a `Certified` verdict on this function is a false
proof, not a conservative one.

`tests/unsupported_row_polarity_gate.rs` pins that it is NOT certified.
