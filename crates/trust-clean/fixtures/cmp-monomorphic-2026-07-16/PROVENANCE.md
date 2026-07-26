# `cmp-monomorphic-2026-07-16` provenance

This focused observational corpus contains six foreign concrete `core::cmp`
`min`/`max` MIR bodies and five hand-authored controls. The hardened hook was
run locally after the merge; `GENERATION.txt` binds the source files, launcher,
dynamically loaded rustc driver, complete target-libdir byte manifest, analyzer
binaries, census budget, and selected body inventory.

`regenerate.sh` compiles the sibling intent crate with the opt-in W16 hook,
prints the selected compiler's version and SHA-256, rejects an empty harvest,
requires exactly six foreign cmp bodies, and requires all six exact bodies to
classify `FULLY_FAITHFUL` through the scalar sentinel-select/tail-call lanes.
The four direct leaves are shape-faithful over a total-but-uninterpreted guard;
the two forwarders require certified callees. This does not establish numeric
minimum/maximum semantics. Future regenerations must update `GENERATION.txt`
rather than relying on a path or version string alone.

The receipt makes the listed inputs and outputs identity-bound and independently
byte-checkable; it is not a hermetic-build or proof-authority claim. The
controls demonstrate recognizable concrete shapes; they do not transfer a
verdict to the real library bodies. In particular, `ctl_clamp_i32` remains a
`SHAPE_GAP`/`W-NESTED-SELECT` input. No file in this directory independently
authorizes a proof or a `FULLY_FAITHFUL` classification.
