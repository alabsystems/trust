# `trust-ir-flip`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-ir-flip` (default: **on**) allows the direct Trust-IR frontend to
supply the MIR that codegen consumes, for bodies where it has already earned it.

The gate is a differential proof, not a preference. A body qualifies only if its
THIR-to-Trust-IR lowering was proven equivalent to the freshly built MIR at the
`mir_built` hook (verdict `DerivedAgreed`). At the `optimized_mir` seam — chosen
because borrowck and CTFE must keep running on the built sibling — the derived
body is re-advanced through the same pass pipeline the built body went through,
then codegen consumes MIR *re-derived from the Trust-IR module*.

Turning it off with `-Ztrust-ir-flip=no` keeps the built MIR everywhere. That is
also what happens automatically for any body without a recorded green module, and
for any structural rejection, pipeline error, or pass panic — those fall back to
the retained built body and log a loud warning. The fallback preserves ordinary
compilation semantics; it is *not* evidence that the body compiled from Trust-IR,
and direct-lane coverage counts only the successful flips.

This option is tracked into the crate hash, because a flip can replace the MIR
codegen and CTFE observe: two builds that differ here must not share an artifact
identity.

Observability: one `info!` line per flipped body — grep for
`compiled from trust-ir` — with a per-Session running tally, and a `warn!` per
fallback. Target `rustc_mir_transform::trust_ir_flip` (for example
`RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info`).

The registry is populated when `mir_built` actually executes, so a green-cached
incremental build contributes no direct-Trust-IR coverage. Run equivalence probes
non-incrementally.
