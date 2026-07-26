# `trust-ir-lower`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-ir-lower` also runs the direct source (THIR) to Trust-IR frontend and
its differential against the freshly built MIR.

The option is **tri-state** — `-Ztrust-ir-lower`, `-Ztrust-ir-lower=no`, or
unset — because no single static default is true of it:

- Under batteries-on verification the direct frontend is not optional. It always
  runs, and an explicit value there changes nothing.
- Under the explicit `-Z trust-verify=off` compatibility lane the decision
  belongs to the caller, and the default is **off** so the ordinary Rust path
  stays clear.

Unset therefore means *follow verification*. A plain `bool` could only declare
one of those two answers and would be a lie in the other lane.

The driver resolves the request into the field before any `Session` or dependency
hash exists, so `trustc x.rs`, `trustc -Ztrust-ir-lower x.rs`, and
`trustc -Ztrust-ir-lower=no x.rs` under verification are **one** tracked identity
rather than three hashes for one compilation. Nothing downstream ever observes an
unresolved request.

Related options: `-Z trust-dump=ir:<dir>` (or the preferred `--emit=trust-ir`)
publishes the lowered artifacts, and `-Z trust-ir-flip` decides whether the
lowered module may go on to supply codegen MIR.
