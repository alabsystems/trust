# `trust-no-r1`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-no-r1` (default: off) disables kernel-certified whole-program R1
caller-propagation strengthening.

R1 strengthens an obligation using facts about *every* caller in the crate: a
precondition that no reachable call site can violate is discharged by that closed
caller set. The strengthened proof is admitted only after the kernel replays both
the strengthened proof and each caller's discharge proof, and the closed-world
claim itself — that the enumerated caller set really is complete — is what stays
trusted; see the `CallerPropagation` row in `docs/TCB.md`.

This flag exists as the negative control for that lane. It returns before the
crate-wide call scan and before any solver is constructed, so running with and
without it is a cheap A/B on whether a given verdict depended on R1 at all.

Setting it can only *lose* proofs, never gain them. It is dependency-tracked
because it changes which obligations resolve.
