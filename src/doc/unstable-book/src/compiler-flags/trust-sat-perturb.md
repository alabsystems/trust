# `trust-sat-perturb`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-sat-perturb=<class>` is a burn-in **negative control**: it
deliberately corrupts one shim lowering class so that the Trust-IR flip's
differential comparator *must* reject the result. A run in which the comparator
accepts a perturbed lowering is a failed control — it means the differential gate
has no teeth.

Accepted classes: `enum-reshape`, `enum-case-value`, `enum-ctor`,
`enum-disc-index`, `switch-map`, `enum-payload`. Anything else is rejected.

It requires **both** `-Z trust-verify=off` and `-Z trust-ir-lower`. Requiring
the first keeps a deliberately corrupted lowering out of every evidence policy;
requiring the second keeps the request from looking valid while being inert
because direct lowering is not running at all.

The option is tracked into the crate hash for the same reason
`-Z trust-ir-flip` is: an uncaught perturbation changes emitted MIR, so
perturbed incremental artifacts must never share an identity with clean ones.

This flag replaced the retired `TRUST_*_PERTURB` environment hooks. Ambient
environment variables are banned inputs to a Trust compilation precisely because
a mutation knob that can be set invisibly is a mutation knob that can be
forgotten. Every one of those names is listed in
`LEGACY_TRUST_SEMANTIC_ENV_VARS`, so a Trust-semantics compilation is a fatal
error if one is set rather than silently running perturbed.
