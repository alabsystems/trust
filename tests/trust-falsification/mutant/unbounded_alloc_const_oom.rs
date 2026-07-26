#![crate_type = "lib"]
// DEFAULT-ON nn host-OOM repro (#nia-oom). A CONSTANT bulk heap allocation whose
// element count folds to `1 << 28` (== UNBOUNDED_ALLOC_ELEM_CEILING), i.e. exactly
// the `vec![None; byte_len]` / `Vec::with_capacity(1<<28)` shape that OOM-killed the
// host. trust-vcgen emits an `UnboundedAllocation` VC `Ge(count, 1<<28)`; the count
// folds to the ground constant `1<<28`, so `alloc_over_ceiling_forced` flags the
// VIOLATION ATOM as forced-true. With batteries-on verification (no activation flag),
// `escalate_refuted_l0_safety_counterexamples` turns this into a HARD ERROR with a
// counterexample allocation size (exit 1) — it is NOT a mere warning and does NOT
// need an extra escalation flag. Opt out only with `-Z trust-verify=off`.
//
// Contrast mutant/bounded_alloc.rs: there the count is the SYMBOLIC parameter `n`,
// which does not fold to a constant and therefore requires solver refutation rather than this
// forced-true fast path. Both fixtures fail under the default strict policy.
pub fn nn_alloc_oom() -> Vec<Option<u8>> {
    vec![None; 1 << 28]
}
