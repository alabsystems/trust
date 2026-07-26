# mass-harvest2-2026-07-21 — wave 2 through the 21 landed lanes (+86 FF) + TWO EXTRACTION DISCOVERIES

Headline: result-widths SWEPT 56/68 (unwrap_or × 14 (T,E) combos + is_ok/is_err
× 6 + wrappers — the payload/discr lanes are width- and error-type-generic).
bool-ops 3 (BitAnd/Or/Xor leaves).

## DISCOVERY 1 — THE SENTINEL WAS DELIBERATELY NEUTERED (soundness hardening, capability cost)
Fresh stage2 dumps no longer carry __trust_total_clone: apply_total_clone_sentinel
is now the identity (real impl quarantined #[cfg(any())], convert.rs ~5799) —
because #[automatically_derived] is proc-macro-SPELLABLE and cannot authenticate
rustc's builtin derive: an obligation-free sentinel on a forgeable attribute was
a false-total channel. CORRECT fail-closed hardening. COST: the sentinel-select
min/max lane + derived-eq lanes decline on ALL FRESH dumps (28/34 of the
twocall-chain family blocked; committed old corpora unaffected). SOUND REPAIR
(the ratified pattern): def-path-PINNED totality for the exact std primitive
comparison family (core::cmp::impls <iN/uN as PartialOrd>::lt/le/gt/ge + Ord::cmp
— total by inspection, unforgeable paths), mirroring PinnedTotalCallable.

## DISCOVERY 2 — W16 SKIPS CONCRETE FOREIGN FNS
Non-generic libcore fns (Ordering::reverse/then, i32::cmp, the saturating_* method
leaves) are NEVER dumped (!requires_monomorphization skip in the W16 hook) —
the ordering family (1/17) + INTRINSIC_CALLEE_NEVER_DUMPED clusters block on
absent callee bodies. Fix: extend the hook to also dump reachable concrete
foreign fns with MIR available (fail-closed unchanged).

## Other named gaps
- Payload-bearing enum Aggregate CONSTRUCTION as fn result (ok()/err(), Some(x)
  returns) — outside every lane's grammar; nearest = the discriminant-switch
  ADT-return lane + payload moves + drop ladder.
- bool UnOp::Not straight-line model (1-line gap).
- then_with generic mono body (branch+Drop shape) + closure-aggregate cascade.
