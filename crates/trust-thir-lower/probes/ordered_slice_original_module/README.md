# Original ordered-slice module observer

Build the changed compiler with normal bootstrap, then compile
`tests/run-make/trust-thir-ordered-slice/patterns.rs` using that compiler with
`--crate-name=ordered_slice_patterns --crate-type=lib --edition=2021
--emit=metadata -Coverflow-checks=off -Ztrust-verify=off -Ztrust-ir-lower
-Ztrust-dump=ir:<output-directory>`. Run this standalone probe with genuine
`targo --unverified run --locked --manifest-path
crates/trust-thir-lower/probes/ordered_slice_original_module/Cargo.toml --
<output-directory>/ordered_slice_patterns.trust-ir.bin`. Use the machine-wide
`build-slot` for the compiler build and probe compilation.

The probe validates and roundtrips the original complete binary module, then
executes eleven original scalar-input functions across twelve asymmetric boundary
inputs: all 132 executions are required for qualification. The original eight
functions and 96 executions remain. All storage and payload operations come from the compiler output. It
requires zero host calls and checks overlapping source-order choices, word/byte stride, empty-slice
branching and zero-sized rest metadata and reference-result dereference. This is empirical regression evidence,
not a universal semantics theorem, source proof or production codegen claim.

Original functions are selected uniquely by the decoded source display path
(with the original name fallback for records without one); `Function.name` is
the actual link symbol and may be mangled. Display paths are observation
selectors only. They do not authenticate source semantics or confer authority.

Qualification requires both the fixture's 24 supported bodies / 12 retained
refusals and this complete-module observer's 132 actual executions. The internal
MIR differential currently records zero samples for exactly `execute_rest`,
`execute_zst`, `execute_zst_repeat` and `execute_unit_array_effects`, with a live
`Inst::Undef` of type `usize`. The fixture permits only that explicit diagnostic
for those four names; the other seven runtime functions require positive
internal samples. Those four observations remain `not-run` and incomplete.
The separate 132 executions do not turn them into differential agreement or
formal correctness. Added controls preserve ordered Unit element side effects,
early return before a later unsupported effect, and the reachable-effect refusal.
