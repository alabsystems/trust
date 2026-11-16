# Original indexed-field compound-assignment module observer

Build the changed compiler normally, then compile
`tests/run-make/trust-array-reference-place/indexed_field_compound_assign.rs`
with direct lowering, overflow checks on, the MIR flip off, and a binary IR dump.
Compile the observer with an independent genuine Trust compiler and explicit
MIR/LLVM oracle flags under canonical admission:

```sh
build-slot -- targo --unverified rustc --locked --manifest-path \
  crates/trust-thir-lower/probes/indexed_field_compound_original_module/Cargo.toml \
  --bin indexed-field-compound-original-module-observer -- \
  -Coverflow-checks=on -Ztrust-ir-lower=off -Ztrust-ir-flip=no -Zcodegen-backend=llvm
build-slot -- "$OBSERVER" "$MODULE"
```

`OBSERVER` is the executable emitted by that build; `MODULE` is the complete
original `.trust-ir.bin` emitted by the changed compiler, without projection or
body edits. Keep the compiler, source, dependency, input and output hashes with
the observation.

The maintained run-make fixture requires all 19 source rows, 17 lowered/spliced
bodies and two retained refusals. The historically named
`compound_nested_sibling_refused` now has a complete nested-value image. This
observer validates and roundtrips the entire original module, then executes all
16 supported scalar-returning functions across 160 cases, preserving the original
141 cases and adding the newly admitted body. Eight controls check effect order, replacement of the whole
array, nested updates, loops, float fields and divergence. Eight parameterized
functions cover bounds, checked overflow, division, signed MIN/-1, mixed-width
shifts and every primitive assignment operator at asymmetric integer boundaries.
Only the exact interpreter Panic code can match a Rust oracle panic; unsupported,
undefined-behavior and fuel errors fail. Successful executions require zero host
calls. No body is rewritten, projected, modelled by a host hook or excluded after
inspection. Source display paths are unique observation selectors, not authority.

The ordinary Rust compilation of the fixture is an independent MIR/LLVM test
oracle. It is not a production fallback. These finite executions establish
regression evidence, not universal refinement, source proof, full compiler
coverage, strict machine-code admission or G1–G8 completion.
