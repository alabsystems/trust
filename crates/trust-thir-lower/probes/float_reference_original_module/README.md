# Original floating-point reference module observer

The maintained run-make fixture compiles all sixteen unchanged functions in
`tests/run-make/trust-float-reference-storage/subject.rs`. Its coverage must
contain sixteen lowered and spliced bodies, zero symbolic or initializer bodies,
and no proof authority. The original shared-borrow fixture also retains its three
float source bodies and now requires successful lowering and splicing.

Build the changed compiler normally. Emit a binary IR dump from that exact
subject with direct lowering enabled and the MIR flip disabled. Compile this
observer using an independent genuine Trust compiler and explicit MIR/LLVM test
oracle flags, under canonical admission:

```sh
build-slot -- targo --unverified rustc --locked --manifest-path \
  crates/trust-thir-lower/probes/float_reference_original_module/Cargo.toml \
  --bin float-reference-original-module-observer -- \
  -Ztrust-ir-lower=off -Ztrust-ir-flip=no -Zcodegen-backend=llvm
build-slot -- "$OBSERVER" "$MODULE"
```

`OBSERVER` is the actual emitted executable. `MODULE` is the complete original
`.trust-ir.bin` emitted by the changed compiler. Preserve source, compiler, tools,
dependencies and input/output hashes. The observer validates and roundtrips all
original module bytes; it never projects, rewrites or models a body.

The 256 cases cover mutable local and parameter storage, calls through real
references, raw addresses of owned locals, `ref mut` bindings, branch writes and
delayed initialization at both primitive widths. Sixteen bit patterns per width
include both signs of zero, subnormals, infinities and quiet/signaling NaN
payloads. Initial and replacement values differ. Both branch outcomes execute.
Results must match the independently compiled exact Rust source by raw bits,
with no host calls. Every interpreter error fails the observation.

These are finite regression observations, not universal source refinement,
floating-point arithmetic proofs, NoUB, machine-code admission or G1–G8
completion. Aggregate fields, captures, coroutine frames and external raw
pointer parameters keep their separate eligibility rules.
