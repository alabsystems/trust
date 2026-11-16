# Actual compiler caller inputs

## Current e76 reconstructed subject

`current-e76-caller/actual-input.json` is a new, complete actual Compiler CER input
capture from engineering compiler `e76b0c5c39485a498b4d01e55bd2d1126e7bedb0`.
`current-e76-caller/subject.rs` is the exact source supplied for this capture.
It was reconstructed from the historical capture's typed IR shape. That capture
does not retain Rust source bytes, and they were not recovered for this repair. This is a new subject, **not unchanged b8**.

The Rust callee reads `*from: u8` before writing `value as u8` to `*to`, then returns
the old byte as `u64`. The C caller forwards two pointers and a `u64`, returning a
`u64`. The capture has no source Alloca and retains the actual five-instruction,
16-byte STP/MOV/BL/LDP/RET caller frame. Its complete canonical Module includes the
current `closure_layouts: []` field. No old JSON was normalized or upgraded.

- Source SHA256: `ff10ebaefda77342ad75ad4d4db16a93ea73efb5f152d3b059098ede29621668`
- Capture SHA256: `e4b0e9030c002ebfa9d3a6395e6322197dffe6f96d5b524e913ddb7eea67cd38`
- Object SHA256: `b20aa8af874f0bc71b54e3144632d0df1c1d17dc4b821f9d402b50d23f17d01b` (647 bytes)

The capture was emitted **before strict refusal**, exit 101: `source_memory_caller`
is Unknown at O5 because M5 caller pre-call memory equality and private-frame
separation remain unproved. All seven PKG-B SemR requests remain pending.
The explicit `--unverified` fixture-data lane grants no proof claim and does not
change the strict codegen output gate. No Rust-source, ABI, SDK-readiness, native
admission or product-completion authority is imported from this capture.

The exact invocation used an isolated dependency-free Cargo package named
`current-source-memory-caller`, version `0.0.0`, edition `2021`, with this source
copied to `src/lib.rs`; `CARGO_INCREMENTAL=0`, offline mode, an owned Cargo home and
output directory. Through native and primary build-tree leases and outer
`build-slot --cpus 6`, actual e76 stage1-tools Targo ran:

```sh
targo --unverified rustc --manifest-path "$fixture/Cargo.toml" --locked --offline \
  --lib --target-dir "$output/target" -- --emit=obj \
  -Copt-level=0 -Cdebuginfo=0 -Csplit-debuginfo=off -Cpanic=abort \
  -Ccodegen-units=1 -Coverflow-checks=on -Ztrust-ir-lower=on \
  -Zcodegen-backend=trust-cg -Ztrust-cg-frontend=trust-ir \
  -Ztrust-cg-f1-backend=compiler -Ztrust-dump=ir:"$output/capture"
```

`RUSTC` selected that e76 stage1 `trustc`; it was not invoked outside the native
Targo custody boundary. Full invocation, compiler identity, protected-input hashes
and terminal stderr are retained in
`<home>/trust-lean-admission-review-data/current-e76-caller-capture/RESULT.json`
and `<home>/trust-lean-admission-review-data/capture-current-caller.log`.

Tests recompile the captured actual M_cg with the current library and demand exact
object-byte equality. Attaching frame DATA must leave grades, obligations and
original proof bytes unchanged. Missing/wrong layouts, the missing P entry, strict
refusal and all concrete native-instruction counterexamples remain checked: raw
output-pointer aliases can overwrite saved FP/LR, and a separated output still
leaves changed stack bytes at an unrestricted memory query. These controls are
counterexamples and observational inputs, not complete frame semantics.

## Historical b8 capture (immutable)

`actual-b8-caller-input.json` remains unchanged, produced by engineering compiler
`b8f24f1b5b575f19686a67cda63ff1bb0025459e`. Its strict compile refused the framed
caller. The old capture omits the later `closure_layouts` field and is rightly
noncanonical under the current decoder. It is not used as a current positive by
the tests in this directory. Other retained historical evidence remains separate.

- Capture SHA256: `fccc4c260617ebf86cc83a8bf32e56a17957aeb48949ea17050a997f116a2dae`
- Object SHA256: `c4b9e1fcbc611f998c791cacd906ae735a5371528725829739995fe92c24e941` (639 bytes)

The historical claim that this object matched an earlier b8 object is historical
only. The fresh subject/capture is separately named and has a different object.
