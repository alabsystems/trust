# flip.rs hermetic fixtures

The `flip::tests` suite (`crates/trust-ir-bridge/src/flip.rs`) loads real dumped
`VerifiableFunction` JSON. These dumps were historically read from ad-hoc
`/tmp/vf*` directories generated out-of-band during development — so a host
reboot/crash that wiped `/tmp` made the whole suite fail with
`load /tmp/vf.../*.json: NotFound`.

The JSON in `crates/trust-ir-bridge/fixtures/*.json` is now committed and pulled
in via `include_str!` (see `fixture_json()` in `flip.rs`), so the suite is
hermetic and reboot-proof. The `/tmp/vf*` path strings remain at the call sites
as stable provenance keys only.

## Regenerating

Each fixture is one function dumped via `-Ztrust-dump=mir:<dir>` (the dump writes one
`<fn-name>.json` per function in the source). With a built compiler
(`./x.py build`, or `build/host/stage2/bin/trustc`):

```bash
TRUSTC=build/host/stage2/bin/trustc
gen() { # <out-dir> <src.rs>
  "$TRUSTC" -Ztrust-policy=advisory "-Ztrust-dump=mir:$1" \
    --edition 2021 --out-dir /tmp/trustc_out "$2"
}
gen /tmp/vfdump  crates/trust-ir-bridge/fixtures/src/add_ovf.rs
gen /tmp/vfdump2 crates/trust-ir-bridge/fixtures/src/vfdump2_idx_shl_dv_rem.rs
gen /tmp/vfdump3 crates/trust-ir-bridge/fixtures/src/vfdump3_mul_ng_cst.rs
gen /tmp/vfmul   crates/trust-ir-bridge/fixtures/src/vfmul_umul.rs
gen /tmp/vfL1    crates/trust-ir-bridge/fixtures/src/vfL1_pre_both.rs
gen /tmp/vfbr    crates/trust-ir-bridge/fixtures/src/vfbr_pick_clamp_branch.rs
gen /tmp/vfloop  crates/trust-ir-bridge/fixtures/src/vfloop_count.rs
# then copy each /tmp/vf*/<fn>.json over the committed fixtures/<fn>.json
```

## Fixture → source map

| fixture | function | source file |
|---|---|---|
| `add_ovf.json` | `add_ovf(a,b:i32)->i32 { a+b }` (overflow) | `add_ovf.rs` |
| `idx.json` | `idx(s:&[i32],i:usize)->i32 { s[i] }` (bounds) | `vfdump2_idx_shl_dv_rem.rs` |
| `shl.json` | `shl(x,n:u32)->u32 { x<<n }` (shift) | `vfdump2_idx_shl_dv_rem.rs` |
| `dv.json` | `dv(a,b:i32)->i32 { a/b }` (div) | `vfdump2_idx_shl_dv_rem.rs` |
| `rem.json` | `rem(a,b:i32)->i32 { a%b }` (rem) | `vfdump2_idx_shl_dv_rem.rs` |
| `mul.json` | `mul(a,b:i32)->i32 { a*b }` (signed mul) | `vfdump3_mul_ng_cst.rs` |
| `ng.json` | `ng(a:i32)->i32 { -a }` (negation) | `vfdump3_mul_ng_cst.rs` |
| `cst.json` | `cst(x:i64)->i32 { x as i32 }` (cast) | `vfdump3_mul_ng_cst.rs` |
| `umul.json` | `umul(a,b:u32)->u32 { a*b }` (unsigned mul) | `vfmul_umul.rs` |
| `pre.json` | `#[requires(x>0)] pre(x:i32)->i32 { x+100 }` | `vfL1_pre_both.rs` |
| `both.json` | `#[requires(x>0)] #[ensures(\|r\| *r>0)] both(x:i32)->i32 { x+1 }` | `vfL1_pre_both.rs` |
| `pick.json` | `#[ensures(\|r\| *r>0)] pick(b:bool)->i32 { if b {1} else {2} }` | `vfbr_pick_clamp_branch.rs` |
| `clamp_branch.json` | `#[requires(x>0)] #[ensures(\|r\| *r>0)] clamp_branch(x:i32,b:bool)->i32 { if b {x} else {1} }` | `vfbr_pick_clamp_branch.rs` |
| `count.json` | `#[ensures(\|r\| *r>=0)] count(n:u32)->u32 { while i<n { c=c.wrapping_add(1); i=i.wrapping_add(1) } c }` | `vfloop_count.rs` |
