# Actual constructor and outlined-panic input

`native_constructor_return_actual.json` contains the three complete
`VerifiableFunction` dumps of the original
`tests/ui/trust/native_bundle_member_link_symbols_distinct.rs` (source SHA256
`9f4d6525694817919f296ad7d4bee91c73c32966c44c5bee148714d74ff0438d`).
Captured with the genuine native aarch64 C6 engineering SDK:
`c6d3ebc2042626ee4a24e77bf33cbf40b916a122`, then assembled with `jq -s
'sort_by(.def_path)'`. The sole subsequent normalization changes the rendered
panic span from `/rustc/<toolchain>/library/core/src/panic.rs` to the relative
`library/core/src/panic.rs`. Its tail, line and column values, function bodies,
and callee identities are unchanged. Replayed fixtures install no authenticated
stdlib source table, so neither spelling confers stdlib authority.

```text
trustc -Ztrust-verify=on -Ztrust-policy=advisory \
  -Ztrust-dump=mir-only:<fresh-dir> --edition 2021 --crate-type lib \
  --crate-name native_bundle_member_link_symbols_distinct \
  tests/ui/trust/native_bundle_member_link_symbols_distinct.rs -o <capture.rlib>
```

This capture is input, not proof. The dump command deliberately skips verification
and reports unknown rows in survey mode; its successful process status is not
qualification.
The focused Rust test separately kernel-checks each constructor's original
aggregate-body rows and the actual caller's outlined-panic VC, together with
missing-model, identity-swap and wrong-value controls. The compiler identity
mint and native UI still require the coordinated rebuilt-compiler gate.
