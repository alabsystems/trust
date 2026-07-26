//! Trust-CG deliberately rejects every backend tuning knob represented by
//! these queries. They must fail explicitly rather than returning successful,
//! empty output through CodegenBackend's default method.

//@ needs-trust-cg-backend
//@ revisions: relocation code tls cpus features stack
//@ dont-check-compiler-stderr
//~? ERROR codegen backend `trust-cg` does not support `--print=
//@[relocation] compile-flags: --print=relocation-models -Zcodegen-backend=trust-cg -Ztrust-verify=off
//@[code] compile-flags: --print=code-models -Zcodegen-backend=trust-cg -Ztrust-verify=off
//@[tls] compile-flags: --print=tls-models -Zcodegen-backend=trust-cg -Ztrust-verify=off
//@[cpus] compile-flags: --print=target-cpus -Zcodegen-backend=trust-cg -Ztrust-verify=off
//@[features] compile-flags: --print=target-features -Zcodegen-backend=trust-cg -Ztrust-verify=off
//@[stack] compile-flags: --print=stack-protector-strategies -Zcodegen-backend=trust-cg -Ztrust-verify=off

fn main() {}
