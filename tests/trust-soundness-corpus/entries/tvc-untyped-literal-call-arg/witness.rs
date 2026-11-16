// trust-soundness-corpus entry `tvc-untyped-literal-call-arg` (trust-vc untyped literal (930d025f)). See entry.json for the claim,
// the witness input and each verifier's expected verdict.
#[path = "src.rs"]
mod src;
fn main() {
    src::never_binding_typed_by_call_arg_used_in_assert();
}
