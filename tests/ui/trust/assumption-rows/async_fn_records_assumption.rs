// Trust (assumption ledger, Stage 1): an async fn lowers to a coroutine, which
// the supportability classifier cannot lower yet. Under the nonfatal lame policy this must
// be a recorded, machine-readable assumption — the build continues and the
// human surface names the capability gap — never a hard abort (that is
// the crate-under-check strict lane's job) and never a silent skip.
//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory
//@ build-pass
//@ dont-check-compiler-stderr
pub async fn tick(x: u32) -> u32 {
    x
}
fn main() {}
//~? RAW Trust: ASSUMPTION [coroutine]
