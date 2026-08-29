//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-PO2): a zero-arg UNREVEALED Opaque — RPIT, TAIT, `async fn`'s
//! return — is NAMED (the shared zero-field `opaque_alias` sort), never
//! revealed. Before this wave every one of these spellings pushed the bare
//! `Ty` tag from `map_ty`'s Alias arm and the body stayed dirty; naming is
//! query-free (no `type_of`, no normalize — the E0391 reveal hazard never
//! arises), the body is marked SYMBOLIC (`param_opaque`, splice refused),
//! and the differential never compares these bodies
//! (`mir.has_opaque_types()` → NotRun, `clean-skip-unrevealed-opaque`).

fn rpit(x: u64) -> impl Iterator<Item = u64> {
    (0..x).map(|v| v * 2)
}

async fn plain_async(x: u64) -> u64 {
    x + 1
}

fn consume_rpit() -> u64 {
    let mut s = 0;
    for v in rpit(4) {
        s += v;
    }
    s
}

fn main() {
    assert_eq!(consume_rpit(), 12);
    let _fut = plain_async(1);
}
