#![cfg(feature = "ay-backend")]
// Regression (P0 false-refutation, 2026-07-02 — the `__slice_len` version-oracle
// mismatch). The guarded `&mut [T]` index
//
//   pub fn zero_at(dst: &mut [u8], i: usize) { if i < dst.len() { dst[i] = 0; } }
//
// lowers its bounds re-read through a `FakeForPtrMetadata` raw pointer
// (`_6 = &raw const *dst; _7 = PtrMetadata(_6)`). The block-def extraction emits
// the tie `Eq(_6__slice_len, dst__slice_len)`, but the S2c establish-point
// versioning could not pin it to the AddressOf statement (`_6` does not
// name-overlap `_6__slice_len` in the raw place algebra), while the PtrMetadata
// read WAS versioned — to the phantom entry-havoc token `_6__slice_len#s1_pre`.
// Name-disjoint, the tie was pruned as irrelevant, the length var was
// unconstrained, and ay REFUTED the provably-safe function with a `len = 0`
// counterexample (superiority fixtures bounded_copy / guarded_mut_slice_bound /
// two_pointer_reverse, all false-FAILED by the ay-in-process default lane).
//
// This is the end-to-end oracle the name-presence test in trust-vcgen cannot
// give: the REAL extracted MIR, the REAL generated VC, and the REAL in-process
// solver must PROVE every bounds obligation — and the unguarded twin must NOT.
use trust_router::{InProcessAyBackend, VerificationBackend};
use trust_types::{VcKind, VerifiableFunction, VerificationResult};
use trust_vcgen::generate_vcs;

fn is_bounds(kind: &VcKind) -> bool {
    matches!(kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
}

#[test]
fn guarded_mut_slice_bounds_vc_proves_in_process() {
    let func: VerifiableFunction = serde_json::from_str(include_str!(
        "../../trust-vcgen/tests/fixtures/guarded_mut_index_mir.json"
    ))
    .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let backend = InProcessAyBackend::new();

    let bounds: Vec<_> = vcs.iter().filter(|vc| is_bounds(&vc.kind)).collect();
    assert!(!bounds.is_empty(), "guarded &mut index must produce a bounds VC");
    for vc in bounds {
        let result = backend.verify(vc);
        assert!(
            matches!(&result, VerificationResult::Proved { .. }),
            "guarded `if i < dst.len() {{ dst[i] = 0 }}` bounds VC must PROVE \
             (a refutation here is a FALSE REFUTATION of provably-safe Rust — \
             the slice-len tie was dropped or version-disjoint), got {result:?}\n\
             formula: {:?}",
            vc.formula
        );
    }
}

#[test]
fn unguarded_mut_slice_bounds_vc_still_refutes() {
    // SOUNDNESS twin: the same shape WITHOUT the guard must NOT prove — the
    // fix reconnects the tie fact, it must not manufacture a proof for an
    // actually-reachable out-of-bounds store.
    let func: VerifiableFunction = serde_json::from_str(include_str!(
        "../../trust-vcgen/tests/fixtures/unguarded_mut_index_mir.json"
    ))
    .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let backend = InProcessAyBackend::new();

    let bounds: Vec<_> = vcs.iter().filter(|vc| is_bounds(&vc.kind)).collect();
    assert!(!bounds.is_empty(), "unguarded &mut index must produce a bounds VC");
    for vc in bounds {
        let result = backend.verify(vc);
        assert!(
            !matches!(&result, VerificationResult::Proved { .. }),
            "unguarded `dst[i] = 0` bounds VC must NOT prove, got {result:?}"
        );
    }
}
