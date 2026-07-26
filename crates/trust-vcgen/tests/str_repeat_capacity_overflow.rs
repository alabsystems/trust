// Trust (str::repeat capacity overflow — sibling of the sum/product silent FA).
//
// `s.repeat(n)` computes its result capacity `s.len() * n` inside the library
// impl, which overflow-panics ("capacity overflow") for large `n` — no
// caller-visible BinaryOp, so the pre-fix verifier emitted ZERO obligations
// (`"ab".repeat(usize::MAX)` compiled clean, rc 0). The fix mints an
// `UnsupportedMir { kind: "str-repeat-capacity-overflow" }` obligation → Unknown →
// runtime-checked in the default lane (the owner-decided demotion), so the
// overflow is honestly accounted and delegated to the runtime capacity check.
//
// Pins:
//  * `str::repeat`   (`<impl str>::repeat`) -> obligation IS minted.
//  * `slice::repeat` (`<impl [T]>::repeat`) -> NOT minted by THIS recognizer — it
//    already mints a runtime-checked obligation via the bulk-alloc capacity path,
//    so my str-gated recognizer must leave it untouched (no double-count, no
//    regression of its existing sound handling).
//
// Fixtures are the REAL MIR extracted with `-Ztrust-dump=mir:<dir>`.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn has_str_repeat_vc(json: &str) -> bool {
    let func: VerifiableFunction =
        serde_json::from_str(json).expect("fixture MIR must deserialize");
    generate_vcs(&func).into_iter().any(|vc| {
        matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "str-repeat-capacity-overflow")
    })
}

#[test]
fn str_repeat_mints_capacity_overflow_obligation() {
    assert!(
        has_str_repeat_vc(include_str!("fixtures/str_repeat_mir.json")),
        "`s.repeat(n)` on a str must mint a str-repeat-capacity-overflow obligation \
         (no more silent 0-obligation accept)"
    );
}

#[test]
fn slice_repeat_is_not_touched_by_str_recognizer() {
    // `slice::repeat` is handled soundly elsewhere; the str-gated recognizer must
    // NOT fire for it (else it would double-count or regress that handling).
    assert!(
        !has_str_repeat_vc(include_str!("fixtures/slice_repeat_mir.json")),
        "`slice::repeat` must NOT trip the str-only capacity-overflow recognizer"
    );
}
