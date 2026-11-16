// Trust (str char-boundary SOUNDNESS regression) — a `str` range-slice at a
// COMPUTED byte offset must NOT be proved on the byte-bounds check alone, because
// it can panic on the UTF-8 char-boundary check (`&s[cut..]` with `cut` mid-
// multibyte-char). `str` is extracted as `[u8]` and the `Index::index` callee
// renders generically, so trust-vcgen distinguishes a str receiver ONLY by the
// `::<__trust_str_index>` marker `func_operand_name` appends. This pins:
//
//  * WITHOUT the marker (a `[u8]` slice, or any non-str receiver): the RangeIndex
//    body emits the ordinary byte-bounds violation `Gt(a, len)` — UNCHANGED, so
//    the entire slice corpus and drop-in Rust are untouched.
//  * WITH the marker (a `&str`) at a non-boundary-safe endpoint (`a` is a param,
//    not a `char_indices()` yield and not the constant 0): the body fails CLOSED
//    (the declined `UnsupportedMir` row, Unknown; until 2026-10-02 an always-true
//    `Bool(true)` violation that refuted on an arbitrary model), so the
//    byte-bounds proof can no longer vacuously "prove" a program that panics
//    mid-char.
//
// The base fixture is the REAL MIR extracted with `-Ztrust-dump=mir:<dir>` from
// `fn str_from(s: &str, a: usize) -> &str { &s[a..] }`. The marker is injected by
// string-replace so the two cases differ ONLY by the receiver's str-ness.
use trust_types::*;
use trust_vcgen::generate_vcs;

const BASE: &str = include_str!("fixtures/str_rangefrom_param_mir.json");

fn slice_bounds_formulas(json: &str) -> Vec<String> {
    let func: VerifiableFunction =
        serde_json::from_str(json).expect("fixture MIR must deserialize");
    generate_vcs(&func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .map(|vc| format!("{:?}", vc.formula))
        .collect()
}

#[test]
fn byte_slice_rangefrom_keeps_byte_bounds_violation() {
    // Unmarked receiver == a `[u8]` slice (no char-boundary panic): the RangeIndex
    // body must still emit the ordinary `a > len` byte-bounds disjunct, so a
    // guarded `&b[a..]` proves and an unguarded one refutes exactly as before.
    let formulas = slice_bounds_formulas(BASE);
    assert!(!formulas.is_empty(), "a str/slice RangeFrom must produce a bounds VC");
    assert!(
        formulas.iter().any(|f| f.contains("Gt") && f.contains("\"a\"")),
        "unmarked (byte-slice) RangeFrom must keep the `a > len` bounds disjunct, got: {formulas:?}"
    );
}

#[test]
fn str_slice_rangefrom_computed_offset_fails_closed() {
    // Marked receiver == a `&str`: the byte-bounds VC alone is UNSOUND (the UTF-8
    // char-boundary panic is unmodeled), and `a` is a plain param — neither a
    // char_indices yield nor the constant 0 — so the body must fail closed. The
    // `a > len` bounds disjunct is REPLACED by the refusal, so `a` no longer
    // appears as the load-bearing upper bound.
    //
    // Trust (2026-10-02, class 10 — false refutation): the refusal is the declined
    // `UnsupportedMir { kind: "str-range-char-boundary-unmodeled" }` row carrying
    // the shared fail-closed formula — Unknown, never proved — no longer an
    // always-true `SliceBoundsCheck` that FAILED on an arbitrary model whether or
    // not `a` was a boundary (the row `str::split_at` gives the same gap).
    let marked =
        BASE.replace("std::ops::Index::index", "std::ops::Index::index::<__trust_str_index>");
    assert!(marked.contains("__trust_str_index"), "marker injection must land");
    let func: VerifiableFunction =
        serde_json::from_str(&marked).expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let declined: Vec<String> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "str-range-char-boundary-unmodeled")
        })
        .map(|vc| format!("{:?}", vc.formula))
        .collect();
    assert!(
        !declined.is_empty(),
        "a marked str RangeFrom at a computed offset must be refused (declined row), got: {vcs:?}"
    );
    assert!(
        declined.iter().all(|f| !f.contains("Gt(Var(\"a\"")),
        "the refusal must not carry the `a > len` byte-bounds disjunct, got: {declined:?}"
    );
    let formulas = slice_bounds_formulas(&marked);
    assert!(
        formulas.iter().all(|f| !f.contains("Gt(Var(\"a\"")),
        "marked str RangeFrom at a computed offset must fail closed — no byte-bounds row \
         may stand for it, got: {formulas:?}"
    );
}
