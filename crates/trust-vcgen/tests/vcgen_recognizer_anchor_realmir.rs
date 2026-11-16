//! Trust (2026-10-04, wave 13): the keyed recognizers end to end — `generate_vcs` plus
//! the deterministic in-process `ay` router, the lane that produced each false
//! verdict — on REAL extracted MIR (`-Ztrust-dump=mir:<dir>` on
//! `scratchpad/stage1-w11fix`, 2026-10-04; `tests/fixtures/vcgen_recognizer_anchor/`).
//!
//! Each `*_lie` row is a program the BEFORE compiler reported proved (or, for the FFI
//! and float rows, reported with an obligation missing); each `*_std` row is std's own
//! method, which must keep its verdict. The fixture sources are quoted in the unit
//! modules beside each recognizer (`generate/{asptr_nonnull_key,slice_inherent_key,
//! bool_from_anchor,f64_method_anchor}_tests.rs`).
//!
//! * ASPTR-KEY-1: std's raw-slice `<*const [VecDeque<u8>]>::as_ptr` is not a container
//!   accessor; `strlen`'s `parameter 0 must be non-null` VC stays posed and unproved.
//! * SLICE-INHERENT-1: a user `W::<[T]>::windows`/`chunks_exact`/`iter` mints no yield
//!   length, index bound or trip count; the sub-slice indexes and `acc += 1` are not
//!   proved.
//! * NUM-METHOD-ANCHOR-1: `core::cmp::max_by_key::<…, PhantomData<m::f64::cos<1>>>`
//!   gets no `[-1, 1]` (its `* 4.0` keeps a float-overflow VC) and a user
//!   `conv::<From<bool>, …>` gets no `{0, 1}` (its index is not proved).

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

fn fixture(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/vcgen_recognizer_anchor/{name}_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("the captured MIR fixture must deserialize")
}

type Row = (VcKind, VerificationResult);

fn verdicts(name: &str) -> Vec<Row> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            router.verify_all(&vcs).into_iter().map(|(vc, r)| (vc.kind, r)).collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

fn is_bounds(k: &VcKind) -> bool {
    matches!(k, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds)
}

fn is_add_overflow(k: &VcKind) -> bool {
    matches!(k, VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, .. })
}

fn is_float_overflow(k: &VcKind) -> bool {
    matches!(k, VcKind::FloatOverflowToInfinity { .. })
}

fn is_ffi_nonnull(k: &VcKind) -> bool {
    matches!(k, VcKind::FfiBoundaryViolation { desc, .. } if desc.contains("non-null"))
}

/// The rows of `name` matching `want`, with at least one present.
fn rows(name: &str, want: fn(&VcKind) -> bool) -> Vec<Row> {
    let rows: Vec<Row> = verdicts(name).into_iter().filter(|(k, _)| want(k)).collect();
    assert!(!rows.is_empty(), "{name}: expected at least one such row");
    rows
}

#[test]
fn a_user_slice_method_mints_no_yield_fact_and_std_keeps_its_proof() {
    for lie in ["slice_win", "slice_chx", "slice_en"] {
        let rows = rows(lie, is_bounds);
        assert!(
            rows.iter().all(|(_, r)| !proved(r)),
            "{lie}: a user iterator's sub-slice index must not be proved: {rows:?}"
        );
    }
    for ctl in ["slice_win_std", "slice_en_std"] {
        let rows = rows(ctl, is_bounds);
        assert!(rows.iter().all(|(_, r)| proved(r)), "{ctl}: std's index stays proved: {rows:?}");
    }
}

#[test]
fn a_user_iter_gets_no_trip_count_and_std_keeps_its_proof() {
    let lie = rows("slice_trip", is_add_overflow);
    assert!(
        lie.iter().all(|(_, r)| !proved(r)),
        "trip: `acc += 1` over 300 items must not be proved: {lie:?}"
    );
    let ctl = rows("slice_trip_std", is_add_overflow);
    assert!(ctl.iter().all(|(_, r)| proved(r)), "trip_std stays proved: {ctl:?}");
}

#[test]
fn a_user_from_bool_spelling_mints_no_zero_one_fact() {
    let lie = rows("boolfrom_lie", is_bounds);
    assert!(lie.iter().all(|(_, r)| !proved(r)), "boolfrom lie: index 7 must not be proved");
    for ctl in ["boolfrom_std_from", "boolfrom_std_u32_from"] {
        let rows = rows(ctl, is_bounds);
        assert!(rows.iter().all(|(_, r)| proved(r)), "{ctl}: std's bool->int stays proved");
    }
}

#[test]
fn a_generic_argument_naming_f64_cos_keeps_the_float_overflow_row() {
    // The row is posed (not discharged at generation by a `[-1, 1]` interval).
    let lie = rows("f64m_lie1", is_float_overflow);
    assert!(lie.iter().all(|(_, r)| !proved(r)), "lie1: `max_by_key(..) * 4.0` may overflow");
    // std's methods keep their intervals: no float-overflow row survives generation,
    // or it is proved.
    for ctl in ["f64m_std_sin", "f64m_std_tanh", "f64m_std_sqrt", "f64m_std_secs"] {
        let rows: Vec<Row> =
            verdicts(ctl).into_iter().filter(|(k, _)| is_float_overflow(k)).collect();
        assert!(rows.iter().all(|(_, r)| proved(r)), "{ctl}: std's interval was lost: {rows:?}");
    }
}

#[test]
fn a_raw_slice_as_ptr_keeps_the_ffi_nonnull_row() {
    for lie in ["asptr_lie", "asptr_lie_vec"] {
        let rows = rows(lie, is_ffi_nonnull);
        assert!(rows.iter().all(|(_, r)| !proved(r)), "{lie}: a null pointer can reach strlen");
    }
    for ctl in ["asptr_std_slice", "asptr_std_vec", "asptr_std_str", "asptr_std_cstr"] {
        let rows: Vec<Row> = verdicts(ctl).into_iter().filter(|(k, _)| is_ffi_nonnull(k)).collect();
        assert!(rows.iter().all(|(_, r)| proved(r)), "{ctl}: std's non-null fact was lost");
    }
}
