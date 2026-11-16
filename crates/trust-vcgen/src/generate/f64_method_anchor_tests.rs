//! Trust (2026-10-04, NUM-METHOD-ANCHOR-1): a std `f64` method's interval is
//! licensed only for a callee DEFINED in a real sysroot crate whose rendering is
//! EXACTLY `{core,std}::f64::<impl f64>::{method}` and whose destination is a float.
//! Pinned on REAL extracted MIR.
//!
//! `float_range::f64_std_method_name` wanted a `core`/`std`/`alloc` root and
//! `::f64::` ANYWHERE, then read the method off the LAST `::` segment with its
//! `<…>` cut off. `core::cmp::max_by_key::<f64, {closure}, core::marker::PhantomData<
//! f64m::m::f64::cos<1>>>` — a real core callee whose generic argument names a user
//! type `m::f64::cos<1>` — came out as `cos`, so `max_by_key(a, b, …)` got the
//! `[-1, 1]` interval and `v * 4.0` lost its `float_overflow_to_infinity (Mul)` row
//! (measured on `scratchpad/stage1-w11fix`, 2026-10-04, default policy: "0 unknown,
//! 1 runtime-checked out of 1"; `lie1(0.5, 1e308)` returns `inf`). Through a helper
//! (`pick`), the false interval reached the caller `lie2` too. The same code with the
//! module named `f64x` (`twin`) keeps the row.

use trust_types::{CalleeKey, Operand, Place, Terminator, Ty, VerifiableFunction};

use super::{f64_std_method_name, float_range, is_unit_bounded_float_call};
use crate::generate::{FloatNanMode, FloatRangeCtx};

fn load(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// `(callee, key, dest local)` of the first call whose path contains `needle`.
fn call<'f>(func: &'f VerifiableFunction, needle: &str) -> (&'f str, Option<&'f CalleeKey>, usize) {
    func.body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func: callee, callee_key, dest, .. } if callee.contains(needle) => {
                Some((callee.as_str(), callee_key.as_ref(), dest.local))
            }
            _ => None,
        })
        .expect("the fixture has the call")
}

/// The NaN-tolerant interval of the call's destination, as the overflow
/// discharge reads it.
fn dest_range(func: &VerifiableFunction, needle: &str) -> Option<(f64, f64)> {
    let (_, _, dest) = call(func, needle);
    let ctx = FloatRangeCtx::new(func, None);
    float_range(
        &ctx,
        FloatNanMode::NanOrBounded,
        None,
        &Operand::Copy(Place::local(dest)),
        &mut Vec::new(),
        32,
    )
}

#[test]
fn a_generic_argument_naming_f64_cos_is_not_cos() {
    for (name, mir) in [("lie1", MIR_LIE1), ("pick", MIR_PICK)] {
        let func = load(mir);
        let (callee, key, _) = call(&func, "max_by_key");
        assert!(callee.contains("::f64::cos<"), "{name}: {callee}");
        assert!(key.is_some_and(|k| k.krate_is_real_sysroot), "{name}: core's own callee");
        assert_eq!(f64_std_method_name(callee, key), None, "{name}: {callee}");
        assert!(!is_unit_bounded_float_call(callee, key), "{name}: {callee}");
        assert_eq!(dest_range(&func, "max_by_key"), None, "{name}: `max_by_key` is unbounded");
    }
    // The renamed twin, refused before and after.
    assert_eq!(dest_range(&load(MIR_TWIN), "max_by_key"), None);
}

#[test]
fn std_f64_methods_keep_their_intervals() {
    for (name, mir, needle, want) in [
        ("std_sin", MIR_STD_SIN, "<impl f64>::sin", (-1.0, 1.0)),
        ("std_tanh", MIR_STD_TANH, "<impl f64>::tanh", (-1.0, 1.0)),
        ("std_abs_clamp", MIR_STD_ABS_CLAMP, "<impl f64>::abs", (0.0, 2.0)),
        ("std_secs", MIR_STD_SECS, "as_secs_f64", (0.0, 36_893_488_147_419_103_232.0)),
    ] {
        let func = load(mir);
        let (callee, key, _) = call(&func, needle);
        assert!(key.is_some_and(|k| k.krate_is_real_sysroot), "{name}: {callee}");
        assert_eq!(dest_range(&func, needle), Some(want), "{name}: {callee}");
    }
    // `sqrt` over `clamp(0.0, 4.0)`: rounded outward around `[0, 2]`.
    let func = load(MIR_STD_SQRT);
    let (lo, hi) = dest_range(&func, "<impl f64>::sqrt").expect("std's sqrt keeps its arm");
    assert!(lo == 0.0 && (2.0..2.000_001).contains(&hi), "sqrt: ({lo}, {hi})");
    // `min`/`max` over `clamp(-1.0, 1.0)`: the operand hulls.
    let func = load(MIR_STD_MIN_MAX);
    assert_eq!(dest_range(&func, "<impl f64>::max"), Some((-1.0, 1.0)));
}

#[test]
fn a_std_f64_method_needs_its_key_and_a_float_destination() {
    let func = load(MIR_STD_SIN);
    let (callee, key, dest) = call(&func, "<impl f64>::sin");
    assert_eq!(callee, "std::f64::<impl f64>::sin");
    assert_eq!(f64_std_method_name(callee, key), Some("sin"));
    assert_eq!(f64_std_method_name(callee, None), None);
    let user = CalleeKey { krate_is_real_sysroot: false, ..key.expect("keyed").clone() };
    assert_eq!(f64_std_method_name(callee, Some(&user)), None);
    // A longer leaf, or a path that merely ends with the entry, is not the method.
    assert_eq!(f64_std_method_name("std::f64::<impl f64>::sinh", key), None);
    assert_eq!(f64_std_method_name("mycrate::std::f64::<impl f64>::sin", key), None);
    // An extraction whose destination is not a float is refused.
    let mut retyped = func.clone();
    let slot = retyped.body.locals.iter_mut().find(|l| l.index == dest).expect("dest local");
    slot.ty = Ty::Int { width: 64, signed: true };
    assert_eq!(dest_range(&retyped, "<impl f64>::sin"), None);
}

/// REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, `scratchpad/stage1-w11fix`,
/// 2026-10-04) of `f64m.rs` (crate `f64m`), under
/// `tests/fixtures/vcgen_recognizer_anchor/`:
///
/// ```text
/// pub mod m { pub mod f64 { pub struct cos<const N: usize>; } }
/// pub fn lie1(a: f64, b: f64) -> f64 {
///     let v = core::cmp::max_by_key(a, b, |_x| PhantomData::<m::f64::cos<1>>); v * 4.0 }
/// pub fn pick(b: f64) -> f64 { core::cmp::max_by_key(0.5, b, |_x| PhantomData::<m::f64::cos<1>>) }
/// pub mod n { pub mod f64x { pub struct cos<const N: usize>; } }
/// pub fn twin(a: f64, b: f64) -> f64 {
///     let v = core::cmp::max_by_key(a, b, |_x| PhantomData::<n::f64x::cos<1>>); v * 4.0 }
/// pub fn std_sin(x: f64) -> f64 { x.sin() * 4.0 }
/// pub fn std_tanh(x: f64) -> f64 { x.tanh() * 4.0 }
/// pub fn std_sqrt(x: f64) -> f64 { x.clamp(0.0, 4.0).sqrt() * 4.0 }
/// pub fn std_abs_clamp(x: f64) -> f64 { x.clamp(-2.0, 2.0).abs() * 4.0 }
/// pub fn std_min_max(x: f64) -> f64 { x.clamp(-1.0, 1.0).min(0.5).max(-0.5) * 4.0 }
/// pub fn std_secs(d: Duration) -> f64 { d.as_secs_f64() * 4.0 }
/// ```
///
/// Measured spellings: `std::f64::<impl f64>::{sin,tanh,sqrt}` keyed `std`;
/// `core::f64::<impl f64>::{abs,clamp,min,max}` and
/// `core::time::Duration::as_secs_f64` keyed `core`; every one
/// `krate_is_real_sysroot: true`.
const MIR_LIE1: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/f64m_lie1_mir.json");
const MIR_PICK: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/f64m_pick_mir.json");
const MIR_TWIN: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/f64m_twin_mir.json");
const MIR_STD_SIN: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/f64m_std_sin_mir.json");
const MIR_STD_TANH: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/f64m_std_tanh_mir.json");
const MIR_STD_SQRT: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/f64m_std_sqrt_mir.json");
const MIR_STD_ABS_CLAMP: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/f64m_std_abs_clamp_mir.json");
const MIR_STD_MIN_MAX: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/f64m_std_min_max_mir.json");
const MIR_STD_SECS: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/f64m_std_secs_mir.json");
