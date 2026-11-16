//! Trust (2026-10-04, NUM-METHOD-ANCHOR-1): the `bool -> integer` conversion fact
//! `0 <= dest <= 1` is std's `From<bool>` impl only — a callee defined in a real
//! sysroot crate whose rendering is EXACTLY a `BOOL_FROM_PATHS` entry. Pinned on
//! REAL extracted MIR.
//!
//! `call_facts::is_bool_from_call` accepted `From<bool>` plus `as core::` ANYWHERE in
//! the rendering. A user generic `conv::<From<bool>, <T as core::ops::Not>::Output>
//! (flag)` (a user `struct From<X>`; `conv` returns 7) renders
//! `boolfrom::conv::<boolfrom::From<bool>, <T as core::ops::bit::Not>::Output>`, so
//! `semantic_guard` pinned its result to `{0, 1}` and `[1u8; 2][x as usize]` read
//! `bounds proved` (measured on `scratchpad/stage1-w11fix`, 2026-10-04, default
//! policy; the program panics with index 7). The same code with the struct named
//! `Frum` is refused.

use trust_types::{CalleeKey, Formula, Terminator, VerifiableFunction};

use super::is_bool_from_call;
use crate::generate::semantic_guard::build_semantic_guard_map;

fn load(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// The rendered callee, key and destination name of the first call whose path
/// contains `needle`.
fn call<'f>(
    func: &'f VerifiableFunction,
    needle: &str,
) -> (&'f str, Option<&'f CalleeKey>, String) {
    func.body
        .blocks
        .iter()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func: callee, callee_key, dest, .. } if callee.contains(needle) => {
                Some((callee.as_str(), callee_key.as_ref(), crate::place_to_var_name(func, dest)))
            }
            _ => None,
        })
        .expect("the fixture has the call")
}

/// Does the semantic guard map carry `dest <= 1` for the (versioned) `dest`?
fn guard_map_bounds_dest_by_one(func: &VerifiableFunction, dest: &str) -> bool {
    fn mentions(f: &Formula, dest: &str) -> bool {
        match f {
            Formula::Le(a, b) => {
                matches!((a.as_ref(), b.as_ref()), (Formula::Var(n, _), Formula::Int(1))
                    if n.split('#').next() == Some(dest))
            }
            Formula::And(parts) => parts.iter().any(|p| mentions(p, dest)),
            _ => false,
        }
    }
    build_semantic_guard_map(func).values().flatten().any(|f| mentions(f, dest))
}

#[test]
fn the_user_generic_spelling_is_not_bool_from() {
    let func = load(MIR_LIE);
    let (callee, key, dest) = call(&func, "::conv::");
    assert!(callee.contains("From<bool>") && callee.contains("as core::"), "{callee}");
    assert!(!is_bool_from_call(callee, key), "{callee}");
    // Even under a forged sysroot key the spelling is not an exact entry.
    let forged = CalleeKey { krate_is_real_sysroot: true, ..key.expect("keyed").clone() };
    assert!(!is_bool_from_call(callee, Some(&forged)), "{callee}");
    assert!(!guard_map_bounds_dest_by_one(&func, &dest), "`conv` returns 7, not a bool");
}

#[test]
fn std_bool_from_keeps_its_zero_one_fact() {
    for (name, mir, needle) in [
        ("std_from", MIR_STD_FROM, "From<bool>>::from"),
        ("std_u32_from", MIR_STD_U32_FROM, "From<bool>>::from"),
    ] {
        let func = load(mir);
        let (callee, key, dest) = call(&func, needle);
        assert!(is_bool_from_call(callee, key), "{name}: {callee}");
        assert!(!is_bool_from_call(callee, None), "{name}: no key");
        let user = CalleeKey { krate_is_real_sysroot: false, ..key.expect("keyed").clone() };
        assert!(!is_bool_from_call(callee, Some(&user)), "{name}: a non-sysroot key");
        assert!(guard_map_bounds_dest_by_one(&func, &dest), "{name}: std's fact is gone");
    }
}

/// REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, `scratchpad/stage1-w11fix`,
/// 2026-10-04) of `boolfrom.rs` (crate `boolfrom`), under
/// `tests/fixtures/vcgen_recognizer_anchor/`:
///
/// ```text
/// pub struct From<X>(pub X);
/// pub fn conv<A, B>(_b: bool) -> u32 { 7 }
/// pub fn lie<T: core::ops::Not>(flag: bool) -> u8 {
///     let x = conv::<From<bool>, <T as core::ops::Not>::Output>(flag);
///     let arr = [1u8; 2]; arr[x as usize] }
/// pub fn std_from(flag: bool) -> u8 { let arr = [1u8; 2]; arr[usize::from(flag)] }
/// pub fn std_u32_from(flag: bool) -> u8 { let arr = [1u8; 2]; arr[u32::from(flag) as usize] }
/// ```
///
/// `std_from` calls `<usize as core::convert::From<bool>>::from`, keyed `core`,
/// `krate_is_real_sysroot: true`; `lie`'s `conv` is keyed `boolfrom`, `false`.
const MIR_LIE: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/boolfrom_lie_mir.json");
const MIR_STD_FROM: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/boolfrom_std_from_mir.json");
const MIR_STD_U32_FROM: &str =
    include_str!("../../tests/fixtures/vcgen_recognizer_anchor/boolfrom_std_u32_from_mir.json");
