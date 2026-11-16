//! REAL-MIR matrix for the return-interval summary
//! (`trust_vcgen::compute_return_interval_summaries`, 2026-09-30).
//!
//! Every fixture is the compiler's OWN extracted MIR, captured from
//! `tests/fixtures/rint_fx.rs` with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> rint_fx.rs
//! ```
//!
//! | fixture | body | summary |
//! |---|---|---|
//! | `rint_widen` | `x as u32 + 1` over `x: u8` | `[1, 256]` |
//! | `rint_index` | `d as usize` over a four-variant enum | `<= 3` |
//! | `rint_clamp10` | `if n > 10 { 10 } else { n }` | `<= 10` |
//! | `rint_capped` | a counter stopped at `min(n, 10)` | `<= 10` |
//! | `rint_wraps` | `x.wrapping_sub(1)` (a call: havocked) | none |
//! | `rint_same` | `x` (the type's own range) | none |
//! | `rint_union` | `u.a = 5; u.b = v; u.a` over a union | none (a union write rebinds no sibling) |
//! | `rint_select_write` | `*if c { &mut x } else { &mut y } = 200; x` | none (a `&mut` taken) |
//! | `rint_guarded` | a guard writing through a held `&mut` on drop | none (a destructor) |
use trust_types::VerifiableFunction;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/");
    let text = std::fs::read_to_string(format!("{path}{name}.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

fn summary_of(name: &str) -> Option<(Option<i128>, Option<i128>)> {
    let func = load(name);
    let map = trust_vcgen::compute_return_interval_summaries(std::slice::from_ref(&func), true);
    map.get(&func.def_path).copied()
}

#[test]
fn widened_byte_plus_one_is_one_to_256() {
    assert_eq!(summary_of("rint_widen"), Some((Some(1), Some(256))));
}

#[test]
fn enum_discriminant_cast_is_below_the_variant_count() {
    assert_eq!(summary_of("rint_index"), Some((None, Some(3))));
}

#[test]
fn branch_clamp_is_at_most_ten() {
    assert_eq!(summary_of("rint_clamp10"), Some((None, Some(10))));
}

/// Formerly a pinned PRECISION limit (the repair raised the loop head to Top, so
/// nothing was known at the exit). Since 2026-10-09 the descending pass propagates
/// the edge-narrowed states and widen points are real back edges, so the counter
/// stopped at `min(n, 10)` keeps its true bound `<= 10`.
#[test]
fn loop_counter_is_at_most_ten() {
    assert_eq!(summary_of("rint_capped"), Some((None, Some(10))));
}

/// A wrapping primitive is a call whose result the interval lane havocs, so the
/// body proves nothing about its return: no entry, never the unwrapped `x - 1`.
#[test]
fn wrapping_call_gets_no_interval() {
    assert_eq!(summary_of("rint_wraps"), None);
}

/// Without enforced overflow asserts (`-C overflow-checks=off` over a body that
/// still carries one), the assert's success edge says nothing: `x as u32 + 1` is
/// then only known to be a `u32`, and `widen` gets no interval.
#[test]
fn unenforced_overflow_asserts_narrow_nothing() {
    let func = load("rint_widen");
    let map = trust_vcgen::compute_return_interval_summaries(std::slice::from_ref(&func), false);
    assert_eq!(map.get(&func.def_path).copied(), None);
}

/// A return that spans the whole type says nothing and is not recorded.
#[test]
fn type_range_return_gets_no_interval() {
    assert_eq!(summary_of("rint_same"), None);
}

/// A `requires` narrows the fixpoint's initial state; the summary must not
/// inherit it, since it describes every call. With `x < 10` as a precondition,
/// `widen` is still summarized over the whole `u8` range.
#[test]
fn preconditions_do_not_narrow_the_summary() {
    let mut func = load("rint_widen");
    let x = func.body.locals[1].clone();
    let name = trust_vcgen::local_var_name(&func, &x);
    func.preconditions.push(trust_types::Formula::Lt(
        Box::new(trust_types::Formula::Var(name, trust_types::Sort::Int)),
        Box::new(trust_types::Formula::Int(10)),
    ));
    let map = trust_vcgen::compute_return_interval_summaries(std::slice::from_ref(&func), true);
    assert_eq!(map.get(&func.def_path).copied(), Some((Some(1), Some(256))));
}

/// Bodies the interval domain cannot follow lend no interval
/// (`return_interval_admissible`). Round 10 and 11 of the review measured each of
/// these shapes giving a false one: `[5, 5]` for the union re-read, `[0, 5]` for
/// the two `&mut` writes of 200.
#[test]
fn bodies_the_domain_cannot_follow_get_no_interval() {
    for name in ["rint_union", "rint_select_write", "rint_guarded"] {
        assert_eq!(summary_of(name), None, "{name}");
    }
}

/// A local whose type lowering gave up (`Ty::Unsupported`) may hold a union the gate
/// cannot see, so the body lends no interval. Round 13 of the review measured a union
/// field inside a struct past the extractor's node budget lowered this way, and its
/// helper's false `[7, 7]` certified a caller's division row.
#[test]
fn a_body_with_an_unsupported_local_gets_no_interval() {
    let mut func = load("rint_widen");
    assert!(summary_of("rint_widen").is_some(), "control: widen alone is summarized");
    let index = func.body.locals.len();
    func.body.locals.push(trust_types::LocalDecl {
        index,
        ty: trust_types::Ty::Unsupported {
            kind: "recursive ADT".to_string(),
            detail: "degraded: produced-node budget".to_string(),
        },
        name: Some("o".to_string()),
    });
    let map = trust_vcgen::compute_return_interval_summaries(std::slice::from_ref(&func), true);
    assert_eq!(map.get(&func.def_path).copied(), None);
}
