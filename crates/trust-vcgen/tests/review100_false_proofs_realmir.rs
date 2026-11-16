// Trust (2026-10-10, review round 100): three false proofs that predate the change
// the round reviewed, pinned on REAL extracted MIR (`-Ztrust-dump=mir`,
// `fixtures/review100/*.json`, the programs quoted on each test). Each panicking
// program verified on stage-1 sa145 (two of them kernel-certified); the end-to-end pins
// are the revisions of `tests/ui/trust/policy_b/review100_false_proofs.rs`.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/review100/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// The verdict of every panic row (bounds and arithmetic overflow) and every
/// fail-honest `UnsupportedMir` row (a withheld fact turns the bounds row into one).
fn panic_rows(name: &str) -> Vec<(String, VerificationResult)> {
    let func = load(name);
    let router = test_router::deterministic_test_router();
    generate_vcs(&func)
        .into_iter()
        .filter(|vc| {
            matches!(
                vc.kind,
                VcKind::SliceBoundsCheck
                    | VcKind::IndexOutOfBounds
                    | VcKind::ArithmeticOverflow { .. }
                    | VcKind::UnsupportedMir { .. }
            )
        })
        .map(|vc| {
            let r = router.verify_all(std::slice::from_ref(&vc)).into_iter().next().unwrap().1;
            (vc.formula.to_smtlib(), r)
        })
        .collect()
}

fn assert_not_all_proved(name: &str) {
    let rows = panic_rows(name);
    assert!(!rows.is_empty(), "{name}: the panicking operation must carry a row");
    assert!(
        rows.iter().any(|(_, r)| !matches!(r, VerificationResult::Proved { .. })),
        "{name}: a panicking program must keep an unproved row\n{rows:#?}"
    );
}

fn assert_all_proved(name: &str) {
    let rows = panic_rows(name);
    assert!(!rows.is_empty(), "{name}: the operation must carry a row");
    for (smt, r) in &rows {
        assert!(
            matches!(r, VerificationResult::Proved { .. }),
            "{name}: must PROVE\n{smt}\n=> {r:?}"
        );
    }
}

/// A. `let k = if c { v.len() } else { n }; if k > 0 { v[k - 1] } else { 0 }` over
/// `v: &Vec<u8>`. The `_len == coll_len(v)` tie is a definition of the call's RETURN
/// TARGET, which here is the join the `k = n` arm also enters, so `k#join == len(v)`
/// held on that path too (`guards::slice_last_some_nonempty_definitions`). Panics at
/// `f(&vec![1, 2, 3], 10, false)`. Controls: a single-valued `let k = v.len()` and
/// `for i in 0..v.len()` keep their proofs.
#[test]
fn a_len_tie_on_a_joined_destination_is_not_a_definition_of_the_join() {
    assert_not_all_proved("join_call_arm");
    assert_all_proved("len_ssa_ok");
    assert_all_proved("for_len_ok");
}

/// B. `let k: i64 = if n > 5 { 5 } else { n }; (k as u64) + 10` and `a[k as usize]`
/// with `if n > 25 { 25 }` over `a: &[u8; 26]`. `value_facts::unsigned_upper_bound`
/// took the clamp bound of a SIGNED local, so `k as u64 <= 5` although `k = -1` casts
/// to `u64::MAX`. Controls: the same clamps over `u64` / `u32` keep their proofs.
#[test]
fn a_signed_clamp_is_no_unsigned_bound_of_its_cast() {
    assert_not_all_proved("signed_clamp_cast_add");
    assert_not_all_proved("signed_clamp_cast_index");
    assert_all_proved("unsigned_clamp_ok");
    assert_all_proved("unsigned_clamp_cast_ok");
}

/// C. An `Option` from `r.next()` carried into the next iteration of an outer loop,
/// where the range end `e = k2 + 0` is redefined before the payload is extracted:
/// `i < e` named the NEW `e` (26) for a value the OLD range (`0..n`) yielded, and
/// `a[i]` over `a: &[u8; 26]` indexed 49 (`f(100, 50, &[0; 26])`).
/// (`iterator_yield::bound_rewritten_between_yield_and_extraction`.)
#[test]
fn a_yield_fact_is_withheld_when_its_bound_is_redefined_before_extraction() {
    assert_not_all_proved("stale_yield_bound");
}

// ---- Review round 101: the same classes in sibling producers (all pre-existing) ----

/// `<[T]>::get` Some-arm seeds (`guards::slice_get_some_index_bound_definitions`) are
/// definitions of the `Some` block, so the call must be the only entry to the switch
/// and the switch's `Some` edge the only entry to the arm. `let o = if c { s.get(i) }
/// else { Some(&0) }; match o { Some(_) => s[i], .. }` and the range twin `if c {
/// s.get(0..4) } else { Some(t) }` then `x[3]` were kernel-certified. Controls: a plain
/// `match s.get(i)` and `if let Some(x) = s.get(1..3)` keep their proofs.
#[test]
fn a_get_seed_holds_only_on_the_call_path() {
    assert_not_all_proved("get_join");
    assert_not_all_proved("get_range_join");
    assert_all_proved("get_ok");
}

/// `last()`/`first()` seed `len(v) >= 1` at any switch on the result's discriminant,
/// so the result must hold one value: `let o = if c { v.last() } else { Some(r) }` made
/// `v.len() - 1` kernel-certified on an empty `v`. Control: `match v.last()`.
#[test]
fn a_last_seed_needs_a_single_valued_option() {
    assert_not_all_proved("last_join");
    assert_all_proved("last_ok");
}

/// `value_facts::clamp_upper_bound` read `v <= C` off the switch edge, but `if !w && v
/// > 5 { 5 } else { v }` also enters the `v` arm from the `w` test: `a[k]` over `a: &[u8;
/// 6]` was kernel-certified and panics at `v = 9, w = true`.
#[test]
fn a_clamp_arm_entered_around_its_test_is_no_bound() {
    assert_not_all_proved("clamp_short_circuit");
    assert_all_proved("unsigned_clamp_ok");
}

/// The stale-bound gate of C, in the enumerate and slice-iter builders: an `Option` from
/// the previous iteration's `s.iter().enumerate()` / `a.windows(n)` / `a.chunks(n)` got
/// the CURRENT `len(s)` / `n`. Controls: the ordinary loops, and a store THROUGH the
/// bound (`for i in 0..v.len() { v[i] = v[i].wrapping_mul(3) }`, sweep r30), which
/// changes no length.
#[test]
fn every_yield_builder_withholds_a_stale_bound() {
    assert_not_all_proved("enumerate_stale");
    assert_not_all_proved("windows_stale");
    assert_not_all_proved("chunks_stale");
    assert_all_proved("enumerate_ok");
    assert_all_proved("windows_ok");
    assert_all_proved("store_through_bound_ok");
}

// ---- Review round 102 (all pre-existing) ----

/// The stale-bound gate also walks from the extraction to every block the fact is
/// attached to: a bound redefined AFTER `if let Some(i) = o` (an inner loop rebuilding
/// `e`, then `a[i]`; a window size `n` rebuilt before `w[n - 1]`) named the new value
/// for the old payload (kernel-certified; indexed 39 into `[u8; 26]`).
#[test]
fn a_yield_fact_is_withheld_when_its_bound_changes_before_the_use() {
    assert_not_all_proved("stale_after_extraction");
    assert_not_all_proved("windows_stale_after_extraction");
}

/// `induction::build_downward_induction_facts`: a `j > K` guard bounds the cursor it
/// TESTED, once, on paths that pass it. `if i > 1 { i -= 1; i -= 1; i -= 1; a[i] }`
/// credited every decrement; `if flag || i > 1 { i -= 1; a[i - 1] }` and a `loop` whose
/// `j > 1` test sits at the bottom reach the decrement around the guard. All three were
/// kernel-certified and panic. Controls: `while i > 0 { i -= 1; a[i] }` and `while i > 1
/// { i -= 1; a[i - 1] }` keep their proofs.
#[test]
fn a_downward_guard_bounds_only_the_first_decrement_it_dominates() {
    assert_not_all_proved("repeated_decrement");
    assert_not_all_proved("short_circuit_decrement");
    assert_not_all_proved("first_iteration_decrement");
    assert_all_proved("reverse_loop_ok");
    assert_all_proved("reverse_loop_minus_one_ok");
}

/// `loop_bounds::build_converging_pointer_facts`: `lo < len` held only at blocks the
/// `lo < hi` true edge DOMINATES. `while lo < hi { hi -= 1; if c { break } lo += 1 }
/// s[lo]` reaches the exit from the true edge (the `break`) and from the false edge:
/// `s[lo]` was kernel-certified and panics on an empty `s`. Control: `s[lo]` in the body.
#[test]
fn a_converging_pointer_fact_needs_a_dominating_guard() {
    assert_not_all_proved("converging_break");
    assert_all_proved("converging_ok");
}

// ---- Review round 103 (all pre-existing) ----

/// A guard credits the cursor only when it tests the cursor's CURRENT value
/// (`loop_bounds::guard_operand_reads_current`): the comparison computed in the switch
/// block, through copies made there. A frozen copy (`let l0 = lo; while l0 < hi { hi -=
/// 1; s[lo]; lo += 2 }`), a bool computed before `lo` is rewritten (`let g = lo < hi; if
/// c { lo = 100 } if g { s[lo] }`), and the downward twins (`let k = j; while k > 1 { j
/// -= 1; a[j - 1] }`; `let k = j; if c { j -= 1 } if !(k > 1) { break }`) were all
/// kernel-certified and panic.
#[test]
fn a_guard_on_a_stale_copy_bounds_nothing() {
    assert_not_all_proved("frozen_copy_converging");
    assert_not_all_proved("stale_bool_converging");
    assert_not_all_proved("frozen_copy_downward");
    assert_not_all_proved("stale_copy_downward");
    assert_all_proved("converging_ok");
    assert_all_proved("reverse_loop_ok");
    assert_all_proved("reverse_loop_minus_one_ok");
}

/// Review round 104 (pre-existing): the `get` Some-arm seed also credits the SOURCE of
/// the index copy, and its staleness check saw only direct writes: `let t = i; let p =
/// &mut i; *p = 100; s.get(t)` then `s[i]` was kernel-certified and indexed 100. A
/// mutably borrowed source gets no credit; a plain `match s.get(i)` keeps its proof.
#[test]
fn a_get_source_written_through_a_borrow_gets_no_credit() {
    assert_not_all_proved("get_source_written_through_borrow");
    assert_all_proved("get_ok");
}

/// Review round 106: the stale-bound closure stops at a call destination (a fresh value)
/// EXCEPT `str::as_bytes`, whose length the resolvers spell on its RECEIVER. With `let s
/// = pick(a, b, k)` rebound each iteration and the `Option` carried over, `0..s.as_bytes()
/// .len()` and `s.as_bytes().iter().enumerate()` named the new, shorter `s`
/// (kernel-certified; indexed 0 into ""). The `&[u8]` twin without the call hop is the
/// control that was refused all along.
#[test]
fn an_as_bytes_bound_follows_its_receiver() {
    assert_not_all_proved("as_bytes_stale_range");
    assert_not_all_proved("as_bytes_stale_enumerate");
    assert_not_all_proved("slice_stale_range_ctl");
}

/// Review round 107: the `as_bytes` arm's `&String` fallback (`owned_container_len_var`)
/// also crosses a length-preserving std `deref`/`deref_mut`/`as_slice` call, naming the
/// length on its first argument: `let r = <&String as Deref>::deref(&s); 0..r.as_bytes()
/// .len()` with `s` rebound per iteration was kernel-certified and indexed past the new
/// `s`. The closure follows that hop too.
#[test]
fn a_deref_hop_bound_follows_its_argument() {
    assert_not_all_proved("deref_hop_stale_range");
}

/// Review round 108 (pre-existing): a base-collection trace (`guards::
/// base_collection_local_unique`) followed `s = copy a` although `s` was reseated through
/// an alias (`let p = &mut s; *p = b`), which `value_count` does not count: `!s.is_empty()`
/// became `len(a) >= 1` and `a[0]` was kernel-certified on an empty `a`. A reference or
/// raw-pointer local whose whole place is `&mut`/`&raw` borrowed ends the trace. Control:
/// the same copy without the alias (`let s = a; for i in 0..s.as_bytes().len() {
/// a.as_bytes()[i] }`) keeps its proof.
#[test]
fn a_reference_reseated_through_an_alias_is_no_base() {
    assert_not_all_proved("reseated_ref_base");
    assert_all_proved("ref_base_ok");
}
