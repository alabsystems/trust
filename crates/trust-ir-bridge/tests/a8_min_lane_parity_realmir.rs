// Trust: 2026-09-16 (round A8) — THE MIN-LANE NAME LICENCE, bridge parity on real MIR.
//
// vcgen's `Ord::min` lane inlined `{s}__slice_len` into a GLOBAL fact licensed by
// `is_parameter(root)` alone and proved `let n = s.len().min(100); s = b; s[..n]`
// kernel-certified (`trust-vcgen/tests/escaped_local_seam_realmir.rs`, the `a8_min_*`
// rows); the licence is now `generate::slice_len_licence` and the fact is withheld for
// a reseated root. The bridge has a twin lane: `native_ord_minmax_facts` states
// `dest <= _4` on the RAW argument temp (a single-write local, a name of one value),
// and `slice_length_local_canonical_map` / `canonicalize_slice_lengths` may rewrite a
// length local to its canonical `{s}__slice_len` at dispatch. These rows measure what
// `generate_native_safety_vcs` emits on the same `-Copt-level=0`/`-O1` captures, in the
// direction the parity contract states — the bridge must never be LOOSER than vcgen:
// no native formula may carry the withheld fact `n <= {s}__slice_len` on a root that
// the body reseats.
//
// NOT covered here, recorded as the open audit item: the dispatch-stage
// `canonicalize_slice_lengths` (lower.rs) runs on the DISPATCHED native formula, after
// this entry point; whether it can rewrite the raw-argument fact `n <= _4` onto an
// unversioned `s__slice_len` beside a post-reseat obligation is a question about that
// stage, measured here only as far as `generate_native_safety_vcs` reaches.
use trust_types::{Formula, VerifiableFunction};

fn fixture(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/data/escaped_seam_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("the captured MIR fixture must deserialize")
}

fn native_vcs(name: &str) -> Vec<trust_types::VerificationCondition> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || trust_ir_bridge::generate_native_safety_vcs(&func).unwrap_or_default())
        .expect("spawn")
        .join()
        .expect("the native lane must not panic")
}

/// Every `Le(Var(x), Var(y))` conjunct with `y` a `__slice_len` name — the shape of a
/// min-lane fact stated on a length NAME rather than on the argument temp.
fn min_facts_on_a_length_name(f: &Formula, out: &mut Vec<(String, String)>) {
    if let Formula::Le(a, b) = f
        && let (Formula::Var(x, _), Formula::Var(y, _)) = (a.as_ref(), b.as_ref())
        && y.contains("__slice_len")
    {
        out.push((x.clone(), y.clone()));
    }
    for c in f.children() {
        min_facts_on_a_length_name(c, out);
    }
}

/// The reseated-root probes (`min_reseat_slice_bug` at both levels, the loop form
/// `min_loop_bug`): NO native formula carries a min fact on a `__slice_len` name. The
/// bridge's fact, where it fires, is `n <= _4` on the raw argument temp (measured on
/// `a8_min_loop_bug_o1`), which is a name of one value.
#[test]
fn no_native_min_fact_is_stated_on_a_reseated_roots_length_name() {
    for name in ["a8_min_reseat_slice_bug_o0", "a8_min_reseat_slice_bug_o1", "a8_min_loop_bug_o1"] {
        let vcs = native_vcs(name);
        assert!(!vcs.is_empty(), "{name}: the native lane must emit the bounds row");
        for vc in &vcs {
            let mut facts = Vec::new();
            min_facts_on_a_length_name(&vc.formula, &mut facts);
            assert!(
                facts.is_empty(),
                "{name}: the native lane states a min fact on a length NAME the body reseats: {facts:?}\n{:?}",
                vc.formula
            );
        }
    }
}

/// The control's native row keeps whatever it had: the entry point emits the bounds
/// row and no formula is the fail-closed `Bool(false)` polarity.
#[test]
fn the_control_keeps_its_native_bounds_row() {
    let vcs = native_vcs("a8_ctl_min_slice_o1");
    assert!(!vcs.is_empty());
    assert!(vcs.iter().all(|vc| vc.formula != Formula::Bool(false)));
}

// ── ROUND A9: the index local inside a projection ──────────────────────────────

/// Every variable name of `f`, with its `#`-version stripped, that carries an
/// `[_<l>]` index segment: the spellings that embed an index local by number.
fn index_segment_vars(f: &Formula, out: &mut Vec<String>) {
    if let Formula::Var(name, _) = f
        && name.contains("[_")
    {
        out.push(name.clone());
    }
    for c in f.children() {
        index_segment_vars(c, out);
    }
}

/// The reseated-INDEX probes of rounds r5b/r5c (`let mut j = 0; let n =
/// s[j].len().min(100); j = k; s[j][..n]` and its `let t = s[j]` spelling; `if a[j] >
/// 5 { return 0 } j = k; for i in 0..a[j] { b[i] }` and the `s[j].len()` form): vcgen's
/// copy tie keyed `{s*[_j]}__slice_len` — an index local embedded BY NUMBER — and
/// proved the `RangeTo` row kernel-certified; its yield lane minted `i < a*[_j]` and
/// proved `b[i]`. MEASURED here on the same captures: the native lane spells no
/// index-embedding name at all (`s__slice_len` throughout, never `s*[_3]`), states no
/// min fact on a length name, and its `RangeTo` row is `Gt(n, _13__slice_len)` on a
/// FREE temp length — satisfiable, never a proof. The bridge is therefore not looser
/// than vcgen on this class, and this row pins that it stays so.
#[test]
fn a9_the_native_lane_keys_nothing_on_an_index_embedding_length_name() {
    for name in [
        "r5b_index_local_min_bug_o0",
        "r5b_index_local_min_bug_o1",
        "r5c_index_local_min_let_bug_o0",
        "r5c_index_local_min_let_bug_o1",
        "r5b_index_elem_end_bug_o0",
        "r5b_index_elem_end_bug_o1",
        "r5c_index_local_len_end_bug_o0",
        "r5c_index_local_len_end_bug_o1",
    ] {
        let vcs = native_vcs(name);
        assert!(!vcs.is_empty(), "{name}: the native lane must emit the bounds rows");
        for vc in &vcs {
            let mut facts = Vec::new();
            min_facts_on_a_length_name(&vc.formula, &mut facts);
            assert!(
                facts.is_empty(),
                "{name}: a min fact on a length NAME: {facts:?}\n{:?}",
                vc.formula
            );
            let mut idx = Vec::new();
            index_segment_vars(&vc.formula, &mut idx);
            assert!(
                idx.is_empty(),
                "{name}: the native lane now spells an index-embedding name ({idx:?}); a fact keyed \
                 on it is a claim about every slot the index local selects — re-measure before \
                 admitting it\n{:?}",
                vc.formula
            );
            assert_ne!(vc.formula, Formula::Bool(false), "{name}: never a vacuous proof");
        }
    }
}

/// The SSA-index controls keep their native rows and none is the fail-closed
/// `Bool(false)` polarity.
#[test]
fn a9_the_ssa_index_controls_keep_their_native_rows() {
    for name in [
        "r5b_ctl_index_elem_end_ssa_o0",
        "r5b_ctl_index_elem_end_ssa_o1",
        "r5b_ctl_index_local_len_ssa_o0",
        "r5b_ctl_index_local_len_ssa_o1",
        "r5c_ctl_index_local_len_end_o0",
        "r5c_ctl_index_local_len_end_o1",
        "r5c_ctl_index_elem_end_guarded_o0",
        "r5c_ctl_index_elem_end_guarded_o1",
    ] {
        let vcs = native_vcs(name);
        assert!(!vcs.is_empty(), "{name}: the native lane must emit the bounds rows");
        assert!(
            vcs.iter().all(|vc| vc.formula != Formula::Bool(false)),
            "{name}: never a vacuous proof"
        );
    }
}

// ── ROUND A11: a store def that outlived the reseat of its index local / prefix ──

/// The round-A10 review's shapes (`rev11c`/`rev11d`/`rev11e`, `-O0` and `-O1`
/// captures): `s[j] = 3; j = k; t[s[j] as usize]` on `&mut [u8]`, on a local array,
/// through `let p = &mut j; *p = k`, and the prefix form `p.0 = 3; p = q; t[p.0]`.
/// vcgen kept the store def `s*[_4] == 3` / `p.0 == 3` across the reseat and PROVED
/// the read kernel-certified (`trust-vcgen/tests/escaped_local_seam_realmir.rs`, the
/// `a11_*` rows). MEASURED on the same captures through `generate_native_safety_vcs`
/// + the deterministic `ay` router (probe harness, 2026-09-16): the native lane's
/// read row is FAILED with a witness on every one of these bodies at both levels —
/// it spells no index-embedding name, and its per-statement store model does not
/// carry the stored value across the whole-local write. The bridge is therefore not
/// looser than vcgen on this class; this row pins the formula-level half of that:
/// every bounds row is emitted, none is the vacuous `Bool(false)`, and no formula
/// keys anything on a `[_<l>]` name.
#[test]
fn a11_the_native_lane_keys_no_store_fact_on_a_reseated_index_or_prefix() {
    for name in [
        "rev11d_store_reseat_read_bug_o0",
        "rev11d_store_reseat_read_bug_o1",
        "rev11d_arr_store_reseat_read_bug_o0",
        "rev11d_arr_store_reseat_read_bug_o1",
        "rev11c_iv_store_reseat_bug_o0",
        "rev11c_iv_store_reseat_bug_o1",
        "rev11c_iv_arr_store_reseat_bug_o0",
        "rev11c_iv_arr_store_reseat_bug_o1",
        "rev11c_iv_ptr_store_reseat_bug_o0",
        "rev11c_iv_ptr_store_reseat_bug_o1",
        "rev11e_field_store_reseat_bug_o0",
        "rev11e_field_store_reseat_bug_o1",
        "rev11e_arr_const_store_reseat_bug_o0",
        "rev11e_arr_const_store_reseat_bug_o1",
    ] {
        let vcs = native_vcs(name);
        assert!(!vcs.is_empty(), "{name}: the native lane must emit the bounds rows");
        for vc in &vcs {
            assert_ne!(vc.formula, Formula::Bool(false), "{name}: never a vacuous proof");
            let mut idx = Vec::new();
            index_segment_vars(&vc.formula, &mut idx);
            assert!(
                idx.is_empty(),
                "{name}: the native lane now spells an index-embedding name ({idx:?}); a store \
                 fact keyed on it would outlive the reseat of the index local — re-measure \
                 before admitting it\n{:?}",
                vc.formula
            );
        }
    }
}

/// The controls (`j = k; s[j] = 3; t[s[j]]`, `p = q; p.0 = 3; t[p.0]`, ok 4) keep
/// their native rows and none is the fail-closed polarity.
#[test]
fn a11_the_store_reseat_controls_keep_their_native_rows() {
    for name in [
        "rev11d_store_reseat_read_ctl_o0",
        "rev11d_store_reseat_read_ctl_o1",
        "rev11c_iv_store_reseat_ctl_o0",
        "rev11c_iv_store_reseat_ctl_o1",
        "rev11c_iv_arr_store_reseat_ctl_o0",
        "rev11c_iv_arr_store_reseat_ctl_o1",
        "rev11e_field_store_reseat_ctl_o0",
        "rev11e_field_store_reseat_ctl_o1",
    ] {
        let vcs = native_vcs(name);
        assert!(!vcs.is_empty(), "{name}: the native lane must emit the bounds rows");
        assert!(
            vcs.iter().all(|vc| vc.formula != Formula::Bool(false)),
            "{name}: never a vacuous proof"
        );
    }
}

// ── ROUND A12: the referent fold outlived the reseat of the referent's locals ──

/// The round-A11 review's shapes (`rev12`/`rev12b`, `-O0` and `-O1` captures) and
/// this round's own (`rev13`): a reference borrowed BEFORE a reseat of a local that
/// roots or indexes its referent, dereferenced AFTER it — `let r = &mut p.a; p = o;
/// *r = 3; t[p.a]`, `let r = &mut s[j]; j = k; *r = 3; t[s[j]]` and their twins.
/// vcgen spelled `*r` by the referent's post-reseat name and PROVED the read
/// kernel-certified (`trust-vcgen/tests/escaped_local_seam_realmir.rs`, the `a12_*`
/// rows). MEASURED on the same captures through `generate_native_safety_vcs` + the
/// deterministic `ay` router (probe harness, 2026-09-17, `rev13/rev12*_bridge_o*.txt`
/// byte-identical to the previous round's): the native lane's read row is FAILED
/// with a witness on every one of these bodies at both levels — it names no
/// referent by fold and its per-statement store model does not carry the stored
/// value across the reseat. The bridge is therefore not looser than vcgen on this
/// class; this row pins the formula-level half: every bounds row is emitted, none is
/// the vacuous `Bool(false)`, and no formula keys anything on a `[_<l>]` name.
#[test]
fn a12_the_native_lane_keys_no_fact_on_a_referent_folded_across_a_reseat() {
    for name in [
        "rev12_br_store_bug_o0",
        "rev12_br_store_bug_o1",
        "rev12_br_arr_store_bug_o0",
        "rev12_br_arr_store_bug_o1",
        "rev12_br_nested_store_bug_o0",
        "rev12_br_nested_store_bug_o1",
        "rev12_br_raw_store_bug_o1",
        "rev12_br_raw_read_after_store_bug_o1",
        "rev12_rp_deref_read_bug_o1",
        "rev12b_sf_field_reseat_bug_o0",
        "rev12b_sf_field_reseat_bug_o1",
        "rev12b_sf_slice_reseat_bug_o0",
        "rev12b_sf_slice_reseat_bug_o1",
        "rev12b_br_store_call_bug_o0",
        "rev12b_br_store_call_bug_o1",
        "rev13_fs_diamond_reseat_bug_o0",
        "rev13_fs_diamond_reseat_bug_o1",
        "rev13_fs_reborrow_chain_bug_o0",
        "rev13_fs_reborrow_chain_bug_o1",
        "rev13_fs_shared_field_reseat_bug_o0",
        "rev13_fs_shared_field_reseat_bug_o1",
        "rev13b_fs_ref_of_ref_chain_bug_o0",
        "rev13b_fs_ref_of_ref_chain_bug_o1",
        "rev13b_fs_ref_of_ref_mid_bug_o0",
        "rev13b_fs_ref_of_ref_mid_bug_o1",
        // Round A12 (fixer): the carriers of a slot's address (`rev14`/`rev14b`).
        "rev14b_cq_dd_bug_o0",
        "rev14b_cq_dd_bug_o1",
        "rev14b_cq_copy_carrier_bug_o0",
        "rev14b_cq_copy_carrier_bug_o1",
        "rev14b_cq_mid_bug_o0",
        "rev14b_cq_mid_bug_o1",
        "rev14b_cq_triple_bug_o0",
        "rev14b_cq_triple_bug_o1",
        "rev14b_cq_raw_dd_bug_o1",
        "rev14b_cq_raw_copy_bug_o1",
        "rev14_cr_dd_read_bug_o0",
        "rev14_cr_dd_read_bug_o1",
        "rev14_cr_copy_carrier_bug_o0",
        "rev14_cr_copy_carrier_bug_o1",
        "rev14_cr_triple_bug_o0",
        "rev14_cr_triple_bug_o1",
    ] {
        let vcs = native_vcs(name);
        assert!(!vcs.is_empty(), "{name}: the native lane must emit the bounds rows");
        for vc in &vcs {
            assert_ne!(vc.formula, Formula::Bool(false), "{name}: never a vacuous proof");
            let mut idx = Vec::new();
            index_segment_vars(&vc.formula, &mut idx);
            assert!(
                idx.is_empty(),
                "{name}: the native lane now spells an index-embedding name ({idx:?}); a fact \
                 keyed on it would outlive the reseat of the index local — re-measure before \
                 admitting it\n{:?}",
                vc.formula
            );
        }
    }
}

/// The raw-pointer twins at `-O0` (`&raw mut s[j]`, `&raw const *q`): the native lane
/// DECLINES the whole body — `generate_native_safety_vcs` emits no row at all
/// (measured, `rev13/rev12_bridge_o0.txt`; the round-A12 fixer's raw carrier twins
/// `rev14b_cq_raw_*` at `-O0` likewise, `rev14/sweep/rev14b_o0.bridge.txt`) — which is
/// the fail-closed direction and not looser than vcgen. What IS true of them, and all
/// this row asserts: no native formula is the vacuous `Bool(false)` and none keys a
/// fact on an index-embedding name; it does NOT require rows the lane does not emit.
///
/// Trust: 2026-09-17 (round A13) — and the decline is now ASSERTED, because the loop
/// below is the only thing this row used to check and it ran zero times, so every one
/// of these six names passed vacuously and a fixture that stopped deserializing, or a
/// lane that silently stopped emitting anywhere, would have read as green. MEASURED on
/// this tree (`rev17/rb_probe`, `bridge_probe` over the six fixtures): ALL SIX emit
/// nothing — not five-and-one, which is what a review of round A12 expected. A future
/// admission of any of these bodies therefore FAILS here and must come back with the
/// same non-vacuity every other row in this file carries; the loop is kept so that it
/// states what such an admission owes.
#[test]
fn a12_the_native_lane_declines_or_refutes_the_raw_pointer_twins_at_o0() {
    for name in [
        "rev12_br_raw_store_bug_o0",
        "rev12_br_raw_read_after_store_bug_o0",
        "rev12_rp_deref_read_bug_o0",
        "rev14b_cq_raw_dd_bug_o0",
        "rev14b_cq_raw_copy_bug_o0",
        "rev14b_cq_raw_copy_ctl_o0",
    ] {
        let vcs = native_vcs(name);
        assert!(
            vcs.is_empty(),
            "{name}: the native lane DECLINED this body when it was measured; it now emits \
             {} row(s) — re-measure the direction of each before admitting them, and move the \
             name to a row that asserts what they prove\n{:?}",
            vcs.len(),
            vcs.iter().map(|vc| (&vc.kind, &vc.location)).collect::<Vec<_>>()
        );
        for vc in &vcs {
            assert_ne!(vc.formula, Formula::Bool(false), "{name}: never a vacuous proof");
            let mut idx = Vec::new();
            index_segment_vars(&vc.formula, &mut idx);
            assert!(idx.is_empty(), "{name}: an index-embedding name ({idx:?})\n{:?}", vc.formula);
        }
    }
}

/// The controls (`p = o; let r = &mut p.a; *r = 3; t[p.a]`, `s = o; let r = &mut
/// s[0]; *r = 3; t[s[0]]`, `j = k; let r = &s[j]; .. t[*r]`, ok) keep their native
/// rows and none is the fail-closed polarity.
#[test]
fn a12_the_fold_controls_keep_their_native_rows() {
    for name in [
        "rev12b_sf_field_reseat_ctl_o0",
        "rev12b_sf_field_reseat_ctl_o1",
        "rev12b_sf_slice_reseat_ctl_o0",
        "rev12b_sf_slice_reseat_ctl_o1",
        "rev12_br_read_ctl_o0",
        "rev12_br_read_ctl_o1",
        "rev12_br_store_ctl_o0",
        "rev12_br_store_ctl_o1",
        "rev13_fs_shared_field_ctl_o0",
        "rev13_fs_shared_field_ctl_o1",
        "rev13_fs_loop_elem_borrow_ctl_o0",
        "rev13_fs_loop_elem_borrow_ctl_o1",
        "rev13b_fs_ref_of_ref_chain_ctl_o0",
        "rev13b_fs_ref_of_ref_chain_ctl_o1",
        "rev14b_cq_raw_copy_ctl_o1",
        "rev14_cr_dd_read_ctl_o0",
        "rev14_cr_dd_read_ctl_o1",
    ] {
        let vcs = native_vcs(name);
        assert!(!vcs.is_empty(), "{name}: the native lane must emit the bounds rows");
        assert!(
            vcs.iter().all(|vc| vc.formula != Formula::Bool(false)),
            "{name}: never a vacuous proof"
        );
    }
}
