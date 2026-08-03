// Regression (task #27): a guarded `&mut [T]` index `if i < dst.len() { dst[i] = .. }`
// must verify, and an unguarded `dst[i] = ..` must still be refuted.
//
// `dst.len()` on a `&mut [T]` lowers via a `FakeForPtrMetadata` raw pointer
// (`_p = &raw const *dst; _len = PtrMetadata(_p)`) — modeled as a const
// `AddressOf` (trust-mir-extract) whose `__slice_len` is tied to `dst__slice_len`
// (trust-vcgen guards). Two things must hold:
//
//   1. The bounds VC's guard (`i < dst__slice_len`) and violation (`i >= _7`) share
//      one slice-length value through the chain
//      `_7 == _6__slice_len == dst__slice_len`, so the conjunction is UNSAT (PROVED).
//   2. The synthetic metadata-read `&raw const` must NOT emit a spurious
//      `[unsafe:sep:addr_of]` source-liveness obligation — it never dereferences —
//      else the safe function false-refutes. (sep_engine::metadata_only_addr_of_locals)
//
// Fixtures are the REAL extracted MIR (via -Ztrust-dump=mir:<dir>) of:
//   guarded:   pub fn zero_at(dst: &mut [u8], i: usize) { if i < dst.len() { dst[i] = 0; } }
//   unguarded: pub fn zero_at_unchecked(dst: &mut [u8], i: usize) { dst[i] = 0; }
use trust_types::*;
use trust_vcgen::generate_vcs;

fn is_unsafe_addr_of(vc: &VerificationCondition) -> bool {
    matches!(&vc.kind, VcKind::Assertion { message } if message.contains("[unsafe:sep:addr_of]"))
}

#[test]
fn guarded_mut_index_proves_without_spurious_unsafe_vc() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/guarded_mut_index_mir.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);

    // No spurious source-liveness obligation for the metadata-read `&raw const`.
    assert!(
        !vcs.iter().any(is_unsafe_addr_of),
        "metadata-only `&raw const` (dst.len()) must not emit an addr_of source-liveness VC: {:#?}",
        vcs.iter().map(|v| format!("{:?}", v.kind)).collect::<Vec<_>>()
    );

    // The bounds VC must exist and share one place-keyed slice length between the
    // dominating guard and the violation (so the conjunction is UNSAT).
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .expect("guarded &mut index must produce a bounds VC");
    let dbg = format!("{:?}", vc.formula);
    assert!(
        dbg.contains("dst__slice_len"),
        "bounds VC must thread the stable `dst__slice_len`: {dbg}"
    );
    // The violation length local must be tied back to the slice length.
    assert!(
        dbg.matches("__slice_len").count() >= 3,
        "guard, AddressOf tie, and PtrMetadata must all share the slice length: {dbg}"
    );

    // Regression (P0 false-refutation, 2026-07-02 — the `__slice_len`
    // version-oracle mismatch): name PRESENCE is not enough. The S2c
    // establish-point versioning renamed the PtrMetadata read to the phantom
    // token `_6__slice_len#s{b}_pre` while the AddressOf tie fact
    // `Eq(_6__slice_len, dst__slice_len)` stayed BARE (unpinnable), so the two
    // were name-DISJOINT, the tie was pruned as irrelevant, and the length var
    // in the violation was UNCONSTRAINED — ay refuted the provably-safe
    // function with a `len = 0` counterexample. Assert CONNECTIVITY: every
    // temp-derived `__slice_len` variable occurring in the bounds VC (any
    // `#token` version) must be Eq-tied — under that EXACT name — to the
    // stable `dst__slice_len`.
    let mut names: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    collect_var_names(&vc.formula, &mut names);
    let mut ties: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    collect_slice_len_ties(&vc.formula, "dst__slice_len", &mut ties);
    for name in &names {
        let base = name.split('#').next().unwrap_or(name);
        if base != "dst__slice_len" && base.ends_with("__slice_len") {
            assert!(
                ties.contains(name),
                "slice-length read `{name}` is not Eq-tied to `dst__slice_len` under its \
                 exact (versioned) name — the tie fact was dropped or version-disjoint, \
                 so the bounds VC is refutable with an unconstrained length: {dbg}"
            );
        }
    }
}

/// Collect every `Var` name in `f` (recursing through all sub-formulas).
fn collect_var_names(f: &Formula, out: &mut std::collections::BTreeSet<String>) {
    let _ = f.clone().map(&mut |node| {
        if let Formula::Var(name, _) = &node {
            out.insert(name.clone());
        }
        node
    });
}

/// Collect the lhs/rhs names of every `Eq(Var(a), Var(b))` conjunct where the
/// OTHER side's version-stripped base is `stable`: the names that ARE tied to
/// the stable parameter length (directly or through its own versioned copies).
fn collect_slice_len_ties(f: &Formula, stable: &str, out: &mut std::collections::BTreeSet<String>) {
    let _ = f.clone().map(&mut |node| {
        if let Formula::Eq(l, r) = &node
            && let (Formula::Var(a, _), Formula::Var(b, _)) = (l.as_ref(), r.as_ref())
        {
            if a.split('#').next() == Some(stable) {
                out.insert(b.clone());
            }
            if b.split('#').next() == Some(stable) {
                out.insert(a.clone());
            }
        }
        node
    });
}

#[test]
fn unguarded_mut_index_still_emits_bounds_obligation() {
    // SOUNDNESS: suppressing the metadata-read addr_of VC must NOT suppress the
    // real bounds obligation. An unguarded `dst[i] = ..` must still be checked
    // (and, lacking a guard, refuted downstream).
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/unguarded_mut_index_mir.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)),
        "unguarded &mut index must still produce a bounds VC: {:#?}",
        vcs.iter().map(|v| format!("{:?}", v.kind)).collect::<Vec<_>>()
    );
}
