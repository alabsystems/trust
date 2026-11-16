// Regression (drop-in, 2026-07-06): nested `v[i][j]` on an IMMUTABLE `&Vec<Vec>`
// refuted `[slice]` (while flat compound guards and `let inner=&v[i]` prove). The two
// syntactic `v[i]` reads (guard `j<v[i].len()` and access `v[i][j]`) lower to SEPARATE
// `Index::index(v,i)` Calls whose inner-collection lengths never tied. Fix
// (`build_immutable_index_len_tie_facts`): for a SHARED-ref base (immutable BY TYPE — no
// resize is formable) with a pure-input index, tie `coll_len(dest_a)==coll_len(dest_b)`.
// SOUND BY CONSTRUCTION (static `Ty::Ref{mutable:false}` gate, not mut-borrow analysis).
//
// Trust (2026-10-04, IDX-TIE-1): the tie now requires std's own scalar
// `<S as Index<usize>>::index` on a std container (`is_std_scalar_index_call` and a
// slice/array/`Seq`/std-`Vec` root), because a method merely NAMED `index` gave a
// false `slice proved`. These three fixtures spelled every index call as the bare
// `std::ops::Index::index`, which the extractor never emits and which names no
// impl; they now carry the extractor's spelling (measured on the stage 1 of
// `936573497e`: `<alloc::vec::Vec<alloc::vec::Vec<u32>> as
// core::ops::index::Index<usize>>::index` for `v[i]`, `<alloc::vec::Vec<u32> as
// core::ops::index::Index<usize>>::index` for `v[i][j]`). The bare spelling is kept
// as a negative (`a_bare_index_spelling_does_not_tie`).
use trust_types::*;
use trust_vcgen::generate_vcs;

fn load(name: &str) -> VerifiableFunction {
    serde_json::from_str(&std::fs::read_to_string(format!("tests/fixtures/{name}.json")).unwrap())
        .unwrap()
}

fn has_len_tie(name: &str) -> bool {
    func_has_len_tie(&load(name))
}

fn func_has_len_tie(f: &VerifiableFunction) -> bool {
    generate_vcs(f).iter().any(|vc| {
        let d = format!("{:?}", vc.formula);
        d.contains("Eq(Var(\"_8\", Int), Var(\"_10\", Int))")
            || d.contains("Eq(Var(\"_10\", Int), Var(\"_8\", Int))")
    })
}

#[test]
fn shared_vec_of_vec_ties_inner_index_lengths() {
    // The FIX: the two `v[i]` inner-Vec coll_lens are tied for a shared `&Vec<Vec>`, so
    // the `j<v[i].len()` guard discharges the `v[i][j]` access (proved end-to-end).
    assert!(has_len_tie("nest2_shared"), "shared &Vec<Vec> must tie the two v[i] lengths");
}

#[test]
fn mut_vec_of_vec_does_not_tie() {
    // SOUNDNESS: a `&mut Vec<Vec>` base is NOT immutable-by-type (it can be resized), so
    // the tie must DECLINE — no false-PROVE. (End-to-end this refutes conservatively.)
    assert!(!has_len_tie("nest2_mutbase"), "&mut Vec<Vec> must NOT tie (resize hazard)");
}

#[test]
fn wrong_index_stays_refutable() {
    // SOUNDNESS: the tie unifies the two `v[i]` LENGTHS only — it must NOT bound the index.
    // `if …j<v[i].len() { v[i][k] }` (access uses `k`, guard is on `j`) has the tie present
    // yet stays refutable, since `k` is unconstrained (validated end-to-end: refutes [slice]).
    let f: VerifiableFunction = serde_json::from_str(
        &std::fs::read_to_string("tests/fixtures/nest_wrongidx.json").unwrap(),
    )
    .unwrap();
    let inner = generate_vcs(&f).into_iter().any(|vc| {
        matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
            && format!("{:?}", vc.formula).contains("Ge(Var(\"k\"")
    });
    assert!(inner, "the `v[i][k]` access keeps a refutable bounds obligation on `k`");
}

#[test]
fn a_bare_index_spelling_does_not_tie() {
    // The SAME shared `&Vec<Vec>` body, with the index calls spelled the old bare
    // way: `std::ops::Index::index` names no impl (a user `Index` impl renders
    // under that trait too), so the tie declines.
    let mut f = load("nest2_shared");
    for block in &mut f.body.blocks {
        if let Terminator::Call { func, .. } = &mut block.terminator
            && func.ends_with("as core::ops::index::Index<usize>>::index")
        {
            *func = "std::ops::Index::index".to_string();
        }
    }
    assert!(!func_has_len_tie(&f), "a bare `Index::index` must not tie the two v[i] lengths");
}
