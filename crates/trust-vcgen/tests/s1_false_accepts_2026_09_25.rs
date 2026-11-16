// Trust (2026-09-25): the vcgen halves of the S1 false-accept fixes, pinned on
// REAL MIR (`-Ztrust-dump=mir`, paths sanitized). Each shape built rc=0 on the
// default lane on stage-1 `ab7e41892` and panicked at runtime; the end-to-end
// pins are the `tests/ui/trust/policy_b/{collect_extend_capacity_charged,
// integer_fold_overflow_charged,btree_range_order_charged}.rs` revisions. These
// tests pin the obligation each lane now MINTS, which a dump can show; they do
// not claim the compiler path (dumps are optimized MIR).
use trust_types::*;

/// Trust (ALLOC-WIDTH-1, 2026-10-08): these fixtures are extractions on a 64-bit
/// host, generated as the compiler generates them there — with the target's
/// pointer width installed (`VcgenContext::with_target_pointer_bits`). Without it
/// the allocation lane judges at 32 bits and grants no live-source bound.
fn generate_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    trust_vcgen::with_target_pointer_bits(Some(64), || trust_vcgen::generate_vcs(func))
}

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn has_unsupported(vcs: &[VerificationCondition], needle: &str) -> bool {
    vcs.iter()
        .any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind.contains(needle)))
}

/// A product of two NON-constant terms anywhere in `f` — the nonlinear shape the
/// in-process solver answers `Unknown`, which a fold row must not carry. Read off
/// the SMT-LIB rendering: a `(* a b)` application whose arguments are not both
/// numerals (`12`, `(- 12)`) or closed arithmetic over numerals.
fn has_symbolic_product(f: &Formula) -> bool {
    #[derive(Debug)]
    enum S {
        Atom(String),
        List(Vec<S>),
    }
    fn parse(tokens: &mut std::iter::Peekable<std::vec::IntoIter<String>>) -> S {
        match tokens.next().as_deref() {
            Some("(") => {
                let mut items = Vec::new();
                while tokens.peek().is_some_and(|t| t != ")") {
                    items.push(parse(tokens));
                }
                tokens.next();
                S::List(items)
            }
            Some(atom) => S::Atom(atom.to_string()),
            None => S::List(Vec::new()),
        }
    }
    fn closed(s: &S) -> bool {
        match s {
            S::Atom(a) => a.chars().all(|c| c.is_ascii_digit()),
            S::List(items) => {
                matches!(items.first(), Some(S::Atom(op)) if ["-", "+", "*"].contains(&op.as_str()))
                    && items[1..].iter().all(closed)
            }
        }
    }
    fn walk(s: &S) -> bool {
        match s {
            S::Atom(_) => false,
            S::List(items) => {
                let symbolic_mul = matches!(items.first(), Some(S::Atom(op)) if op == "*")
                    && items[1..].iter().filter(|a| !closed(a)).count() >= 2;
                symbolic_mul || items.iter().any(walk)
            }
        }
    }
    let text = f.to_smtlib();
    let tokens: Vec<String> = text
        .replace('(', " ( ")
        .replace(')', " ) ")
        .split_whitespace()
        .map(str::to_string)
        .collect();
    let mut it = tokens.into_iter().peekable();
    let mut any = false;
    while it.peek().is_some() {
        any |= walk(&parse(&mut it));
    }
    any
}

#[test]
fn the_symbolic_product_instrument_has_a_positive_control() {
    let x = Formula::Var("x".into(), Sort::Int);
    let y = Formula::Var("y".into(), Sort::Int);
    let two = Formula::Int(2);
    assert!(has_symbolic_product(&Formula::Gt(
        Box::new(Formula::Mul(Box::new(x.clone()), Box::new(y))),
        Box::new(two.clone())
    )));
    assert!(!has_symbolic_product(&Formula::Gt(
        Box::new(Formula::Mul(Box::new(two.clone()), Box::new(x))),
        Box::new(two)
    )));
}

// ---- F4: the fold recognizer fires on rustc's qualified spelling ----

#[test]
fn a_qualified_slice_sum_mints_the_unbounded_fold_row() {
    // `v.iter().sum::<u32>()`: `<core::slice::iter::Iter<'_, u32> as
    // core::iter::traits::iterator::Iterator>::sum::<u32>`. Zero rows before.
    let vcs = generate_vcs(&load(include_str!("fixtures/s1_iter_sum_u32_qualified_mir.json")));
    assert!(
        has_unsupported(&vcs, "iterator-fold-overflow"),
        "a slice sum's item count is unbounded: the fold row must be minted"
    );
}

#[test]
fn a_range_sum_mints_a_linear_overflow_row() {
    for (name, json) in [
        ("unguarded", include_str!("fixtures/s1_range_sum_unguarded_mir.json")),
        ("guarded", include_str!("fixtures/s1_range_sum_guarded_mir.json")),
    ] {
        let vcs = generate_vcs(&load(json));
        let rows: Vec<_> = vcs
            .iter()
            .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
            .collect();
        assert_eq!(rows.len(), 1, "{name}: `(a..b).sum()` has a derivable count: one Add row");
        assert!(
            !has_symbolic_product(&rows[0].formula),
            "{name}: the fold row must stay LINEAR (a symbolic product is answered Unknown \
             and reported runtime-checked)"
        );
    }
}

// ---- F2: `extend` is an allocation sink ----

/// Trust (2026-11-11): the fixture's one `extend` call with the element-size token
/// the extractor stamps on it today. The fixture was dumped on 2026-09-25, before
/// W4 HASHMAP r3 (`2b5f15e9cf`, 2026-09-29) stamped an `extend` into a contiguous
/// std collection with its receiver's exact element size (`trust-mir-extract`'s
/// `contiguous_extend_or_unzip_elem_bytes`). A current extraction renders this call
/// `…::extend::<…::RepeatN<u64>>::<__trust_elem_bytes@8>`, the spelling
/// `fixtures/zst_receiver_growth/ext_vec_zst.json` (dumped 2026-10-14) carries at
/// `@0`. This appends that suffix and changes nothing else; it is not a re-extraction.
fn with_extend_elem_bytes(mut func: VerifiableFunction, elem_bytes: u64) -> VerifiableFunction {
    let mut stamped = 0;
    for block in &mut func.body.blocks {
        if let Terminator::Call { func: callee, .. } = &mut block.terminator
            && callee.contains(" as core::iter::traits::collect::Extend<")
        {
            callee.push_str(&render_trailing_elem_bytes_token(elem_bytes));
            stamped += 1;
        }
    }
    assert_eq!(stamped, 1, "the fixture has exactly one `extend` call");
    func
}

fn has_extend_allocation_row(vcs: &[VerificationCondition]) -> bool {
    vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::UnboundedAllocation { callee, .. } if callee == "Extend::extend"
        )
    })
}

#[test]
fn a_vec_extend_from_repeat_n_is_charged_as_an_allocation() {
    let fixture = || load(include_str!("fixtures/s1_vec_extend_repeat_n_mir.json"));
    // As the compiler extracts it today: the `Vec<u64>` receiver's element is 8 bytes.
    let stamped = generate_vcs(&with_extend_elem_bytes(fixture(), 8));
    assert!(
        has_extend_allocation_row(&stamped),
        "`v.extend(repeat_n(x, n))` reserves `n`: it must carry an allocation row"
    );
    // Trust (2026-11-11): as dumped, the call carries no element-size token. Since
    // `1b5061bbe0` ("Keep unknown allocation layouts out of count-only proofs") a
    // counted row with no derivable stride is a visible Unknown, not the count-only
    // row `n >= 2^28` that a guard on `n` would discharge whatever the element's size.
    // Still a charge, never a proof.
    let unstamped = generate_vcs(&fixture());
    let element_size_unknown = "UnboundedAllocation::Extend::extend::element-size-not-derivable";
    assert!(
        has_unsupported(&unstamped, element_size_unknown) && !has_extend_allocation_row(&unstamped),
        "without an element size, `v.extend(repeat_n(x, n))` must keep the visible \
         element-size Unknown and no count-only row"
    );
}

// ---- F3: a zero-sized source bounds nothing ----

#[test]
fn a_zero_sized_source_loses_the_bounded_source_grant_and_a_sized_one_keeps_it() {
    let zst = generate_vcs(&load(include_str!("fixtures/s1_vec_collect_zst_refs_mir.json")));
    assert!(
        has_unsupported(&zst, "UnboundedAllocation::Iterator::collect::count-not-derivable"),
        "`v.iter().collect::<Vec<&()>>()` over `&[()]`: the grant must be withheld"
    );
    let sized = generate_vcs(&load(include_str!("fixtures/s1_vec_collect_u64_refs_mir.json")));
    assert!(
        !has_unsupported(&sized, "UnboundedAllocation")
            && !sized.iter().any(|vc| matches!(vc.kind, VcKind::UnboundedAllocation { .. })),
        "`v.iter().collect::<Vec<&u64>>()` over `&[u64]` keeps the grant"
    );
}

// ---- F5: `BTreeMap::range` joins the call-site panic family ----

#[test]
fn a_btree_range_mints_the_ordering_row_in_both_the_unguarded_and_guarded_bodies() {
    for (name, json) in [
        ("unordered", include_str!("fixtures/s1_btree_range_unordered_mir.json")),
        ("guarded", include_str!("fixtures/s1_btree_range_guarded_mir.json")),
    ] {
        let vcs = generate_vcs(&load(json));
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.starts_with("BTreeMap/BTreeSet::range")
            )),
            "{name}: `m.range(a..b)` must carry the `start <= end` row (the guard discharges \
             it in the guarded body; it does not remove it)"
        );
    }
}
