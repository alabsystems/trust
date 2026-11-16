//! RANDOM-CFG DIFFERENTIAL of the SSA statement-version oracle against the retired
//! reaching-version fixpoint (`legacy_version_oracle`), on the shapes the generated
//! families do not reach: DEAD blocks (never targeted from the live region) with
//! dead-to-live edges and dead cycles, self-loops, back edges into `bb0`, irreducible
//! regions, `Cleanup` unwinds on `Call` / `Assert` / `Drop`, `Opaque` terminators,
//! opaque stores through a pointer PARAMETER (CONFINED to a field of a `&mut S`), a
//! `&mut` borrow and a raw pointer, calls handed a shared reborrow `&*p` (a REFINED
//! havoc),
//! `CopyNonOverlapping` with a zero and a non-zero count, `Deinit`, index-local
//! reseats, field writes and array-index writes.
//!
//! Every seed is reproducible (xorshift), and a failure prints the body as JSON. The
//! seed counts are sized for the crate's suite; the WS-E reviews ran the same
//! generators at 6,800 bodies (the harness is `ADV_SEEDS` / `ADV_MAXN`-scalable).
//!
//! What is compared:
//!  * the raw reaching sets `IN[b][k]` for every block and every tracked name, and the
//!    tracked universe;
//!  * the write index's gen-sets and OUT tokens (`legacy_gen_out`);
//!  * every `(block, statement index, name)` query the rename makes, the `#e` gate,
//!    the may-reassigned probe, the coverage probe and the stale-at probe, through the
//!    per-query differential `StmtVersionCtx` runs under `cfg(test)`, and the
//!    statement-prefix kill against the materialised `writes_until` set;
//!  * the whole `generate_vcs` output, the full `Debug` rendering of every VC, once per
//!    oracle.

use std::collections::BTreeSet;

use serde_json::{Value, json};
use trust_types::{BlockId, VerifiableFunction};

use super::legacy_version_oracle::{LegacyStmtVersions, legacy_gen_out, with_legacy_answers};
use super::{StmtVersionCtx, generate_vcs};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }

    fn chance(&mut self, pct: u64) -> bool {
        self.below(100) < pct
    }
}

fn span() -> Value {
    json!({"file": "random.rs", "line_start": 1, "col_start": 0, "line_end": 1, "col_end": 1})
}

fn u(w: u32) -> Value {
    json!({"Int": {"width": w, "signed": false}})
}

fn place(l: usize) -> Value {
    json!({"local": l, "projections": []})
}

fn proj(l: usize, p: Value) -> Value {
    json!({"local": l, "projections": p})
}

fn copy(p: Value) -> Value {
    json!({"Copy": p})
}

fn cu(v: u64) -> Value {
    json!({"Constant": {"Uint": [v, 32]}})
}

fn assign(p: Value, rv: Value) -> Value {
    json!({"Assign": {"place": p, "rvalue": rv, "span": span()}})
}

fn unwind(r: &mut Rng, n: usize) -> Value {
    match r.below(3) {
        0 => json!({"Cleanup": r.below(n as u64) as usize}),
        1 => json!("Continue"),
        _ => json!("Unreachable"),
    }
}

// Locals.
const RET: usize = 0;
const C: usize = 1;
const P: usize = 2;
const X: usize = 3;
const Y: usize = 4;
const S: usize = 5;
const A: usize = 6;
const I: usize = 7;
const Q: usize = 8;
const Z: usize = 9;
const RP: usize = 10;
const T: usize = 11;
const B: usize = 12;
const SR: usize = 13;

fn locals() -> Vec<Value> {
    let adt = json!({"Adt": {"name": "S", "fields": [["f0", u(32)], ["f1", u(32)]],
        "variants": [], "disc_index_safe": false, "faithful_enum_repr": null, "layout": null,
        "enum_layout": null, "adt_kind": "Struct"}});
    let l = |i: usize, ty: Value, name: &str| json!({"index": i, "ty": ty, "name": name});
    vec![
        json!({"index": RET, "ty": u(32), "name": null}),
        l(C, u(32), "c"),
        // A `&mut S` PARAMETER: stores through it are opaque and CONFINED to the
        // written field, and a shared reborrow of `*p` handed to a call is REFINED.
        l(P, json!({"Ref": {"mutable": true, "inner": adt.clone()}}), "p"),
        l(X, u(32), "x"),
        l(Y, u(32), "y"),
        l(S, adt.clone(), "s"),
        l(A, json!({"Array": {"elem": u(32), "len": 4}}), "a"),
        l(I, u(64), "i"),
        l(Q, json!({"Ref": {"mutable": true, "inner": u(32)}}), "q"),
        l(Z, u(32), "z"),
        l(RP, json!({"RawPtr": {"mutable": true, "pointee": u(32)}}), "rp"),
        l(T, u(32), "t"),
        l(B, json!("Bool"), "b"),
        l(SR, json!({"Ref": {"mutable": false, "inner": adt}}), "sr"),
    ]
}

fn stmt(r: &mut Rng, rich: bool) -> Value {
    let k = if rich { r.below(18) } else { r.below(4) };
    match k {
        0 => assign(place([X, Y, Z, T][r.below(4) as usize]), json!({"Use": cu(r.below(9))})),
        1 => assign(place(X), json!({"BinaryOp": ["Add", copy(place(Y)), cu(1)]})),
        2 => assign(place(Y), json!({"Use": copy(place(X))})),
        3 => assign(place(Z), json!({"BinaryOp": ["Add", copy(place(Z)), copy(place(X))]})),
        4 => assign(proj(S, json!([{"Field": r.below(2)}])), json!({"Use": cu(r.below(5))})),
        5 => assign(proj(A, json!([{"Index": I}])), json!({"Use": cu(r.below(5))})),
        6 => assign(place(I), json!({"Use": {"Constant": {"Uint": [r.below(4), 64]}}})),
        7 => assign(place(Q), json!({"Ref": {"mutable": true, "place": place(X)}})),
        8 => assign(proj(Q, json!(["Deref"])), json!({"Use": cu(r.below(5))})),
        9 => {
            assign(proj(P, json!(["Deref", {"Field": r.below(2)}])), json!({"Use": cu(r.below(5))}))
        }
        16 | 17 => {
            assign(place(T), json!({"Use": copy(proj(P, json!(["Deref", {"Field": r.below(2)}])))}))
        }
        10 => assign(place(RP), json!({"AddressOf": [true, place(Y)]})),
        11 => assign(proj(RP, json!(["Deref"])), json!({"Use": cu(r.below(5))})),
        12 => json!({"Deinit": {"place": place(Z)}}),
        13 => json!({"CopyNonOverlapping": {"src": copy(place(RP)), "dst": copy(place(RP)),
            "count": {"Constant": {"Uint": [r.below(2), 64]}}, "elem_ty": u(32),
            "span": span()}}),
        14 => assign(place(T), json!({"Use": copy(proj(A, json!([{"Index": I}])))})),
        _ => assign(place(B), json!({"BinaryOp": ["Lt", copy(place(X)), copy(place(Y))]})),
    }
}

fn term(r: &mut Rng, n: usize, targets: &dyn Fn(&mut Rng) -> usize, rich: bool) -> Value {
    let k = if rich { r.below(11) } else { r.below(4) };
    match k {
        0 => json!({"Goto": targets(r)}),
        1 | 2 => {
            let t1 = targets(r);
            let t2 = targets(r);
            json!({"SwitchInt": {"discr": copy(place(C)), "targets": [[0, t1]], "otherwise": t2,
                "exhaustive_enum_unreachable": false, "span": span()}})
        }
        3 => json!("Return"),
        4 | 5 => {
            let args = match r.below(3) {
                0 => vec![copy(place(P))],
                1 => vec![json!({"Move": place(SR)})],
                _ => vec![cu(3)],
            };
            let dest =
                [place(X), place(Z), proj(S, json!([{"Field": 0}]))][r.below(3) as usize].clone();
            let t = targets(r);
            json!({"Call": {"func": "ext::f", "args": args, "dest": dest, "target": t,
                "span": span(), "atomic": null, "is_foreign": false, "is_unsafe_sig": false,
                "unwind": unwind(r, n)}})
        }
        6 => json!({"Assert": {"cond": copy(place(B)), "expected": true, "msg": "BoundsCheck",
            "target": targets(r), "span": span(), "unwind": unwind(r, n)}}),
        7 => json!({"Drop": {"place": place(Q), "target": targets(r), "span": span(),
            "unwind": unwind(r, n)}}),
        8 => json!({"Opaque": {"kind": "Yield", "targets": [targets(r), targets(r)],
            "span": span()}}),
        9 => json!("Resume"),
        _ => json!("Unreachable"),
    }
}

fn env_or(name: &str, default: u64) -> u64 {
    std::env::var(name).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

/// A random body. `dead_tail` blocks at the end are never targeted by a live-region
/// block; they target anything (dead->live edges, dead cycles).
fn random_fn(seed: u64, rich: bool) -> VerifiableFunction {
    let mut r = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let n = 2 + r.below(env_or("ADV_MAXN", 9)) as usize;
    let dead_tail = if r.chance(40) { 1 + r.below(3) as usize } else { 0 };
    let total = n + dead_tail;
    let chain = env_or("ADV_CHAIN", 0);
    let mut blocks = Vec::new();
    // Half the rich bodies bind the shared reborrow `sr = &*p` once, up front, so a call
    // handed `move sr` is refined; in the other half `sr` is never bound and the
    // refinement declines.
    let reborrow_up_front = rich && r.chance(50);
    for b in 0..total {
        let nst = r.below(4) as usize;
        let mut stmts: Vec<Value> = (0..nst).map(|_| stmt(&mut r, rich)).collect();
        if b == 0 && reborrow_up_front {
            stmts.insert(
                0,
                assign(
                    place(SR),
                    json!({"Ref": {"mutable": false, "place": proj(P, json!(["Deref"]))}}),
                ),
            );
        }
        let live_region = b < n;
        let tgt = move |r: &mut Rng| -> usize {
            if live_region && r.chance(chain) {
                (b + 1) % n
            } else if live_region {
                r.below(n as u64) as usize
            } else {
                r.below(total as u64) as usize
            }
        };
        let t = term(&mut r, n, &tgt, rich);
        blocks.push(json!({"id": b, "stmts": stmts, "terminator": t}));
    }
    let v = json!({
        "name": format!("random_{seed}"), "def_path": format!("random::f{seed}"), "span": span(),
        "body": {"locals": locals(), "blocks": blocks, "arg_count": 2, "return_ty": u(32)},
        "contracts": [], "preconditions": [], "postconditions": [],
        "spec": {"requires": [], "ensures": [], "invariants": []},
    });
    serde_json::from_value(v).expect("a random body deserializes")
}

fn probes(sv: &StmtVersionCtx) -> Vec<String> {
    let mut base: BTreeSet<String> = sv.ssa().tracked_names().into_iter().collect();
    for n in [
        "x",
        "y",
        "z",
        "t",
        "b",
        "c",
        "p",
        "q",
        "rp",
        "s",
        "a",
        "i",
        "_7",
        "p*",
        "q*",
        "rp*",
        "s.0",
        "s.1",
        "a[_7]",
        "a[1]",
        "x__slice_len",
        "q__slice_len",
        "p*__slice_len",
        "a[_7]__slice_len",
        "unrelated",
        "_3",
        "_9",
        "p*.0",
        "p*.1",
        "sr",
        "sr*",
    ] {
        base.insert(n.to_string());
    }
    let mut out = base.clone();
    for n in &base {
        for step in [".0", "*", "[_7]", "[0]", "__slice_len"] {
            out.insert(format!("{n}{step}"));
        }
    }
    out.into_iter().collect()
}

fn panic_text(p: &(dyn std::any::Any + Send)) -> String {
    p.downcast_ref::<String>()
        .cloned()
        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_default()
}

/// Run `check` on every seeded body; a failure names the seed and prints the body.
pub(super) fn for_each_body(
    count: u64,
    rich_modes: &[bool],
    mut check: impl FnMut(&VerifiableFunction),
) {
    let base = env_or("ADV_BASE", 1);
    for &rich in rich_modes {
        for seed in base..base + count {
            let func = random_fn(seed * 2 + u64::from(rich), rich);
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| check(&func)));
            if let Err(e) = r {
                let body = serde_json::to_string(&func).unwrap_or_default();
                panic!("seed {seed} rich={rich}: {}\nBODY: {body}", panic_text(&*e));
            }
        }
    }
}

fn dead_blocks(func: &VerifiableFunction) -> usize {
    let n = func.body.blocks.len();
    let mut live = vec![false; n];
    let mut stack = vec![0usize];
    live[0] = true;
    while let Some(v) = stack.pop() {
        for t in super::full_graph_terminator_targets(&func.body.blocks[v].terminator, BlockId(v)) {
            if t.0 < n && !live[t.0] {
                live[t.0] = true;
                stack.push(t.0);
            }
        }
    }
    live.iter().filter(|l| !**l).count()
}

#[test]
fn random_cfgs_reaching_sets_match_the_retired_fixpoint() {
    let (mut sets, mut non_entry, mut dead) = (0usize, 0usize, 0usize);
    for_each_body(env_or("ADV_SEEDS", 250), &[false, true], |func| {
        dead += dead_blocks(func);
        let sv = StmtVersionCtx::build(func);
        let legacy = LegacyStmtVersions::build(func);
        assert!(legacy.converged(), "the retired fixpoint did not converge");
        let legacy_names: BTreeSet<String> =
            legacy.entry_map().values().flat_map(|em| em.keys().cloned()).collect();
        let ssa_names: BTreeSet<String> = sv.ssa().tracked_names().into_iter().collect();
        // The retired universe is the keys of its IN maps: names that reach SOME block
        // entry (a name gen'd only by blocks with no successor never appears there).
        for name in &legacy_names {
            assert!(ssa_names.contains(name), "the retired oracle tracks `{name}`; SSA does not");
        }
        for b in &func.body.blocks {
            let em = legacy.entry_map().get(&b.id).cloned().unwrap_or_default();
            for k in &ssa_names {
                let want = em.get(k).cloned().unwrap_or_default();
                let got = sv.ssa().entry_tokens(b.id.0, k);
                assert_eq!(got, want, "IN[{:?}][{k}] differs in {}", b.id, func.def_path);
                sets += 1;
                non_entry += usize::from(got.iter().any(|t| t != "e"));
            }
        }
    });
    assert!(sets > 10_000 && non_entry > 1_000 && dead > 50, "vacuous: {sets}/{non_entry}/{dead}");
}

#[test]
fn random_cfgs_gen_sets_and_out_tokens_match() {
    use super::block_writes::{GenFamily, HMode};
    let (mut checked, mut part_versions, mut part_kills) = (0usize, 0usize, 0usize);
    let mut refined = 0usize;
    for_each_body(env_or("ADV_SEEDS", 250), &[true], |func| {
        let sv = StmtVersionCtx::build(func);
        let legacy = legacy_gen_out(func).expect("no budget installed in parity tests");
        for (bi, block) in func.body.blocks.iter().enumerate() {
            let bw = sv.ssa().writes().block(bi).expect("a write index per block");
            refined += usize::from(matches!(
                super::terminator_def_names_structured(func, block).havoc,
                super::TermHavoc::Refined(_)
            ));
            part_versions += usize::from(matches!(bw.h_mode(GenFamily::Versions), HMode::Part(_)));
            part_kills += usize::from(matches!(bw.h_mode(GenFamily::Kills), HMode::Part(_)));
            let got: std::collections::BTreeMap<String, String> = sv
                .ssa()
                .writes()
                .gen_with_tokens(bi)
                .into_iter()
                .map(|(name, tok)| {
                    let tok = match tok {
                        Some(j) => format!("s{}_{j}", block.id.0),
                        None => format!("s{}_t", block.id.0),
                    };
                    (name, tok)
                })
                .collect();
            let want: std::collections::BTreeMap<String, String> =
                legacy[bi].iter().map(|(a, b)| (a.clone(), b.clone())).collect();
            checked += got.len();
            assert_eq!(got, want, "gen/out at bb{bi} of {}", func.def_path);
        }
    });
    // The PART havoc groups (confined stores, refined calls) must actually occur.
    assert!(
        checked > 1_000 && part_versions > 50 && part_kills > 5 && refined > 10,
        "vacuous: {checked} entries, {part_versions} / {part_kills} PART blocks, {refined} \
         refined calls"
    );
}

#[test]
fn random_cfgs_every_point_query_matches() {
    let mut prefix_kills = 0usize;
    for_each_body(env_or("ADV_QUERY_SEEDS", 20), &[false, true], |func| {
        let sv = StmtVersionCtx::build(func);
        let probes = probes(&sv);
        for b in &func.body.blocks {
            let block_havoc = !super::deref_store_havoc_names(func, b).is_empty();
            for name in &probes {
                for i in 0..=b.stmts.len() + 1 {
                    let _ = sv.version_token_at(func, b.id, i, name);
                    let _ = sv.is_versioned_stale_at(func, b.id, i, name);
                    // The statement-prefix kill, against the materialised set.
                    let got = sv.prefix_kill_rebinds(func, b.id, i, name, block_havoc);
                    // The prefix's writes (destinations and preceding opaque-store
                    // havoc) under the destination relation; the conservative
                    // whole-block havoc under the plain relation a havoc base name
                    // carries (2026-09-29, `KillSet::havoc`).
                    let set = super::writes_until_uncached(func, b, i);
                    let want = set.iter().any(|n| super::dest_write_rebinds(n, name))
                        || (block_havoc
                            && super::deref_store_havoc_names(func, b)
                                .iter()
                                .any(|n| super::write_rebinds(n, name)));
                    assert_eq!(got, want, "prefix kill of `{name}` at {:?}[{i}]", b.id);
                    prefix_kills += 1;
                }
                let _ = sv.full_graph_union_is_entry_only(b.id, name);
                let _ = sv.may_reassigned_rebinds(b.id, name);
                let _ = sv.entry_map_covers(b.id, name);
            }
        }
    });
    assert!(prefix_kills > 20_000, "vacuous: {prefix_kills}");
}

#[test]
fn random_cfgs_generate_byte_identical_vcs() {
    let (mut generated, mut versioned) = (0usize, 0usize);
    for_each_body(env_or("ADV_GEN_SEEDS", 100), &[false, true], |func| {
        let render = |vcs: &[trust_types::VerificationCondition]| -> Vec<String> {
            vcs.iter().map(|vc| format!("{vc:?}")).collect()
        };
        // A body the generator itself rejects (a panic unrelated to the oracles) is
        // skipped; a DIFFERENTIAL panic inside either run is a failure.
        let legacy = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            with_legacy_answers(|| render(&generate_vcs(func)))
        }));
        let ssa =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| render(&generate_vcs(func))));
        match (legacy, ssa) {
            (Ok(a), Ok(b)) => {
                assert_eq!(a, b, "generation differs between the oracles for {}", func.def_path);
                generated += 1;
                versioned += b.iter().filter(|line| line.contains('#')).count();
            }
            (Err(e), _) | (_, Err(e)) => {
                let text = panic_text(&*e);
                assert!(
                    !text.contains("differential"),
                    "a differential failed during generation: {text}"
                );
            }
        }
    });
    assert!(generated > 100 && versioned > 100, "vacuous: {generated}/{versioned}");
}

/// The rebinder index ([`super::rebind_index::RebindIndex`]) and the incremental
/// rebinder set the definition extraction's clobber walk uses
/// ([`super::rebind_index::RebindSet`]) against the two predicates, over a grammar of
/// unusual spellings (`#` tokens, `$`, nested or unbalanced brackets, empty names).
#[test]
fn rebinder_structures_match_the_predicates_on_a_random_grammar() {
    use super::rebind_index::{NameTable, RebindIndex, RebindMode, RebindSet};
    let atoms = ["x", "_3", "_30", "a", "", "self", "arr$6$v1", "x_y"];
    let steps = [
        ".0",
        ".1",
        "[0]",
        "[_3]",
        "[_k]",
        "[_30]",
        "*",
        "__slice_len",
        "#s1_0",
        "#e",
        "[a[_3]]",
        "[",
        "]",
        "[_3",
        "$v2",
        "_",
        // Downcast payloads (`@` is a projection separator; W4 vecslice): a whole
        // write of `x` must rebind `x@1.0`, and the index must split there too.
        "@1.0",
        "@0",
        // Literal index spellings that may name one element (`place_names_overlap`'s
        // literal-index alias, c40884c0106; channel 7 of the index since the merge of
        // 2026-10-14): pattern minimum lengths, from-end constants, a shared-slice
        // constant, a subslice.
        "[0;min=1]",
        "[0;min=2]",
        "[-1;min=1]",
        "[1;slice]",
        "[1..-0]",
    ];
    let mut r = Rng(0x1234_5678_9abc_def1);
    let mk = |r: &mut Rng| {
        let mut s = atoms[r.below(atoms.len() as u64) as usize].to_string();
        for _ in 0..r.below(4) {
            s.push_str(steps[r.below(steps.len() as u64) as usize]);
        }
        s
    };
    let mut related = 0usize;
    for _ in 0..3000 {
        let mut table = NameTable::default();
        let mut set = RebindSet::default();
        let mut set_derived = RebindSet::default();
        let mut ref_derived = RebindSet::default();
        let members: Vec<u32> = (0..1 + r.below(12))
            .map(|_| {
                let n = mk(&mut r);
                set.insert(&n);
                set_derived.insert_with_derived_slice_len(&n);
                ref_derived.insert(&n);
                if !n.ends_with(super::SLICE_LEN_SUFFIX) {
                    ref_derived.insert(&format!("{n}{}", super::SLICE_LEN_SUFFIX));
                }
                table.intern(&n)
            })
            .collect();
        let index = RebindIndex::build(&table, members.iter().copied());
        for _ in 0..20 {
            let read = mk(&mut r);
            for mode in [RebindMode::Plain, RebindMode::Dest] {
                let mut got: BTreeSet<String> = BTreeSet::new();
                index.for_each_rebinder(&read, mode, |w| {
                    got.insert(table.name(w).to_string());
                });
                let want: BTreeSet<String> = members
                    .iter()
                    .map(|&w| table.name(w).to_string())
                    .filter(|w| match mode {
                        RebindMode::Plain => super::write_rebinds(w, &read),
                        RebindMode::Dest => super::dest_write_rebinds(w, &read),
                    })
                    .collect();
                related += want.len();
                assert_eq!(got, want, "{mode:?} rebinders of `{read}`");
                assert_eq!(index.any_rebinder(&read, mode), !want.is_empty());
                if mode == RebindMode::Plain {
                    assert_eq!(set.any_rebinder(&read), !want.is_empty(), "RebindSet on `{read}`");
                }
            }
            assert_eq!(
                set_derived.any_rebinder(&read),
                ref_derived.any_rebinder(&read),
                "insert_with_derived_slice_len on `{read}`"
            );
            let read_len = format!("{read}{}", super::SLICE_LEN_SUFFIX);
            assert_eq!(
                set_derived.any_rebinder(&read_len),
                ref_derived.any_rebinder(&read_len),
                "insert_with_derived_slice_len on `{read_len}`"
            );
            let read_len_proj = format!("{read_len}.0");
            assert_eq!(
                set_derived.any_rebinder(&read_len_proj),
                ref_derived.any_rebinder(&read_len_proj),
                "insert_with_derived_slice_len on `{read_len_proj}`"
            );
        }
    }
    assert!(related > 1000, "vacuous: {related}");
}
