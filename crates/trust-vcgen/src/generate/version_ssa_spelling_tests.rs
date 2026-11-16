//! THE SPELLING OF A JOINED VERSION TOKEN (D15): a joined reaching set whose retired
//! `_`-joined spelling is longer than 33 bytes is spelled `h` + the first 128 bits of a
//! SHA-256 Merkle hash of its (canonical) treap, checked against a process-wide
//! collision registry that falls back to the exact retired spelling on a collision.
//!
//! What is pinned here:
//!  * PARTITION IDENTITY with the retired spelling: two queries share a token iff their
//!    retired tokens are equal — across queries, oracle instances, functions, memo on
//!    and off — on the generated families and the random CFGs, at the production
//!    threshold and with EVERY joined set hashed, with full-width hashes and with hashes
//!    truncated to a few bits (collisions guaranteed, every one caught);
//!  * the D15 hazard itself: two oracle instances whose FIRST joined answers are
//!    different sets (the ordinal spelling `j0` for both — merged SMT variables) spell
//!    them differently, and spell each set the same way;
//!  * a forced collision falls back to the exact retired spelling;
//!  * byte identity of whole generations across instances and memo modes;
//!  * the output bytes are now linear (`diamond_chain`, `loop_joins`,
//!    `confined_store_blocks`).

use std::collections::BTreeMap;

use trust_types::{BlockId, VerifiableFunction};

use super::legacy_version_oracle::{LegacyStmtVersions, without_differential};
use super::version_ssa::{retired_spelling_of_texts, spell_test, spell_token_texts};
use super::{StmtVersionCtx, generate_vcs, version_ssa_families as families};

/// Every `(block, read)` pair the inter-block arm can be asked for a function: every
/// tracked name at every block.
fn points(func: &VerifiableFunction, sv: &StmtVersionCtx) -> Vec<(BlockId, String)> {
    let names = sv.ssa().tracked_names();
    let mut out = Vec::new();
    for b in &func.body.blocks {
        for n in &names {
            out.push((b.id, n.clone()));
        }
    }
    out
}

/// A bijection check between two spellings of the same answers: `new -> retired` and
/// `retired -> new` must both be functions.
#[derive(Default)]
struct Partition {
    fwd: BTreeMap<String, String>,
    back: BTreeMap<String, String>,
    hashed: usize,
    joined: usize,
}

impl Partition {
    fn add(&mut self, new: Option<String>, retired: Option<String>, at: &str) {
        let (new, retired) = (new.unwrap_or_default(), retired.unwrap_or_default());
        self.hashed += usize::from(new.starts_with('h'));
        self.joined += usize::from(retired.len() > 33 || retired.contains("_s"));
        if let Some(prev) = self.fwd.insert(new.clone(), retired.clone()) {
            assert_eq!(prev, retired, "`{new}` spells two different sets ({at})");
        }
        if let Some(prev) = self.back.insert(retired.clone(), new.clone()) {
            assert_eq!(prev, new, "one set `{retired}` has two spellings ({at})");
        }
    }
}

/// Feed every point of `func` — the SSA oracle's inter-block answer against the
/// retired oracle's answer in the RETIRED spelling — into `p`, from a FRESH oracle
/// instance each time.
fn feed(func: &VerifiableFunction, p: &mut Partition) {
    let sv = without_differential(|| StmtVersionCtx::build(func));
    let legacy = LegacyStmtVersions::build(func);
    assert!(legacy.converged());
    for (b, n) in points(func, &sv) {
        let new = sv.ssa().inter_block_token(b.0, &n);
        let retired = legacy.inter_block_token_retired(b, &n);
        p.add(new, retired, &format!("{} {b:?} {n}", func.def_path));
    }
}

fn corpus() -> Vec<VerifiableFunction> {
    let mut out = Vec::new();
    for n in [2usize, 5, 9, 16] {
        out.extend(families::all_families(n));
    }
    out
}

#[test]
fn hashed_spellings_partition_reads_exactly_as_the_retired_spelling() {
    // Production threshold, full-width hashes; then every joined set hashed; then
    // hashes truncated to 6 and to 0 bits (every node collides with the empty set).
    for (threshold, bits) in [(None, 128), (Some(0), 128), (Some(0), 6), (Some(0), 0)] {
        let (p, collisions) = spell_test::isolated(bits, threshold, || {
            let mut p = Partition::default();
            for func in corpus() {
                feed(&func, &mut p);
            }
            p
        });
        println!(
            "PARTITION families threshold={threshold:?} bits={bits}: {} spellings, {} long \
             joins, {} hashed answers, {collisions} collisions caught",
            p.fwd.len(),
            p.joined,
            p.hashed
        );
        assert!(p.joined > 200, "vacuous corpus: {} joined answers", p.joined);
        match (threshold, bits) {
            (_, 128) => {
                assert!(p.hashed > 50, "no hashed spelling at threshold {threshold:?}");
                assert_eq!(collisions, 0, "a 128-bit collision on the corpus");
            }
            (_, 0) => {
                assert_eq!(p.hashed, 0, "a 0-bit hash must collide on every node");
                assert!(collisions > 0);
            }
            _ => assert!(collisions > 0 && p.hashed > 0, "6 bits: {collisions} / {}", p.hashed),
        }
    }
}

/// The same partition identity on the extracted real-MIR corpus and the random CFGs
/// (dead blocks, irreducible regions, unwinds, confined and refined havocs), with EVERY
/// joined set hashed — at full width, and truncated to 6 bits.
#[test]
fn hashed_spellings_partition_the_extracted_and_random_corpora_exactly() {
    let extracted = super::version_ssa_parity_tests::corpus();
    assert!(extracted.len() >= 60, "the extracted corpus shrank to {}", extracted.len());
    for bits in [128u32, 6] {
        let ((p, skipped), collisions) = spell_test::isolated(bits, Some(0), || {
            let mut p = Partition::default();
            let mut skipped = 0usize;
            for (_, func) in &extracted {
                // A body the retired fixpoint does not converge on has no reference.
                if LegacyStmtVersions::build(func).converged() {
                    feed(func, &mut p);
                } else {
                    skipped += 1;
                }
            }
            super::version_ssa_random_tests::for_each_body(60, &[false, true], |func| {
                feed(func, &mut p);
            });
            (p, skipped)
        });
        println!(
            "PARTITION extracted+random bits={bits}: {} spellings, {} joins, {} hashed \
             answers, {collisions} collisions caught, {skipped} unconverged bodies skipped",
            p.fwd.len(),
            p.joined,
            p.hashed
        );
        assert!(p.hashed > 100, "vacuous: {} hashed answers", p.hashed);
        if bits == 128 {
            assert_eq!(collisions, 0);
        } else {
            assert!(collisions > 0, "6-bit hashes over this corpus must collide");
        }
    }
}

/// The D15 hazard: oracle A's first joined answer is `x`'s set after diamond 7, oracle
/// B's is `x`'s set after diamond 6. An ordinal spelling calls both `j0`, and one VC
/// holding both reads would merge two SMT variables.
#[test]
fn two_instances_first_joined_answers_never_share_a_spelling() {
    let func = families::diamond_chain(8);
    let join = |i: usize| BlockId(4 + 4 * i);
    without_differential(|| {
        let a = StmtVersionCtx::build(&func);
        let b = StmtVersionCtx::build(&func);
        let a7 = a.version_token_at(&func, join(7), 0, "x").expect("joined");
        let b6 = b.version_token_at(&func, join(6), 0, "x").expect("joined");
        assert!(a7.starts_with('h') && b6.starts_with('h'), "{a7} / {b6}");
        assert_ne!(a7, b6, "two different reaching sets share one spelling across instances");
        // And each set has ONE spelling whichever instance, in whichever order, asks.
        assert_eq!(a.version_token_at(&func, join(6), 0, "x").as_deref(), Some(b6.as_str()));
        assert_eq!(b.version_token_at(&func, join(7), 0, "x").as_deref(), Some(a7.as_str()));
    });
}

/// Twin of the test above: the SAME set, asked first by two instances, is one spelling.
#[test]
fn two_instances_spell_one_set_identically() {
    let func = families::diamond_chain(8);
    without_differential(|| {
        let a = StmtVersionCtx::build(&func);
        let b = StmtVersionCtx::build(&func);
        let ta = a.version_token_at(&func, BlockId(32), 0, "x");
        let tb = b.version_token_at(&func, BlockId(32), 0, "x");
        assert!(ta.as_deref().is_some_and(|t| t.starts_with('h')));
        assert_eq!(ta, tb);
    });
}

/// A forced collision: with 1-bit hashes the second distinct hashed set collides, and
/// it — not the first — takes the exact retired spelling.
#[test]
fn a_collision_falls_back_to_the_exact_retired_spelling() {
    let x: Vec<String> = (0..6).map(|i| format!("s{}_0", 10 + i)).collect();
    let y: Vec<String> = (0..6).map(|i| format!("s{}_0", 20 + i)).collect();
    let (spelled, collisions) = spell_test::isolated(1, Some(0), || {
        let sx = spell_token_texts(x.iter().map(String::as_str)).expect("joined");
        let sy = spell_token_texts(y.iter().map(String::as_str)).expect("joined");
        // Asked again, in the other order: the registry's decisions are permanent.
        let sy2 = spell_token_texts(y.iter().map(String::as_str)).expect("joined");
        let sx2 = spell_token_texts(x.iter().map(String::as_str)).expect("joined");
        assert_eq!((&sx, &sy), (&sx2, &sy2), "a spelling changed between two asks");
        (sx, sy)
    });
    assert!(collisions > 0, "a 1-bit hash over two 6-token treaps must collide");
    let (sx, sy) = spelled;
    assert_ne!(sx, sy, "a collision merged two different sets");
    let retired_x = retired_spelling_of_texts(x.iter().map(String::as_str));
    let retired_y = retired_spelling_of_texts(y.iter().map(String::as_str));
    // At least one of them lost its hash, and whichever did is spelled exactly.
    assert!(sx == retired_x || sy == retired_y, "{sx} / {sy}");
    for (s, retired) in [(&sx, &retired_x), (&sy, &retired_y)] {
        assert!(s == retired || s.starts_with('h'), "{s} is neither a hash nor exact");
    }
}

/// Short joins keep the retired spelling byte for byte; long ones are 33 bytes.
#[test]
fn short_joins_are_retired_and_long_joins_are_33_bytes() {
    assert_eq!(spell_token_texts(["e"]), None);
    assert_eq!(spell_token_texts(std::iter::empty::<&str>()), None);
    assert_eq!(spell_token_texts(["s1_0"]).as_deref(), Some("s1_0"));
    assert_eq!(spell_token_texts(["s1_t", "e"]).as_deref(), Some("e_s1_t"));
    assert_eq!(spell_token_texts(["s2_0", "s4_0", "s5_0"]).as_deref(), Some("s2_0_s4_0_s5_0"));
    // 33 bytes exactly stays retired; 34 is hashed.
    let at = ["s100_0", "s101_0", "s102_0", "s103_0", "s1_10"];
    assert_eq!(retired_spelling_of_texts(at).len(), 33);
    assert_eq!(spell_token_texts(at).as_deref(), Some("s100_0_s101_0_s102_0_s103_0_s1_10"));
    let over = ["s100_0", "s101_0", "s102_0", "s103_0", "s1_100"];
    let h = spell_token_texts(over).expect("joined");
    assert!(h.len() == 33 && h.starts_with('h') && h[1..].bytes().all(|c| c.is_ascii_hexdigit()));
    // Order and duplicates of the input do not matter: a function of the SET.
    let shuffled = ["s1_100", "s103_0", "s100_0", "s102_0", "s101_0", "s100_0"];
    assert_eq!(spell_token_texts(shuffled).as_deref(), Some(h.as_str()));
}

/// Whole generations are byte-identical across fresh instances, memo modes and the
/// order functions are generated in (the hashed spellings included).
#[test]
fn generation_is_byte_identical_across_instances_and_memo_modes() {
    let render = |f: &VerifiableFunction| -> Vec<String> {
        without_differential(|| generate_vcs(f).iter().map(|vc| format!("{vc:?}")).collect())
    };
    let funcs = [families::diamond_chain(9), families::loop_joins(9)];
    let first: Vec<Vec<String>> = funcs.iter().map(render).collect();
    assert!(first.iter().flatten().any(|v| v.contains("#h")), "no hashed token reached a VC");
    let reversed: Vec<Vec<String>> = funcs.iter().rev().map(render).collect();
    assert_eq!(first, reversed.into_iter().rev().collect::<Vec<_>>());
    let unmemoized: Vec<Vec<String>> =
        funcs.iter().map(|f| crate::fn_memo::with_analysis_memo_disabled(|| render(f))).collect();
    assert_eq!(first, unmemoized);
}

/// The measurement D15 was opened on, now linear: the answered bytes of the families
/// whose joined answers grow with the input grow at most ~2x per doubling.
#[test]
fn joined_answer_bytes_are_linear() {
    for (name, mk) in [
        ("diamond_chain", &families::diamond_chain as &dyn Fn(usize) -> VerifiableFunction),
        ("loop_joins", &families::loop_joins),
        ("confined_store_blocks", &families::confined_store_blocks),
    ] {
        let bytes: Vec<u64> = [64usize, 128, 256, 512]
            .iter()
            .map(|&n| super::version_ssa_scaling_tests::answer_bytes(&mk(n)))
            .collect();
        for w in bytes.windows(2) {
            assert!(
                (w[1] as f64) <= 2.3 * w[0] as f64,
                "{name}: answer bytes {bytes:?} grow super-linearly"
            );
        }
    }
}
