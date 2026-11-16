// trust-vcgen/src/generate/version_ssa.rs: the INTER-BLOCK statement-version oracle as
// query-driven SSA over the dominator tree.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// WHAT IT ANSWERS. For a block `b` and a tracked name `k`, the set IN[b][k] of OUT
// tokens (`s{p}_{j}`, `s{p}_t`, or the entry sentinel `e`) that may reach `b`'s entry —
// exactly the least fixpoint the retired `path_defs::entry_versions_fixpoint` computed
// over the unwind-inclusive predecessor relation `full_graph_terminator_targets`, with
// `in[bb0]` seeded with `e` for every tracked name. The version token of a read `r` at
// `b`'s entry is the union of IN[b][k] over the tracked names `k` that REBIND `r`
// (`write_rebinds(k, r)`), spelled `None` when the union is empty or exactly `{e}`, else
// by THE SPELLING below.
//
// THE SPELLING (D15). The retired oracle spelled a set as its `_`-joined,
// lexicographically sorted token list, so a read after `i` joins carried `i` tokens and
// the answers of a chain of joins were quadratic in bytes. A set is now spelled that way
// only while the list is at most 33 bytes (every singleton and every short join, byte
// for byte as before); a longer one is `h` + 32 hex digits: the first 128 bits of a
// SHA-256 MERKLE hash of the set's treap, computed at most once per node. Both are
// functions of the SET alone — never of query order or oracle instance — because token
// keys are content (`TokId`) and the treap of a set is unique. A process-wide REGISTRY
// (`SetHashRegistry`) records what every used hash denotes and catches a collision,
// falling back to the exact retired spelling, so two reads share a spelling iff their
// sets are equal — the retired spelling's partition of reads into SMT variables, with
// no premise on the hash inside one process. See `SetHashRegistry` for its reach.
//
// WHY IT REPLACES THE FIXPOINT. The retired fixpoint materialised IN[b][k] for EVERY
// block and EVERY tracked name — twice, as `String` maps — so memory was
// Θ(blocks x names) whatever was queried (`ever-init-many-locals`: 1400 blocks x ~1000
// names), with a step cap and budget polls whose trip handed back a PARTIAL map
// (the false-accept direction). This oracle stores O(size) index data and resolves
// only what is asked, memoising only the SSA joins (phis) a query actually reaches.
//
// BUDGET. The resolution has no truncated state of its own and consults no budget.
// Its INPUTS do not share that property: the gen-sets come from the per-statement
// definition extraction (`guards::extract_block_definitions`), which polls the
// ambient verify budget and silently returns FEWER names on a trip, so an oracle
// built after a trip may version too few reads — the retired fixpoint's
// false-accept direction, narrower. The `#e` mint gate fails closed on such an
// oracle (`FnWrites::built_after_trip`, the retired `entry_full == None`), and
// everything else rests on the consumers' post-generation discards
// (`trust_types::verify_budget`, "A trip is fail-closed only where a consumer
// DISCARDS"), which must stay for as long as the extraction polls.
//
// DEF SITES. A name's def sites are the blocks whose gen-set holds it (real defs),
// plus PSEUDO-DEFS: every loop header (the target of a dominator back edge,
// `CfgIndex::innermost_loop`) whose natural loop contains a real def of the name.
// A pseudo-def "defines" the name as its own entry value — its join, IN[h] = OUT[h]
// — which is an identity of the dataflow equations (any node may be given its true
// OUT as a constant without changing the least fixpoint), so the sets are unchanged.
// What it buys is the FORWARD reachability argument below: a def-site-free path into
// `b` that uses a back edge `u -> h` either revisits `h` (cut the cycle) or starts
// inside `h`'s loop — and then `h` is a pseudo-def, so the path is not def-site-free
// after all. So every def site that reaches `b` without passing another does so along
// FORWARD edges, and `CfgIndex::topo_f` (SCC ranks of the graph without its back
// edges) prunes the ones that cannot. Without it, a name defined once inside a loop
// body and read after the loop resolved one join per block of the body (every join
// between the def and the header was a trivial phi reached around the back edge):
// Θ(names x joins) for O(1)-sized answers. The one exception is `b` itself being a
// loop header that is a pseudo-def: its entry value IS its join, back edges included.
//
// THE RESOLUTION (per `(b, k)`), over `CfgIndex`'s augmented graph (`E` defines every
// name as `e` and feeds `bb0`; `R` feeds every dead block with nothing):
//
//   0. If `b` is a loop header and a pseudo-def of `k`: IN[b] is `b`'s join.
//   1. `d` := the deepest STRICT dominator of `b` that is a def site of `k` (`E`
//      counts; `R`, defining nothing, is the fallback).
//   2. Every def site reaching `b` other than `d` lies strictly inside `d`'s dominator
//      subtree and off `b`'s dominator path (LEMMA: after the last visit of a strict
//      dominator `a` on any path to `b`, the path stays inside `a`'s subtree; a def
//      site outside it, or `d` itself, reaches `b` only through `d`'s exit, where
//      `d`'s OUT replaces it), and reaches it along forward edges (above), so its
//      forward rank is at most `b`'s. Let `y*` be the deepest `LCA(o, b)` over those
//      def sites `o` — attained at `b`'s two preorder neighbours among them (for
//      `x < y < b` in preorder, `LCA(x, b)` is an ancestor of `LCA(y, b)`, and
//      symmetrically), which a range-minimum descent over each def list finds in
//      O(log). None: IN[b] = OUT[d].
//   3. No def site that can reach `b` lies strictly inside the subtree of `c*` (the
//      child of `y*` toward `b`, or `b` itself when `y* = b`) except on `b`'s path,
//      where there is none below `d`. So for every `x` strictly below `c*` on the path,
//      IN[x] = IN[idom(x)] (the lemma again; a site that reaches `x` reaches it
//      forward, and `x` reaches `b` forward, so its rank passed the filter), and
//      IN[b] = IN[c*]. Walking up from `c*`, a single-predecessor node's predecessor
//      IS its immediate dominator, so IN[x] = IN[idom(x)] there too, up to `J` :=
//      the deepest node with two or more predecessors in `(d, c*]`.
//   4. If there is such a `J`, IN[b] = IN[J] = ∪ over `J`'s predecessors `p` of
//      OUT[p] (the dataflow equation itself): OUT[p] is `{token(p, k)}` when `p`
//      really defines `k`, `{e}` for `E`, `∅` for `R`, else IN[p] — resolved the same
//      way. A `J` is resolved once (memoised at `(J, k)`), and cycles of such joins
//      are solved as strongly connected components (Tarjan): every member of an SCC
//      gets the union of the SCC's external operands, which is the least fixpoint of
//      `S_m = ∪ operands` on a strongly connected system. Otherwise IN[b] = OUT[d]
//      (a pseudo-def's OUT is its join).
//
// Every step is an identity of the retired fixpoint's equations, so the sets are equal
// — and, spelled through one function (`spell_token_texts`), so are the tokens and every
// VC built from them; `version_ssa_parity_tests` and `version_ssa_random_tests` assert it
// against the retired fixpoint kept as a `cfg(test)` differential, and
// `version_ssa_spelling_tests` pins the partition against the retired spelling
// itself. Pruning is by QUERY only: a join nobody asks about is never built. (Pruning
// by MIR liveness would be unsound here: a threaded fact names a place at program
// points where MIR considers it dead.)
//
// THE SETS are persistent treaps, hash-consed (`SetStore`): a set is one id, equal sets
// are equal ids, and a union shares every subtree it does not rebuild — so a chain of
// joins each adding one token costs O(log) nodes per join, not a copy of the growing
// set. (Flat sorted vectors, the previous form, stored Θ(n²) elements to answer ONE
// query whose answer was Θ(n).)
//
// REBINDER UNIONS. A read's token is a union over the tracked names that rebind it,
// which can be many (`self` against every tracked `self*.f_i`). Resolving them one by
// one costs Θ(|rebinders|) per read even when one def changed since the last read
// (`confined_store_blocks`: 8,258 / 32,898 / 131,330 / 524,802 resolutions at n =
// 64..512). Instead the rebinders (sorted) form a balanced REBINDER TREE whose inner
// nodes are GROUP subjects — a run of rebinders, with def-site lists covering every def
// site of its members (built as their union: the PART group minus the classes that
// exclude EVERY havoc member) and the pseudo-defs they induce — and the read's token is
// IN[b] of the root. Every identity of steps 0-4 holds for a group `G` member by
// member, because each member's def sites are among `G`'s and every extra site is a
// node whose true OUT may stand in for it: `IN[b][k] = OUT[d][k]` (resp. `IN[J][k]`)
// for every `k ∈ G`, so `∪_k IN[b][k]` is `∪_k OUT[d][k]` (resp. the join's union). The
// one new equation is OUT of a group at a block `d` that really defines some member
// (`group_out`): the union, over its two children `c`, of `OUT[d][c]` when `d` defines
// a member of `c`, else `IN[d][c]` — memoised per `(d, G)`, and one level down the
// tree. Inside a group, every operand of a join either passes all of it through or is a
// finished value of a smaller group, so a cycle of joins stays in one group and is one
// SCC of the same shape as a name's; the union of the members' least fixpoints over one
// graph is the least fixpoint of the union. So the sets are the ones the per-name
// fan-out computed (`version_ssa_parity_tests`, `version_ssa_random_tests` check the
// partition against the retired fixpoint).
//
// THE SOUNDNESS INVARIANT of a group's lists is ONE-SIDED: the real list must be a
// SUPERSET of its members' real def sites, and the pseudo list must hold at least the
// headers its own real list induces (`subj_lists` derives it from the lists, so that
// half holds by construction). An extra site is harmless — `group_out` re-derives each
// child's OUT or IN there, so a site that defines no member passes IN through unchanged
// — and making the lists exactly the union buys only efficiency (fewer sites to
// resolve). A MISSING site is unsound, in the false-accept direction: its token never
// enters the union, so a read after it keeps an older version and a stale fact can
// discharge a real obligation. The PART exclusion is where a site can go missing: a
// group may exclude a class only if it excludes EVERY havoc member, so the group's
// exclusion list is the INTERSECTION of its children's; a too-large list (the first
// child's alone, or the union of both) drops PART def sites of the other child's havoc
// members (`a_group_keeps_the_part_defs_of_either_childs_havoc_members`). A NAME's real
// list, by contrast, must be exact: its OUT at a listed site is its token there, not a
// re-derivation.
//
// COST of the tree: a group is resolved at a block only on the root's path or beside
// it, so `n` reads each after one new def cost O(log |rebinders|) resolutions each;
// `(d, G)` values are shared across reads, and across reads whose rebinders share a run
// (groups are interned by member set). A block that defines EVERY member of a large
// group still descends to each member once (memoised per block), which is the per-name
// cost of the retired fan-out. A group's lists are built lazily, the first time it is
// resolved, from its members' explicit def blocks, so a tree whose groups are all
// resolved holds each def block once per level: O(defs · log |rebinders|) list entries
// (`cfg_work`, `pseudo_defs`).
//
// COST. Build: O((B + E) · α) for the dominator index and the loop forest, O(Σ gen)
// for the def lists (with the whole-function havoc list and the every-local copy list
// shared as ONE list each, see `block_writes`). Query: O(log B) per `(b, k)` step,
// plus the joins it reaches. A spelled answer is at most 33 bytes, and hashing it costs
// the nodes of its treap not yet hashed in this oracle. What remains super-linear is a
// name defined inside `L` nested loops and read outside them: it resolves the `L`
// headers' joins, which is the size of its minimal SSA form.

use std::cell::RefCell;
use std::rc::Rc;

use trust_types::VerifiableFunction;
use trust_types::fx::{FxHashMap, FxHashSet};

use super::block_writes::{FnWrites, GenFamily, HMode};
use super::cfg_index::{CfgIndex, NONE};
use super::rebind_index::{NameId, RebindIndex, RebindMode};

/// A version token by its CONTENT: `e` is `0`, `s{b}_{j}` is `1 + (b << 32 | j)` and
/// `s{b}_t` spells `j = u32::MAX`. A pure function of the token — never of the order in
/// which an oracle first met it — so the treap of a set (ordered by this key,
/// prioritised by a fixed hash of it) is the SAME tree in every oracle instance, and so
/// is every hash computed over that tree (`set_hash`).
type TokId = u64;
/// Id of a hash-consed token set.
pub(crate) type SetId = u32;

const E_TOK: TokId = 0;
const EMPTY_SET: SetId = 0;
const E_SET: SetId = 1;

/// The key of `s{block}_{stmt}` (`stmt == u32::MAX`: the terminator marker `s{block}_t`).
/// `(u32::MAX, u32::MAX)` is never minted (`ANY_DEF_BLOCK` uses statement 0), so the key
/// never wraps.
fn tok_key(block: u32, stmt: u32) -> TokId {
    debug_assert!(block != u32::MAX || stmt != u32::MAX, "reserved token key");
    1 + ((u64::from(block) << 32) | u64::from(stmt))
}

/// The retired spelling of one token.
fn tok_text(t: TokId) -> String {
    if t == E_TOK {
        return super::ENTRY_VERSION_SENTINEL.to_string();
    }
    let raw = t - 1;
    let (block, stmt) = ((raw >> 32) as u32, raw as u32);
    if stmt == u32::MAX { format!("s{block}_t") } else { format!("s{block}_{stmt}") }
}

fn decimal_len(mut v: u32) -> u64 {
    let mut n = 1;
    while v >= 10 {
        v /= 10;
        n += 1;
    }
    n
}

/// `tok_text(t).len()`, without allocating.
fn tok_text_len(t: TokId) -> u64 {
    if t == E_TOK {
        return super::ENTRY_VERSION_SENTINEL.len() as u64;
    }
    let raw = t - 1;
    let (block, stmt) = ((raw >> 32) as u32, raw as u32);
    // `s` + block + `_` + (`t` | stmt)
    2 + decimal_len(block) + if stmt == u32::MAX { 1 } else { decimal_len(stmt) }
}

/// The key of one retired token spelling, or `None` for any other text.
#[cfg(any(test, feature = "version-oracle-differential"))]
fn parse_tok(token: &str) -> Option<TokId> {
    if token == super::ENTRY_VERSION_SENTINEL {
        return Some(E_TOK);
    }
    let (block, stmt) = token.strip_prefix('s')?.split_once('_')?;
    // Only the canonical decimal spelling `tok_text` prints, so parsing is its inverse.
    let decimal = |d: &str| {
        !d.is_empty()
            && d.bytes().all(|c| c.is_ascii_digit())
            && (d == "0" || !d.starts_with('0'))
            && d.parse::<u32>().is_ok()
    };
    if !decimal(block) {
        return None;
    }
    let block: u32 = block.parse().ok()?;
    let stmt = match stmt {
        "t" => u32::MAX,
        s if decimal(s) => s.parse::<u32>().ok().filter(|&s| s != u32::MAX)?,
        _ => return None,
    };
    (block != u32::MAX || stmt != u32::MAX).then(|| tok_key(block, stmt))
}

// ---------------------------------------------------------------------------
// The spelling of a joined set: exact when short, else a collision-checked hash
// ---------------------------------------------------------------------------

/// The byte length of a hashed spelling: `h` and 32 lowercase hex digits (128 bits).
/// A joined set whose retired spelling is at most this long keeps the retired
/// spelling, so the hashed form never makes a token longer.
const HASHED_SPELLING_LEN: u64 = 1 + 32;

/// Domain separator of the set hash. Bump the version if the node encoding changes.
const SET_HASH_DOMAIN: &[u8] = b"trust-vcgen/version_ssa/joined-token-set/v1";

/// SHA-256 (the digest `trust_types::digest` already carries for every artifact digest),
/// truncated to its first 128 bits.
fn sha256_128(parts: &[&[u8]]) -> u128 {
    let d = trust_types::digest::stable_sha256_parts(parts);
    let mut first = [0u8; 16];
    first.copy_from_slice(&d[..16]);
    let h = u128::from_be_bytes(first);
    #[cfg(test)]
    let h = spell_test::mask(h);
    h
}

/// The hash of the empty set (a leaf of every treap).
fn empty_hash() -> u128 {
    sha256_128(&[SET_HASH_DOMAIN, &[0]])
}

/// The Merkle hash of treap node `(key, left, right)` from its children's hashes.
fn node_hash(key: TokId, hl: u128, hr: u128) -> u128 {
    sha256_128(&[SET_HASH_DOMAIN, &[1], &key.to_be_bytes(), &hl.to_be_bytes(), &hr.to_be_bytes()])
}

/// What a registered hash denotes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HashContent {
    Empty,
    Node { key: TokId, left: u128, right: u128 },
}

/// THE COLLISION REGISTRY: every set hash ever used to spell a token in this process,
/// with the exact content it denotes — one treap node, by its key and its children's
/// (registered) hashes. Invariant: a registered hash denotes exactly one set (induction
/// on registration order: the children were registered first). A node whose hash is
/// already registered with DIFFERENT content is a COLLISION; it — and every node above
/// it — is poisoned, and a set with a poisoned root is spelled the retired way, which is
/// exact. So two sets share a hashed spelling only if they are equal: the partition of
/// reads into SMT variables is the retired spelling's, with no premise on the hash.
///
/// PROCESS-GLOBAL on purpose: its reach must include every place two spelled tokens can
/// meet — one VC assembled from several oracle instances (a `gen_work` scope, the
/// function-analysis memo, an evicted memo slot, a nested scope, the R1 pre-pass, a
/// `callsite_replay` view), on any thread. A registry scoped to less (an oracle, a
/// thread, a function) would need an argument that no VC mixes tokens across that
/// scope; one per process needs none.
///
/// Its decisions are permanent (entries are never removed or replaced), so a set's
/// spelling is a pure function of the set for the life of the process. Memory: one
/// entry per distinct hashed treap node (40 bytes of content), shared across every
/// function whose joined sets share structure.
#[derive(Debug)]
struct SetHashRegistry {
    nodes: FxHashMap<u128, HashContent>,
    collisions: u64,
}

impl SetHashRegistry {
    fn new() -> SetHashRegistry {
        let mut nodes = FxHashMap::default();
        nodes.insert(empty_hash(), HashContent::Empty);
        SetHashRegistry { nodes, collisions: 0 }
    }

    /// Register `content` at `h`: `true` when `h` now denotes exactly `content`, `false`
    /// on a collision (the entry keeps its first content).
    fn register(&mut self, h: u128, content: HashContent) -> bool {
        match self.nodes.entry(h) {
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert(content);
                true
            }
            std::collections::hash_map::Entry::Occupied(o) => {
                if *o.get() == content {
                    true
                } else {
                    self.collisions += 1;
                    crate::fn_memo::count_set_hash_collisions(1);
                    false
                }
            }
        }
    }
}

static SET_HASH_REGISTRY: std::sync::LazyLock<std::sync::Mutex<SetHashRegistry>> =
    std::sync::LazyLock::new(|| std::sync::Mutex::new(SetHashRegistry::new()));

/// Run `f` on the registry in force: the process-global one, or (tests) the calling
/// thread's isolated one.
fn with_registry<R>(f: impl FnOnce(&mut SetHashRegistry) -> R) -> R {
    #[cfg(test)]
    let f = match spell_test::run_isolated(f) {
        Ok(r) => return r,
        Err(f) => f,
    };
    // A panic while the lock was held cannot leave a half-registered node: `register`
    // inserts one complete entry or none, so a poisoned lock's data is still exact.
    let mut reg = SET_HASH_REGISTRY.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    f(&mut reg)
}

/// The byte length at or below which a joined set keeps its retired spelling.
fn hashed_threshold() -> u64 {
    #[cfg(test)]
    if let Some(t) = spell_test::threshold() {
        return t;
    }
    HASHED_SPELLING_LEN
}

/// The retired spelling of a set of token texts: sorted, deduplicated, `_`-joined.
pub(crate) fn retired_spelling_of_texts<'a>(tokens: impl IntoIterator<Item = &'a str>) -> String {
    let mut texts: Vec<&str> = tokens.into_iter().collect();
    texts.sort_unstable();
    texts.dedup();
    texts.join("_")
}

/// The spelling [`VersionSsa`] gives the reaching set whose tokens have the retired
/// texts `tokens`: `None` for `∅` and `{e}`, else [`SetStore::spell`]'s. The retired
/// oracle (the differential) and the reference scans spell through this, so every
/// oracle spells one set one way.
#[cfg(any(test, feature = "version-oracle-differential"))]
pub(crate) fn spell_token_texts<'a>(tokens: impl IntoIterator<Item = &'a str>) -> Option<String> {
    let texts: std::collections::BTreeSet<&str> = tokens.into_iter().collect();
    if texts.is_empty() || (texts.len() == 1 && texts.contains(super::ENTRY_VERSION_SENTINEL)) {
        return None;
    }
    let mut store = SetStore::new();
    let mut acc = EMPTY_SET;
    for t in &texts {
        // A text that is no token spelling cannot come from a reaching set; spell the
        // whole set the retired way (exact) rather than guess.
        let Some(k) = parse_tok(t) else { return Some(retired_spelling_of_texts(texts)) };
        let s = store.singleton(k);
        acc = store.union(acc, s);
    }
    Some(store.spell(acc))
}

// ---------------------------------------------------------------------------
// Persistent hash-consed token sets
// ---------------------------------------------------------------------------

/// A node's Merkle hash: not yet computed, computed, or POISONED (its hash, or a
/// descendant's, collided in the registry, so no set rooted here is spelled by hash).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NodeHash {
    Unknown,
    Known(u128),
    Poisoned,
}

/// Token sets as persistent TREAPS, hash-consed: node 0 is the empty set, and every
/// other id is a node `(key, left, right)` interned by its triple. The priority of a
/// key is a fixed hash of it (ties broken by the key), so the treap of a SET is unique
/// — equal sets are the same id — and a union rebuilds only the O(log) spine it
/// changes, sharing the rest. Keys are CONTENT keys (`TokId`), so the treap of a set is
/// also the same tree in every store, which is what makes a hash over it a function of
/// the set alone.
///
/// Per node, O(1) at cons time: the subtree's element count and summed token-text
/// length (so a set's retired spelling length is known without walking it), and —
/// lazily, only under a set that is spelled by hash — its Merkle hash.
struct SetStore {
    key: Vec<TokId>,
    left: Vec<SetId>,
    right: Vec<SetId>,
    count: Vec<u32>,
    text_len: Vec<u64>,
    hash: Vec<NodeHash>,
    cons: FxHashMap<(TokId, SetId, SetId), SetId>,
    union_memo: FxHashMap<(SetId, SetId), SetId>,
}

fn prio(t: TokId) -> (u64, TokId) {
    // splitmix64: a fixed, well-mixed priority per key.
    let mut z = t.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    (z ^ (z >> 31), t)
}

impl SetStore {
    fn new() -> SetStore {
        let mut s = SetStore {
            key: vec![TokId::MAX],
            left: vec![EMPTY_SET],
            right: vec![EMPTY_SET],
            count: vec![0],
            text_len: vec![0],
            hash: vec![NodeHash::Unknown],
            cons: FxHashMap::default(),
            union_memo: FxHashMap::default(),
        };
        let e = s.node(E_TOK, EMPTY_SET, EMPTY_SET);
        debug_assert_eq!(e, E_SET);
        s
    }

    fn node(&mut self, k: TokId, l: SetId, r: SetId) -> SetId {
        if let Some(&id) = self.cons.get(&(k, l, r)) {
            return id;
        }
        crate::fn_memo::count_leafset_elems(1);
        let id = self.key.len() as SetId;
        self.key.push(k);
        self.left.push(l);
        self.right.push(r);
        self.count.push(self.count[l as usize] + self.count[r as usize] + 1);
        self.text_len.push(self.text_len[l as usize] + self.text_len[r as usize] + tok_text_len(k));
        self.hash.push(NodeHash::Unknown);
        self.cons.insert((k, l, r), id);
        id
    }

    fn singleton(&mut self, t: TokId) -> SetId {
        self.node(t, EMPTY_SET, EMPTY_SET)
    }

    /// `(keys of s below k, keys of s above k)`.
    fn split(&mut self, s: SetId, k: TokId) -> (SetId, SetId) {
        if s == EMPTY_SET {
            return (EMPTY_SET, EMPTY_SET);
        }
        let (sk, sl, sr) = (self.key[s as usize], self.left[s as usize], self.right[s as usize]);
        if sk == k {
            (sl, sr)
        } else if sk < k {
            let (l, r) = self.split(sr, k);
            (self.node(sk, sl, l), r)
        } else {
            let (l, r) = self.split(sl, k);
            (l, self.node(sk, r, sr))
        }
    }

    fn union(&mut self, a: SetId, b: SetId) -> SetId {
        if a == b || b == EMPTY_SET {
            return a;
        }
        if a == EMPTY_SET {
            return b;
        }
        let memo_key = if a < b { (a, b) } else { (b, a) };
        if let Some(&u) = self.union_memo.get(&memo_key) {
            return u;
        }
        crate::fn_memo::count_leafset_unions(1);
        let (hi, lo) =
            if prio(self.key[a as usize]) > prio(self.key[b as usize]) { (a, b) } else { (b, a) };
        let k = self.key[hi as usize];
        let (hl, hr) = (self.left[hi as usize], self.right[hi as usize]);
        let (l, r) = self.split(lo, k);
        let ul = self.union(hl, l);
        let ur = self.union(hr, r);
        let u = self.node(k, ul, ur);
        self.union_memo.insert(memo_key, u);
        u
    }

    /// The union of many sets, reduced pairwise.
    fn union_many(&mut self, ids: &[SetId]) -> SetId {
        let mut v: Vec<SetId> = ids.iter().copied().filter(|&s| s != EMPTY_SET).collect();
        v.sort_unstable();
        v.dedup();
        while v.len() > 1 {
            let mut next = Vec::with_capacity(v.len().div_ceil(2));
            for pair in v.chunks(2) {
                next.push(if let [a, b] = pair { self.union(*a, *b) } else { pair[0] });
            }
            v = next;
        }
        v.first().copied().unwrap_or(EMPTY_SET)
    }

    /// The elements of `s`, in key order.
    fn elements(&self, s: SetId) -> Vec<TokId> {
        let mut out = Vec::with_capacity(self.count.get(s as usize).copied().unwrap_or(0) as usize);
        let mut stack: Vec<SetId> = Vec::new();
        let mut cur = s;
        loop {
            while cur != EMPTY_SET {
                stack.push(cur);
                cur = self.left[cur as usize];
            }
            // The left spine is pushed, so `cur` is empty here: the walk is over exactly
            // when the stack is too, which is the pop failing.
            let Some(top) = stack.pop() else { break };
            out.push(self.key[top as usize]);
            cur = self.right[top as usize];
        }
        out
    }

    /// The retired spelling of a non-empty `s`: its token texts, sorted and `_`-joined.
    fn retired_spelling(&self, s: SetId) -> String {
        let texts: Vec<String> = self.elements(s).into_iter().map(tok_text).collect();
        retired_spelling_of_texts(texts.iter().map(String::as_str))
    }

    /// THE SPELLING of a non-empty set other than `{e}`. Its retired spelling when that
    /// is at most [`HASHED_SPELLING_LEN`] bytes (every singleton, and every short join,
    /// byte-identical to the retired oracle), else `h` + the 128-bit hash of its treap
    /// — unless the registry found a collision under it, and then the retired spelling
    /// again. Both branches are functions of the set: the length is, the treap is, and
    /// the registry's decisions are permanent. So is the partition: the retired
    /// spelling is injective, the hashed one is injective where it is used (the
    /// registry), and the two cannot meet (`h` versus `e` / `s`).
    ///
    /// COST: O(1) for a set whose hash is known, else O(nodes of `s` not yet hashed in
    /// this store) — each node is hashed once per store, so a chain of joins sharing
    /// structure costs its new nodes, not its answers.
    fn spell(&mut self, s: SetId) -> String {
        debug_assert!(s != EMPTY_SET && s != E_SET);
        let n = u64::from(self.count[s as usize]);
        let retired_len = self.text_len[s as usize] + n - 1;
        if n >= 2
            && retired_len > hashed_threshold()
            && let Some(h) = self.set_hash(s)
        {
            return format!("h{}", trust_types::digest::lowercase_hex(&h.to_be_bytes()));
        }
        self.retired_spelling(s)
    }

    /// The Merkle hash of `s`, registering every node under it not yet hashed in this
    /// store; `None` when `s` is poisoned.
    fn set_hash(&mut self, s: SetId) -> Option<u128> {
        if self.hash[s as usize] == NodeHash::Unknown {
            with_registry(|reg| {
                // Post-order, iteratively (children before parents).
                let mut stack: Vec<(SetId, bool)> = vec![(s, false)];
                while let Some((n, children_done)) = stack.pop() {
                    if self.hash[n as usize] != NodeHash::Unknown {
                        continue;
                    }
                    if n == EMPTY_SET {
                        self.hash[0] = NodeHash::Known(empty_hash());
                        continue;
                    }
                    let (l, r) = (self.left[n as usize], self.right[n as usize]);
                    if !children_done {
                        stack.push((n, true));
                        stack.push((l, false));
                        stack.push((r, false));
                        continue;
                    }
                    self.hash[n as usize] = match (self.hash[l as usize], self.hash[r as usize]) {
                        (NodeHash::Known(hl), NodeHash::Known(hr)) => {
                            crate::fn_memo::count_set_hash_nodes(1);
                            let key = self.key[n as usize];
                            let h = node_hash(key, hl, hr);
                            if reg.register(h, HashContent::Node { key, left: hl, right: hr }) {
                                NodeHash::Known(h)
                            } else {
                                NodeHash::Poisoned
                            }
                        }
                        _ => NodeHash::Poisoned,
                    };
                }
            });
        }
        match self.hash[s as usize] {
            NodeHash::Known(h) => Some(h),
            _ => None,
        }
    }
}

/// Test seams for the spelling: an ISOLATED registry per thread, hashes truncated to a
/// few bits (collisions on demand), and a lower spelling threshold (every join hashed).
#[cfg(test)]
pub(crate) mod spell_test {
    use std::cell::{Cell, RefCell};

    use super::SetHashRegistry;

    thread_local! {
        static REGISTRY: RefCell<Option<SetHashRegistry>> = const { RefCell::new(None) };
        static BITS: Cell<u32> = const { Cell::new(128) };
        static THRESHOLD: Cell<Option<u64>> = const { Cell::new(None) };
    }

    /// Keep the low `BITS` bits of a hash.
    pub(super) fn mask(h: u128) -> u128 {
        match BITS.with(Cell::get) {
            b if b >= 128 => h,
            b => h & ((1u128 << b) - 1),
        }
    }

    pub(super) fn threshold() -> Option<u64> {
        THRESHOLD.with(Cell::get)
    }

    /// `Ok(f(isolated registry))` inside [`isolated`], else `Err(f)`.
    pub(super) fn run_isolated<R, F: FnOnce(&mut SetHashRegistry) -> R>(f: F) -> Result<R, F> {
        REGISTRY.with(|r| match r.borrow_mut().as_mut() {
            Some(reg) => Ok(f(reg)),
            None => Err(f),
        })
    }

    /// Run `f` on this thread with a FRESH registry, hashes truncated to `bits` bits
    /// and (when given) the spelling threshold `threshold`; the collisions the registry
    /// counted.
    pub(crate) fn isolated<R>(
        bits: u32,
        threshold: Option<u64>,
        f: impl FnOnce() -> R,
    ) -> (R, u64) {
        struct Restore(u32, Option<u64>, Option<SetHashRegistry>);
        impl Drop for Restore {
            fn drop(&mut self) {
                BITS.with(|b| b.set(self.0));
                THRESHOLD.with(|t| t.set(self.1));
                REGISTRY.with(|r| *r.borrow_mut() = self.2.take());
            }
        }
        let old_bits = BITS.with(|b| b.replace(bits));
        let old_threshold = THRESHOLD.with(|t| t.replace(threshold));
        let fresh = SetHashRegistry::new();
        let old_registry = REGISTRY.with(|r| r.borrow_mut().replace(fresh));
        let _restore = Restore(old_bits, old_threshold, old_registry);
        let out = f();
        let collisions = REGISTRY.with(|r| r.borrow().as_ref().map_or(0, |reg| reg.collisions));
        (out, collisions)
    }
}

/// "No class" for a def-list entry, and "exclude nothing" for a query.
const NO_CLASS: u32 = u32::MAX;

// ---------------------------------------------------------------------------
// Def-site lists
// ---------------------------------------------------------------------------

/// One segment-tree node over a def list: the smallest forward rank, the class of an
/// entry attaining it, and the smallest rank among entries of any OTHER class — enough
/// to answer "smallest rank excluding one class" in O(1) per node.
#[derive(Clone, Copy, Debug)]
struct Seg {
    m1: u32,
    c1: u32,
    m2: u32,
}

const SEG_EMPTY: Seg = Seg { m1: u32::MAX, c1: NO_CLASS, m2: u32::MAX };

fn seg_merge(a: Seg, b: Seg) -> Seg {
    let (f, s) = if a.m1 <= b.m1 { (a, b) } else { (b, a) };
    Seg { m1: f.m1, c1: f.c1, m2: f.m2.min(if s.c1 != f.c1 { s.m1 } else { s.m2 }) }
}

fn seg_best(x: Seg, excl: u32) -> u32 {
    if excl == NO_CLASS || x.c1 != excl { x.m1 } else { x.m2 }
}

/// A sorted list of def sites (nodes of the augmented graph), with the forest the
/// dominator relation induces on them and skew-binary jump pointers over it, so the
/// deepest listed dominator of a node is found in O(log); a segment tree over their
/// forward ranks, so the nearest listed node on either side of a preorder position
/// whose rank passes a bound is found in O(log); and, for a list whose entries carry
/// CLASSES (the PART havoc group, see `block_writes`), per-entry jumps over runs of one
/// class, so every query can skip ONE class at no extra cost.
#[derive(Debug)]
struct DefList {
    /// Node ids, sorted by dominator preorder.
    nodes: Vec<u32>,
    /// `pre` of each node (parallel to `nodes`).
    pre: Vec<u32>,
    /// Index (into `nodes`) of the nearest listed proper dominator, or `NONE`.
    parent: Vec<u32>,
    jump: Vec<u32>,
    /// Per entry: its class (empty when the list is unclassed).
    class: Vec<u32>,
    /// Nearest listed proper dominator with a different class (`NONE` when none).
    parent_other: Vec<u32>,
    /// Power-of-two segment tree over the entries' forward ranks, leaves at `size`.
    size: usize,
    seg: Vec<Seg>,
}

impl DefList {
    fn build(cfg: &CfgIndex, nodes: Vec<u32>, classes: Option<Vec<u32>>) -> DefList {
        let list = Self::build_uncounted(cfg, nodes, classes);
        crate::fn_memo::count_cfg_work(list.nodes.len() as u64);
        list
    }

    fn build_uncounted(cfg: &CfgIndex, nodes: Vec<u32>, classes: Option<Vec<u32>>) -> DefList {
        let dom = cfg.dom();
        let classed = classes.is_some();
        let mut pairs: Vec<(u32, u32)> = match classes {
            Some(c) => nodes.into_iter().zip(c).collect(),
            None => nodes.into_iter().map(|v| (v, NO_CLASS)).collect(),
        };
        pairs.sort_unstable_by_key(|&(v, _)| dom.pre(v));
        pairs.dedup_by_key(|&mut (v, _)| v);
        let n = pairs.len();
        let mut nodes: Vec<u32> = Vec::with_capacity(n);
        let mut class: Vec<u32> = if classed { Vec::with_capacity(n) } else { Vec::new() };
        let mut pre: Vec<u32> = Vec::with_capacity(n);
        for &(v, c) in &pairs {
            nodes.push(v);
            if classed {
                class.push(c);
            }
            pre.push(dom.pre(v));
        }
        let mut parent = vec![NONE; n];
        let mut jump = vec![NONE; n];
        let mut depth = vec![0u32; n];
        let mut stack: Vec<u32> = Vec::new();
        for t in 0..n {
            while let Some(&top) = stack.last() {
                if dom.last(nodes[top as usize]) < pre[t] {
                    stack.pop();
                } else {
                    break;
                }
            }
            match stack.last() {
                Some(&p) => {
                    parent[t] = p;
                    depth[t] = depth[p as usize] + 1;
                    let j = jump[p as usize];
                    let jj = jump[j as usize];
                    jump[t] = if depth[p as usize] - depth[j as usize]
                        == depth[j as usize] - depth[jj as usize]
                    {
                        jj
                    } else {
                        p
                    };
                }
                None => {
                    jump[t] = t as u32;
                }
            }
            stack.push(t as u32);
        }
        let mut parent_other = Vec::new();
        if classed {
            parent_other = vec![NONE; n];
            for t in 0..n {
                let p = parent[t];
                parent_other[t] = if p == NONE {
                    NONE
                } else if class[p as usize] != class[t] {
                    p
                } else {
                    parent_other[p as usize]
                };
            }
        }
        let size = n.next_power_of_two().max(1);
        let mut seg = vec![SEG_EMPTY; 2 * size];
        for (t, &v) in nodes.iter().enumerate() {
            let c = if classed { class[t] } else { NO_CLASS };
            seg[size + t] = Seg { m1: cfg.topo_f(v), c1: c, m2: u32::MAX };
        }
        for i in (1..size).rev() {
            seg[i] = seg_merge(seg[2 * i], seg[2 * i + 1]);
        }
        DefList { nodes, pre, parent, jump, class, parent_other, size, seg }
    }

    fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    fn class_of(&self, t: usize) -> u32 {
        if self.class.is_empty() { NO_CLASS } else { self.class[t] }
    }

    /// Whether node `v` is listed (and not of class `excl`).
    fn contains(&self, cfg: &CfgIndex, v: u32, excl: u32) -> bool {
        let p = cfg.dom().pre(v);
        match self.pre.binary_search(&p) {
            Ok(t) => excl == NO_CLASS || self.class_of(t) != excl,
            Err(_) => false,
        }
    }

    /// The deepest listed STRICT dominator of `b` not of class `excl`.
    fn deepest_strict_dominator(&self, cfg: &CfgIndex, b: u32, excl: u32) -> Option<u32> {
        let dom = cfg.dom();
        let pb = dom.pre(b);
        let k = self.pre.partition_point(|&p| p < pb);
        if k == 0 {
            return None;
        }
        let covers = |t: u32| dom.subtree_contains_pre(self.nodes[t as usize], pb);
        let mut t = (k - 1) as u32;
        loop {
            if covers(t) {
                break;
            }
            crate::fn_memo::count_query_steps(1);
            let j = self.jump[t as usize];
            if j != t && !covers(j) {
                t = j;
            } else {
                let p = self.parent[t as usize];
                if p == NONE {
                    return None;
                }
                t = p;
            }
        }
        // The listed dominators of `b` are `t` and its forest ancestors; skip a run of
        // the excluded class in one jump.
        if excl != NO_CLASS && self.class_of(t as usize) == excl {
            t = self.parent_other[t as usize];
            if t == NONE {
                return None;
            }
        }
        Some(self.nodes[t as usize])
    }

    /// The listed node with the LARGEST preorder in `(lo, hi]` whose forward rank is at
    /// most `rank` and whose class is not `excl`.
    fn last_in(&self, lo: u32, hi: u32, rank: u32, excl: u32) -> Option<u32> {
        let l = self.pre.partition_point(|&p| p <= lo);
        let r = self.pre.partition_point(|&p| p <= hi);
        if l >= r {
            return None;
        }
        self.search(1, (0, self.size), (l, r), rank, excl, true).map(|t| self.nodes[t])
    }

    /// The listed node with the SMALLEST preorder in `(lo, hi]` whose forward rank is
    /// at most `rank` and whose class is not `excl`.
    fn first_in(&self, lo: u32, hi: u32, rank: u32, excl: u32) -> Option<u32> {
        let l = self.pre.partition_point(|&p| p <= lo);
        let r = self.pre.partition_point(|&p| p <= hi);
        if l >= r {
            return None;
        }
        self.search(1, (0, self.size), (l, r), rank, excl, false).map(|t| self.nodes[t])
    }

    /// The last (`rightmost`) or first entry of index range `range` under segment node
    /// `node` (covering `[nl, nr)`) that passes `rank` / `excl` — O(log) nodes visited.
    fn search(
        &self,
        node: usize,
        (nl, nr): (usize, usize),
        range: (usize, usize),
        rank: u32,
        excl: u32,
        rightmost: bool,
    ) -> Option<usize> {
        if nr <= range.0 || range.1 <= nl || seg_best(self.seg[node], excl) > rank {
            return None;
        }
        crate::fn_memo::count_query_steps(1);
        if nr - nl == 1 {
            return Some(nl);
        }
        let mid = usize::midpoint(nl, nr);
        let lo_half = (2 * node, (nl, mid));
        let hi_half = (2 * node + 1, (mid, nr));
        let (first, second) = if rightmost { (hi_half, lo_half) } else { (lo_half, hi_half) };
        self.search(first.0, first.1, range, rank, excl, rightmost)
            .or_else(|| self.search(second.0, second.1, range, rank, excl, rightmost))
    }
}

/// The loop headers whose loop contains a node of `nodes` (the pseudo-defs those
/// nodes induce), as a def list.
///
/// COST: `O(|nodes| + |headers|)`, counted as `pseudo_defs`. Every such header is in
/// the iterated dominance frontier of `nodes` (it joins the entry path with the back
/// path from the def), so this is bounded by the MINIMAL SSA form of the name — one
/// header per enclosing loop of each def, which is `Θ(depth)` per def only when defs
/// sit `depth` loops deep (the back-edge ladder, where every block heads a loop
/// enclosing all later ones, is that worst case, and its joins are the same size).
fn pseudo_defs(cfg: &CfgIndex, nodes: &[u32]) -> DefList {
    let mut seen: FxHashSet<u32> = FxHashSet::default();
    let mut out: Vec<u32> = Vec::new();
    for &v in nodes {
        let mut h = cfg.innermost_loop(v);
        while h != NONE && seen.insert(h) {
            out.push(h);
            h = cfg.loop_parent(h);
        }
    }
    crate::fn_memo::count_pseudo_defs((nodes.len() + out.len()) as u64);
    DefList::build_uncounted(cfg, out, None)
}

// ---------------------------------------------------------------------------
// Subjects
// ---------------------------------------------------------------------------

/// The def-site lists of one SUBJECT — a tracked name, or a group of them (see the
/// module doc): the real def lists (each with the one class it must skip) and the
/// pseudo-def lists.
struct SubjLists {
    real: Vec<(Rc<DefList>, u32)>,
    pseudo: Vec<Rc<DefList>>,
}

impl SubjLists {
    fn all(&self) -> impl Iterator<Item = (&DefList, u32)> {
        self.real
            .iter()
            .map(|(l, c)| (&**l, *c))
            .chain(self.pseudo.iter().map(|l| (&**l, NO_CLASS)))
    }

    fn really_defines(&self, cfg: &CfgIndex, v: u32) -> bool {
        self.real.iter().any(|(l, c)| l.contains(cfg, v, *c))
    }

    fn is_pseudo(&self, cfg: &CfgIndex, v: u32) -> bool {
        self.pseudo.iter().any(|l| l.contains(cfg, v, NO_CLASS))
    }
}

/// A read name's rebinders in one family, the root of their REBINDER TREE (see the
/// module doc; a name id when there is one rebinder, `NONE` when there is none), and
/// the memoised per-block answers.
struct ReadGroup {
    /// The rebinders themselves (the per-name test probes).
    #[cfg(test)]
    rebinders: Vec<NameId>,
    root: u32,
    per_block: RefCell<FxHashMap<u32, SetId>>,
}

/// An inner node of a rebinder tree: a GROUP subject, whose members are a sorted run of
/// two or more tracked names, split at its midpoint into two children (each a name id
/// or a group id). Groups are interned by their member set, so reads whose rebinders
/// share a run share its nodes and their memoised values.
struct GroupInfo {
    children: [u32; 2],
    /// Some member is in the havoc list / in the every-local list.
    any_h: bool,
    any_all: bool,
    /// The PART classes that exclude EVERY havoc member (sorted; meaningful when
    /// `any_h`): a PART block defines some member iff its class is not among them.
    /// SOUNDNESS: this list must never be too LARGE — a class wrongly in it drops PART
    /// def sites of some member (the false-accept direction; see the module doc).
    excl: Rc<[u32]>,
    /// Every member's explicit def blocks (unsorted, may repeat).
    explicit_nodes: Rc<[u32]>,
    /// Lazily, the group's def-site lists: built as the union of its members', and
    /// required to be a SUPERSET of it (a missing site is unsound; an extra one only
    /// costs work — see the module doc).
    lists: std::cell::OnceCell<Rc<SubjLists>>,
}

// ---------------------------------------------------------------------------
// The resolution state
// ---------------------------------------------------------------------------

/// Where a subject's value at a block entry comes from: a def site's OUT (`E`'s is
/// the entry value, `R`'s is nothing, a pseudo-def's is its own join), or a join.
#[derive(Clone, Copy, Debug)]
enum Site {
    Def(u32),
    Join(u32),
}

/// The SSA VALUE a read denotes at a program point — an IDENTITY, not a reaching set.
///
/// Trust (2026-10-01, the dominating-guard staleness defect). The version TOKEN of a
/// read is the spelling of its reaching-def SET (D15), and two points can share a set
/// while reading different values: in
///
/// ```text
/// loop { G: if a > MIN { if c { D: a = MIN; if c2 { continue } } B: return -a } .. }
/// ```
///
/// `a` reaches both `G` and `B` as `{e, D}` (through the back edge at `G`, through `D`
/// at `B`), yet on the path `G -> D -> B` the value `B` negates is `D`'s, not the one
/// `G` tested. Comparing tokens let the guard's `a > MIN` bound the negation there —
/// an overflowing program whose refutation was lost. A [`ValueId`] names the def
/// statement or the JOIN (phi) whose value the read sees, so `G` reads the header's
/// join and `B` reads the join at `B`: different identities.
///
/// THE CONTRACT A CONSUMER MAY RELY ON: when program point `p` DOMINATES program point
/// `q` and both report the same `ValueId` for a name, every execution reaching `q`
/// reads at `q` the very value it read at `p` on its last visit there. (The id's
/// defining point — a def statement, or a join node — dominates both; were it
/// re-executed between the last `p` and `q`, the path from it to `q` would avoid `p`,
/// and prefixed with the path to its first execution, which precedes every `p`, it
/// would reach `q` without `p`.) Without dominance the equality means nothing, which is
/// why no API here offers it unqualified.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ValueId {
    /// The function-entry value (a parameter's, or a never-written name's).
    Entry,
    /// The value statement `stmt` of `block` wrote (`u32::MAX`: its terminator).
    Def { block: u32, stmt: u32 },
    /// The join (phi) at augmented-graph node `node`.
    Phi { node: u32 },
    /// Trust (2026-10-17, gate RCA precision T3): the value a read rebound by TWO OR
    /// MORE tracked names (`_7` beside its pointee tie `_7*`, a field beside its
    /// aggregate) holds at the exit of `block`, a real def site of that read's GROUP
    /// subject that strictly dominates the read with no def site of any member between
    /// ([`VersionSsa::entry_value_id_grouped`], the only producer). Unlike [`Self::Def`]
    /// it does not name ONE statement (members `block` does not write keep their
    /// incoming values) and its token need not be a singleton, so the one consumer that
    /// keeps a token on it (`guard_value_spelling`) asks what it asks of [`Self::Phi`].
    GroupOut { block: u32 },
}

/// The resolved value of a subject at a program point, before it is flattened to a set.
#[derive(Clone, Copy, Debug)]
enum Val {
    Set(SetId),
    /// The join at this node (memoised per `(node, subject)`).
    Phi(u32),
}

#[derive(Clone, Copy, Debug)]
enum PhiState {
    Unvisited,
    /// On the Tarjan stack with this discovery index. Its low-link lives on its frame
    /// in `phi_set` while that frame is open, and nothing reads it after.
    OnStack {
        index: u32,
    },
    Done(SetId),
}

struct SsaState {
    out_memo: FxHashMap<(u32, NameId), TokId>,
    sets: SetStore,
    spell: FxHashMap<SetId, Option<Rc<str>>>,
    phi_ids: FxHashMap<(u32, u32), u32>,
    /// OUT of a group at a block that really defines one of its members.
    group_out: FxHashMap<(u32, u32), SetId>,
    phi_state: Vec<PhiState>,
    /// A finished-but-open SCC member's own union of external operands.
    phi_acc: Vec<SetId>,
    tarjan_stack: Vec<u32>,
    next_index: u32,
}

impl SsaState {
    fn new() -> SsaState {
        SsaState {
            out_memo: FxHashMap::default(),
            sets: SetStore::new(),
            spell: FxHashMap::default(),
            phi_ids: FxHashMap::default(),
            group_out: FxHashMap::default(),
            phi_state: Vec::new(),
            phi_acc: Vec::new(),
            tarjan_stack: Vec::new(),
            next_index: 0,
        }
    }

    /// Token id of `s{block}_{stmt}` (`stmt == u32::MAX` spells the terminator marker
    /// `s{block}_t`).
    fn tok(&mut self, block: u32, stmt: u32) -> TokId {
        tok_key(block, stmt)
    }

    /// The spelling of a reaching set: `None` for `∅` and `{e}`, else
    /// [`SetStore::spell`]'s (memoised per set).
    fn spelling(&mut self, s: SetId) -> Option<Rc<str>> {
        if let Some(cached) = self.spell.get(&s) {
            return cached.clone();
        }
        let out = if s == EMPTY_SET || s == E_SET {
            None
        } else {
            let text: Rc<str> = Rc::from(self.sets.spell(s));
            crate::fn_memo::count_token_bytes(text.len() as u64);
            Some(text)
        };
        self.spell.insert(s, out.clone());
        out
    }
}

/// Which gen-sets a [`Resolver`] resolves over, and what a def contributes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Family {
    /// The statement-version gen-sets (`block_written_names`); a def contributes its
    /// OUT token.
    Versions,
    /// The kill gen-sets of the retired `v2_may_reassigned_per_block`
    /// (`block_entry_fact_kill_names` ∪ `terminator_def_names`); every def
    /// contributes the same token — only "some def reaches" is asked.
    Kills,
}

impl Family {
    fn gen_family(self) -> GenFamily {
        match self {
            Family::Versions => GenFamily::Versions,
            Family::Kills => GenFamily::Kills,
        }
    }
}

/// The token every def contributes under [`Family::Kills`].
const ANY_DEF_BLOCK: u32 = u32::MAX;

/// The query-driven SSA resolution over one family of gen-sets.
struct Resolver {
    family: Family,
    /// Every tracked name (the union of the family's gen-sets).
    universe: RebindIndex,
    /// Per name: its EXPLICIT def blocks.
    explicit: FxHashMap<NameId, Rc<DefList>>,
    /// Blocks whose gen-set holds the whole havoc list / holds it minus a class's
    /// exclusion (entries classed) / holds the every-local list.
    full: Rc<DefList>,
    part: Rc<DefList>,
    all: Rc<DefList>,
    /// The pseudo-defs the three groups induce.
    pseudo_full: Rc<DefList>,
    pseudo_part: Rc<DefList>,
    pseudo_all: Rc<DefList>,
    /// Lazily: each name's lists; each read's group.
    subjects: RefCell<FxHashMap<u32, Rc<SubjLists>>>,
    reads: RefCell<FxHashMap<Rc<str>, Rc<ReadGroup>>>,
    /// Subject ids below this are names; group `g` is `groups[g - names_len]`.
    names_len: u32,
    groups: RefCell<Vec<Rc<GroupInfo>>>,
    group_ids: RefCell<FxHashMap<Rc<[NameId]>, u32>>,
    /// Per havoc name: the PART classes that exclude it (sorted).
    name_excl: RefCell<FxHashMap<NameId, Rc<[u32]>>>,
    /// The PART list minus the entries of a set of two or more classes.
    part_without: RefCell<FxHashMap<Rc<[u32]>, Rc<DefList>>>,
    state: RefCell<SsaState>,
}

impl Resolver {
    fn build(cfg: &CfgIndex, writes: &FnWrites, family: Family) -> Resolver {
        let gf = family.gen_family();
        let mut explicit: FxHashMap<NameId, Vec<u32>> = FxHashMap::default();
        let (mut full, mut part, mut part_class, mut all) =
            (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        let mut tracked: Vec<NameId> = Vec::new();
        // One write-index entry per block of the body `cfg` indexes: `VersionSsa::build`
        // makes both from the same `func`, so these are `cfg`'s blocks `0..n_blocks()`.
        for (b, bw) in writes.blocks().iter().enumerate() {
            let mut add = |k: NameId| {
                explicit.entry(k).or_default().push(b as u32);
                tracked.push(k);
            };
            match family {
                Family::Versions => bw.gen_explicit().iter().copied().for_each(&mut add),
                Family::Kills => {
                    bw.stmt_explicit().iter().copied().for_each(&mut add);
                    bw.term_explicit().iter().copied().for_each(&mut add);
                }
            }
            match bw.h_mode(gf) {
                HMode::None => {}
                HMode::Full => full.push(b as u32),
                HMode::Part(c) => {
                    part.push(b as u32);
                    part_class.push(c);
                }
            }
            if bw.gen_all() {
                all.push(b as u32);
            }
        }
        // The havoc names some gen-set holds: all of them once any block holds the
        // whole list; else those some PART class does not exclude.
        if !full.is_empty() {
            tracked.extend_from_slice(writes.havoc_names());
        } else if !part.is_empty() {
            let classes = writes.classes(gf).len();
            for &k in writes.havoc_names() {
                if writes.classes(gf).excluding(&writes.names, k).len() < classes {
                    tracked.push(k);
                }
            }
        }
        if !all.is_empty() {
            tracked.extend(writes.all_names());
        }
        tracked.sort_unstable();
        tracked.dedup();
        crate::fn_memo::count_tracked_names(tracked.len() as u64);
        let universe = RebindIndex::build(&writes.names, tracked.iter().copied());
        let explicit: FxHashMap<NameId, Rc<DefList>> =
            explicit.into_iter().map(|(k, v)| (k, Rc::new(DefList::build(cfg, v, None)))).collect();
        let pseudo_full = Rc::new(pseudo_defs(cfg, &full));
        let pseudo_part = Rc::new(pseudo_defs(cfg, &part));
        let pseudo_all = Rc::new(pseudo_defs(cfg, &all));
        Resolver {
            family,
            universe,
            explicit,
            full: Rc::new(DefList::build(cfg, full, None)),
            part: Rc::new(DefList::build(cfg, part, Some(part_class))),
            all: Rc::new(DefList::build(cfg, all, None)),
            pseudo_full,
            pseudo_part,
            pseudo_all,
            subjects: RefCell::new(FxHashMap::default()),
            reads: RefCell::new(FxHashMap::default()),
            names_len: writes.names.len() as u32,
            groups: RefCell::new(Vec::new()),
            group_ids: RefCell::new(FxHashMap::default()),
            name_excl: RefCell::new(FxHashMap::default()),
            part_without: RefCell::new(FxHashMap::default()),
            state: RefCell::new(SsaState::new()),
        }
    }

    /// The PART classes that exclude havoc name `k` (memoised; one probe of the class
    /// table per name).
    fn excl_of(&self, writes: &FnWrites, k: NameId) -> Rc<[u32]> {
        if let Some(x) = self.name_excl.borrow().get(&k) {
            return Rc::clone(x);
        }
        let x: Rc<[u32]> = if self.part.is_empty() {
            Rc::from(Vec::new())
        } else {
            Rc::from(writes.classes(self.family.gen_family()).excluding(&writes.names, k))
        };
        self.name_excl.borrow_mut().insert(k, Rc::clone(&x));
        x
    }

    /// The PART list without the entries of any class in `many` (two or more classes),
    /// memoised per class set.
    fn part_without(&self, cfg: &CfgIndex, many: &[u32]) -> Rc<DefList> {
        if let Some(l) = self.part_without.borrow().get(many) {
            return Rc::clone(l);
        }
        let (nodes, classes): (Vec<u32>, Vec<u32>) = self
            .part
            .nodes
            .iter()
            .zip(&self.part.class)
            .filter(|(_, c)| many.binary_search(c).is_err())
            .map(|(&v, &c)| (v, c))
            .unzip();
        let l = Rc::new(DefList::build(cfg, nodes, Some(classes)));
        self.part_without.borrow_mut().insert(Rc::from(many), Rc::clone(&l));
        l
    }

    fn group_info(&self, g: u32) -> Rc<GroupInfo> {
        Rc::clone(&self.groups.borrow()[(g - self.names_len) as usize])
    }

    /// The subject id of the sorted, deduplicated run `members` (non-empty): the name
    /// itself for one member, else its interned group, built with its subtree.
    fn subject_of(&self, writes: &FnWrites, members: &[NameId]) -> u32 {
        if let [k] = members {
            return *k;
        }
        if let Some(&g) = self.group_ids.borrow().get(members) {
            return g;
        }
        let mid = members.len() / 2;
        let children =
            [self.subject_of(writes, &members[..mid]), self.subject_of(writes, &members[mid..])];
        // (havoc member?, every-local member?, classes excluding every havoc member,
        // explicit def blocks) of one child.
        let facts = |c: u32| -> (bool, bool, Rc<[u32]>, Rc<[u32]>) {
            if c < self.names_len {
                let h = writes.in_havoc(c);
                let excl = if h { self.excl_of(writes, c) } else { Rc::from(Vec::new()) };
                let explicit = self
                    .explicit
                    .get(&c)
                    .map_or_else(|| Rc::from(Vec::new()), |l| Rc::from(&l.nodes[..]));
                (h, writes.in_all(c), excl, explicit)
            } else {
                let gi = self.group_info(c);
                (gi.any_h, gi.any_all, Rc::clone(&gi.excl), Rc::clone(&gi.explicit_nodes))
            }
        };
        let (h0, a0, x0, e0) = facts(children[0]);
        let (h1, a1, x1, e1) = facts(children[1]);
        let excl: Rc<[u32]> = match (h0, h1) {
            (true, true) => x0.iter().copied().filter(|c| x1.binary_search(c).is_ok()).collect(),
            (true, false) => x0,
            (false, true) => x1,
            (false, false) => Rc::from(Vec::new()),
        };
        let mut explicit_vec = Vec::with_capacity(e0.len() + e1.len());
        explicit_vec.extend_from_slice(&e0);
        explicit_vec.extend_from_slice(&e1);
        let explicit_nodes: Rc<[u32]> = Rc::from(explicit_vec);
        let info = GroupInfo {
            children,
            any_h: h0 || h1,
            any_all: a0 || a1,
            excl,
            explicit_nodes,
            lists: std::cell::OnceCell::new(),
        };
        let mut groups = self.groups.borrow_mut();
        let g = self.names_len + groups.len() as u32;
        groups.push(Rc::new(info));
        self.group_ids.borrow_mut().insert(Rc::from(members), g);
        g
    }

    /// The def-site lists of subject `s`: a name's (exact), or a group's union of its
    /// members' (real def sites) with the pseudo-defs they induce — for a group, a
    /// SUPERSET is sound and a missing site is not (see the module doc).
    fn subj_lists(&self, cfg: &CfgIndex, writes: &FnWrites, s: u32) -> Rc<SubjLists> {
        if s < self.names_len {
            return self.name_lists(cfg, writes, s);
        }
        let gi = self.group_info(s);
        Rc::clone(gi.lists.get_or_init(|| {
            let explicit = Rc::new(DefList::build(cfg, gi.explicit_nodes.to_vec(), None));
            let mut pseudo = vec![Rc::new(pseudo_defs(cfg, &explicit.nodes))];
            let mut real = vec![(explicit, NO_CLASS)];
            if gi.any_h {
                real.push((Rc::clone(&self.full), NO_CLASS));
                pseudo.push(Rc::clone(&self.pseudo_full));
                if !self.part.is_empty() {
                    match &*gi.excl {
                        [] => real.push((Rc::clone(&self.part), NO_CLASS)),
                        [c] => real.push((Rc::clone(&self.part), *c)),
                        many => real.push((self.part_without(cfg, many), NO_CLASS)),
                    }
                    pseudo.push(Rc::clone(&self.pseudo_part));
                }
            }
            if gi.any_all {
                real.push((Rc::clone(&self.all), NO_CLASS));
                pseudo.push(Rc::clone(&self.pseudo_all));
            }
            real.retain(|(l, _)| !l.is_empty());
            pseudo.retain(|l| !l.is_empty());
            Rc::new(SubjLists { real, pseudo })
        }))
    }

    /// The def-site lists of tracked name `k`.
    fn name_lists(&self, cfg: &CfgIndex, writes: &FnWrites, k: NameId) -> Rc<SubjLists> {
        if let Some(sl) = self.subjects.borrow().get(&k) {
            return Rc::clone(sl);
        }
        let mut real: Vec<(Rc<DefList>, u32)> = Vec::new();
        let mut pseudo: Vec<Rc<DefList>> = Vec::new();
        if let Some(l) = self.explicit.get(&k) {
            real.push((Rc::clone(l), NO_CLASS));
            pseudo.push(Rc::new(pseudo_defs(cfg, &l.nodes)));
        }
        if writes.in_havoc(k) {
            if !self.full.is_empty() {
                real.push((Rc::clone(&self.full), NO_CLASS));
                pseudo.push(Rc::clone(&self.pseudo_full));
            }
            if !self.part.is_empty() {
                let excluded = writes.classes(self.family.gen_family()).excluding(&writes.names, k);
                match excluded.as_slice() {
                    [] => real.push((Rc::clone(&self.part), NO_CLASS)),
                    [c] => real.push((Rc::clone(&self.part), *c)),
                    many => {
                        // Excluded by two or more classes: a list of its own (one pass
                        // over the group, once per such name).
                        let (nodes, classes): (Vec<u32>, Vec<u32>) = self
                            .part
                            .nodes
                            .iter()
                            .zip(&self.part.class)
                            .filter(|(_, c)| !many.contains(c))
                            .map(|(&v, &c)| (v, c))
                            .unzip();
                        real.push((Rc::new(DefList::build(cfg, nodes, Some(classes))), NO_CLASS));
                    }
                }
                pseudo.push(Rc::clone(&self.pseudo_part));
            }
        }
        if writes.in_all(k) && !self.all.is_empty() {
            real.push((Rc::clone(&self.all), NO_CLASS));
            pseudo.push(Rc::clone(&self.pseudo_all));
        }
        pseudo.retain(|l| !l.is_empty());
        let sl = Rc::new(SubjLists { real, pseudo });
        self.subjects.borrow_mut().insert(k, Rc::clone(&sl));
        sl
    }

    /// The read group of `read` (its rebinders in `mode`, and the root of their
    /// rebinder tree).
    fn read_group(&self, writes: &FnWrites, read: &str, mode: RebindMode) -> Rc<ReadGroup> {
        if let Some(g) = self.reads.borrow().get(read) {
            return Rc::clone(g);
        }
        let mut rebinders: Vec<NameId> = Vec::new();
        self.universe.for_each_rebinder(read, mode, |k| rebinders.push(k));
        rebinders.sort_unstable();
        rebinders.dedup();
        let root = if rebinders.is_empty() { NONE } else { self.subject_of(writes, &rebinders) };
        let g = Rc::new(ReadGroup {
            #[cfg(test)]
            rebinders,
            root,
            per_block: RefCell::default(),
        });
        self.reads.borrow_mut().insert(Rc::from(read), Rc::clone(&g));
        g
    }
}

/// The function's statement-version oracle, inter-block half (and the may-reassigned
/// view over the kill gen-sets).
pub(crate) struct VersionSsa {
    cfg: CfgIndex,
    writes: FnWrites,
    versions: Resolver,
    kills: std::cell::OnceCell<Resolver>,
}

impl VersionSsa {
    pub(crate) fn build(func: &VerifiableFunction) -> VersionSsa {
        crate::fn_memo::count_entry_versions();
        let cfg = CfgIndex::build(func);
        let writes = FnWrites::build(func);
        writes.count_entries();
        let versions = Resolver::build(&cfg, &writes, Family::Versions);
        VersionSsa { cfg, writes, versions, kills: std::cell::OnceCell::new() }
    }

    pub(crate) fn writes(&self) -> &FnWrites {
        &self.writes
    }

    fn kills(&self) -> &Resolver {
        self.kills.get_or_init(|| Resolver::build(&self.cfg, &self.writes, Family::Kills))
    }

    /// OUT of subject `subj` at a real def site `d` of it: a name's token, or a
    /// group's union over its children (see [`Self::group_out`]).
    fn defined_out(&self, r: &Resolver, st: &mut SsaState, d: u32, subj: u32) -> SetId {
        if subj < r.names_len {
            self.def_set(r, st, d, subj)
        } else {
            self.group_out(r, st, d, subj)
        }
    }

    /// OUT[d] of GROUP `g` at a block `d` that really defines one of its members: the
    /// union, over its two children `c`, of OUT[d][c] — `c`'s own def-site value when
    /// `d` defines one of `c`'s members, else IN[d][c] (a block passes through what
    /// it does not define). Memoised per `(d, g)`; every call descends one level of
    /// the rebinder tree, so the recursion is as deep as the tree.
    fn group_out(&self, r: &Resolver, st: &mut SsaState, d: u32, g: u32) -> SetId {
        if let Some(&s) = st.group_out.get(&(d, g)) {
            return s;
        }
        let gi = r.group_info(g);
        let mut parts = [EMPTY_SET; 2];
        for (part, &c) in parts.iter_mut().zip(&gi.children) {
            let sl = r.subj_lists(&self.cfg, &self.writes, c);
            *part = if sl.really_defines(&self.cfg, d) {
                self.defined_out(r, st, d, c)
            } else {
                self.entry_set(r, &sl, st, d, c)
            };
        }
        let s = st.sets.union(parts[0], parts[1]);
        st.group_out.insert((d, g), s);
        s
    }

    /// The token set real def site `d` contributes for NAME `subj`.
    fn def_set(&self, r: &Resolver, st: &mut SsaState, d: u32, subj: u32) -> SetId {
        debug_assert!(subj < r.names_len, "a group's OUT is `group_out`");
        if r.family == Family::Kills {
            let t = st.tok(ANY_DEF_BLOCK, 0);
            return st.sets.singleton(t);
        }
        let t = if let Some(&t) = st.out_memo.get(&(d, subj)) {
            t
        } else {
            let t = match self.writes.out_token(d as usize, subj) {
                Some(j) => st.tok(d, j),
                None => st.tok(d, u32::MAX),
            };
            st.out_memo.insert((d, subj), t);
            t
        };
        st.sets.singleton(t)
    }

    /// OUT of def site `d`: `{e}` for `E`, `∅` for `R`, the token for a real def, the
    /// join for a pseudo-def.
    fn def_val(&self, r: &Resolver, sl: &SubjLists, st: &mut SsaState, d: u32, subj: u32) -> Val {
        if d == self.cfg.entry_def() {
            return Val::Set(E_SET);
        }
        if d == self.cfg.root() {
            return Val::Set(EMPTY_SET);
        }
        if sl.really_defines(&self.cfg, d) {
            return Val::Set(self.defined_out(r, st, d, subj));
        }
        Val::Phi(d)
    }

    /// IN[b][subj] as a value: a def site's set, or the join it resolves to (steps 0-4
    /// of the module doc).
    fn resolve_entry(
        &self,
        r: &Resolver,
        sl: &SubjLists,
        st: &mut SsaState,
        b: u32,
        subj: u32,
    ) -> Val {
        match self.resolve_site(sl, b) {
            Site::Def(d) => self.def_val(r, sl, st, d, subj),
            Site::Join(j) => Val::Phi(j),
        }
    }

    /// Where IN[b][subj] comes from (steps 0-4 of the module doc), before any set is
    /// built: the def site `d` whose OUT reaches `b`'s entry unchanged, or the join
    /// whose value it is. [`Self::resolve_entry`] is exactly this followed by
    /// [`Self::def_val`]; [`Self::entry_value_id`] reads the site itself.
    fn resolve_site(&self, sl: &SubjLists, b: u32) -> Site {
        crate::fn_memo::count_ssa_queries(1);
        let cfg = &self.cfg;
        let dom = cfg.dom();
        // 0. A loop header that is a pseudo-def: its entry value is its own join.
        if cfg.is_loop_header(b) && sl.is_pseudo(cfg, b) {
            return Site::Join(b);
        }
        let e = cfg.entry_def();
        let pb = dom.pre(b);
        // 1. The deepest strict dominator that is a def site.
        let mut d = cfg.root();
        if dom.dominates(e, b) && b != e {
            d = e;
        }
        for (list, excl) in sl.all() {
            if let Some(x) = list.deepest_strict_dominator(cfg, b, excl)
                && dom.depth(x) > dom.depth(d)
            {
                d = x;
            }
        }
        let (pd, ld) = (dom.pre(d), dom.last(d));
        // 2. `b`'s preorder neighbours among the def sites strictly inside `d`'s
        //    subtree that can reach it along forward edges (the predecessor side
        //    includes `b` itself).
        let tb = cfg.topo_f(b);
        let mut before: Option<u32> = None;
        let mut after: Option<u32> = None;
        let mut consider = |x: u32| {
            let px = dom.pre(x);
            if px > pd && px <= pb {
                if before.is_none_or(|y| px > dom.pre(y)) {
                    before = Some(x);
                }
            } else if px > pb && px <= ld && after.is_none_or(|y| px < dom.pre(y)) {
                after = Some(x);
            }
        };
        if cfg.topo_f(e) <= tb {
            consider(e);
        }
        for (list, excl) in sl.all() {
            if let Some(x) = list.last_in(pd, pb, tb, excl) {
                consider(x);
            }
            if let Some(x) = list.first_in(pb, ld, tb, excl) {
                consider(x);
            }
        }
        let mut ystar: Option<u32> = None;
        for o in [before, after].into_iter().flatten() {
            let y = if o == b { b } else { dom.lca(o, b) };
            if ystar.is_none_or(|z| dom.depth(y) > dom.depth(z)) {
                ystar = Some(y);
            }
        }
        let Some(ystar) = ystar else {
            return Site::Def(d);
        };
        // 3. `c*`, and the deepest join in `(d, c*]`.
        let cstar = if ystar == b { b } else { dom.level_ancestor(b, dom.depth(ystar) + 1) };
        let j = cfg.nearest_join(cstar);
        if j != NONE && dom.depth(j) > dom.depth(d) { Site::Join(j) } else { Site::Def(d) }
    }

    /// OUT[p] for a predecessor `p` of a join.
    fn exit_value(
        &self,
        r: &Resolver,
        sl: &SubjLists,
        st: &mut SsaState,
        p: u32,
        subj: u32,
    ) -> Val {
        if p == self.cfg.entry_def() {
            return Val::Set(E_SET);
        }
        if p == self.cfg.root() {
            return Val::Set(EMPTY_SET);
        }
        if sl.really_defines(&self.cfg, p) {
            return Val::Set(self.defined_out(r, st, p, subj));
        }
        self.resolve_entry(r, sl, st, p, subj)
    }

    fn phi_id(st: &mut SsaState, j: u32, subj: u32) -> u32 {
        if let Some(&id) = st.phi_ids.get(&(j, subj)) {
            return id;
        }
        let id = st.phi_state.len() as u32;
        st.phi_ids.insert((j, subj), id);
        st.phi_state.push(PhiState::Unvisited);
        st.phi_acc.push(EMPTY_SET);
        id
    }

    /// The set of the join at `j` for `subj` — iterative Tarjan over the joins it
    /// reaches.
    fn phi_set(&self, r: &Resolver, sl: &SubjLists, st: &mut SsaState, j: u32, subj: u32) -> SetId {
        struct Frame {
            id: u32,
            /// Tarjan's discovery index and low-link of this join. The low-link changes
            /// only while this frame is the top one (its own operands, then its
            /// children's low-links as they close), so it lives here, not in `phi_state`.
            index: u32,
            lowlink: u32,
            ops: Vec<Val>,
            next: usize,
            /// The sets of the operands resolved so far (unioned once, at the end).
            acc: Vec<SetId>,
        }
        let root = Self::phi_id(st, j, subj);
        if let PhiState::Done(s) = st.phi_state[root as usize] {
            return s;
        }
        let open = |st: &mut SsaState, id: u32, node: u32| -> Frame {
            crate::fn_memo::count_ssa_phis(1);
            let index = st.next_index;
            st.next_index += 1;
            st.phi_state[id as usize] = PhiState::OnStack { index };
            st.tarjan_stack.push(id);
            let ops =
                self.cfg.preds(node).iter().map(|&p| self.exit_value(r, sl, st, p, subj)).collect();
            Frame { id, index, lowlink: index, ops, next: 0, acc: Vec::new() }
        };
        let mut frames: Vec<Frame> = vec![open(st, root, j)];
        while let Some(f) = frames.last_mut() {
            if f.next < f.ops.len() {
                let op = f.ops[f.next];
                f.next += 1;
                match op {
                    Val::Set(s) => f.acc.push(s),
                    Val::Phi(node) => {
                        let c = Self::phi_id(st, node, subj);
                        match st.phi_state[c as usize] {
                            PhiState::Done(s) => f.acc.push(s),
                            PhiState::OnStack { index } => f.lowlink = f.lowlink.min(index),
                            PhiState::Unvisited => {
                                let frame = open(st, c, node);
                                frames.push(frame);
                            }
                        }
                    }
                }
                continue;
            }
            // Every operand is in: close the top frame (the one just inspected).
            let Some(f) = frames.pop() else { break };
            st.phi_acc[f.id as usize] = st.sets.union_many(&f.acc);
            if f.lowlink == f.index {
                // `f` roots its SCC: the members are it and everything above it on the
                // Tarjan stack (pushed when opened, it is popped only with its own SCC).
                let mut member_sets: Vec<SetId> = Vec::new();
                let mut members: Vec<u32> = Vec::new();
                while let Some(m) = st.tarjan_stack.pop() {
                    member_sets.push(st.phi_acc[m as usize]);
                    members.push(m);
                    if m == f.id {
                        break;
                    }
                }
                let scc_set = st.sets.union_many(&member_sets);
                for m in members {
                    st.phi_state[m as usize] = PhiState::Done(scc_set);
                }
                if let Some(parent) = frames.last_mut() {
                    parent.acc.push(scc_set);
                }
            } else if let Some(parent) = frames.last_mut() {
                // Still open: its SCC's root is below it, and the parent inherits the
                // low-link.
                parent.lowlink = parent.lowlink.min(f.lowlink);
            }
        }
        // INVARIANT (reports/tcb-hardening-audit.md, 2026-09-30): the Tarjan stack is
        // empty when a walk starts (a walk returns only after closing its root, which
        // empties it; nothing catches a panic between walks), so the root holds the
        // smallest index on it, its low-link is its own index, and closing it completes
        // its SCC.
        match st.phi_state[root as usize] {
            PhiState::Done(s) => s,
            _ => EMPTY_SET, // invariant: the root join completes its SCC
        }
    }

    fn entry_set(
        &self,
        r: &Resolver,
        sl: &SubjLists,
        st: &mut SsaState,
        b: u32,
        subj: u32,
    ) -> SetId {
        match self.resolve_entry(r, sl, st, b, subj) {
            Val::Set(s) => s,
            Val::Phi(j) => self.phi_set(r, sl, st, j, subj),
        }
    }

    /// IN[b][k] for a tracked name `k` of `r` (the per-name test probes).
    #[cfg(test)]
    fn name_entry_set(&self, r: &Resolver, st: &mut SsaState, b: u32, k: NameId) -> SetId {
        let sl = r.name_lists(&self.cfg, &self.writes, k);
        self.entry_set(r, &sl, st, b, k)
    }

    /// The union of IN[b][k] over the rebinders of `read` in `r` (`mode`), memoised per
    /// `(block, read)`: IN[b] of the root of their rebinder tree (see the module doc).
    fn rebinder_union(&self, r: &Resolver, b: u32, read: &str, mode: RebindMode) -> SetId {
        let g = r.read_group(&self.writes, read, mode);
        if let Some(&s) = g.per_block.borrow().get(&b) {
            return s;
        }
        let s = if g.root == NONE {
            EMPTY_SET
        } else {
            let sl = r.subj_lists(&self.cfg, &self.writes, g.root);
            let mut st = r.state.borrow_mut();
            self.entry_set(r, &sl, &mut st, b, g.root)
        };
        g.per_block.borrow_mut().insert(b, s);
        s
    }

    /// The CFG index this oracle resolves over (dominator tree, forward ranks, loops).
    pub(crate) fn cfg(&self) -> &CfgIndex {
        &self.cfg
    }

    /// Trust (2026-10-16, S2): the tracked names whose value at loop header `h`'s
    /// entry is `h`'s own JOIN — step 0 of the resolution (`h` is a loop header and a
    /// pseudo-def of the name: its natural loop really defines it). A read of such a
    /// name at `h`, and at every point its entry value reaches unchanged, is spelled
    /// by a token that has a back-edge operand and NO defining equation. `None` when
    /// the answer is not available exactly: `h` is out of range, or the write index
    /// was built after the verify budget tripped (its gen-sets may be short, so a
    /// missing def could hide a pseudo-def). Unreachable headers answer the empty set.
    pub(crate) fn loop_header_join_names(&self, h: usize) -> Option<Vec<String>> {
        if h >= self.cfg.n_blocks() || self.writes.built_after_trip() {
            return None;
        }
        let h = h as u32;
        if !self.cfg.is_loop_header(h) || !self.cfg.dom().dominates(self.cfg.entry_def(), h) {
            return Some(Vec::new());
        }
        let r = &self.versions;
        let mut out = Vec::new();
        for k in 0..self.writes.names.len() as NameId {
            let text = self.writes.names.name(k);
            if r.universe.contains(text).is_none() {
                continue;
            }
            let sl = r.name_lists(&self.cfg, &self.writes, k);
            if sl.is_pseudo(&self.cfg, h) {
                out.push(text.to_string());
            }
        }
        Some(out)
    }

    /// The number of names this oracle's write index knows (the S2 screen's cost
    /// bound reads it before asking [`Self::loop_header_join_names`]).
    pub(crate) fn name_count(&self) -> usize {
        self.writes.names.len()
    }

    /// The [`ValueId`] `read` denotes at `b`'s ENTRY, or `None` when it cannot be named
    /// exactly: `b` is not reachable from `bb0`, two or more tracked names rebind the
    /// read (its value is a union of theirs, which no single identity names), or the
    /// write index was built after the ambient budget tripped (its gen-sets may be
    /// short, so a missing def could make two different values look equal).
    ///
    /// Same resolution as [`Self::inter_block_token`] — the same read group, the same
    /// steps 0-4 — read at the SITE instead of flattened to a set: a real def site
    /// names its OUT statement, `E` the entry value, a pseudo-def or a join its phi.
    pub(crate) fn entry_value_id(&self, b: usize, read: &str) -> Option<ValueId> {
        self.entry_value_id_impl(b, read, false)
    }

    /// [`Self::entry_value_id`], answering a read that two or more tracked names rebind
    /// too (where that one answers `None`).
    ///
    /// Trust (2026-10-17, gate RCA precision T3): the GROUP's own site resolution names
    /// such a read, exactly as a single name's does. The read group is the
    /// rebinder-tree subject whose def-site lists are a SUPERSET of every member's (the
    /// invariant the tokens already rest on), and `resolve_site` finds where its entry
    /// value comes from. Every step of that resolution is a statement about the
    /// subject's VALUE, not only its set: with no def site of any member on the paths
    /// from the site to `b`, no member is written there, so the read holds at `b` what
    /// it held at the site. A join or pseudo-def is the group's phi
    /// ([`ValueId::Phi`]); a real def site is [`ValueId::GroupOut`], never a
    /// [`ValueId::Def`] (the site may write only some members). The [`ValueId`]
    /// contract's proof (the identity's point dominates both reads and cannot
    /// re-execute between them) holds unchanged: `resolve_site` returns only a strict
    /// dominator of `b` as a def site, and the joins of the single-name case. The read
    /// group is a function of the read's NAME (`Resolver::read_group`, memoised per
    /// name), so one name is resolved through the same subject at every point and two
    /// of its ids compare like a single name's.
    ///
    /// Only the path-guard spelling asks this (`guard_value_spelling`): a guard on such
    /// a read was respelled guard-local even with nothing written between the guard and
    /// the row (PATH-GUARD-VALUE-1's recorded residual; aterm-phase `phase.rs:1342`
    /// composer_index `while k < b.len() && b[k] == b' '` refuted, `b` a `&[u8]` read
    /// as the length of the `&String` it came from, rebound by `_7` and `_7*`). Every
    /// other consumer keeps [`Self::entry_value_id`]'s `None`, so its answer for such a
    /// read is unchanged.
    pub(crate) fn entry_value_id_grouped(&self, b: usize, read: &str) -> Option<ValueId> {
        self.entry_value_id_impl(b, read, true)
    }

    fn entry_value_id_impl(&self, b: usize, read: &str, groups: bool) -> Option<ValueId> {
        if b >= self.cfg.n_blocks() || self.writes.built_after_trip() {
            return None;
        }
        let b = b as u32;
        let e = self.cfg.entry_def();
        if !self.cfg.dom().dominates(e, b) {
            return None;
        }
        let r = &self.versions;
        // The read group's rebinder-tree root: `NONE` for no rebinder, a name id for
        // exactly one, a group id (`>= names_len`) for two or more.
        let g = r.read_group(&self.writes, read, RebindMode::Plain);
        match g.root {
            NONE => Some(ValueId::Entry),
            k if k < r.names_len => {
                let sl = r.name_lists(&self.cfg, &self.writes, k);
                match self.resolve_site(&sl, b) {
                    Site::Def(d) if d == e => Some(ValueId::Entry),
                    Site::Def(d) if d == self.cfg.root() => None,
                    Site::Def(d) if sl.really_defines(&self.cfg, d) => Some(ValueId::Def {
                        block: d,
                        stmt: self.writes.out_token(d as usize, k).unwrap_or(u32::MAX),
                    }),
                    Site::Def(d) | Site::Join(d) => Some(ValueId::Phi { node: d }),
                }
            }
            group if groups => {
                let sl = r.subj_lists(&self.cfg, &self.writes, group);
                match self.resolve_site(&sl, b) {
                    Site::Def(d) if d == e => Some(ValueId::Entry),
                    Site::Def(d) if d == self.cfg.root() => None,
                    Site::Def(d) if sl.really_defines(&self.cfg, d) => {
                        Some(ValueId::GroupOut { block: d })
                    }
                    Site::Def(d) | Site::Join(d) => Some(ValueId::Phi { node: d }),
                }
            }
            _ => None,
        }
    }

    /// The inter-block arm of `version_token_at`: the retired
    /// `StmtVersionCtx::inter_block_token`, byte-identical.
    pub(crate) fn inter_block_token(&self, b: usize, read: &str) -> Option<String> {
        if b >= self.cfg.n_blocks() {
            return None;
        }
        let r = &self.versions;
        let s = self.rebinder_union(r, b as u32, read, RebindMode::Plain);
        r.state.borrow_mut().spelling(s).map(|t| t.to_string())
    }

    /// The `#e` mint gate: the union is exactly `{e}`.
    ///
    /// Fails closed (`false`, no `#e` mint) on an oracle whose write index was built
    /// after the ambient budget tripped: its gen-sets may be short, so "no def reaches"
    /// is not established (the retired gate answered `false` whenever its fixpoint
    /// had not converged).
    pub(crate) fn union_is_entry_only(&self, b: usize, read: &str) -> bool {
        if b >= self.cfg.n_blocks() || self.writes.built_after_trip() {
            return false;
        }
        self.rebinder_union(&self.versions, b as u32, read, RebindMode::Plain) == E_SET
    }

    /// THE MAY-REASSIGNED VIEW — `v2_may_reassigned_per_block(func)[b]` probed per read
    /// instead of materialised: whether some name in that set `dest_write_rebinds`
    /// `read` (the kill test `formula_mentions_redef` applies to every name of the
    /// set).
    ///
    /// The retired set at `b` is `gen_stmt[b] ∪ in[b]`, where `in[b]` — the union over
    /// predecessors of `in[p] ∪ gen_stmt[p] ∪ gen_term[p]` — holds exactly the names
    /// some block defines on a path of at least one edge into `b`. Such a path exists
    /// iff a def of the name REACHES `b`'s entry def-free (take the last def on it),
    /// i.e. iff the kill family's reaching set at `b` holds a def token. So the probe
    /// is: some kill name of `gen_stmt[b]` rebinds `read` (by lookup in the block's own
    /// indexes), or some tracked kill name that `dest_write_rebinds` `read` reaches `b`.
    pub(crate) fn may_reassigned_rebinds(&self, b: usize, read: &str) -> bool {
        // Not a block of this body: no rebinder, as the retired oracle answered.
        if b >= self.cfg.n_blocks() {
            return false;
        }
        // `cfg` and `writes` are built from the same `func` (`build`), so an in-range
        // block always has a write entry. Were one ever missing, answer "may rebind":
        // for a kill test that drops the hypothesis rather than keeping a stale one.
        let Some(bw) = self.writes.block(b) else {
            return true;
        };
        // `any_opaque_store` counts every statement `path_defs::write_havocs_function_list`
        // accepts: an opaque deref store, and (LAUNDERED-ALIAS-STORE, 2026-10-11) its
        // symmetric half, a write into escaped storage that an unresolved pointer copy
        // can read. Both havoc the same list `h`.
        if bw.stmt_explicit_dest_rebinds(&self.writes.names, read)
            || (bw.any_opaque_store() && self.writes.havoc_dest_rebinds(read))
            || (bw.gen_all() && self.writes.all_dest_rebinds(read))
        {
            return true;
        }
        let s = self.rebinder_union(self.kills(), b as u32, read, RebindMode::Dest);
        s != EMPTY_SET && s != E_SET
    }

    /// Some tracked rebinder of `read` has a non-empty reaching set at `b`.
    #[cfg(test)]
    pub(crate) fn covers(&self, b: usize, read: &str) -> bool {
        if b >= self.cfg.n_blocks() {
            return false;
        }
        let r = &self.versions;
        let g = r.read_group(&self.writes, read, RebindMode::Plain);
        let mut st = r.state.borrow_mut();
        g.rebinders.iter().any(|&k| self.name_entry_set(r, &mut st, b as u32, k) != EMPTY_SET)
    }

    /// The rebinders of `read` (statement versions), as text, in rebinder-tree order:
    /// the first half is the root's first child (parity tests).
    #[cfg(test)]
    pub(crate) fn rebinder_names(&self, read: &str) -> Vec<String> {
        let r = &self.versions;
        let g = r.read_group(&self.writes, read, RebindMode::Plain);
        g.rebinders.iter().map(|&k| self.writes.names.name(k).to_string()).collect()
    }

    /// The byte length of the RETIRED spelling of the inter-block answer for `read` at
    /// `b` (0 for `None`) — the size of the answer SET, which is what the resolution
    /// work is proportional to, whatever the spelling (scaling tests).
    #[cfg(test)]
    pub(crate) fn retired_answer_len(&self, b: usize, read: &str) -> u64 {
        if b >= self.cfg.n_blocks() {
            return 0;
        }
        let r = &self.versions;
        let s = self.rebinder_union(r, b as u32, read, RebindMode::Plain);
        if s == EMPTY_SET || s == E_SET {
            return 0;
        }
        let st = r.state.borrow();
        st.sets.text_len[s as usize] + u64::from(st.sets.count[s as usize]) - 1
    }

    /// The inter-block answer for `read` at `b` in the RETIRED spelling at every length
    /// (the sorted `_`-joined token list; `None` for `∅` / `{e}`): the exact SET,
    /// whatever the spelling hashes (parity tests).
    #[cfg(test)]
    pub(crate) fn inter_block_token_retired(&self, b: usize, read: &str) -> Option<String> {
        if b >= self.cfg.n_blocks() {
            return None;
        }
        let r = &self.versions;
        let s = self.rebinder_union(r, b as u32, read, RebindMode::Plain);
        if s == EMPTY_SET || s == E_SET {
            return None;
        }
        Some(r.state.borrow().sets.retired_spelling(s))
    }

    /// Some tracked rebinder of `read` reaches `b` with a set other than `∅` / `{e}`.
    #[cfg(test)]
    pub(crate) fn has_non_entry_rebinder(&self, b: usize, read: &str) -> bool {
        if b >= self.cfg.n_blocks() {
            return false;
        }
        let r = &self.versions;
        let g = r.read_group(&self.writes, read, RebindMode::Plain);
        let mut st = r.state.borrow_mut();
        g.rebinders.iter().any(|&k| {
            let s = self.name_entry_set(r, &mut st, b as u32, k);
            s != EMPTY_SET && s != E_SET
        })
    }

    /// Every tracked name, as text (parity tests).
    #[cfg(test)]
    pub(crate) fn tracked_names(&self) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        for id in 0..self.writes.names.len() as NameId {
            let text = self.writes.names.name(id);
            if self.versions.universe.contains(text).is_some() {
                out.push(text.to_string());
            }
        }
        out.sort();
        out
    }

    /// IN[b][name] spelled as the retired map's `BTreeSet<String>` (parity tests).
    #[cfg(test)]
    pub(crate) fn entry_tokens(&self, b: usize, name: &str) -> std::collections::BTreeSet<String> {
        let r = &self.versions;
        let Some(k) = r.universe.contains(name) else { return Default::default() };
        let mut st = r.state.borrow_mut();
        let s = self.name_entry_set(r, &mut st, b as u32, k);
        st.sets.elements(s).into_iter().map(tok_text).collect()
    }
}
