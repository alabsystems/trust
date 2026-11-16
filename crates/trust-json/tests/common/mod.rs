// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Helpers shared by the two halves of the acceptance gate.
//!
//! `differential_json.rs` (generated inputs: float bit patterns, Unicode
//! sweeps, random trees, byte soup) and `acceptance_gate.rs` (the checked-in
//! corpus, the hazard table, the typed-lens differential) are separate test
//! binaries, so anything they both need lives here rather than being written
//! twice. Two copies of [`same`] that drift apart would silently weaken
//! whichever gate holds the weaker copy. `adversarial.rs` takes the incumbent's
//! parse from here for the same reason.
//!
//! Nothing in this file asserts. It converts, compares and formats; the
//! decisions are in the test files.

#![allow(dead_code)] // each test binary uses a different subset.

use incumbent_serde_json as inc;
use trust_json as tj;

// ---------------------------------------------------------------------------
// A deterministic PRNG. No `rand` dependency, and reproducible failures.
// ---------------------------------------------------------------------------

pub struct Lcg(u64);

impl Lcg {
    pub fn new(seed: u64) -> Self {
        Lcg(seed)
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        // xorshift the high bits down; the raw LCG low bits are weak.
        let x = self.0;
        x ^ (x >> 31)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

// ---------------------------------------------------------------------------
// Tree conversion, ours -> theirs.
// ---------------------------------------------------------------------------

/// Rebuild one of our trees as one of the incumbent's.
///
/// This is the bridge that lets a single `#[derive(Deserialize)]` be driven by
/// BOTH trees (see `acceptance_gate.rs`), so it has to be lossless on every
/// axis [`same`] checks — in particular it must preserve which of the three
/// number carriers a value landed in, because `u64`, `i64` and `f64` are
/// distinguishable to a `Deserialize` impl and render differently.
pub fn to_inc(v: &tj::Value) -> inc::Value {
    match v {
        tj::Value::Null => inc::Value::Null,
        tj::Value::Bool(b) => inc::Value::Bool(*b),
        tj::Value::Number(n) => {
            if let Some(u) = n.as_u64() {
                inc::Value::Number(u.into())
            } else if let Some(i) = n.as_i64() {
                inc::Value::Number(i.into())
            } else {
                inc::Value::Number(inc::Number::from_f64(n.as_f64().unwrap()).unwrap())
            }
        }
        tj::Value::String(s) => inc::Value::String(s.clone()),
        tj::Value::Array(a) => inc::Value::Array(a.iter().map(to_inc).collect()),
        tj::Value::Object(o) => {
            let mut m = inc::Map::new();
            for (k, v) in o {
                m.insert(k.clone(), to_inc(v));
            }
            inc::Value::Object(m)
        }
    }
}

// ---------------------------------------------------------------------------
// The incumbent's object order, made independent of the build graph.
// ---------------------------------------------------------------------------

/// Which `Map` backing the incumbent has in THIS test binary.
///
/// `serde_json`'s `preserve_order` feature swaps its default `BTreeMap`
/// (key-sorted iteration) for an `IndexMap` (insertion order). Cargo unifies
/// features over every package one invocation selects, and a dependency can
/// only ADD a feature, so this crate's `Cargo.toml` cannot keep it off: the
/// backing is decided by how the test was invoked. `-p trust-json` alone gets
/// the `BTreeMap`; any selection that also contains `trust-certify` (which asks
/// for `preserve_order` since f2c4e2ccce) or the compiler's `trust-mc-driver`
/// gets the `IndexMap`, and so does `-p trust-json --features
/// incumbent-serde-json/preserve_order`, which asks for it directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IncumbentOrder {
    /// The default backing: objects iterate in key (UTF-8 byte) order.
    Sorted,
    /// `preserve_order` was unified in: objects iterate in insertion order.
    Insertion,
}

/// Measure [`IncumbentOrder`] on a two-key probe.
pub fn incumbent_order() -> Result<IncumbentOrder, String> {
    let probe = inc::from_str::<inc::Value>(r#"{"b":0,"a":0}"#).map_err(|e| e.to_string())?;
    match inc::to_string(&probe).map_err(|e| e.to_string())?.as_str() {
        r#"{"a":0,"b":0}"# => Ok(IncumbentOrder::Sorted),
        r#"{"b":0,"a":0}"# => Ok(IncumbentOrder::Insertion),
        other => Err(format!("incumbent object order is neither sorted nor insertion: {other}")),
    }
}

/// The incumbent's tree with every object rebuilt in key order: the iteration
/// order of its default `BTreeMap<String, Value>` backing (`String`'s `Ord`,
/// i.e. by UTF-8 bytes).
///
/// trust-json's [`tj::Map`] is key-sorted by design (`src/map.rs`), and every
/// expectation in this gate was written against the default backing. On that
/// backing this function is the identity; when `preserve_order` was unified in
/// (see [`IncumbentOrder`]) it yields what the default backing would have
/// iterated. Only the ORDER of entries changes: keys, values, number carriers
/// and duplicate-key collapse are the incumbent's own. Every incumbent tree
/// whose object order can reach a byte comparison or a `Deserialize` in this
/// gate comes through here, so none of those comparisons depends on which
/// other packages an invocation selected.
///
/// Iterative, so a deep tree cannot exhaust a test thread's stack.
pub fn key_sorted(mut v: inc::Value) -> inc::Value {
    {
        let mut pending: Vec<&mut inc::Value> = vec![&mut v];
        while let Some(node) = pending.pop() {
            match node {
                inc::Value::Array(items) => pending.extend(items.iter_mut()),
                inc::Value::Object(map) => {
                    let mut entries: Vec<(String, inc::Value)> =
                        std::mem::take(map).into_iter().collect();
                    entries.sort_unstable_by(|x, y| x.0.cmp(&y.0));
                    map.extend(entries);
                    pending.extend(map.values_mut());
                }
                _ => {}
            }
        }
    }
    v
}

/// The incumbent's `from_str::<Value>`, in the default backing's key order.
pub fn inc_from_str(src: &str) -> Result<inc::Value, inc::Error> {
    inc::from_str::<inc::Value>(src).map(key_sorted)
}

/// The incumbent's `from_slice::<Value>`, in the default backing's key order.
pub fn inc_from_slice(src: &[u8]) -> Result<inc::Value, inc::Error> {
    inc::from_slice::<inc::Value>(src).map(key_sorted)
}

// ---------------------------------------------------------------------------
// Structural equality.
// ---------------------------------------------------------------------------

/// Structural equality that is STRICTER than `==` on either side: numbers must
/// agree on which of the three carriers they landed in, and floats are compared
/// by bit pattern so `0.0` and `-0.0` are distinguishable.
pub fn same(a: &tj::Value, b: &inc::Value) -> Result<(), String> {
    same_at(a, b, "$")
}

fn same_at(a: &tj::Value, b: &inc::Value, path: &str) -> Result<(), String> {
    match (a, b) {
        (tj::Value::Null, inc::Value::Null) => Ok(()),
        (tj::Value::Bool(x), inc::Value::Bool(y)) if x == y => Ok(()),
        (tj::Value::String(x), inc::Value::String(y)) if x == y => Ok(()),
        (tj::Value::Number(x), inc::Value::Number(y)) => {
            if x.is_u64() != y.is_u64() || x.is_i64() != y.is_i64() || x.is_f64() != y.is_f64() {
                return Err(format!(
                    "{path}: number carrier differs: tj(u{},i{},f{}) inc(u{},i{},f{})",
                    x.is_u64(),
                    x.is_i64(),
                    x.is_f64(),
                    y.is_u64(),
                    y.is_i64(),
                    y.is_f64()
                ));
            }
            if x.as_u64() != y.as_u64() || x.as_i64() != y.as_i64() {
                return Err(format!("{path}: integer value differs: {x} vs {y}"));
            }
            match (x.as_f64(), y.as_f64()) {
                (Some(p), Some(q)) if p.to_bits() != q.to_bits() => Err(format!(
                    "{path}: float bits differ: {:#018x} vs {:#018x}",
                    p.to_bits(),
                    q.to_bits()
                )),
                _ => Ok(()),
            }
        }
        (tj::Value::Array(x), inc::Value::Array(y)) => {
            if x.len() != y.len() {
                return Err(format!("{path}: array len {} vs {}", x.len(), y.len()));
            }
            for (i, (p, q)) in x.iter().zip(y).enumerate() {
                same_at(p, q, &format!("{path}[{i}]"))?;
            }
            Ok(())
        }
        (tj::Value::Object(x), inc::Value::Object(y)) => {
            if x.len() != y.len() {
                // Name one key that is on a single side, not every key: an
                // object in the corpus or the 100k-key adversarial input
                // would otherwise put its whole key list in the message.
                let only_ours = x.keys().find(|k| !y.contains_key(k.as_str()));
                let only_theirs = y.keys().find(|k| !x.contains_key(k.as_str()));
                return Err(format!(
                    "{path}: object len {} vs {}; first key only ours: {only_ours:?}, \
                     first key only theirs: {only_theirs:?}",
                    x.len(),
                    y.len()
                ));
            }
            for (k, v) in x {
                match y.get(k) {
                    Some(w) => same_at(v, w, &format!("{path}.{k}"))?,
                    None => return Err(format!("{path}: key {k:?} missing on the incumbent side")),
                }
            }
            Ok(())
        }
        _ => {
            Err(format!("{path}: shape differs: ours={} theirs={}", kind_of_tj(a), kind_of_inc(b)))
        }
    }
}

pub fn kind_of_tj(v: &tj::Value) -> &'static str {
    match v {
        tj::Value::Null => "null",
        tj::Value::Bool(_) => "bool",
        tj::Value::Number(_) => "number",
        tj::Value::String(_) => "string",
        tj::Value::Array(_) => "array",
        tj::Value::Object(_) => "object",
    }
}

pub fn kind_of_inc(v: &inc::Value) -> &'static str {
    match v {
        inc::Value::Null => "null",
        inc::Value::Bool(_) => "bool",
        inc::Value::Number(_) => "number",
        inc::Value::String(_) => "string",
        inc::Value::Array(_) => "array",
        inc::Value::Object(_) => "object",
    }
}

// ---------------------------------------------------------------------------
// Parse agreement.
// ---------------------------------------------------------------------------

/// Both implementations must accept, or both must reject.
///
/// On acceptance the trees must be [`same`] AND re-serialize to the same bytes.
/// On rejection the LINE, the COLUMN, the message and the EOF-ness must match:
/// *agreeing on accept while disagreeing on reject is a real defect*, and a
/// replacement that rejects the same inputs a byte later is still a different
/// diagnostic in every consumer that prints one.
pub fn agree_on_parse(src: &str) {
    let mine = tj::from_str(src);
    let theirs = inc_from_str(src);
    match (&mine, &theirs) {
        (Ok(a), Ok(b)) => {
            if let Err(why) = same(a, b) {
                panic!("parse of {} differs: {why}", abbreviated(src));
            }
            // ... and the bytes on the way back out.
            let (mine, theirs) = (tj::to_string(a).unwrap(), inc::to_string(b).unwrap());
            if let Some(d) = first_difference(&mine, &theirs) {
                panic!("re-serialization of {} differs at {d}", abbreviated(src));
            }
        }
        (Err(a), Err(b)) => {
            assert_eq!(
                (a.line(), a.column()),
                (b.line(), b.column()),
                "error position for {}: {a} vs {b}",
                abbreviated(src)
            );
            assert_eq!(a.to_string(), b.to_string(), "error text for {}", abbreviated(src));
            assert_eq!(
                a.classify() == tj::Category::Eof,
                b.classify() == inc::error::Category::Eof,
                "error category for {}",
                abbreviated(src)
            );
        }
        (Ok(a), Err(b)) => panic!(
            "trust-json accepted {} as {}; incumbent rejected: {b}",
            abbreviated(src),
            abbreviated(&a.to_string())
        ),
        (Err(a), Ok(b)) => panic!(
            "trust-json rejected {} ({a}); incumbent accepted: {}",
            abbreviated(src),
            abbreviated(&b.to_string())
        ),
    }
}

// ---------------------------------------------------------------------------
// Failure rendering.
// ---------------------------------------------------------------------------

/// Render the first byte at which two renderings diverge, with a window around
/// it from each side.
///
/// The corpus holds documents up to a megabyte, so a bare `assert_eq!` on two
/// serializations prints two megabytes of near-identical text and buries the
/// one byte that matters. The brief's requirement — *"ANY disagreement: report
/// the exact input and both outputs"* — is met by naming the offset and
/// showing both sides at it; the input is named by path, and the full outputs
/// are reproducible from it.
pub fn first_difference(ours: &str, theirs: &str) -> Option<String> {
    if ours == theirs {
        return None;
    }
    let (a, b) = (ours.as_bytes(), theirs.as_bytes());
    let at = a.iter().zip(b).position(|(x, y)| x != y).unwrap_or(a.len().min(b.len()));
    Some(format!(
        "byte {at} of {} (ours) / {} (theirs)\n     ours: {}\n   theirs: {}",
        a.len(),
        b.len(),
        window(ours, at),
        window(theirs, at),
    ))
}

/// How many bytes of an input a failure message reproduces before it
/// abbreviates. Every generated or hand-written case that is not one of the
/// enormous inputs fits, so those still print whole.
pub const SHOWN_BYTES: usize = 160;

/// An input as a failure message names it: whole, `Debug`-escaped, when it is
/// at most [`SHOWN_BYTES`] long; otherwise its head and its length.
///
/// `adversarial.rs` feeds megabyte inputs (a 1 MiB escape string, a 100k-key
/// object), and a note that repeats the input and both renderings in full was
/// one 5 MB line in which the divergence could not be found. The divergence
/// itself is [`first_difference`]'s job; this only says WHICH input it was.
pub fn abbreviated(s: &str) -> String {
    if s.len() <= SHOWN_BYTES {
        return format!("{s:?}");
    }
    let cut = (0..=SHOWN_BYTES / 2).rev().find(|i| s.is_char_boundary(*i)).unwrap_or(0);
    format!("\"{}\"… ({} bytes)", s[..cut].escape_debug(), s.len())
}

fn window(s: &str, at: usize) -> String {
    let lo = at.saturating_sub(60);
    let hi = (at + 60).min(s.len());
    // Snap to char boundaries; the corpus is full of multi-byte text.
    let lo = (lo..=at).find(|i| s.is_char_boundary(*i)).unwrap_or(at);
    let hi = (hi..=s.len()).find(|i| s.is_char_boundary(*i)).unwrap_or(s.len());
    let mut out = String::new();
    if lo > 0 {
        out.push('…');
    }
    out.push_str(&s[lo..hi].escape_debug().to_string());
    if hi < s.len() {
        out.push('…');
    }
    out
}
