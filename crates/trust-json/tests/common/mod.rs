// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Helpers shared by the two halves of the acceptance gate.
//!
//! `differential_json.rs` (generated inputs: float bit patterns, Unicode
//! sweeps, random trees, byte soup) and `acceptance_gate.rs` (the checked-in
//! corpus, the hazard table, the typed-lens differential) are separate test
//! binaries, so anything they both need lives here rather than being written
//! twice. Two copies of [`same`] that drift apart would silently weaken
//! whichever gate holds the weaker copy.
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
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
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
                let ours: Vec<&str> = x.keys().map(String::as_str).collect();
                let theirs: Vec<&str> = y.keys().map(String::as_str).collect();
                return Err(format!(
                    "{path}: object len {} vs {}; ours={ours:?} theirs={theirs:?}",
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
        _ => Err(format!(
            "{path}: shape differs: ours={} theirs={}",
            kind_of_tj(a),
            kind_of_inc(b)
        )),
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
    let theirs = inc::from_str::<inc::Value>(src);
    match (&mine, &theirs) {
        (Ok(a), Ok(b)) => {
            if let Err(why) = same(a, b) {
                panic!("parse of {src:?} differs: {why}");
            }
            // ... and the bytes on the way back out.
            assert_eq!(
                tj::to_string(a).unwrap(),
                inc::to_string(b).unwrap(),
                "re-serialization of {src:?}"
            );
        }
        (Err(a), Err(b)) => {
            assert_eq!(
                (a.line(), a.column()),
                (b.line(), b.column()),
                "error position for {src:?}: {a} vs {b}"
            );
            assert_eq!(a.to_string(), b.to_string(), "error text for {src:?}");
            assert_eq!(
                a.classify() == tj::Category::Eof,
                b.classify() == inc::error::Category::Eof,
                "error category for {src:?}"
            );
        }
        (Ok(a), Err(b)) => panic!("trust-json accepted {src:?} as {a}; incumbent rejected: {b}"),
        (Err(a), Ok(b)) => panic!("trust-json rejected {src:?} ({a}); incumbent accepted: {b}"),
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
    let at = a
        .iter()
        .zip(b)
        .position(|(x, y)| x != y)
        .unwrap_or(a.len().min(b.len()));
    Some(format!(
        "byte {at} of {} (ours) / {} (theirs)\n     ours: {}\n   theirs: {}",
        a.len(),
        b.len(),
        window(ours, at),
        window(theirs, at),
    ))
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
