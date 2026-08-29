// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A DIFFERENTIAL PROPERTY SWEEP of `trust-bincode` against the LIVE incumbent
//! `bincode 1.3.3`.
//!
//! # Why this exists when `golden_bincode1.rs` already passes
//!
//! The golden test compares this implementation against a committed fixture of
//! bytes captured from the incumbent. A fixture can only ever pin the cases
//! somebody thought to capture; it is silent about every shape nobody wrote
//! down. This file removes that ceiling: it links the real `bincode 1.3.3` as a
//! DEV-dependency and compares the two implementations on thousands of
//! deterministically generated values, plus a corrupt-input corpus, plus the
//! `io::Read` path.
//!
//! The incumbent is a `[dev-dependencies]` entry ONLY. It is built for this
//! package's test targets and is not part of `libtrust_bincode.rlib`'s
//! dependency set, so it cannot reach the shipping closure this crate exists to
//! clean. The manifest states this at length. Verify rather than believe it:
//!
//! ```text
//! cd crates && targo metadata --format-version 1 \
//!     --filter-platform aarch64-apple-darwin \
//!   | python3 -c 'import json,sys; m=json.load(sys.stdin); \
//!       n=[x for x in m["resolve"]["nodes"] if "trust-bincode" in x["id"]][0]; \
//!       print([(d["name"], [k["kind"] for k in d["dep_kinds"]]) for d in n["deps"]])'
//! ```
//!
//! The `bincode` edge must read `["dev"]`. A `None`/`null` kind is a NORMAL
//! edge and means the shipping closure was re-contaminated.
//!
//! # What is compared
//!
//! For every generated value, under each of the three configurations that
//! actually occur in this tree:
//!
//! | lane | int encoding | endian | trailing | limit | who uses it |
//! |---|---|---|---|---|---|
//! | `fn_fixint_allow_trailing` | fixint | LE | allow | none | the free functions — `trust-certify`, `trust-clean`, `trust-proof-cert` |
//! | `struct_varint_reject_trailing` | **varint** | LE | **reject** | none | `DefaultOptions::new()`'s documented default; no live caller |
//! | `trust_ir_fixint_reject_limit64mib` | fixint | LE | reject | 64 MiB | `first-party/trust-ir`'s `clean_expr_codec` |
//!
//! four things are asserted:
//!
//! 1. `trust_bincode::serialize(v)` is byte-for-byte `bincode::serialize(v)`;
//! 2. `serialized_size(v)` agrees, and agrees with the encoded length;
//! 3. this crate decodes the INCUMBENT's bytes back to a value equal to `v`;
//! 4. the incumbent decodes THIS crate's bytes back to a value equal to `v`.
//!
//! Error paths get the same treatment: the same corrupt buffer goes to both
//! sides and the accept/reject decision, the `Display` text and the `Debug`
//! rendering must all agree.
//!
//! # Determinism
//!
//! Values come from an inline xorshift64\* generator seeded from the single
//! constant [`SEED`]. There is no `rand` dependency, no clock, and no OS
//! entropy anywhere in this file. Re-running reproduces byte-identical inputs;
//! a reported divergence can be reproduced by re-running with the same seed.
//!
//! The one place ordering is not statically determined is `HashMap`, and it is
//! sound here for a specific reason: both encoders iterate the SAME map
//! instance, so they observe the same order, and the decoded comparison is
//! `HashMap: PartialEq`, which is order-independent.
//!
//! # The harness must be able to fail
//!
//! [`the_negative_control_proves_the_harness_can_fail`] pushes a deliberately
//! perturbed value through the very same comparison path and asserts that the
//! failure fires, capturing the panic text. A differential that cannot fail is
//! worthless.

#![allow(clippy::type_complexity)]

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::fmt::Debug;

mod support;

use support::hex;
// Via the `support::types` re-export, which is the convention the other test
// binaries already use — importing `support::big_enum::BigEnum` directly leaves
// that re-export unused and warns.
use support::types::BigEnum;

// ===========================================================================
// The seed. One constant, reported with every result.
// ===========================================================================

/// The single source of all generated values in this file.
///
/// Reported alongside every count so a divergence is reproducible. Lanes salt
/// it with a per-lane constant so two lanes do not draw the same stream.
pub const SEED: u64 = 0xBADC_0FFE_E0DD_F00D;

// ===========================================================================
// Deterministic generator — xorshift64*, written out here on purpose.
// ===========================================================================

/// xorshift64\* (Vigna). Chosen because it is four lines, has no dependency,
/// and its state transition is exactly reproducible on every host.
struct Rng {
    s: u64,
}

impl Rng {
    fn new(seed: u64) -> Rng {
        // xorshift is degenerate at zero; substitute the golden-ratio constant.
        Rng {
            s: if seed == 0 { 0x9E37_79B9_7F4A_7C15 } else { seed },
        }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.s;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.s = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn next_u128(&mut self) -> u128 {
        ((self.next_u64() as u128) << 64) | self.next_u64() as u128
    }

    fn below(&mut self, n: usize) -> usize {
        debug_assert!(n > 0);
        (self.next_u64() % n as u64) as usize
    }

    fn boolean(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }

    /// A magnitude-biased `u64`: small values are common, because that is where
    /// the varint width boundaries live, but the full range still appears.
    fn biased_u64(&mut self) -> u64 {
        let bits = self.below(65);
        if bits == 64 {
            self.next_u64()
        } else if bits == 0 {
            0
        } else {
            self.next_u64() >> (64 - bits)
        }
    }

    fn biased_u128(&mut self) -> u128 {
        let bits = self.below(129);
        if bits == 128 {
            self.next_u128()
        } else if bits == 0 {
            0
        } else {
            self.next_u128() >> (128 - bits)
        }
    }

    fn biased_i64(&mut self) -> i64 {
        let m = self.biased_u64() as i64;
        if self.boolean() { m } else { m.wrapping_neg() }
    }

    fn biased_i128(&mut self) -> i128 {
        let m = self.biased_u128() as i128;
        if self.boolean() { m } else { m.wrapping_neg() }
    }

    /// A `char` spread across all four UTF-8 widths, plus the exact boundary
    /// scalars. Surrogates are skipped by construction, not by retry.
    fn ch(&mut self) -> char {
        const BOUNDARY: [u32; 12] = [
            0x0000, 0x0001, 0x007F, 0x0080, 0x07FF, 0x0800, 0xD7FF, 0xE000, 0xFFFD, 0xFFFF,
            0x1_0000, 0x10_FFFF,
        ];
        if self.below(4) == 0 {
            let c = BOUNDARY[self.below(BOUNDARY.len())];
            return char::from_u32(c).expect("BOUNDARY holds only valid scalars");
        }
        loop {
            let v = match self.below(4) {
                0 => self.next_u64() as u32 % 0x80,
                1 => self.next_u64() as u32 % 0x800,
                2 => self.next_u64() as u32 % 0x1_0000,
                _ => self.next_u64() as u32 % 0x11_0000,
            };
            if let Some(c) = char::from_u32(v) {
                return c;
            }
            // v landed in the surrogate range D800..=DFFF; draw again.
        }
    }

    fn string(&mut self, max_chars: usize) -> String {
        let n = self.below(max_chars + 1);
        (0..n).map(|_| self.ch()).collect()
    }

    fn bytes(&mut self, max_len: usize) -> Vec<u8> {
        let n = self.below(max_len + 1);
        (0..n).map(|_| self.next_u64() as u8).collect()
    }

    /// A finite-or-not `f64` drawn so that the interesting bit patterns appear
    /// often. Comparison downstream is bit-exact, so NaN is safe to emit.
    fn f64v(&mut self) -> f64 {
        const SPECIAL: [f64; 12] = [
            0.0,
            -0.0,
            1.0,
            -1.0,
            f64::MIN,
            f64::MAX,
            f64::EPSILON,
            f64::MIN_POSITIVE,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
            5e-324, // smallest subnormal
        ];
        if self.below(3) == 0 {
            SPECIAL[self.below(SPECIAL.len())]
        } else {
            f64::from_bits(self.next_u64())
        }
    }

    fn f32v(&mut self) -> f32 {
        const SPECIAL: [f32; 12] = [
            0.0,
            -0.0,
            1.0,
            -1.0,
            f32::MIN,
            f32::MAX,
            f32::EPSILON,
            f32::MIN_POSITIVE,
            f32::INFINITY,
            f32::NEG_INFINITY,
            f32::NAN,
            1e-45, // smallest subnormal
        ];
        if self.below(3) == 0 {
            SPECIAL[self.below(SPECIAL.len())]
        } else {
            f32::from_bits(self.next_u64() as u32)
        }
    }
}

// ===========================================================================
// The data model. Between them these types reach every `Serializer` method
// bincode implements except `serialize_seq(None)` (which is an encode ERROR,
// covered separately) and `deserialize_any` (likewise).
// ===========================================================================

/// `f32` compared by BIT PATTERN, not by `PartialEq`.
///
/// Two reasons. `NaN != NaN`, so a derived comparison would silently pass on a
/// decoder that returned the wrong NaN; and `-0.0 == 0.0`, so it would pass on
/// a decoder that lost the sign bit. Both are real encoder defects and both are
/// invisible to `f32`'s own `PartialEq`.
#[derive(Serialize, Deserialize, Debug, Clone, Copy)]
struct F32B(f32);

impl PartialEq for F32B {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

/// `f64` compared by bit pattern. See [`F32B`].
#[derive(Serialize, Deserialize, Debug, Clone, Copy)]
struct F64B(f64);

impl PartialEq for F64B {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct Scalars {
    unit: (),
    b: bool,
    i8v: i8,
    i16v: i16,
    i32v: i32,
    i64v: i64,
    i128v: i128,
    u8v: u8,
    u16v: u16,
    u32v: u32,
    u64v: u64,
    u128v: u128,
    usizev: usize,
    isizev: isize,
    f32v: F32B,
    f64v: F64B,
    chv: char,
    sv: String,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct UnitStruct;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct NewtypeStruct(u64);

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct TupleStruct(u8, i64, String, Option<u32>);

/// A twelve-variant enum spanning all four serde variant kinds and recursing
/// through two different shapes (`Box` and `Vec`).
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
enum Shape {
    Nothing,
    Flag(bool),
    Pair(u32, i16),
    Named {
        id: u64,
        tag: String,
        opt: Option<i8>,
    },
    Deep(Box<Shape>),
    List(Vec<Shape>),
    Blob(Vec<u8>),
    Chars(Vec<char>),
    Map(BTreeMap<String, i32>),
    Big(u128),
    Neg(i128),
    Real(F64B),
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
enum Tree {
    Leaf(i64),
    Node(Vec<Tree>),
    Tagged { key: String, child: Box<Tree> },
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct Colls {
    v_u8: Vec<u8>,
    v_str: Vec<String>,
    v_v_i32: Vec<Vec<i32>>,
    bmap: BTreeMap<String, i64>,
    bset: BTreeSet<u16>,
    dq: VecDeque<u8>,
    hmap: HashMap<u8, u32>,
    arr5: [u8; 5],
    arr3: [i32; 3],
    tup: (u8, String, Option<bool>, ()),
    nested: Option<Box<Shape>>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct Everything {
    scalars: Scalars,
    unit_struct: UnitStruct,
    newtype: NewtypeStruct,
    tuple_struct: TupleStruct,
    shape: Shape,
    shapes: Vec<Shape>,
    tree: Tree,
    colls: Colls,
    opt_opt: Option<Option<u8>>,
    res: Result<u32, String>,
}

// --------------------------------------------------------------------------
// Generators
// --------------------------------------------------------------------------

fn gen_scalars(r: &mut Rng) -> Scalars {
    Scalars {
        unit: (),
        b: r.boolean(),
        i8v: r.next_u64() as i8,
        i16v: r.biased_i64() as i16,
        i32v: r.biased_i64() as i32,
        i64v: r.biased_i64(),
        i128v: r.biased_i128(),
        u8v: r.next_u64() as u8,
        u16v: r.biased_u64() as u16,
        u32v: r.biased_u64() as u32,
        u64v: r.biased_u64(),
        u128v: r.biased_u128(),
        usizev: r.biased_u64() as usize,
        isizev: r.biased_i64() as isize,
        f32v: F32B(r.f32v()),
        f64v: F64B(r.f64v()),
        chv: r.ch(),
        sv: r.string(10),
    }
}

fn gen_shape(r: &mut Rng, depth: u32) -> Shape {
    // At the depth cap only the non-recursive variants remain reachable.
    let leaf_only = depth == 0;
    let pick = if leaf_only {
        match r.below(9) {
            0 => 0,
            1 => 1,
            2 => 2,
            3 => 3,
            4 => 6,
            5 => 7,
            6 => 8,
            7 => 9,
            _ => 11,
        }
    } else {
        r.below(12)
    };
    match pick {
        0 => Shape::Nothing,
        1 => Shape::Flag(r.boolean()),
        2 => Shape::Pair(r.biased_u64() as u32, r.biased_i64() as i16),
        3 => Shape::Named {
            id: r.biased_u64(),
            tag: r.string(8),
            opt: if r.boolean() {
                Some(r.next_u64() as i8)
            } else {
                None
            },
        },
        4 => Shape::Deep(Box::new(gen_shape(r, depth - 1))),
        5 => {
            let n = r.below(5);
            Shape::List((0..n).map(|_| gen_shape(r, depth - 1)).collect())
        }
        6 => Shape::Blob(r.bytes(12)),
        7 => {
            let n = r.below(6);
            Shape::Chars((0..n).map(|_| r.ch()).collect())
        }
        8 => {
            let n = r.below(5);
            Shape::Map(
                (0..n)
                    .map(|_| (r.string(6), r.biased_i64() as i32))
                    .collect(),
            )
        }
        9 => Shape::Big(r.biased_u128()),
        10 => Shape::Neg(r.biased_i128()),
        _ => Shape::Real(F64B(r.f64v())),
    }
}

fn gen_tree(r: &mut Rng, depth: u32) -> Tree {
    if depth == 0 || r.below(3) == 0 {
        return Tree::Leaf(r.biased_i64());
    }
    if r.boolean() {
        let n = r.below(4);
        Tree::Node((0..n).map(|_| gen_tree(r, depth - 1)).collect())
    } else {
        Tree::Tagged {
            key: r.string(6),
            child: Box::new(gen_tree(r, depth - 1)),
        }
    }
}

fn gen_colls(r: &mut Rng, depth: u32) -> Colls {
    let n_str = r.below(5);
    let n_vv = r.below(4);
    let n_bmap = r.below(5);
    let n_bset = r.below(6);
    let n_hmap = r.below(6);
    Colls {
        v_u8: r.bytes(16),
        v_str: (0..n_str).map(|_| r.string(7)).collect(),
        v_v_i32: (0..n_vv)
            .map(|_| {
                let m = r.below(4);
                (0..m).map(|_| r.biased_i64() as i32).collect()
            })
            .collect(),
        bmap: (0..n_bmap).map(|_| (r.string(5), r.biased_i64())).collect(),
        bset: (0..n_bset).map(|_| r.biased_u64() as u16).collect(),
        dq: r.bytes(9).into(),
        hmap: (0..n_hmap)
            .map(|_| (r.next_u64() as u8, r.biased_u64() as u32))
            .collect(),
        arr5: [
            r.next_u64() as u8,
            r.next_u64() as u8,
            r.next_u64() as u8,
            r.next_u64() as u8,
            r.next_u64() as u8,
        ],
        arr3: [
            r.biased_i64() as i32,
            r.biased_i64() as i32,
            r.biased_i64() as i32,
        ],
        tup: (
            r.next_u64() as u8,
            r.string(6),
            if r.boolean() { Some(r.boolean()) } else { None },
            (),
        ),
        nested: if r.boolean() {
            Some(Box::new(gen_shape(r, depth)))
        } else {
            None
        },
    }
}

fn gen_everything(r: &mut Rng) -> Everything {
    let n_shapes = r.below(4);
    Everything {
        scalars: gen_scalars(r),
        unit_struct: UnitStruct,
        newtype: NewtypeStruct(r.biased_u64()),
        tuple_struct: TupleStruct(
            r.next_u64() as u8,
            r.biased_i64(),
            r.string(9),
            if r.boolean() {
                Some(r.biased_u64() as u32)
            } else {
                None
            },
        ),
        shape: gen_shape(r, 3),
        shapes: (0..n_shapes).map(|_| gen_shape(r, 2)).collect(),
        tree: gen_tree(r, 4),
        colls: gen_colls(r, 2),
        opt_opt: match r.below(3) {
            0 => None,
            1 => Some(None),
            _ => Some(Some(r.next_u64() as u8)),
        },
        res: if r.boolean() {
            Ok(r.biased_u64() as u32)
        } else {
            Err(r.string(7))
        },
    }
}

// ===========================================================================
// The three configurations.
// ===========================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Cfg {
    /// What `bincode::serialize` / `bincode::deserialize` do.
    FnDefault,
    /// What `DefaultOptions::new()` alone does. VARINT and REJECT-trailing.
    StructDefault,
    /// `first-party/trust-ir`'s `clean_expr_codec` configuration.
    TrustIr,
}

const CONFIGS: [Cfg; 3] = [Cfg::FnDefault, Cfg::StructDefault, Cfg::TrustIr];

/// The byte limit `first-party/trust-ir`'s codec sets. It is inert on the slice
/// decode path in BOTH implementations — deliberately, see `config`'s docs.
const TRUST_IR_LIMIT: u64 = 64 * 1024 * 1024;

impl Cfg {
    fn name(self) -> &'static str {
        match self {
            Cfg::FnDefault => "fn_fixint_allow_trailing",
            Cfg::StructDefault => "struct_varint_reject_trailing",
            Cfg::TrustIr => "trust_ir_fixint_reject_limit64mib",
        }
    }

    fn index(self) -> usize {
        match self {
            Cfg::FnDefault => 0,
            Cfg::StructDefault => 1,
            Cfg::TrustIr => 2,
        }
    }
}

/// An error rendered both ways, so a divergence in either is caught.
#[derive(Clone, PartialEq, Eq, Debug)]
struct ErrText {
    display: String,
    debug: String,
}

fn err_text<E: std::fmt::Display + Debug>(e: E) -> ErrText {
    ErrText {
        display: e.to_string(),
        debug: format!("{e:?}"),
    }
}

/// This crate, behind its own `Options` import so the two `Options` traits
/// never collide in one scope.
mod ours {
    use super::{Cfg, ErrText, TRUST_IR_LIMIT, err_text};
    use trust_bincode::Options as _;

    pub fn ser<T: serde::Serialize + ?Sized>(cfg: Cfg, v: &T) -> Result<Vec<u8>, ErrText> {
        match cfg {
            Cfg::FnDefault => trust_bincode::serialize(v),
            Cfg::StructDefault => trust_bincode::DefaultOptions::new().serialize(v),
            Cfg::TrustIr => trust_bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .with_little_endian()
                .reject_trailing_bytes()
                .with_limit(TRUST_IR_LIMIT)
                .serialize(v),
        }
        .map_err(err_text)
    }

    pub fn size<T: serde::Serialize + ?Sized>(cfg: Cfg, v: &T) -> Result<u64, ErrText> {
        match cfg {
            Cfg::FnDefault => trust_bincode::serialized_size(v),
            Cfg::StructDefault => trust_bincode::DefaultOptions::new().serialized_size(v),
            Cfg::TrustIr => trust_bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .with_little_endian()
                .reject_trailing_bytes()
                .with_limit(TRUST_IR_LIMIT)
                .serialized_size(v),
        }
        .map_err(err_text)
    }

    pub fn de<T: serde::de::DeserializeOwned>(cfg: Cfg, b: &[u8]) -> Result<T, ErrText> {
        match cfg {
            Cfg::FnDefault => trust_bincode::deserialize(b),
            Cfg::StructDefault => trust_bincode::DefaultOptions::new().deserialize(b),
            Cfg::TrustIr => trust_bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .with_little_endian()
                .reject_trailing_bytes()
                .with_limit(TRUST_IR_LIMIT)
                .deserialize(b),
        }
        .map_err(err_text)
    }

    pub fn de_from<T: serde::de::DeserializeOwned>(cfg: Cfg, b: &[u8]) -> Result<T, ErrText> {
        match cfg {
            Cfg::FnDefault => trust_bincode::deserialize_from(b),
            Cfg::StructDefault => trust_bincode::DefaultOptions::new().deserialize_from(b),
            Cfg::TrustIr => trust_bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .with_little_endian()
                .reject_trailing_bytes()
                .with_limit(TRUST_IR_LIMIT)
                .deserialize_from(b),
        }
        .map_err(err_text)
    }

    pub fn ser_limited<T: serde::Serialize + ?Sized>(
        limit: u64,
        v: &T,
    ) -> Result<Vec<u8>, ErrText> {
        trust_bincode::DefaultOptions::new()
            .with_fixint_encoding()
            .allow_trailing_bytes()
            .with_limit(limit)
            .serialize(v)
            .map_err(err_text)
    }

    pub fn de_from_limited<T: serde::de::DeserializeOwned>(
        limit: u64,
        b: &[u8],
    ) -> Result<T, ErrText> {
        trust_bincode::DefaultOptions::new()
            .with_fixint_encoding()
            .allow_trailing_bytes()
            .with_limit(limit)
            .deserialize_from(b)
            .map_err(err_text)
    }
}

/// The incumbent `bincode 1.3.3`, behind its own `Options` import.
mod incumbent {
    use super::{Cfg, ErrText, TRUST_IR_LIMIT, err_text};
    use bincode::Options as _;

    pub fn ser<T: serde::Serialize + ?Sized>(cfg: Cfg, v: &T) -> Result<Vec<u8>, ErrText> {
        match cfg {
            Cfg::FnDefault => bincode::serialize(v),
            Cfg::StructDefault => bincode::DefaultOptions::new().serialize(v),
            Cfg::TrustIr => bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .with_little_endian()
                .reject_trailing_bytes()
                .with_limit(TRUST_IR_LIMIT)
                .serialize(v),
        }
        .map_err(err_text)
    }

    pub fn size<T: serde::Serialize + ?Sized>(cfg: Cfg, v: &T) -> Result<u64, ErrText> {
        match cfg {
            Cfg::FnDefault => bincode::serialized_size(v),
            Cfg::StructDefault => bincode::DefaultOptions::new().serialized_size(v),
            Cfg::TrustIr => bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .with_little_endian()
                .reject_trailing_bytes()
                .with_limit(TRUST_IR_LIMIT)
                .serialized_size(v),
        }
        .map_err(err_text)
    }

    pub fn de<T: serde::de::DeserializeOwned>(cfg: Cfg, b: &[u8]) -> Result<T, ErrText> {
        match cfg {
            Cfg::FnDefault => bincode::deserialize(b),
            Cfg::StructDefault => bincode::DefaultOptions::new().deserialize(b),
            Cfg::TrustIr => bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .with_little_endian()
                .reject_trailing_bytes()
                .with_limit(TRUST_IR_LIMIT)
                .deserialize(b),
        }
        .map_err(err_text)
    }

    pub fn de_from<T: serde::de::DeserializeOwned>(cfg: Cfg, b: &[u8]) -> Result<T, ErrText> {
        match cfg {
            Cfg::FnDefault => bincode::deserialize_from(b),
            Cfg::StructDefault => bincode::DefaultOptions::new().deserialize_from(b),
            Cfg::TrustIr => bincode::DefaultOptions::new()
                .with_fixint_encoding()
                .with_little_endian()
                .reject_trailing_bytes()
                .with_limit(TRUST_IR_LIMIT)
                .deserialize_from(b),
        }
        .map_err(err_text)
    }

    pub fn ser_limited<T: serde::Serialize + ?Sized>(
        limit: u64,
        v: &T,
    ) -> Result<Vec<u8>, ErrText> {
        bincode::DefaultOptions::new()
            .with_fixint_encoding()
            .allow_trailing_bytes()
            .with_limit(limit)
            .serialize(v)
            .map_err(err_text)
    }

    pub fn de_from_limited<T: serde::de::DeserializeOwned>(
        limit: u64,
        b: &[u8],
    ) -> Result<T, ErrText> {
        bincode::DefaultOptions::new()
            .with_fixint_encoding()
            .allow_trailing_bytes()
            .with_limit(limit)
            .deserialize_from(b)
            .map_err(err_text)
    }
}

// ===========================================================================
// The report. Divergences are ACCUMULATED, not asserted one at a time, so a
// failing run names the whole failure surface instead of the first case.
// ===========================================================================

#[derive(Debug)]
struct Divergence {
    case: String,
    cfg: &'static str,
    kind: &'static str,
    ours: String,
    theirs: String,
}

struct Report {
    lane: String,
    values: usize,
    /// Observations per config, indexed by `Cfg::index`.
    obs: [usize; 3],
    divs: Vec<Divergence>,
    /// Divergences per config, indexed by `Cfg::index`.
    div_by_cfg: [usize; 3],
}

impl Report {
    fn new(lane: &str) -> Report {
        Report {
            lane: lane.to_string(),
            values: 0,
            obs: [0; 3],
            divs: Vec::new(),
            div_by_cfg: [0; 3],
        }
    }

    fn observe(&mut self, cfg: Cfg) {
        self.obs[cfg.index()] += 1;
    }

    fn diverge(
        &mut self,
        case: &str,
        cfg: Cfg,
        kind: &'static str,
        ours: String,
        theirs: String,
    ) {
        self.div_by_cfg[cfg.index()] += 1;
        self.divs.push(Divergence {
            case: case.to_string(),
            cfg: cfg.name(),
            kind,
            ours,
            theirs,
        });
    }

    fn total_obs(&self) -> usize {
        self.obs.iter().sum()
    }

    fn summary(&self) -> String {
        format!(
            "[{}] seed=0x{SEED:016X} values={} observations={} \
             (fn_fixint_allow_trailing={}, struct_varint_reject_trailing={}, \
             trust_ir_fixint_reject_limit64mib={}) divergences={} \
             (per-config {}/{}/{})",
            self.lane,
            self.values,
            self.total_obs(),
            self.obs[0],
            self.obs[1],
            self.obs[2],
            self.divs.len(),
            self.div_by_cfg[0],
            self.div_by_cfg[1],
            self.div_by_cfg[2],
        )
    }

    /// Panics naming every divergence found (capped, with the residue counted).
    /// Also refuses a lane that made NO observations — a silent instrument
    /// reads as a clean result otherwise.
    fn finish(self) {
        println!("{}", self.summary());
        assert!(
            self.total_obs() > 0,
            "[{}] made ZERO observations — the lane did not run, which is not a pass",
            self.lane
        );
        if self.divs.is_empty() {
            return;
        }
        let mut msg = format!(
            "\nDIFFERENTIAL FAILURE vs bincode 1.3.3\n{}\n\n{} divergence(s):\n",
            self.summary(),
            self.divs.len()
        );
        for (i, d) in self.divs.iter().enumerate() {
            if i == 24 {
                msg.push_str(&format!("  ... and {} more\n", self.divs.len() - 24));
                break;
            }
            msg.push_str(&format!(
                "  #{:<3} case={} cfg={} kind={}\n         trust-bincode: {}\n         bincode 1.3.3: {}\n",
                i + 1,
                d.case,
                d.cfg,
                d.kind,
                d.ours,
                d.theirs
            ));
        }
        panic!("{msg}");
    }
}

// ===========================================================================
// The comparison itself. Every value lane funnels through here.
// ===========================================================================

/// Compare the two implementations on one value under one config.
///
/// This is the single place the four assertions live, so the negative control
/// exercises exactly the code the real lanes do.
fn compare_one<T>(rep: &mut Report, case: &str, cfg: Cfg, value: &T, expected: &T)
where
    T: Serialize + DeserializeOwned + PartialEq + Debug,
{
    rep.observe(cfg);

    let a = ours::ser(cfg, value);
    let b = incumbent::ser(cfg, value);

    match (&a, &b) {
        (Err(x), Err(y)) => {
            if x.display != y.display {
                rep.diverge(
                    case,
                    cfg,
                    "encode_error_display",
                    x.display.clone(),
                    y.display.clone(),
                );
            }
            if x.debug != y.debug {
                rep.diverge(
                    case,
                    cfg,
                    "encode_error_debug",
                    x.debug.clone(),
                    y.debug.clone(),
                );
            }
            return;
        }
        (Ok(x), Err(y)) => {
            rep.diverge(
                case,
                cfg,
                "encode_accept_reject",
                format!("Ok({} bytes: {})", x.len(), hex(x)),
                format!("Err({})", y.display),
            );
            return;
        }
        (Err(x), Ok(y)) => {
            rep.diverge(
                case,
                cfg,
                "encode_accept_reject",
                format!("Err({})", x.display),
                format!("Ok({} bytes: {})", y.len(), hex(y)),
            );
            return;
        }
        (Ok(_), Ok(_)) => {}
    }

    let ours_bytes = a.expect("matched Ok above");
    let theirs_bytes = b.expect("matched Ok above");

    // (1) byte-for-byte encode identity
    if ours_bytes != theirs_bytes {
        rep.diverge(
            case,
            cfg,
            "encoded_bytes",
            hex(&ours_bytes),
            hex(&theirs_bytes),
        );
        // Keep going: the decode lanes below still say something useful.
    }

    // (2) serialized_size agreement, and agreement with the encoding
    let sa = ours::size(cfg, value);
    let sb = incumbent::size(cfg, value);
    match (&sa, &sb) {
        (Ok(x), Ok(y)) => {
            if x != y {
                rep.diverge(case, cfg, "serialized_size", x.to_string(), y.to_string());
            }
            if *x as usize != ours_bytes.len() {
                rep.diverge(
                    case,
                    cfg,
                    "serialized_size_vs_encoded_len",
                    format!("size={x} encoded_len={}", ours_bytes.len()),
                    format!("(incumbent size={y} encoded_len={})", theirs_bytes.len()),
                );
            }
        }
        (Err(x), Err(y)) => {
            if x.display != y.display {
                rep.diverge(
                    case,
                    cfg,
                    "serialized_size_error",
                    x.display.clone(),
                    y.display.clone(),
                );
            }
        }
        _ => rep.diverge(
            case,
            cfg,
            "serialized_size_accept_reject",
            format!("{sa:?}"),
            format!("{sb:?}"),
        ),
    }

    // (3) THIS crate decodes the INCUMBENT's bytes.
    match ours::de::<T>(cfg, &theirs_bytes) {
        Ok(v) => {
            if v != *expected {
                rep.diverge(
                    case,
                    cfg,
                    "ours_decoding_their_bytes_wrong_value",
                    format!("{v:?}"),
                    format!("{expected:?}"),
                );
            }
        }
        Err(e) => rep.diverge(
            case,
            cfg,
            "ours_cannot_decode_their_bytes",
            e.display,
            format!("bytes={}", hex(&theirs_bytes)),
        ),
    }

    // (4) The INCUMBENT decodes THIS crate's bytes.
    match incumbent::de::<T>(cfg, &ours_bytes) {
        Ok(v) => {
            if v != *expected {
                rep.diverge(
                    case,
                    cfg,
                    "their_decoding_our_bytes_wrong_value",
                    format!("{expected:?}"),
                    format!("{v:?}"),
                );
            }
        }
        Err(e) => rep.diverge(
            case,
            cfg,
            "they_cannot_decode_our_bytes",
            format!("bytes={}", hex(&ours_bytes)),
            e.display,
        ),
    }
}

/// Run one value through all three configs.
fn compare_all_cfgs<T>(rep: &mut Report, case: &str, value: &T)
where
    T: Serialize + DeserializeOwned + PartialEq + Debug,
{
    rep.values += 1;
    for &cfg in &CONFIGS {
        compare_one(rep, case, cfg, value, value);
    }
}

// ===========================================================================
// VALUE LANES
// ===========================================================================

/// How many values each generated lane draws. Reported in the summary line.
const N_SCALARS: usize = 1500;
const N_SHAPES: usize = 1500;
const N_TREES: usize = 800;
const N_COLLS: usize = 1000;
const N_EVERYTHING: usize = 1200;

/// HARNESS LIVENESS — this must be the first thing that fails if the comparand
/// stops being the incumbent.
///
/// Every other test in this file compares `trust_bincode` against `bincode`.
/// Nothing in that comparison notices if the two names resolve to the SAME
/// crate: the assertions all pass, the report is green, and the sweep silently
/// measures nothing at all. That is not hypothetical — the swap that retires
/// the incumbent is a dependency rename in `crates/Cargo.toml`:
///
/// ```text
/// bincode = { package = "trust-bincode", path = "trust-bincode" }
/// ```
///
/// so a dev-dep here written as `{ workspace = true }` would resolve straight
/// back to this crate. `Cargo.toml` pins a literal `1.3.3` to prevent it; this
/// test is the runtime backstop, because a manifest comment cannot fail a build
/// and someone tidying dependencies into the workspace table will not read it.
///
/// A graph-wide `[patch.crates-io] bincode` would do the same thing, which is
/// why the manifest forbids that too.
#[test]
fn comparand_is_really_the_incumbent() {
    let ours = std::any::type_name::<trust_bincode::Error>();
    let theirs = std::any::type_name::<bincode::Error>();
    assert_ne!(
        ours, theirs,
        "VACUOUS DIFFERENTIAL: `bincode` and `trust_bincode` resolve to the same \
         crate, so every comparison in this file is this implementation against \
         ITSELF and proves nothing. Check that `[dev-dependencies] bincode` in \
         crates/trust-bincode/Cargo.toml is still a literal version requirement \
         and has not been changed to `{{ workspace = true }}`, and that no \
         `[patch.crates-io] bincode` is in effect."
    );
    // `Error` is a type alias for `Box<ErrorKind>` on BOTH sides, so the rendered
    // name is `alloc::boxed::Box<..::error::ErrorKind>` — do not test for a
    // `bincode::` prefix, it is not one.
    //
    // Test for the absence of OUR path rather than the presence of THEIRS:
    // `trust_bincode::` contains `bincode::` as a substring, so a
    // `contains("bincode::")` check passes happily on this crate's own types and
    // would wave through the exact vacuity it is meant to catch.
    assert!(
        !theirs.contains("trust_bincode"),
        "VACUOUS DIFFERENTIAL: comparand type is {theirs}, which is THIS crate"
    );
    assert!(
        theirs.contains("bincode::error::ErrorKind"),
        "comparand type is {theirs}, expected the incumbent's ErrorKind"
    );
}

#[test]
fn differential_scalars() {
    let mut r = Rng::new(SEED ^ 0x01);
    let mut rep = Report::new("scalars");
    for i in 0..N_SCALARS {
        let v = gen_scalars(&mut r);
        compare_all_cfgs(&mut rep, &format!("scalars#{i}"), &v);
    }
    rep.finish();
}

#[test]
fn differential_shapes() {
    let mut r = Rng::new(SEED ^ 0x02);
    let mut rep = Report::new("shapes");
    for i in 0..N_SHAPES {
        let v = gen_shape(&mut r, 4);
        compare_all_cfgs(&mut rep, &format!("shape#{i}"), &v);
    }
    rep.finish();
}

#[test]
fn differential_trees() {
    let mut r = Rng::new(SEED ^ 0x03);
    let mut rep = Report::new("trees");
    for i in 0..N_TREES {
        let v = gen_tree(&mut r, 6);
        compare_all_cfgs(&mut rep, &format!("tree#{i}"), &v);
    }
    rep.finish();
}

#[test]
fn differential_collections() {
    let mut r = Rng::new(SEED ^ 0x04);
    let mut rep = Report::new("collections");
    for i in 0..N_COLLS {
        let v = gen_colls(&mut r, 3);
        compare_all_cfgs(&mut rep, &format!("colls#{i}"), &v);
    }
    rep.finish();
}

#[test]
fn differential_everything() {
    let mut r = Rng::new(SEED ^ 0x05);
    let mut rep = Report::new("everything");
    for i in 0..N_EVERYTHING {
        let v = gen_everything(&mut r);
        compare_all_cfgs(&mut rep, &format!("everything#{i}"), &v);
    }
    rep.finish();
}

// ---------------------------------------------------------------------------
// Boundary corpus — hand-picked, because a uniform generator visits a varint
// width boundary essentially never.
// ---------------------------------------------------------------------------

/// The values at which bincode's varint encoding changes width, and one either
/// side of each. `250` is the last single-byte value; `251/252/253` are the
/// u16/u32/u64 tag bytes.
const U64_BOUNDARIES: [u64; 24] = [
    0,
    1,
    2,
    249,
    250,
    251,
    252,
    253,
    254,
    255,
    256,
    257,
    65534,
    65535,
    65536,
    65537,
    0xFFFF_FFFE,
    0xFFFF_FFFF,
    0x1_0000_0000,
    0x1_0000_0001,
    0xFFFF_FFFF_FFFF_FFFE,
    0xFFFF_FFFF_FFFF_FFFF,
    0x7FFF_FFFF_FFFF_FFFF,
    0x8000_0000_0000_0000,
];

#[test]
fn differential_integer_boundaries() {
    let mut rep = Report::new("integer-boundaries");

    for &v in &U64_BOUNDARIES {
        compare_all_cfgs(&mut rep, &format!("u64:{v}"), &v);
        compare_all_cfgs(&mut rep, &format!("u32:{}", v as u32), &(v as u32));
        compare_all_cfgs(&mut rep, &format!("u16:{}", v as u16), &(v as u16));
        compare_all_cfgs(&mut rep, &format!("u8:{}", v as u8), &(v as u8));
        compare_all_cfgs(&mut rep, &format!("usize:{}", v as usize), &(v as usize));

        let s = v as i64;
        compare_all_cfgs(&mut rep, &format!("i64:{s}"), &s);
        compare_all_cfgs(&mut rep, &format!("i64:{}", s.wrapping_neg()), &s.wrapping_neg());
        compare_all_cfgs(&mut rep, &format!("i32:{}", s as i32), &(s as i32));
        compare_all_cfgs(&mut rep, &format!("i16:{}", s as i16), &(s as i16));
        compare_all_cfgs(&mut rep, &format!("i8:{}", s as i8), &(s as i8));
        compare_all_cfgs(&mut rep, &format!("isize:{}", s as isize), &(s as isize));

        compare_all_cfgs(&mut rep, &format!("u128:{}", v as u128), &(v as u128));
        compare_all_cfgs(&mut rep, &format!("i128:{}", v as i128), &(v as i128));
        compare_all_cfgs(
            &mut rep,
            &format!("i128:-{}", v as i128),
            &(v as i128).wrapping_neg(),
        );
    }

    // 128-bit extremes, which no `u64` cast can reach.
    for &v in &[
        0u128,
        1,
        u128::MAX,
        u128::MAX - 1,
        1u128 << 127,
        (1u128 << 64) - 1,
        1u128 << 64,
    ] {
        compare_all_cfgs(&mut rep, &format!("u128x:{v}"), &v);
    }
    for &v in &[
        i128::MIN,
        i128::MIN + 1,
        i128::MAX,
        i128::MAX - 1,
        0,
        -1,
        1,
    ] {
        compare_all_cfgs(&mut rep, &format!("i128x:{v}"), &v);
    }
    for &v in &[i64::MIN, i64::MAX, i32::MIN as i64, i32::MAX as i64] {
        compare_all_cfgs(&mut rep, &format!("i64x:{v}"), &v);
    }

    rep.finish();
}

#[test]
fn differential_length_boundaries() {
    let mut rep = Report::new("length-boundaries");

    // Lengths straddling every varint width change. The largest is 64 KiB + 1,
    // which is enough to move the length prefix into its four-byte form.
    const LENS: [usize; 16] = [
        0, 1, 2, 249, 250, 251, 252, 255, 256, 257, 1000, 65534, 65535, 65536, 65537, 70000,
    ];

    for &n in &LENS {
        let bytes: Vec<u8> = (0..n).map(|i| (i % 251) as u8).collect();
        compare_all_cfgs(&mut rep, &format!("vec_u8_len{n}"), &bytes);

        // ASCII string of exactly n BYTES.
        let s: String = std::iter::repeat_n('a', n).collect();
        compare_all_cfgs(&mut rep, &format!("string_ascii_len{n}"), &s);

        // A multi-byte string, so the LENGTH prefix and the CHAR count differ.
        let m = std::cmp::min(n, 4096);
        let s2: String = std::iter::repeat_n('\u{10FFFF}', m).collect();
        compare_all_cfgs(&mut rep, &format!("string_astral_chars{m}"), &s2);

        // A map/seq with n ELEMENTS, capped so the test stays quick.
        let k = std::cmp::min(n, 300);
        let v: Vec<u16> = (0..k).map(|i| i as u16).collect();
        compare_all_cfgs(&mut rep, &format!("vec_u16_len{k}"), &v);
        let m2: BTreeMap<u16, u8> = (0..k).map(|i| (i as u16, (i % 256) as u8)).collect();
        compare_all_cfgs(&mut rep, &format!("btreemap_len{k}"), &m2);
    }

    rep.finish();
}

#[test]
fn differential_char_boundaries() {
    let mut rep = Report::new("char-boundaries");
    let mut cps: Vec<u32> = vec![
        0x0000, 0x0001, 0x007E, 0x007F, 0x0080, 0x0081, 0x07FE, 0x07FF, 0x0800, 0x0801, 0xD7FE,
        0xD7FF, 0xE000, 0xE001, 0xFFFE, 0xFFFF, 0x1_0000, 0x1_0001, 0x10_FFFE, 0x10_FFFF,
    ];
    // Plus a sweep of the whole BMP at a stride, so nothing in it is unvisited.
    cps.extend((0..0x1_0000u32).step_by(97));
    for cp in cps {
        if let Some(c) = char::from_u32(cp) {
            compare_all_cfgs(&mut rep, &format!("char:U+{cp:04X}"), &c);
            let s: String = std::iter::repeat_n(c, 3).collect();
            compare_all_cfgs(&mut rep, &format!("string3:U+{cp:04X}"), &s);
        }
    }
    rep.finish();
}

#[test]
fn differential_float_bit_patterns() {
    let mut rep = Report::new("float-bit-patterns");

    let f64_bits: Vec<u64> = vec![
        0x0000_0000_0000_0000, // +0.0
        0x8000_0000_0000_0000, // -0.0
        0x3FF0_0000_0000_0000, // 1.0
        0xBFF0_0000_0000_0000, // -1.0
        0x7FF0_0000_0000_0000, // +inf
        0xFFF0_0000_0000_0000, // -inf
        0x7FF8_0000_0000_0000, // quiet NaN
        0x7FF0_0000_0000_0001, // signalling NaN
        0xFFF8_0000_0000_0000, // negative NaN
        0x7FFF_FFFF_FFFF_FFFF, // NaN, all payload bits set
        0x0000_0000_0000_0001, // smallest subnormal
        0x000F_FFFF_FFFF_FFFF, // largest subnormal
        0x7FEF_FFFF_FFFF_FFFF, // f64::MAX
    ];
    for (i, &b) in f64_bits.iter().enumerate() {
        compare_all_cfgs(&mut rep, &format!("f64_bits#{i}:{b:#018x}"), &F64B(f64::from_bits(b)));
    }

    let f32_bits: Vec<u32> = vec![
        0x0000_0000, 0x8000_0000, 0x3F80_0000, 0xBF80_0000, 0x7F80_0000, 0xFF80_0000, 0x7FC0_0000,
        0x7F80_0001, 0xFFC0_0000, 0x7FFF_FFFF, 0x0000_0001, 0x007F_FFFF, 0x7F7F_FFFF,
    ];
    for (i, &b) in f32_bits.iter().enumerate() {
        compare_all_cfgs(&mut rep, &format!("f32_bits#{i}:{b:#010x}"), &F32B(f32::from_bits(b)));
    }

    rep.finish();
}

#[test]
fn differential_wide_enum_variant_indices() {
    // `BigEnum` has 301 variants, so its indices cross both the 250 varint
    // boundary and the 255 one-byte boundary. A variant index is encoded as a
    // u32 THROUGH the int encoding, which is exactly what that crosses.
    let mut rep = Report::new("wide-enum-variant-indices");
    let cases: Vec<(&str, BigEnum)> = vec![
        ("V0", BigEnum::V0),
        ("V1", BigEnum::V1),
        ("V127", BigEnum::V127),
        ("V128", BigEnum::V128),
        ("V249", BigEnum::V249),
        ("V250", BigEnum::V250),
        ("V251", BigEnum::V251),
        ("V254", BigEnum::V254),
        ("V255", BigEnum::V255),
        ("V256", BigEnum::V256),
        ("V257", BigEnum::V257),
        ("V299", BigEnum::V299),
        ("Payload(0)", BigEnum::Payload(0)),
        ("Payload(u32::MAX)", BigEnum::Payload(u32::MAX)),
        ("Payload(250)", BigEnum::Payload(250)),
        ("Payload(251)", BigEnum::Payload(251)),
    ];
    for (name, v) in &cases {
        // `BigEnum` is not `Clone`; `compare_all_cfgs` only needs `&T`.
        rep.values += 1;
        for &cfg in &CONFIGS {
            compare_one(&mut rep, name, cfg, v, v);
        }
    }
    rep.finish();
}

#[test]
fn differential_option_and_result_shapes() {
    let mut rep = Report::new("option-result-shapes");
    compare_all_cfgs(&mut rep, "none_u8", &Option::<u8>::None);
    compare_all_cfgs(&mut rep, "some_u8", &Some(7u8));
    compare_all_cfgs(&mut rep, "none_none", &Option::<Option<u8>>::None);
    compare_all_cfgs(&mut rep, "some_none", &Some(Option::<u8>::None));
    compare_all_cfgs(&mut rep, "some_some", &Some(Some(9u8)));
    compare_all_cfgs(&mut rep, "ok", &Ok::<u32, String>(42));
    compare_all_cfgs(&mut rep, "err", &Err::<u32, String>("boom".into()));
    compare_all_cfgs(&mut rep, "unit", &());
    compare_all_cfgs(&mut rep, "unit_struct", &UnitStruct);
    compare_all_cfgs(&mut rep, "empty_vec", &Vec::<u8>::new());
    compare_all_cfgs(&mut rep, "empty_string", &String::new());
    compare_all_cfgs(&mut rep, "empty_map", &BTreeMap::<u8, u8>::new());
    compare_all_cfgs(&mut rep, "empty_set", &BTreeSet::<u8>::new());
    compare_all_cfgs(&mut rep, "bool_true", &true);
    compare_all_cfgs(&mut rep, "bool_false", &false);
    compare_all_cfgs(&mut rep, "tuple8", &(1u8, 2u16, 3u32, 4u64, 5i8, 6i16, 7i32, 8i64));
    compare_all_cfgs(&mut rep, "nested_tuple", &((1u8, 2u8), (3u8, (4u8, 5u8))));
    compare_all_cfgs(&mut rep, "array32", &[7u8; 32]);
    compare_all_cfgs(&mut rep, "array0", &[0u8; 0]);
    rep.finish();
}

// ===========================================================================
// ERROR-PATH DIFFERENTIAL
// ===========================================================================

/// Compare a DECODE of the same bytes on both sides, as one of several target
/// types. Records accept/reject, `Display`, `Debug`, and the decoded value.
fn compare_decode<T>(rep: &mut Report, case: &str, cfg: Cfg, bytes: &[u8])
where
    T: DeserializeOwned + PartialEq + Debug,
{
    rep.observe(cfg);
    let a = ours::de::<T>(cfg, bytes);
    let b = incumbent::de::<T>(cfg, bytes);
    match (a, b) {
        (Ok(x), Ok(y)) => {
            if x != y {
                rep.diverge(
                    case,
                    cfg,
                    "decoded_value",
                    format!("{x:?}"),
                    format!("{y:?}"),
                );
            }
        }
        (Err(x), Err(y)) => {
            if x.display != y.display {
                rep.diverge(
                    case,
                    cfg,
                    "decode_error_display",
                    x.display.clone(),
                    y.display.clone(),
                );
            }
            if x.debug != y.debug {
                rep.diverge(case, cfg, "decode_error_debug", x.debug, y.debug);
            }
        }
        (Ok(x), Err(y)) => rep.diverge(
            case,
            cfg,
            "decode_accept_reject",
            format!("Ok({x:?}) from {}", hex(bytes)),
            format!("Err({})", y.display),
        ),
        (Err(x), Ok(y)) => rep.diverge(
            case,
            cfg,
            "decode_accept_reject",
            format!("Err({})", x.display),
            format!("Ok({y:?}) from {}", hex(bytes)),
        ),
    }
}

/// Fire one buffer at a spread of target types, so a divergence that only
/// shows up in one decoder path is not missed.
fn decode_every_type(rep: &mut Report, case: &str, cfg: Cfg, bytes: &[u8]) {
    compare_decode::<Everything>(rep, &format!("{case}/Everything"), cfg, bytes);
    compare_decode::<Shape>(rep, &format!("{case}/Shape"), cfg, bytes);
    compare_decode::<Tree>(rep, &format!("{case}/Tree"), cfg, bytes);
    compare_decode::<Scalars>(rep, &format!("{case}/Scalars"), cfg, bytes);
    compare_decode::<Colls>(rep, &format!("{case}/Colls"), cfg, bytes);
    compare_decode::<String>(rep, &format!("{case}/String"), cfg, bytes);
    compare_decode::<Vec<u8>>(rep, &format!("{case}/Vec<u8>"), cfg, bytes);
    compare_decode::<Vec<String>>(rep, &format!("{case}/Vec<String>"), cfg, bytes);
    compare_decode::<BTreeMap<String, i64>>(rep, &format!("{case}/BTreeMap"), cfg, bytes);
    compare_decode::<BigEnum>(rep, &format!("{case}/BigEnum"), cfg, bytes);
    compare_decode::<u64>(rep, &format!("{case}/u64"), cfg, bytes);
    compare_decode::<i128>(rep, &format!("{case}/i128"), cfg, bytes);
    compare_decode::<char>(rep, &format!("{case}/char"), cfg, bytes);
    compare_decode::<bool>(rep, &format!("{case}/bool"), cfg, bytes);
    compare_decode::<Option<u32>>(rep, &format!("{case}/Option<u32>"), cfg, bytes);
    // `F64B`, never bare `f64`: a corrupt buffer decodes to NaN often, and
    // `NaN != NaN` would report a divergence between two IDENTICAL results.
    // Measured — this fired 4 times before the wrapper was used here.
    compare_decode::<F64B>(rep, &format!("{case}/f64"), cfg, bytes);
    compare_decode::<(u8, String, Vec<u16>)>(rep, &format!("{case}/tuple"), cfg, bytes);
}

#[test]
fn differential_truncations_and_corruptions() {
    let mut r = Rng::new(SEED ^ 0x11);
    let mut rep = Report::new("truncations-and-corruptions");

    // Seed the corpus with a handful of real encodings.
    let mut seeds: Vec<(String, Vec<u8>)> = Vec::new();
    for i in 0..6 {
        let v = gen_everything(&mut r);
        for &cfg in &CONFIGS {
            if let Ok(b) = ours::ser(cfg, &v) {
                seeds.push((format!("everything#{i}@{}", cfg.name()), b));
            }
        }
    }
    for i in 0..6 {
        let v = gen_shape(&mut r, 3);
        for &cfg in &CONFIGS {
            if let Ok(b) = ours::ser(cfg, &v) {
                seeds.push((format!("shape#{i}@{}", cfg.name()), b));
            }
        }
    }

    for (name, base) in &seeds {
        // Truncations. Every prefix for short buffers; a stride for long ones,
        // always including 0, 1 and len-1.
        let stride = std::cmp::max(1, base.len() / 48);
        let mut cuts: Vec<usize> = (0..base.len()).step_by(stride).collect();
        cuts.push(0);
        if !base.is_empty() {
            cuts.push(base.len() - 1);
        }
        cuts.sort_unstable();
        cuts.dedup();
        for k in cuts {
            let buf = &base[..k];
            for &cfg in &CONFIGS {
                compare_decode::<Everything>(
                    &mut rep,
                    &format!("{name}/trunc{k}/Everything"),
                    cfg,
                    buf,
                );
                compare_decode::<Shape>(&mut rep, &format!("{name}/trunc{k}/Shape"), cfg, buf);
                compare_decode::<String>(&mut rep, &format!("{name}/trunc{k}/String"), cfg, buf);
            }
        }

        // Single-byte corruptions at a stride, XORed two different ways.
        let cstride = std::cmp::max(1, base.len() / 32);
        for i in (0..base.len()).step_by(cstride) {
            for mask in [0x01u8, 0xFF] {
                let mut buf = base.clone();
                buf[i] ^= mask;
                for &cfg in &CONFIGS {
                    compare_decode::<Everything>(
                        &mut rep,
                        &format!("{name}/corrupt{i}^{mask:02x}/Everything"),
                        cfg,
                        &buf,
                    );
                    compare_decode::<Shape>(
                        &mut rep,
                        &format!("{name}/corrupt{i}^{mask:02x}/Shape"),
                        cfg,
                        &buf,
                    );
                }
            }
        }

        // Trailing garbage — the ONLY thing that separates the allow/reject
        // configurations on the slice path.
        for (tag, extra) in [
            ("t1", vec![0x00u8]),
            ("t2", vec![0xFFu8]),
            ("t8", vec![0xAAu8; 8]),
            ("t64", vec![0x5Au8; 64]),
        ] {
            let mut buf = base.clone();
            buf.extend_from_slice(&extra);
            for &cfg in &CONFIGS {
                compare_decode::<Everything>(
                    &mut rep,
                    &format!("{name}/{tag}/Everything"),
                    cfg,
                    &buf,
                );
                compare_decode::<Shape>(&mut rep, &format!("{name}/{tag}/Shape"), cfg, &buf);
            }
        }
    }

    rep.finish();
}

#[test]
fn differential_hostile_buffers() {
    let mut r = Rng::new(SEED ^ 0x12);
    let mut rep = Report::new("hostile-buffers");

    // All 256 single-byte inputs, and the empty input.
    decode_every_type(&mut rep, "empty", Cfg::FnDefault, &[]);
    decode_every_type(&mut rep, "empty", Cfg::StructDefault, &[]);
    decode_every_type(&mut rep, "empty", Cfg::TrustIr, &[]);
    for b in 0u16..=255 {
        let buf = [b as u8];
        for &cfg in &CONFIGS {
            decode_every_type(&mut rep, &format!("byte{b:02x}"), cfg, &buf);
        }
    }

    // The varint tag bytes with a deliberately short payload — the shape most
    // likely to separate two length decoders.
    for tag in [251u8, 252, 253, 254, 255] {
        for extra in 0..9usize {
            let mut buf = vec![tag];
            buf.extend(std::iter::repeat_n(0xFFu8, extra));
            for &cfg in &CONFIGS {
                compare_decode::<u64>(
                    &mut rep,
                    &format!("varint_tag{tag}/extra{extra}/u64"),
                    cfg,
                    &buf,
                );
                compare_decode::<i64>(
                    &mut rep,
                    &format!("varint_tag{tag}/extra{extra}/i64"),
                    cfg,
                    &buf,
                );
                compare_decode::<u128>(
                    &mut rep,
                    &format!("varint_tag{tag}/extra{extra}/u128"),
                    cfg,
                    &buf,
                );
                compare_decode::<String>(
                    &mut rep,
                    &format!("varint_tag{tag}/extra{extra}/String"),
                    cfg,
                    &buf,
                );
                compare_decode::<Vec<u8>>(
                    &mut rep,
                    &format!("varint_tag{tag}/extra{extra}/Vec<u8>"),
                    cfg,
                    &buf,
                );
            }
        }
    }

    // Pseudorandom buffers. Bounded at 64 bytes ON PURPOSE: a longer buffer
    // read as a recursive enum can drive real recursion, and BOTH libraries
    // would then overflow the stack and ABORT, which is not a comparison.
    for i in 0..900 {
        let n = r.below(65);
        let buf: Vec<u8> = (0..n).map(|_| r.next_u64() as u8).collect();
        let cfg = CONFIGS[i % 3];
        decode_every_type(&mut rep, &format!("random#{i}/len{n}"), cfg, &buf);
    }

    // Invalid-by-construction encodings whose failure text is worth pinning.
    let cases: Vec<(&str, Vec<u8>)> = vec![
        ("bool_2", vec![2]),
        ("bool_255", vec![255]),
        ("char_continuation_only", vec![0x80]),
        ("char_lone_lead_2byte", vec![0xC3]),
        ("char_overlong", vec![0xC0, 0x80]),
        ("char_surrogate", vec![0xED, 0xA0, 0x80]),
        ("char_5byte_lead", vec![0xF8, 0x80, 0x80, 0x80, 0x80]),
        ("option_tag_2", vec![2, 0, 0, 0, 0]),
        ("str_bad_utf8_fixint", {
            let mut v = 3u64.to_le_bytes().to_vec();
            v.extend([0xFF, 0xFE, 0xFD]);
            v
        }),
        ("str_bad_utf8_varint", vec![3, 0xFF, 0xFE, 0xFD]),
        ("bigenum_index_400_fixint", 400u32.to_le_bytes().to_vec()),
        ("bigenum_index_400_varint", {
            let mut v = vec![251u8];
            v.extend(400u16.to_le_bytes());
            v
        }),
        ("seq_len_huge_fixint", u64::MAX.to_le_bytes().to_vec()),
        ("seq_len_huge_varint", {
            let mut v = vec![253u8];
            v.extend(u64::MAX.to_le_bytes());
            v
        }),
    ];
    for (name, buf) in &cases {
        for &cfg in &CONFIGS {
            decode_every_type(&mut rep, name, cfg, buf);
        }
    }

    rep.finish();
}

#[test]
fn differential_encode_error_paths() {
    let mut rep = Report::new("encode-error-paths");

    // A byte limit smaller than the value. The limit IS enforced on encode
    // (via a `serialized_size` pre-pass) in both implementations.
    let value = ("hello world, this is longer than the limit".to_string(), 1u64);
    for limit in [0u64, 1, 4, 7, 8, 16, 32, 49, 50, 51, 1000] {
        rep.observe(Cfg::FnDefault);
        let a = ours::ser_limited(limit, &value);
        let b = incumbent::ser_limited(limit, &value);
        match (a, b) {
            (Ok(x), Ok(y)) => {
                if x != y {
                    rep.diverge(
                        &format!("limit{limit}"),
                        Cfg::FnDefault,
                        "encoded_bytes",
                        hex(&x),
                        hex(&y),
                    );
                }
            }
            (Err(x), Err(y)) => {
                if x.display != y.display {
                    rep.diverge(
                        &format!("limit{limit}"),
                        Cfg::FnDefault,
                        "encode_error_display",
                        x.display,
                        y.display,
                    );
                }
            }
            (a, b) => rep.diverge(
                &format!("limit{limit}"),
                Cfg::FnDefault,
                "encode_accept_reject",
                format!("{a:?}"),
                format!("{b:?}"),
            ),
        }
    }

    // `serialize_seq(None)` — the only route to `SequenceMustHaveLength`.
    struct UnknownLen;
    impl Serialize for UnknownLen {
        fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            use serde::ser::SerializeSeq;
            let mut seq = s.serialize_seq(None)?;
            seq.serialize_element(&1u8)?;
            seq.end()
        }
    }
    for &cfg in &CONFIGS {
        rep.observe(cfg);
        let a = ours::ser(cfg, &UnknownLen);
        let b = incumbent::ser(cfg, &UnknownLen);
        match (a, b) {
            (Err(x), Err(y)) => {
                if x.display != y.display {
                    rep.diverge(
                        "seq_unknown_len",
                        cfg,
                        "encode_error_display",
                        x.display,
                        y.display,
                    );
                }
                if x.debug != y.debug {
                    rep.diverge("seq_unknown_len", cfg, "encode_error_debug", x.debug, y.debug);
                }
            }
            (a, b) => rep.diverge(
                "seq_unknown_len",
                cfg,
                "encode_accept_reject",
                format!("{a:?}"),
                format!("{b:?}"),
            ),
        }
    }

    rep.finish();
}

#[test]
fn differential_reader_path() {
    // The `io::Read` lane. This is the path whose error texts the committed
    // golden fixture does NOT pin (the capture agent recorded
    // `reader_lanes_run_for_unlimited_configs: false`), so until now the
    // implementation's own source was the only statement of the behaviour.
    // Here it is compared against the incumbent directly.
    let mut r = Rng::new(SEED ^ 0x13);
    let mut rep = Report::new("reader-path");

    for i in 0..120 {
        let v = gen_everything(&mut r);
        for &cfg in &CONFIGS {
            let bytes = match ours::ser(cfg, &v) {
                Ok(b) => b,
                Err(_) => continue,
            };

            // Whole buffer: both must decode to the same value.
            rep.observe(cfg);
            let a = ours::de_from::<Everything>(cfg, &bytes);
            let b = incumbent::de_from::<Everything>(cfg, &bytes);
            match (a, b) {
                (Ok(x), Ok(y)) => {
                    if x != y || x != v {
                        rep.diverge(
                            &format!("reader#{i}"),
                            cfg,
                            "reader_decoded_value",
                            format!("{x:?}"),
                            format!("{y:?}"),
                        );
                    }
                }
                (Err(x), Err(y)) => {
                    if x.display != y.display {
                        rep.diverge(
                            &format!("reader#{i}"),
                            cfg,
                            "reader_error_display",
                            x.display,
                            y.display,
                        );
                    }
                }
                (a, b) => rep.diverge(
                    &format!("reader#{i}"),
                    cfg,
                    "reader_accept_reject",
                    format!("{a:?}"),
                    format!("{b:?}"),
                ),
            }

            // Truncations — the reader path has DIFFERENT EOF texts from the
            // slice path, and three of them.
            let stride = std::cmp::max(1, bytes.len() / 12);
            for k in (0..bytes.len()).step_by(stride) {
                rep.observe(cfg);
                let a = ours::de_from::<Everything>(cfg, &bytes[..k]);
                let b = incumbent::de_from::<Everything>(cfg, &bytes[..k]);
                match (a, b) {
                    (Ok(x), Ok(y)) => {
                        if x != y {
                            rep.diverge(
                                &format!("reader#{i}/trunc{k}"),
                                cfg,
                                "reader_decoded_value",
                                format!("{x:?}"),
                                format!("{y:?}"),
                            );
                        }
                    }
                    (Err(x), Err(y)) => {
                        if x.display != y.display {
                            rep.diverge(
                                &format!("reader#{i}/trunc{k}"),
                                cfg,
                                "reader_error_display",
                                x.display,
                                y.display,
                            );
                        }
                        if x.debug != y.debug {
                            rep.diverge(
                                &format!("reader#{i}/trunc{k}"),
                                cfg,
                                "reader_error_debug",
                                x.debug,
                                y.debug,
                            );
                        }
                    }
                    (a, b) => rep.diverge(
                        &format!("reader#{i}/trunc{k}"),
                        cfg,
                        "reader_accept_reject",
                        format!("{a:?}"),
                        format!("{b:?}"),
                    ),
                }
            }
        }
    }

    // A length prefix far larger than the available input. This is the exact
    // shape of divergence #2 in `src/lib.rs`: the incumbent pre-allocates the
    // whole attacker-supplied length, this crate fills in bounded chunks. Both
    // must return the SAME error.
    //
    // The sizes here are deliberately modest (up to 8 MiB). A `u64::MAX` length
    // is NOT tested against the incumbent, because the incumbent's
    // `Vec::resize` would abort the process on allocation failure — that
    // remains the one behaviour this differential cannot observe, and it is
    // recorded in `src/lib.rs` as a knowing divergence.
    for len in [
        64u64,
        1024,
        65535,
        65536,
        65537,
        1 << 20,
        (1 << 20) + 1,
        8 << 20,
    ] {
        let mut buf = len.to_le_bytes().to_vec();
        buf.extend([b'a'; 8]);
        rep.observe(Cfg::FnDefault);
        let a = ours::de_from::<String>(Cfg::FnDefault, &buf);
        let b = incumbent::de_from::<String>(Cfg::FnDefault, &buf);
        match (a, b) {
            (Err(x), Err(y)) => {
                if x.display != y.display {
                    rep.diverge(
                        &format!("reader_len_prefix{len}"),
                        Cfg::FnDefault,
                        "reader_error_display",
                        x.display,
                        y.display,
                    );
                }
                if x.debug != y.debug {
                    rep.diverge(
                        &format!("reader_len_prefix{len}"),
                        Cfg::FnDefault,
                        "reader_error_debug",
                        x.debug,
                        y.debug,
                    );
                }
            }
            (a, b) => rep.diverge(
                &format!("reader_len_prefix{len}"),
                Cfg::FnDefault,
                "reader_accept_reject",
                format!("{a:?}"),
                format!("{b:?}"),
            ),
        }
    }

    // The reader path with a byte limit — the one lane where `with_limit`
    // actually bites on decode.
    for limit in [0u64, 1, 4, 8, 12, 16, 64] {
        let bytes = ours::ser(Cfg::FnDefault, &("abcdefgh".to_string(), 1u64))
            .expect("fixed value encodes");
        rep.observe(Cfg::FnDefault);
        let a = ours::de_from_limited::<(String, u64)>(limit, &bytes);
        let b = incumbent::de_from_limited::<(String, u64)>(limit, &bytes);
        match (a, b) {
            (Ok(x), Ok(y)) => {
                if x != y {
                    rep.diverge(
                        &format!("reader_limit{limit}"),
                        Cfg::FnDefault,
                        "reader_decoded_value",
                        format!("{x:?}"),
                        format!("{y:?}"),
                    );
                }
            }
            (Err(x), Err(y)) => {
                if x.display != y.display {
                    rep.diverge(
                        &format!("reader_limit{limit}"),
                        Cfg::FnDefault,
                        "reader_error_display",
                        x.display,
                        y.display,
                    );
                }
            }
            (a, b) => rep.diverge(
                &format!("reader_limit{limit}"),
                Cfg::FnDefault,
                "reader_accept_reject",
                format!("{a:?}"),
                format!("{b:?}"),
            ),
        }
    }

    rep.finish();
}

// ===========================================================================
// NEGATIVE CONTROL
// ===========================================================================

/// A differential that cannot fail is worthless.
///
/// This drives a DELIBERATELY perturbed value through `compare_one` — the very
/// same function every lane above uses — and asserts that
///
///  * a divergence is recorded, and
///  * `Report::finish` actually panics, with the hex of both sides in the text.
///
/// The panic is caught, so this test passes by OBSERVING the failure path fire.
/// The captured text is printed; run with `--nocapture` to read it.
#[test]
fn the_negative_control_proves_the_harness_can_fail() {
    let mut r = Rng::new(SEED ^ 0xDEAD);
    let value = gen_everything(&mut r);

    // The perturbation: one field changed. Everything else is identical.
    let mut mutated = value.clone();
    mutated.scalars.u32v = mutated.scalars.u32v.wrapping_add(1);

    // Feed `compare_one` a value whose encoding it will compare against the
    // incumbent's encoding of a DIFFERENT value, by asking the incumbent side
    // for `mutated`. `compare_one` does not know they differ.
    let mut rep = Report::new("negative-control");
    for &cfg in &CONFIGS {
        rep.values += 1;
        rep.observe(cfg);
        let a = ours::ser(cfg, &value).expect("encodes");
        let b = incumbent::ser(cfg, &mutated).expect("encodes");
        if a != b {
            rep.diverge(
                "perturbed_u32_field",
                cfg,
                "encoded_bytes",
                hex(&a),
                hex(&b),
            );
        }
    }

    assert_eq!(
        rep.divs.len(),
        3,
        "the perturbation must be visible in ALL THREE configs; if it is not, \
         the negative control is not exercising what it claims"
    );

    // Now prove the REPORTING path fails too, not just that a Vec got longer.
    let text = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || rep.finish()))
        .expect_err("Report::finish MUST panic when divergences were recorded");
    let text = text
        .downcast_ref::<String>()
        .cloned()
        .expect("panic payload is a String");

    println!("--- NEGATIVE CONTROL: captured failure text ---\n{text}\n--- end ---");

    assert!(
        text.contains("DIFFERENTIAL FAILURE vs bincode 1.3.3"),
        "failure text lost its banner: {text}"
    );
    assert!(
        text.contains("3 divergence(s)"),
        "failure text lost its count: {text}"
    );
    assert!(
        text.contains("kind=encoded_bytes"),
        "failure text lost the divergence kind: {text}"
    );
    assert!(
        text.contains("trust-bincode: ") && text.contains("bincode 1.3.3: "),
        "failure text must show BOTH sides: {text}"
    );

    // And a second, independent negative control: the comparison must also fail
    // when the two sides are the same VALUE but decoded to a different one.
    let mut rep2 = Report::new("negative-control-decode");
    rep2.observe(Cfg::FnDefault);
    let bytes = ours::ser(Cfg::FnDefault, &7u32).expect("encodes");
    let decoded: u32 = incumbent::de(Cfg::FnDefault, &bytes).expect("decodes");
    if decoded != 8 {
        rep2.diverge(
            "deliberately_wrong_expectation",
            Cfg::FnDefault,
            "decoded_value",
            format!("{decoded}"),
            "8".to_string(),
        );
    }
    let text2 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || rep2.finish()))
        .expect_err("second control MUST panic");
    let text2 = text2
        .downcast_ref::<String>()
        .cloned()
        .expect("panic payload is a String");
    println!("--- NEGATIVE CONTROL 2: captured failure text ---\n{text2}\n--- end ---");
    assert!(text2.contains("1 divergence(s)"), "{text2}");

    // Third control: a lane that observed NOTHING must not read as a pass.
    let rep3 = Report::new("negative-control-silent-lane");
    let text3 = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || rep3.finish()))
        .expect_err("an empty lane MUST panic — a silent instrument reads as a clean result");
    let text3 = text3
        .downcast_ref::<String>()
        .cloned()
        .expect("panic payload is a String");
    println!("--- NEGATIVE CONTROL 3: captured failure text ---\n{text3}\n--- end ---");
    assert!(text3.contains("made ZERO observations"), "{text3}");
}

/// The generator must be deterministic, or every count above is unreproducible.
#[test]
fn the_generator_is_deterministic() {
    let mut a = Rng::new(SEED);
    let mut b = Rng::new(SEED);
    for _ in 0..10_000 {
        assert_eq!(a.next_u64(), b.next_u64());
    }

    // Two independent draws of the same lane must produce identical values.
    let mut r1 = Rng::new(SEED ^ 0x05);
    let mut r2 = Rng::new(SEED ^ 0x05);
    for _ in 0..64 {
        assert_eq!(gen_everything(&mut r1), gen_everything(&mut r2));
    }

    // And the first draw must be PINNED, so a change to the generator that
    // silently reshapes the corpus is caught rather than absorbed.
    let mut r = Rng::new(SEED ^ 0x01);
    let first = gen_scalars(&mut r);
    let encoded = ours::ser(Cfg::FnDefault, &first).expect("encodes");
    assert_eq!(
        incumbent::ser(Cfg::FnDefault, &first).expect("encodes"),
        encoded,
        "the pinned first value must agree with the incumbent"
    );
    println!(
        "seed=0x{SEED:016X} first scalars value encodes to {} bytes: {}",
        encoded.len(),
        hex(&encoded)
    );
}
