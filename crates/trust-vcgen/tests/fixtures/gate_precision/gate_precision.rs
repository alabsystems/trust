// Copyright 2026 Andrew Yates | License: Apache 2.0
//! Gate RCA precision (2026-10-17): the shapes of the candidate gate's lost rows, each
//! beside a negative control that must stay unproved. Captured with
//! `-Ztrust-dump=mir-only` for `crates/trust-vcgen/tests/gate_precision_realmir.rs`.
#![allow(dead_code)]

// ---- T5: a PROJECTED slice-range bound read in the index call's own block ----------
pub struct Stack {
    buf: [u8; 64],
    len: usize,
}
impl Stack {
    /// aterm-core stack_response.rs:46 — `self.buf[self.len..64]` and
    /// `self.buf[self.len..end]` after `self.len + bytes.len()` (both correct).
    pub fn push_bytes(&mut self, bytes: &[u8]) {
        let end = self.len + bytes.len();
        if end > 64 {
            let avail = 64 - self.len;
            self.buf[self.len..64].copy_from_slice(&bytes[..avail]);
            self.len = 64;
            return;
        }
        self.buf[self.len..end].copy_from_slice(bytes);
        self.len = end;
    }
    /// Negative control: no guard at all — refuted at `len > 64`.
    pub fn unguarded(&mut self) {
        self.buf[self.len..].fill(0);
    }
    /// Negative control: the bound is read, then the field is overwritten IN THE SAME
    /// BLOCK before the index call. The range holds `n`, the field at the call holds 0;
    /// naming the field at the call would prove `0 <= 64` (false proof). Panics at n = 65.
    pub fn stale_store(&mut self, n: usize) -> u8 {
        self.len = n;
        let r = self.len..64;
        self.len = 0;
        self.buf[r][0]
    }
}

pub struct Sha {
    buf: [u8; 64],
    buf_len: usize,
}
impl Sha {
    /// aterm-digest sha256.rs:150 — `self.buf[self.buf_len..]` under `buf_len > 56`.
    pub fn finalize(&mut self) -> u8 {
        if self.buf_len >= 64 {
            return 0;
        }
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if self.buf_len > 56 {
            self.buf[self.buf_len..].fill(0);
            self.buf_len = 0;
        }
        self.buf[0]
    }
}

#[inline(never)]
pub fn sink(b: &mut [u8]) -> usize {
    b.len()
}
/// astream-aead stream.rs:468 — `&mut buf[*filled..]` under `*filled < buf.len()`.
pub fn fill(buf: &mut [u8], filled: &mut usize) {
    while *filled < buf.len() {
        let n = sink(&mut buf[*filled..]);
        if n == 0 {
            return;
        }
        *filled = buf.len();
    }
}

// ---- T6: hardened BoundsCheck twins under a JOINED `enumerate` entrance -------------
pub struct Table {
    pub tag: u32,
}
fn tables<'t>(a: Option<&'t Table>, b: Option<&'t Table>) -> [Option<&'t Table>; 2] {
    [a, b]
}
/// aterm-font shape/map.rs:233 MapBuilder::new (correct).
pub fn map_builder_new(a: Option<&Table>, b: Option<&Table>) -> [Option<u32>; 2] {
    let mut chosen = [None; 2];
    let mut index = [None; 2];
    for (i, table) in tables(a, b).iter().enumerate() {
        let Some(table) = table else { continue };
        chosen[i] = Some(table.tag);
        index[i] = Some(i as u32);
    }
    let _ = index;
    chosen
}
/// Negative control: the same loop over THREE tables indexing a two-slot array —
/// panics at i = 2; its twin must stay refuted.
pub fn map_builder_short(a: Option<&Table>, b: Option<&Table>) -> [Option<u32>; 2] {
    let mut chosen = [None; 2];
    for (i, table) in [a, b, a].iter().enumerate() {
        let Some(table) = table else { continue };
        chosen[i] = Some(table.tag);
    }
    chosen
}

// ---- T4: a slice of a RECURSIVE (compacted) enum is at most isize::MAX long ---------
pub enum Delim {
    Paren,
    Brace,
}
pub enum Tt {
    Ident(String),
    Punct(char, bool),
    Group(Delim, Vec<Tt>),
}
impl Tt {
    fn is_punct(&self, c: char) -> bool {
        matches!(self, Tt::Punct(p, _) if *p == c)
    }
}
/// aterm-wasm-abi-macros parse.rs:373 (correct: `i < p.len() <= isize::MAX`).
pub fn without_lifetime(p: &[Tt]) -> usize {
    let mut n = 0;
    let mut i = 0;
    while i < p.len() {
        if p[i].is_punct('\'') {
            i += 2;
            continue;
        }
        n += 1;
        i += 1;
    }
    n
}
pub enum One {
    A,
}
/// Negative control: a ZERO-SIZED element, so `p.len()` may be `usize::MAX` and
/// `i += 2` overflows at `i = usize::MAX - 1`.
pub fn skip_zst(p: &[One]) -> usize {
    let mut i = 0;
    while i < p.len() {
        i += 2;
    }
    i
}

// ---- T7: an f32 add of a tiny constant keeps its row (and proves) -------------------
pub struct Pet {
    quiet: f32,
    hold_end_q: f32,
}
impl Pet {
    /// aterm-effects kitty_pet.rs:7601 (correct: `+ 4.0` cannot round to infinity).
    pub fn perform_trick(&mut self) {
        self.quiet = self.quiet.max(1.4);
        self.hold_end_q = self.quiet + 4.0;
    }
    /// Negative control: a constant near `f32::MAX` overflows `quiet + C` for a large
    /// `quiet`; the row must be emitted and refuted.
    pub fn huge(&mut self) {
        self.hold_end_q = self.quiet + 3.0e38;
    }
}

// ---- T8: a range end copied from a field the body writes after the loop -------------
#[derive(Clone, Copy, Default)]
pub struct Glyph {
    pub cluster: u32,
}
pub struct Buffer {
    info: Vec<Glyph>,
    len: usize,
}
impl Buffer {
    fn merge(&mut self, start: usize, end: usize) {
        let end = end.min(self.len);
        for i in start..end {
            self.info[i].cluster = 0;
        }
    }
    /// aterm-font shape/buffer.rs:550 delete_glyphs_inplace (correct `i + 1`).
    pub fn delete(&mut self) {
        let mut j = 0;
        for i in 0..self.len {
            if i + 1 < self.len {
                self.merge(i, i + 2);
                continue;
            }
            j += 1;
        }
        self.len = j;
    }
    /// Negative control: `i + 2` overflows at `len = usize::MAX`, `i = usize::MAX - 1`.
    pub fn delete_two(&mut self) {
        let mut j = 0;
        for i in 0..self.len {
            if i + 2 < self.len {
                self.merge(i, i);
            }
            j += 1;
        }
        self.len = j;
    }
}

// ---- T2: `n = a.min(s.len())` over a slice the loop reseats --------------------------
/// aterm-ctl redial.rs:1142/1144 (correct: `n <= s.len()` for the `s` of this iteration).
pub fn relay(a: usize, mut s: &[u8], out: &mut Vec<u8>) {
    while !s.is_empty() {
        let n = a.min(s.len());
        out.extend_from_slice(&s[..n]);
        s = &s[n..];
    }
}
/// Negative control (the round-A8 shape): the slice is reseated between the `min` and
/// the index, so `n` is bounded by the OLD length only. Panics at `a = 2, s = [0; 2],
/// b = [0]`.
pub fn min_then_reseat<'a>(a: usize, mut s: &'a [u8], b: &'a [u8]) -> usize {
    let n = a.min(s.len());
    s = b;
    s[..n].len()
}

// ---- T3: a guard on a read two tracked names rebind ----------------------------------
/// aterm-phase phase.rs:1342 composer_index (correct: `b[k]` under `k < b.len()`).
pub fn caret_col(rows: &[String]) -> Option<usize> {
    let mut i = rows.len();
    while i > 0 {
        i -= 1;
        let b = rows[i].as_bytes();
        let mut k = 0;
        while k < b.len() && b[k] == b' ' {
            k += 1;
        }
        if b.get(k) == Some(&0xE2) {
            return Some(i);
        }
    }
    None
}

// ---- T1: a closure's by-reference capture across a call ------------------------------
#[inline(never)]
pub fn opaque_sink(x: usize) -> usize {
    core::hint::black_box(x)
}
/// aterm-conformance scan.rs:1460 / aterm-control selection.rs:357, minimal: `w` is
/// captured by reference, `p / w` asserts it nonzero, a call runs, `p % w` reads it again
/// (correct: nothing can change `w` between the reads in a defined execution).
pub fn capture_ref_div_rem(w: usize, p: usize) -> usize {
    let f = |p: usize| {
        let q = p / w;
        opaque_sink(q);
        p % w
    };
    f(p)
}
/// aterm-control selection.rs:357 (two by-reference captures, two calls of the closure).
pub fn word_cells(first_row: i32, cols: usize, start: usize, last: usize) -> ((i32, u16), (i32, u16)) {
    let cell = |g: usize| -> (i32, u16) {
        let dr = i32::try_from(g / cols).unwrap_or(i32::MAX);
        let c = u16::try_from(g % cols).unwrap_or(u16::MAX);
        (first_row.saturating_add(dr), c)
    };
    (cell(start), cell(last))
}

// ---- D2: a reference out of `Iterator::next`'s `Option<&T>`, read again after a call --
pub struct TrailCell {
    pub row: usize,
    pub col: usize,
}
pub struct TrailInput {
    pub rows: usize,
    pub cols: usize,
    pub trail: Vec<TrailCell>,
    pub sizes: Vec<u8>,
    pub cached: Option<&'static TrailCell>,
}
#[inline(never)]
pub fn row_is_uniform(input: &TrailInput, row: usize) -> bool {
    input.sizes.get(row).is_some()
}
/// aterm-render lib.rs:17913 `draw_trail`: `t.col + 1` under `t.col >= cols => continue`,
/// a call between the guard and the add (correct: `t.col < cols <= usize::MAX`).
pub fn draw_trail(input: &TrailInput) -> usize {
    let cols = input.cols;
    let mut acc = 0;
    for t in &input.trail {
        if t.row >= input.rows || t.col >= cols {
            continue;
        }
        if row_is_uniform(input, t.row) {
            acc ^= t.col + 1;
        }
    }
    acc
}
/// The same over `enumerate` (`Option<(usize, &TrailCell)>`).
pub fn draw_trail_enumerate(input: &TrailInput) -> usize {
    let mut acc = 0;
    for (i, t) in input.trail.iter().enumerate() {
        if t.col >= input.cols {
            continue;
        }
        if row_is_uniform(input, i) {
            acc ^= t.col + 1;
        }
    }
    acc
}
/// Control: the `Option<&TrailCell>` is LOADED FROM MEMORY (`input.cached`): its payload
/// may carry raw-pointer bits a callee writes through, so the add must stay unproved.
pub fn cached_trail(input: &TrailInput) -> usize {
    if let Some(t) = input.cached {
        if t.col >= input.cols {
            return 0;
        }
        if row_is_uniform(input, t.row) {
            return t.col + 1;
        }
    }
    0
}
/// Control: no guard on `t.col`: refuted at `t.col = usize::MAX`.
pub fn unguarded_trail(input: &TrailInput) -> usize {
    let mut acc = 0;
    for t in &input.trail {
        if row_is_uniform(input, t.row) {
            acc ^= t.col + 1;
        }
    }
    acc
}
