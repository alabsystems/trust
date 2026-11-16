//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A store to an element of an ARRAY field through `&mut Self` leaves the other
//! fields' facts alone.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29, on the ordinary-Rust sweep (m01, m01b, m18,
//! p01): each function below was refuted with the guarded counter at `usize::MAX`.
//! The element store `(*s).items[i] = x` is an opaque store through the `&mut`
//! parameter, and only an all-`Field` path counted as confined to its own place, so
//! the store re-versioned the sibling `(*s).len` the guard had bounded. An index
//! into an array field stays in that field's inline storage; the element it hits is
//! the written name's business (`path_defs::opaque_store_confined_to_written_place`).
//! `array_field_store_spares_siblings_refused.rs` holds the stores that DO reach
//! the guarded value.

pub struct Stack {
    items: [u32; 8],
    len: usize,
}

pub fn push_first(s: &mut Stack, x: u32) -> bool {
    if s.len < 8 {
        s.items[0] = x;
        s.len += 1;
        true
    } else {
        false
    }
}

pub fn push(s: &mut Stack, x: u32) -> bool {
    if s.len < 8 {
        s.items[s.len] = x;
        s.len += 1;
        true
    } else {
        false
    }
}

pub struct Ring {
    buf: [u8; 16],
    head: usize,
    count: usize,
}

impl Ring {
    pub fn push(&mut self, b: u8) -> bool {
        if self.count >= 16 || self.head >= 16 {
            return false;
        }
        let idx = (self.head + self.count) % 16;
        self.buf[idx] = b;
        self.count += 1;
        true
    }
}

pub struct Grid {
    cells: [[u8; 4]; 4],
    filled: usize,
}

pub fn mark(g: &mut Grid, r: usize, c: usize) -> usize {
    if g.filled < 16 && r < 4 && c < 4 {
        g.cells[r][c] = 1;
        g.filled + 1
    } else {
        0
    }
}
