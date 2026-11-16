#![allow(dead_code)]

use std::cell::Cell;

trait Pattern {
    type Searcher<'a>;
}
struct Plain;
struct Mutable;
struct Searcher<'a> {
    text: &'a str,
    at: usize,
}
impl Pattern for Plain {
    type Searcher<'a> = Searcher<'a>;
}
impl Pattern for Mutable {
    type Searcher<'a> = Cell<usize>;
}
struct Split<'a, P: Pattern> {
    searcher: P::Searcher<'a>,
    finished: bool,
}

impl<'a, P: Pattern> Split<'a, P> {
    fn remainder(&self) -> bool {
        self.finished
    }
}
struct Marker;
struct Adapter<I, F> {
    iter: I,
    marker: F,
}
struct Lines<'a>(Adapter<Split<'a, Plain>, Marker>);
struct Words<'a> {
    inner: Adapter<Split<'a, Plain>, Marker>,
}
impl Lines<'_> {
    pub fn remaining_lines(&self) -> bool {
        self.0.iter.remainder()
    }
}
impl Words<'_> {
    pub fn remaining_words(&self) -> bool {
        self.inner.iter.remainder()
    }
}
impl Split<'_, Plain> {
    // Existing borrow-pointer guards must still prevent address observation
    // and laundering a frame slot out through a cast/return.
    pub fn observe_address(&self) -> usize {
        self as *const Self as usize
    }
    pub fn escape_local_snapshot(&self) -> *const u8 {
        let value = self.finished;
        core::ptr::addr_of!(value) as *const u8
    }
}
struct MutableLines<'a>(Adapter<Split<'a, Mutable>, Marker>);
impl MutableLines<'_> {
    pub fn mutable_receiver(&self) -> bool {
        self.0.iter.remainder()
    }
}
struct GenericLines<'a, P: Pattern>(Adapter<Split<'a, P>, Marker>);
impl<P: Pattern> GenericLines<'_, P> {
    pub fn generic_receiver(&self) -> bool {
        self.0.iter.remainder()
    }
}

fn freeze_gat(_: &Split<'_, Plain>) {}
fn mutable_gat(_: &Split<'_, Mutable>) {}
fn unknown_gat<P: Pattern>(_: &Split<'_, P>) {}

struct DirectCell(Cell<usize>);
fn mutable_direct(_: &DirectCell) {}

// A reference's own Freeze status says nothing about its non-Freeze referent.
fn shared_cell(_: &Cell<usize>) {}
fn plain_scalar(_: &usize) {}
fn const_generic<const N: usize>(_: &[u8; N]) {}
