// Trust (OD-1-T3-CENSUS-WALK): real-MIR source for the D33 unsafe-operation
// census pins in `tests/census_walk_realmir.rs`. Every function projects THROUGH
// a recursive type, so the extractor spells the type as a bare recursive marker
// with its definition in the body's `datatype_defs` table.
#![allow(dead_code)]

/// The clean-ck0 `Term` shape: a recursive enum behind `Box`.
pub enum Term {
    Var(u32),
    App(Box<Term>, Box<Term>),
    Lam(u32, Box<Term>),
}

/// Safe: matches two levels deep through `&Term` and the boxed payload.
pub fn term_head(t: &Term) -> u32 {
    match t {
        Term::Var(x) => *x,
        Term::App(f, _) => match &**f {
            Term::Var(y) => *y,
            _ => 0,
        },
        Term::Lam(_, b) => match &**b {
            Term::Var(z) => *z,
            _ => 1,
        },
    }
}

/// A recursive enum behind plain references.
pub enum Chain<'a> {
    End(u32),
    Link(u32, &'a Chain<'a>),
}

/// Safe: reads the second link's payload.
pub fn chain_second(c: &Chain<'_>) -> u32 {
    match c {
        Chain::End(v) => *v,
        Chain::Link(_, next) => match next {
            Chain::End(v) => *v,
            Chain::Link(v, _) => *v,
        },
    }
}

/// A recursive struct behind plain references.
pub struct Node<'a> {
    pub val: u32,
    pub next: Option<&'a Node<'a>>,
}

/// Safe: reads the next node's value.
pub fn node_next_val(n: &Node<'_>) -> u32 {
    match n.next {
        Some(m) => m.val,
        None => n.val,
    }
}

/// A recursive enum whose variant carries a tuple: the pattern below binds
/// through `Downcast` then TWO `Field`s, and through a second marker level, so
/// the census must type a NON-final variant field (no last-step exemption).
pub enum Tree<'a> {
    Leaf(u32),
    Node((u32, u32), &'a Tree<'a>),
}

/// Safe: `[Deref, Downcast(1), Field(0), Field(1)]` on `t`, and the same
/// shape ending `Field(0), Field(0)` on the copied `&Tree` one level down.
pub fn tree_pairs(t: &Tree<'_>) -> u32 {
    match t {
        Tree::Node((_, b), Tree::Node((c, _), _)) => *b ^ *c,
        Tree::Node((a, _), Tree::Leaf(w)) => *a ^ *w,
        Tree::Leaf(v) => *v,
    }
}

/// CONTROL: a union reached through a recursive struct. Must stay refused.
#[derive(Clone, Copy)]
pub union Bits {
    pub a: u32,
    pub b: f32,
}

pub struct UNode<'a> {
    pub bits: Bits,
    pub next: Option<&'a UNode<'a>>,
}

pub fn unode_next_bits(n: &UNode<'_>) -> u32 {
    match n.next {
        Some(m) => unsafe { m.bits.a },
        None => 0,
    }
}

/// CONTROL: a raw pointer in a variant of a recursive enum. Must stay refused.
pub enum RawChain<'a> {
    Leaf(*const u32),
    Link(&'a RawChain<'a>),
}

pub fn raw_chain_second(r: &RawChain<'_>) -> u32 {
    match r {
        RawChain::Link(next) => match next {
            RawChain::Leaf(p) => unsafe { **p },
            RawChain::Link(_) => 0,
        },
        RawChain::Leaf(_) => 0,
    }
}
