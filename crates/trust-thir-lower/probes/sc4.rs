// LANE SC (follow-on) — FAMILY A, the SHORT-CIRCUIT-OVER-CALLS family: the largest single group
// in G25's residual (6 bodies) and the one with no committed fixture. Each shape reproduces one
// of the census's sub-shapes, with a CONVERTING CONTROL beside it whose ONLY difference is that
// its short-circuit operands are not calls.
#![allow(dead_code, clippy::all)]

pub struct V {
    k: u64,
}

impl V {
    #[inline(never)]
    pub fn p(&self, x: u64) -> bool {
        x == self.k
    }
    #[inline(never)]
    pub fn q(&self, x: u64) -> bool {
        x != self.k
    }
    #[inline(never)]
    pub fn r(&self, x: u64) -> bool {
        x > self.k
    }
    #[inline(never)]
    pub fn s(&self, x: u64) -> bool {
        x < self.k
    }
    #[inline(never)]
    pub fn cnt(&self, x: u64) -> u64 {
        x
    }

    // A1 — `call condbr call br const br ret`, 4 trust-ir blocks: two calls under one `||`.
    //      (== try_struct_eta_eq, try_structure_eta_expansion, try_string_lit_expansion, arc_eq)
    pub fn a1_two_calls(&self, a: u64, b: u64) -> bool {
        self.p(a) || self.q(b)
    }
    pub fn a1b_two_calls_and(&self, a: u64, b: u64) -> bool {
        self.p(a) && self.q(b)
    }
    // A2 — a call, then a CONST-armed comparison: built SPLITS the const arm, delta 2.
    //      (== env::sorry_summary::…::is_fully_verified)
    pub fn a2_call_then_const_cmp(&self, a: u64) -> bool {
        self.p(a) || self.cnt(a) == 0
    }
    // A3 — a FOUR-way `||` chain over calls: 6 blocks, THREE CondBrs sharing ONE short-circuit
    //      arm, so that arm has 3 predecessors. (== cert::def_eq::…::try_type_directed_eq)
    pub fn a3_four_way(&self, a: u64, b: u64) -> bool {
        self.p(a) || self.q(b) || self.r(a) || self.s(b)
    }

    // ---- THE CONVERTING CONTROLS live OUTSIDE the impl, as free functions over scalars: an
    // ---- outer body that reads `self.k` takes a `Load` through a ref param, which this shim
    // ---- refuses for an unrelated reason, and a control that is `unsupported` isolates nothing.
}

/// The same short-circuit SHAPES with NON-CALL operands. The only difference from `a1`/`a2`/`a3`
/// is that these operands are not `Inst::Call`, so a verdict split between the two groups names
/// the call and nothing else.
pub fn a0_two_no_calls(a: u64, b: u64, k: u64) -> bool {
    a == k || b != k
}
pub fn a4_four_way_no_calls(a: u64, b: u64, k: u64) -> bool {
    a == k || b != k || a > k || b < k
}
pub fn a5_call_then_const_no_call(a: u64, k: u64) -> bool {
    a == k || a == 0
}
