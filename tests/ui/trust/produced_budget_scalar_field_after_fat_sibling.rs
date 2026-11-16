//@ revisions: default certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! A guarded decrement of a `u32` field declared AFTER a fat field proves, under the
//! default policy and under `-Ztrust-policy=certify` (TRUST-KI-1014-1, 2026-10-14).
//!
//! The extractor's produced-node budget (8000 nodes) is metered over a whole type
//! walk. `T4` below is 11,111 nodes, so lowering `self: &mut Late` spends the budget
//! inside `big`, and every type lowered after that point degrades to the fail-closed
//! `Unsupported` leaf. Scalars did too, so `grace` was `Unsupported` in `Late` and
//! `u32` in `Early`. `self.grace -= 1` then failed VC-generation admission ("CheckedBinaryOp
//! lhs must match the tuple payload's supported fixed-width integer type") and
//! `Late::tick` was one `MalformedTrustIr` row: an error under both policies here,
//! while `Early::tick` proved both of its rows (the `Sub` overflow and its hardened
//! twin). Found on aterm-wasm: `AtermTerminal::reflow_grace -= 1` in
//! `pump_reflow_on_render_tick`, MalformedTrustIr on the channel seal `b58a105dde`.
//! A scalar leaf is now exempt from that bail; the extracted types are pinned in
//! `crates/trust-mir-extract/tests/produced_budget_scalar_leaf.rs`.

type T1 = (u64, u64, u64, u64, u64, u64, u64, u64, u64, u64);
type T2 = (T1, T1, T1, T1, T1, T1, T1, T1, T1, T1);
type T3 = (T2, T2, T2, T2, T2, T2, T2, T2, T2, T2);
type T4 = (T3, T3, T3, T3, T3, T3, T3, T3, T3, T3);

pub struct Late {
    pub big: T4,
    pub grace: u32,
}

impl Late {
    pub fn tick(&mut self) {
        if self.grace > 0 {
            self.grace -= 1;
        }
    }
}

// Control: the same struct with `grace` declared first proved before the fix.
pub struct Early {
    pub grace: u32,
    pub big: T4,
}

impl Early {
    pub fn tick(&mut self) {
        if self.grace > 0 {
            self.grace -= 1;
        }
    }
}
