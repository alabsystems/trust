//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-CT: the CHAIN-TEMP SLOT — `&mut <call rvalue>` (a builder chain's
// first autoref receiver) mints Alloca + whole-value Store and the borrow is
// the slot address, exactly the temp local built MIR materializes. Gated on
// the affirmative Call allow-list (a PLACE never spells ExprKind::Call — the
// CLAUDE.md four-sites rule), a non-diverged non-ledgered result value, and
// the wave-SB snapshotable aggregate set. Links 2+ ride wave-CR (an
// `&mut`-returning method's result is already ledgered). The slot is
// frame-classed: `let r = &mut B::new(); r as *const B` keeps refusing with
// Return(borrow ptr escapes tail), probe-pinned.

pub struct B {
    pub v: i64,
    pub n: u32,
}

impl B {
    pub fn new() -> B {
        B { v: 1, n: 2 }
    }
    pub fn bump(&mut self) -> &mut B {
        self.v += 1;
        self
    }
    pub fn get(&self) -> i64 {
        self.v
    }
}

pub fn chain() -> i64 {
    B::new().bump().bump().get()
}

// wave-CTL: LITERAL rvalues join the allow-list — a literal is never a place,
// so the four-sites hazard is satisfied affirmatively, and built MIR
// materializes the same temp.
pub fn lit_slot(c: bool) -> i64 {
    let r = &mut 5i64;
    if c {
        *r += 2;
    }
    *r
}

fn main() {
    assert_eq!(chain(), 3);
    assert_eq!(lit_slot(true), 7);
    assert_eq!(lit_slot(false), 5);
}
