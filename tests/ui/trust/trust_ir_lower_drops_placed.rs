//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ edition: 2021
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (step 2 increment 4b): THE PRODUCER EMITS DROPS. Every body here owns a value whose type
//! needs dropping and lets it go out of scope; the direct trust-ir now carries the `Inst::Drop`
//! rustc's drop elaboration performs, at the same point, and the effect-conservation gate finds
//! the claim equal to the MIR oracle (`drop_oracle.rs`). Before this change each body was
//! `Abstracted(drop, ..)` (plus `Abstracted(destructor, ..)` for a `Drop` impl) and strict refused
//! it — so this file compiling under strict IS the check that fails before the change.
//!
//! `scalar_guard` is also THE INTERPRETATION HAZARD PIN (design §1.6): its parameters are
//! scalars, so the interpretation differential would sample it, and the reference interpreter
//! refuses `Inst::Drop` with a `TypeError` that counts as a THIR defect — a false divergence,
//! which strict turns into a compile error. A drop-bearing body is forced out of interpretation
//! (`drops::drops_force_not_interpretable`), so it compiles.
//!
//! The refusals (shapes the producer does not place yet) are pinned, with their reasons, in
//! `trust_ir_effect_conservation_drop_elided.rs`.

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

pub struct Guard(pub i32);

impl Drop for Guard {
    fn drop(&mut self) {
        unsafe { close(self.0) };
    }
}

pub struct G(pub u64);

impl Drop for G {
    fn drop(&mut self) {
        unsafe { close(self.0 as i32) };
    }
}

#[inline(never)]
pub fn take(_g: Guard) {}

/// A binding dropped at the end of its block.
pub fn guard_scope(fd: i32) {
    let _g = Guard(fd);
}

/// A parameter dropped at the end of the body.
pub fn consume(_f: Guard) {}

/// The interpretation hazard pin: scalar parameters, a drop.
pub fn scalar_guard(x: u64) -> u64 {
    let _g = G(x);
    x
}

/// A shared borrow of a value whose glue only frees memory.
pub fn drop_string(s: String) -> usize {
    s.len()
}

/// Moved on the early-return edge (dead there), live on the fallthrough (dropped there).
pub fn early(g: Guard, c: bool) -> u32 {
    if c {
        take(g);
        return 1;
    }
    2
}

/// Two returns sharing rustc's return tree: live at one, moved at the other. rustc guards that
/// one node with a flag; the producer places the drop on the live edge only.
pub fn two_returns(g: Guard, c: bool, d: bool) -> u32 {
    if c {
        return 1;
    }
    if d {
        take(g);
        return 2;
    }
    3
}

/// A binding re-initialized every iteration, dropped at the `break` and at the back edge.
pub fn lp(fd: i32, n: u32) {
    let mut i = 0;
    loop {
        let _g = Guard(fd);
        if i == n {
            break;
        }
        i += 1;
    }
}

/// Two bindings, dropped in reverse declaration order.
pub fn two_bindings(a: i32, b: i32) {
    let _x = Guard(a);
    let _y = Guard(b);
}

/// A nested block's binding is dropped at the inner block's end, before the outer one's.
pub fn nested(a: i32, b: i32) -> i32 {
    let _x = Guard(a);
    {
        let _y = Guard(b);
    }
    a + b
}

/// Moved on every path: nothing to drop.
pub fn moved(g: Guard) {
    take(g);
}
