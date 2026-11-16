//@ needs-trust-verify
//@ edition: 2021
//@ revisions: enum_ok enum_bug havoc_ok havoc_bug box_ok box_bug
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[enum_ok] check-pass
//@[enum_bug] check-fail
//@[havoc_ok] check-pass
//@[havoc_bug] check-fail
//@[box_ok] check-pass
//@[box_bug] check-fail
//! ENC-DEFECTS (unaimed corpus, class 13): three vcgen state-encoding bugs that
//! REFUSED correct programs on a counterexample no execution can produce. Each
//! `*_ok` revision was refused on stage-1 `a4b52d0f3`; each `*_bug` revision is an
//! unsound neighbour of it that panics at runtime (measured with a
//! `-Ztrust-verify=off` driver) and must stay refused.
//!
//!   * 13a — a FIELDLESS enum's discriminant read was not tied to the value that
//!     built it: `let m = if x < 255 { Up } else { Idle }; match m { Up => x + 1 }`
//!     refuted at `_4 = 1, __trust_mir__discr_m = 0, x = 255`. The value's integer
//!     model is now its discriminant (construction pins the tag, the read returns
//!     it), so the ordinary place versioning carries the link — including through
//!     a projected place behind `&mut self`.
//!   * 13b — a call that cannot write the `&mut self` fields havocked them: a std
//!     call over MOVED scalar temporaries, and a call receiving `&*self` of a
//!     pure `Freeze` type (a protected shared reborrow; docs/TCB.md "Shared-reborrow
//!     immutability across a call").
//!   * 13c — a `Box` reached through a validity-rooted REFERENCE: rustc's
//!     `NullReferenceConstructed` check on `&**a` was never discharged (the
//!     `NullPointerDereference` twin was), and the separation engine refused the
//!     `Deref` of the reference in the box's access path.

#![allow(dead_code)]

// ======================= 13a: fieldless enum discriminants =======================

#[derive(Clone, Copy)]
pub enum M {
    Idle,
    Up,
}

#[derive(Clone, Copy)]
#[repr(i8)]
pub enum S {
    Neg = -1,
    Pos = 5,
}

#[derive(Clone, Copy)]
pub enum Motion {
    Idle,
    Up,
}

pub struct Elevator {
    pub floor: u8,
    pub top: u8,
    pub motion: Motion,
}

/// d3/iso/v14d.
#[cfg(enum_ok)]
pub fn local_ok(x: u8) -> u8 {
    let m = if x < 255 { M::Up } else { M::Idle };
    match m {
        M::Up => x + 1,
        M::Idle => x,
    }
}

/// Explicit, negative discriminants: the tag is the DECODED value (`-1`, not 255).
#[cfg(enum_ok)]
pub fn signed_ok(x: u8) -> u8 {
    let s = if x < 255 { S::Neg } else { S::Pos };
    match s {
        S::Neg => x + 1,
        S::Pos => x,
    }
}

/// The enum FIELD of a local struct.
#[cfg(enum_ok)]
pub fn local_struct(x: u8) -> u8 {
    let mut e = Elevator { floor: x, top: 255, motion: Motion::Idle };
    e.motion = if e.floor < e.top { Motion::Up } else { Motion::Idle };
    match e.motion {
        Motion::Up => e.floor + 1,
        Motion::Idle => e.floor,
    }
}

impl Elevator {
    /// The enum field behind `&mut self`, stored then matched.
    #[cfg(enum_ok)]
    pub fn tick_param(&mut self, floor: u8) -> u8 {
        self.motion = if floor < 255 { Motion::Up } else { Motion::Idle };
        match self.motion {
            Motion::Up => floor + 1,
            Motion::Idle => floor,
        }
    }

    #[cfg(enum_bug)]
    pub fn tick_param_swapped(&mut self, floor: u8) -> u8 {
        //[enum_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::Elevator::tick_param_swapped`
        self.motion = if floor < 255 { Motion::Idle } else { Motion::Up };
        match self.motion {
            Motion::Up => floor + 1,
            Motion::Idle => floor,
        }
    }
}

#[cfg(enum_bug)]
pub fn local_swapped(x: u8) -> u8 {
    //[enum_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::local_swapped`
    let m = if x < 255 { M::Idle } else { M::Up };
    match m {
        M::Up => x + 1,
        M::Idle => x,
    }
}

#[cfg(enum_bug)]
pub fn local_reassigned(x: u8) -> u8 {
    //[enum_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::local_reassigned`
    let mut m = if x < 255 { M::Up } else { M::Idle };
    m = M::Up;
    match m {
        M::Up => x + 1,
        M::Idle => x,
    }
}

#[cfg(enum_bug)]
pub fn signed_swapped(x: u8) -> u8 {
    //[enum_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::signed_swapped`
    let s = if x < 255 { S::Pos } else { S::Neg };
    match s {
        S::Neg => x + 1,
        S::Pos => x,
    }
}

// ======================= 13b: calls that cannot write `*self` =======================

pub struct Quota {
    pub used: u32,
    pub limit: u32,
}

impl Quota {
    fn remaining(&self) -> u32 {
        self.limit.saturating_sub(self.used)
    }

    fn bump(&mut self) {
        self.used = u32::MAX;
    }

    /// A std call over MOVED `u32` temporaries between the guard and the use.
    #[cfg(havoc_ok)]
    pub fn consume_moved(&mut self, n: u32) -> Option<u32> {
        if self.used > self.limit || n > self.limit - self.used {
            return None;
        }
        let _r = self.limit.saturating_sub(self.used);
        self.used += n;
        Some(self.limit - self.used)
    }

    /// A `&self` call between the guard and the use.
    #[cfg(havoc_ok)]
    pub fn consume_shared(&mut self, n: u32) -> Option<u32> {
        if self.used > self.limit || n > self.limit - self.used {
            return None;
        }
        let _r = self.remaining();
        self.used += n;
        Some(self.limit - self.used)
    }

    /// A `&mut self` call between the guard and the use really writes `used`.
    #[cfg(havoc_bug)]
    pub fn consume_mut_call(&mut self, n: u32) -> Option<u32> {
        //[havoc_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::Quota::consume_mut_call`
        if self.used > self.limit || n > self.limit - self.used {
            return None;
        }
        self.bump();
        self.used += n;
        Some(self.limit - self.used)
    }
}

/// `used` lives in a `Cell`: a `&self` call CAN write it, and does.
pub struct CellQuota {
    pub used: core::cell::Cell<u32>,
    pub limit: u32,
}

impl CellQuota {
    fn poke(&self) {
        self.used.set(u32::MAX);
    }

    #[cfg(havoc_bug)]
    pub fn consume_cell(&mut self, n: u32) -> u32 {
        //[havoc_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::CellQuota::consume_cell`
        let used = *self.used.get_mut();
        if used > self.limit || n > self.limit - used {
            return 0;
        }
        self.poke();
        *self.used.get_mut() + n
    }
}

/// A `&mut self` whose pointee is a fieldless enum and nothing else: no scalar
/// leaf for the TRUST-10 sibling (`refine_shared_reborrow_havoc`) to spare, so it is
/// 13b's whole-pointee narrowing that keeps the stored state across the `&self`
/// call (added at the 2026-09-28 rebase reconciliation, which made 13b the
/// fallback where the sibling declines).
#[derive(Clone, Copy)]
pub enum Phase {
    Idle,
    Busy,
}

pub struct Machine {
    pub phase: Phase,
}

impl Machine {
    fn is_busy(&self) -> bool {
        matches!(self.phase, Phase::Busy)
    }

    fn force_busy(&mut self) {
        self.phase = Phase::Busy;
    }

    #[cfg(havoc_ok)]
    pub fn step(&mut self, x: u8) -> u8 {
        self.phase = if x < 255 { Phase::Busy } else { Phase::Idle };
        let _b = self.is_busy();
        match self.phase {
            Phase::Busy => x + 1,
            Phase::Idle => x,
        }
    }

    /// The `&mut self` call between the store and the match really sets `Busy`.
    #[cfg(havoc_bug)]
    pub fn step_forced(&mut self, x: u8) -> u8 {
        //[havoc_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::Machine::step_forced`
        self.phase = if x < 255 { Phase::Busy } else { Phase::Idle };
        self.force_busy();
        match self.phase {
            Phase::Busy => x + 1,
            Phase::Idle => x,
        }
    }
}

// ======================= 13c: a `Box` behind a validity-rooted reference =======================

pub enum Expr {
    Num(i64),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

/// d3/p09 verbatim.
#[cfg(box_ok)]
pub fn eval(e: &Expr) -> Option<i64> {
    match e {
        Expr::Num(n) => Some(*n),
        Expr::Add(a, b) => eval(a)?.checked_add(eval(b)?),
        Expr::Sub(a, b) => eval(a)?.checked_sub(eval(b)?),
        Expr::Mul(a, b) => eval(a)?.checked_mul(eval(b)?),
        Expr::Div(a, b) => eval(a)?.checked_div(eval(b)?),
    }
}

/// `**b` through a shared reference parameter (d3/iso/v09f).
#[cfg(box_ok)]
pub fn read_through_ref(b: &Box<i64>) -> i64 {
    **b
}

/// `&**b` handed on (d3/iso/v09h).
#[cfg(box_ok)]
pub fn reborrow_through_ref(b: &Box<i64>) -> i64 {
    first(b)
}

#[cfg(box_ok)]
fn first(x: &i64) -> i64 {
    *x
}

/// The same deref through a RAW pointer: no validity guarantee.
#[cfg(box_bug)]
pub unsafe fn read_through_raw(b: *const Box<i64>) -> i64 {
    //[box_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::read_through_raw`
    unsafe { **b }
}

/// A box read out of a UNION field: the bytes carry no validity guarantee.
pub union BoxOrWord {
    pub b: core::mem::ManuallyDrop<Box<i64>>,
    pub w: usize,
}

#[cfg(box_bug)]
pub fn read_through_union(u: &BoxOrWord) -> i64 {
    //[box_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::read_through_union`
    unsafe { **u.b }
}

/// A box fabricated by `unsafe` in the same function.
#[cfg(box_bug)]
pub fn read_fabricated(p: *mut i64) -> i64 {
    //[box_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::read_fabricated`
    let b: &Box<i64> = unsafe { &*(&p as *const *mut i64 as *const Box<i64>) };
    **b
}

/// The box behind the reference is freed by a callee the reference is handed
/// to, then read (the independent review's rc12). The helper is refused in its
/// own body; the CALLER must be refused too — before the 2026-09-28 reference-lane
/// fence it was only an advisory (its three box-deref rows were dropped).
#[cfg(box_bug)]
pub struct Held {
    pub b: Box<i64>,
}

#[cfg(box_bug)]
#[inline(never)]
fn dup_and_free(h: &Held) {
    //[box_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::dup_and_free`
    unsafe { drop(core::ptr::read(&h.b)) }
}

#[cfg(box_bug)]
pub fn read_after_helper_freed(h: &Held) -> i64 {
    //[box_bug]~^ ERROR Trust Level 0 safety verification incomplete for `enc_defects_precision::read_after_helper_freed`
    dup_and_free(h);
    *h.b
}
