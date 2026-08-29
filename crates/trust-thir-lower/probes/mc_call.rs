// WAVE-MC — the CALL-RESULT / CALL-ARGUMENT marker probe.
//
// Every body here reproduces, shape for shape, one of the eleven `derived_mir: agreed`,
// `markers_exact: false` bodies of `clean-kernel` whose trust-ir carries an `Inst::Call`.
// Nothing is `#[inline(never)]`: `mir_built` is pre-inlining and the differential reads
// `mir_built`, so the call survives regardless.
#![allow(dead_code, clippy::needless_return)]

#[derive(Copy, Clone)]
pub struct M(u64);

impl M {
    // callee: by-value Copy receiver, scalar return
    #[inline]
    pub fn range(self) -> u32 {
        (self.0 >> 44) as u32
    }

    // A: CALL RESULT IN AN OPERAND POSITION  (== expr::meta::ExprMeta::has_loose_bvars)
    //    trust-ir: %1 = call @range(%0); %2 = const u32 0; %3 = icmp ugt %1,%2; ret %3
    #[inline]
    pub fn a_call_operand(self) -> bool {
        self.range() > 0
    }
}

pub struct R {
    n: usize,
}

impl R {
    #[inline]
    pub fn before(&self) -> usize {
        self.n
    }

    // B: TAIL CALL through an autoref receiver  (== tc::branch_sharing::RecursorApp::major_idx)
    //    trust-ir: %1 = call @before(%0); ret %1
    #[inline]
    pub fn b_tail_call(&self) -> usize {
        self.before()
    }
}

pub struct N(u64);

impl N {
    #[inline]
    pub fn h(&self) -> u64 {
        self.0
    }
}

// C: TAIL CALL on a free fn over a &-param  (== env::native_reducers_name::lean4_name_hash)
#[inline]
pub fn c_tail_free(name: &N) -> u64 {
    name.h()
}

#[derive(Copy, Clone, PartialEq)]
pub enum T {
    A,
    B,
}

impl T {
    #[inline]
    pub fn nr(self) -> bool {
        matches!(self, T::B)
    }
}

pub struct O {
    t: T,
}

impl O {
    #[inline]
    pub fn trust(&self) -> T {
        self.t
    }

    // D: CALL RESULT AS THE SOLE ARGUMENT OF A SECOND CALL
    //    (== env::origin::ConstantOrigin::needs_recheck)
    //    trust-ir: %1 = call @trust(%0); %2 = call @nr(%1); ret %2
    #[inline]
    pub fn d_call_call(&self) -> bool {
        self.trust().nr()
    }
}

pub struct E(bool);

impl E {
    #[inline]
    pub fn q(&self) -> bool {
        self.0
    }
}

// E: CALL RESULT UNDER `!`  (== proof_irrel::try_infer_type_quick::{closure#1}, whose
//    trust-ir spells `!x` as select(x, false, true))
#[inline]
pub fn e_not_call(t: &E) -> bool {
    !t.q()
}

#[derive(Copy, Clone, Default)]
pub struct BI(u8);
#[derive(Copy, Clone, Default)]
pub struct BN(u8);

pub struct BD {
    i: BI,
    n: BN,
}

impl Default for BD {
    // F: TWO CALL RESULTS AS AGGREGATE FIELDS
    //    (== <expr::types::BinderData as Default>::default)
    //    trust-ir: %0 = call; %1 = call; %2 = const struct; insertfield; insertfield; ret
    #[inline]
    fn default() -> BD {
        BD { i: BI::default(), n: BN::default() }
    }
}

// --- the four ORDERING questions the plan must answer, measured rather than reasoned -------

#[inline]
pub fn f1(a: u32) -> u32 {
    a
}
#[inline]
pub fn f2(a: u32, b: u32) -> u32 {
    a + b
}
#[inline]
pub fn g1(m: M) -> u32 {
    m.0 as u32
}

// Q1: a call whose result feeds a SECOND call that ALSO has a param argument.
//     Which retires first in the successor block?
#[inline]
pub fn q1(x: u32, y: u32) -> u32 {
    f2(f1(x), y)
}

// Q2: two param args to one call.
#[inline]
pub fn q2(x: u32, y: u32) -> u32 {
    f2(x, y)
}

// Q3: a call with a CONSTANT argument beside a param.
#[inline]
pub fn q3(x: u32) -> u32 {
    f2(x, 7)
}

// Q4: a call result consumed by a binop whose other operand is a param.
#[inline]
pub fn q4(x: u32, y: u32) -> u32 {
    f1(x) + y
}

// Q5: the exact target shape — by-value Copy struct receiver, result into an icmp.
#[inline]
pub fn q5(m: M) -> bool {
    g1(m) > 0
}

// Q6: a call taking no arguments at all, result into an icmp.
#[inline]
pub fn f0() -> u32 {
    3
}
#[inline]
pub fn q6() -> bool {
    f0() > 0
}

// Q7: a call result RETURNED but not the immediately-next node (a dead const between).
#[inline]
pub fn q7(x: u32) -> u32 {
    let _ = 1u32;
    f1(x)
}

// Q8: nested calls, result of inner is the ONLY arg of outer, outer returned.
#[inline]
pub fn q8(x: u32) -> u32 {
    f1(f1(x))
}
