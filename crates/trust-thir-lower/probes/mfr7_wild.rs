// LANE MF-R8 (seventh review) — WHERE NO CORPUS HAS BEEN.
//
// Rounds 1-6 wrote 1,280 bodies and every one of them is a free `#[inline(never)] pub fn` over
// scalars, refs and one flat struct. Nothing in that population is a CLOSURE body, a body the
// compiler instantiates TWICE from one source, a `const fn` also evaluated at compile time, a
// body with an arm the compiler proves unreachable, or a body whose source shadows a binding so
// two `let`s compete for one slot. Each of those reaches `lower_ir_to_mir` as its OWN
// `LocalDefId` with its OWN typeck root — the seam the sixth review's attack A lives on — and
// each of them is a body shape whose marker discipline nobody has ever measured.
//
// Rows that come back UNSUPPORTED are a measurement too: they say the fragment refuses the shape.
// Rows that come back `agreed` are new surface for every attack in this lane.
//
// No body name in this file appears in any of the 32 probe files rounds 1-6 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::redundant_closure_call)]
#![allow(clippy::needless_bool, clippy::nonminimal_bool, clippy::precedence)]
#![allow(clippy::unnecessary_cast, clippy::shadow_unrelated, clippy::manual_swap)]

#[derive(Clone, Copy)]
pub struct Wid {
    pub s: u32,
    pub t: u32,
}

// --- A: CLOSURES. Each closure body is its own MIR body with its own def id, and its typeck
//        ROOT is the enclosing function — the exact `def` vs `typeck_root_def_id` distinction
//        the round-6 repair pins. Capture by ref, by value, and nothing at all. -------------

#[inline(never)]
pub fn w01_closure_nocapture(a: u32, b: u32) -> u32 {
    let f = |x: u32, y: u32| x ^ y;
    f(a, b)
}

#[inline(never)]
pub fn w02_closure_capture_copy(a: u32, b: u32) -> u32 {
    let f = |y: u32| a ^ y;
    f(b)
}

#[inline(never)]
pub fn w03_closure_capture_two(a: u32, b: u32, c: u32) -> u32 {
    let f = |y: u32| (a ^ b) ^ y;
    f(c)
}

#[inline(never)]
pub fn w04_closure_capture_by_ref(p: &Wid, a: u32) -> u32 {
    let f = |y: u32| p.s ^ y;
    f(a)
}

#[inline(never)]
pub fn w05_closure_capture_by_ref_two_fields(p: &Wid, a: u32) -> u32 {
    let f = |y: u32| (p.s ^ p.t) ^ y;
    f(a)
}

#[inline(never)]
pub fn w06_closure_cmp_inside(a: u32, b: u32) -> bool {
    let f = |x: u32, y: u32| x == y;
    f(a, b)
}

#[inline(never)]
pub fn w07_closure_branch_inside(a: u32, b: u32, c: u32) -> u32 {
    let f = |x: u32| if x == a { b } else { c };
    f(a)
}

#[inline(never)]
pub fn w08_two_closures_one_body(a: u32, b: u32) -> u32 {
    let f = |x: u32| x ^ a;
    let g = |x: u32| x ^ b;
    f(a) ^ g(b)
}

#[inline(never)]
pub fn w09_closure_returning_tuple(a: u32, b: u32) -> (u32, u32) {
    let f = |x: u32, y: u32| (x ^ y, y ^ x);
    f(a, b)
}

// --- B: GENERIC BODIES INSTANTIATED TWICE. One source body, two monomorphizations — two MIR
//        bodies from ONE `LocalDefId`, which is a shape no plan in this shim has ever been
//        asked about. ------------------------------------------------------------------------

#[inline(never)]
pub fn w10_generic_xor<T: core::ops::BitXor<Output = T> + Copy>(a: T, b: T) -> T {
    a ^ b
}

#[inline(never)]
pub fn w11_generic_xor_u32(a: u32, b: u32) -> u32 {
    w10_generic_xor(a, b)
}

#[inline(never)]
pub fn w12_generic_xor_u64(a: u64, b: u64) -> u64 {
    w10_generic_xor(a, b)
}

#[inline(never)]
pub fn w13_generic_pair_xor<T: core::ops::BitXor<Output = T> + Copy>(a: T, b: T, c: T) -> T {
    (a ^ b) ^ c
}

#[inline(never)]
pub fn w14_generic_pair_u32(a: u32, b: u32, c: u32) -> u32 {
    w13_generic_pair_xor(a, b, c)
}

#[inline(never)]
pub fn w15_generic_pair_u16(a: u16, b: u16, c: u16) -> u16 {
    w13_generic_pair_xor(a, b, c)
}

// --- C: CONST-EVALUATED BODIES. A `const fn` is lowered for runtime AND interpreted by CTFE;
//        an associated const forces the second. --------------------------------------------

pub const fn w16_const_fn_xor(a: u32, b: u32) -> u32 {
    a ^ b
}

pub const W17_CONST_USE: u32 = w16_const_fn_xor(5, 9);

#[inline(never)]
pub fn w18_const_fn_at_runtime(a: u32, b: u32) -> u32 {
    w16_const_fn_xor(a, b) ^ W17_CONST_USE
}

pub const fn w19_const_fn_pair(a: u32, b: u32, c: u32) -> u32 {
    (a ^ b) ^ c
}

pub const W20_CONST_PAIR: u32 = w19_const_fn_pair(1, 2, 3);

#[inline(never)]
pub fn w21_const_pair_at_runtime(a: u32, b: u32, c: u32) -> u32 {
    w19_const_fn_pair(a, b, c) ^ W20_CONST_PAIR
}

// --- D: UNREACHABLE ARMS. A `match` on a bool with a proven-dead arm, and a body whose tail is
//        provably not reached — the marker channel REFUSES a marker in an unwalked block, so
//        these test the interaction between the gate's counts and the channel's block sweep. --

#[inline(never)]
pub fn w22_match_bool_both_arms(c: bool, a: u32, b: u32) -> u32 {
    match c {
        true => a ^ b,
        false => b ^ a,
    }
}

#[inline(never)]
pub fn w23_match_const_true(a: u32, b: u32) -> u32 {
    match true {
        true => a ^ b,
        false => b ^ a,
    }
}

#[inline(never)]
pub fn w24_if_const_false(a: u32, b: u32) -> u32 {
    if false { a ^ b } else { b ^ a }
}

#[inline(never)]
pub fn w25_match_int_with_wildcard(k: u32, a: u32, b: u32) -> u32 {
    match k {
        0 => a ^ b,
        1 => b ^ a,
        _ => a ^ a,
    }
}

#[inline(never)]
pub fn w26_match_int_dense_four(k: u32, a: u32, b: u32) -> u32 {
    match k {
        0 => a ^ b,
        1 => b ^ a,
        2 => a ^ a,
        _ => b ^ b,
    }
}

// --- E: SHADOWED LOCALS REUSING A SLOT. Two `let`s with one name, of one type, in one block —
//        built may or may not reuse the storage slot, and the marker channel alpha-renames by
//        FIRST APPEARANCE, so a slot reuse and a fresh slot render differently. -------------

#[inline(never)]
pub fn w27_shadow_same_type_twice(a: u32, b: u32) -> u32 {
    let t = a ^ b;
    let t = t ^ a;
    t
}

#[inline(never)]
pub fn w28_shadow_three_deep(a: u32, b: u32, c: u32) -> u32 {
    let t = a ^ b;
    let t = t ^ c;
    let t = t ^ a;
    t
}

#[inline(never)]
pub fn w29_shadow_changes_type(a: u32, b: u32) -> u64 {
    let t = a ^ b;
    let t = t as u64;
    t ^ 1
}

#[inline(never)]
pub fn w30_shadow_in_inner_block(a: u32, b: u32) -> u32 {
    let t = a ^ b;
    {
        let t = t ^ a;
        t ^ b
    }
}

#[inline(never)]
pub fn w31_shadow_across_branch(c: bool, a: u32, b: u32) -> u32 {
    let t = a ^ b;
    let t = if c { t ^ a } else { t ^ b };
    t
}

// --- F: LOOPS WITH VALUES. `loop`/`break value` is a join the branch plan has never seen. -----

#[inline(never)]
pub fn w32_loop_break_immediate(a: u32, b: u32) -> u32 {
    loop {
        break a ^ b;
    }
}

#[inline(never)]
pub fn w33_loop_break_conditional(a: u32, b: u32) -> u32 {
    let mut i = a;
    loop {
        if i == b {
            break i ^ a;
        }
        i = i ^ 1;
    }
}

#[inline(never)]
pub fn w34_while_accumulate(a: u32, b: u32) -> u32 {
    let mut i = 0u32;
    let mut acc = a;
    while i < b {
        acc = acc ^ i;
        i = i ^ 1;
    }
    acc
}

// --- G: MUT PARAMS AND REASSIGNMENT — one source binding, several stores into one slot. ------

#[inline(never)]
pub fn w35_mut_param_two_stores(mut a: u32, b: u32) -> u32 {
    a = a ^ b;
    a = a ^ b;
    a
}

#[inline(never)]
pub fn w36_mut_local_then_cmp(a: u32, b: u32) -> bool {
    let mut t = a ^ b;
    t = t ^ a;
    t == b
}

#[inline(never)]
pub fn w37_swap_via_temp(a: u32, b: u32) -> u32 {
    let mut x = a;
    let mut y = b;
    let z = x;
    x = y;
    y = z;
    x ^ y
}

// --- H: NESTED FUNCTION ITEM — an item inside a body, a second def id under one source fn. ---

#[inline(never)]
pub fn w38_nested_item(a: u32, b: u32) -> u32 {
    #[inline(never)]
    fn inner(x: u32, y: u32) -> u32 {
        x ^ y
    }
    inner(a, b) ^ a
}

#[inline(never)]
pub fn w39_nested_item_with_branch(a: u32, b: u32) -> u32 {
    #[inline(never)]
    fn inner(x: u32, y: u32) -> u32 {
        if x == y { x } else { y }
    }
    inner(a, b) ^ b
}

// --- I: ASSOCIATED / TRAIT-METHOD BODIES — a body whose def id hangs off an impl, not a module.

impl Wid {
    #[inline(never)]
    pub fn w40_method_xor(&self, a: u32) -> u32 {
        self.s ^ a
    }

    #[inline(never)]
    pub fn w41_method_two_fields(&self, a: u32) -> u32 {
        (self.s ^ self.t) ^ a
    }

    #[inline(never)]
    pub fn w42_method_cmp(&self, a: u32) -> bool {
        self.s == a
    }

    #[inline(never)]
    pub fn w43_assoc_fn(a: u32, b: u32) -> u32 {
        a ^ b
    }
}

pub trait W44Trait {
    fn w44_trait_xor(&self, a: u32) -> u32;
}

impl W44Trait for Wid {
    #[inline(never)]
    fn w44_trait_xor(&self, a: u32) -> u32 {
        (self.s ^ self.t) ^ a
    }
}
