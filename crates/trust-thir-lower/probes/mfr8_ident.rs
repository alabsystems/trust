// LANE MF-R10 (eighth review) — WHAT `names_this_body` ACTUALLY COMPARES.
//
// Round 7's identity pin is a RUNTIME comparison of ONE def-path segment:
//
//     tcx.def_path(def).data.last()  ==  func.name.rsplit("::").next()
//
// and its own commit names that as residual #4: "A shadow onto a def whose last segment is
// spelled the same would survive it." Every corpus so far has one function per name, at crate
// root, so the pin has never been asked a question it could get wrong.
//
// This file is a population of COLLIDING LAST SEGMENTS: the same final segment reached through
// different modules, inherent impls on different types, a trait impl, a derived impl, a const
// initializer, a static initializer, an associated const, and closures (whose own last segment is
// `{closure#0}`, the segment `typeck_root_def_id` removes). Every one of these is a body the pin
// must either accept as itself or refuse — and a corpus where the last segment is unique cannot
// tell those apart.
//
// No body name in this file appears in any of the 35 probe files rounds 1-7 wrote.

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::precedence)]
#![allow(clippy::nonminimal_bool, clippy::needless_bool, clippy::trivially_copy_pass_by_ref)]

#[derive(Clone, Copy)]
pub struct Ia {
    pub a: u32,
    pub b: u32,
}

#[derive(Clone, Copy)]
pub struct Ib {
    pub a: u32,
    pub b: u32,
}

pub trait Seg {
    fn iseg(&self) -> u32;
}

// --- A: THE SAME LAST SEGMENT IN TWO MODULES. --------------------------------------------

pub mod mod_one {
    #[inline(never)]
    pub fn d01_dup_seg(a: u32, b: u32) -> u32 {
        a ^ b
    }

    #[inline(never)]
    pub fn d02_dup_cmp(a: u32, b: u32) -> bool {
        (a & b) == 0
    }

    pub mod deeper {
        #[inline(never)]
        pub fn d01_dup_seg(a: u32, b: u32) -> u32 {
            a | b
        }
    }
}

pub mod mod_two {
    #[inline(never)]
    pub fn d01_dup_seg(a: u32, b: u32) -> u32 {
        a & b
    }

    #[inline(never)]
    pub fn d02_dup_cmp(a: u32, b: u32) -> bool {
        (a | b) == 0
    }
}

#[inline(never)]
pub fn d01_dup_seg(a: u32, b: u32) -> u32 {
    a ^ b ^ 1
}

// --- B: INHERENT METHODS SHARING A NAME ACROSS TYPES. ------------------------------------

impl Ia {
    #[inline(never)]
    pub fn d03_meth(&self) -> u32 {
        self.a ^ self.b
    }

    #[inline(never)]
    pub fn d04_meth_cmp(&self) -> bool {
        self.a == self.b
    }

    #[inline(never)]
    pub fn d05_assoc(a: u32, b: u32) -> u32 {
        a & b
    }

    pub const D06_ASSOC_CONST: u32 = 11 ^ 6;
}

impl Ib {
    #[inline(never)]
    pub fn d03_meth(&self) -> u32 {
        self.a & self.b
    }

    #[inline(never)]
    pub fn d04_meth_cmp(&self) -> bool {
        self.a != self.b
    }

    #[inline(never)]
    pub fn d05_assoc(a: u32, b: u32) -> u32 {
        a | b
    }

    pub const D06_ASSOC_CONST: u32 = 13 & 6;
}

// --- C: A TRAIT IMPL. The body's def path ends in the TRAIT method's segment. --------------

impl Seg for Ia {
    #[inline(never)]
    fn iseg(&self) -> u32 {
        self.a | self.b
    }
}

impl Seg for Ib {
    #[inline(never)]
    fn iseg(&self) -> u32 {
        self.a ^ self.b
    }
}

// --- D: CONST AND STATIC INITIALIZER BODIES — the `{const-init}` suffix the pin steps over. -

pub const D07_CONST_XOR: u32 = 21 ^ 5;
pub const D08_CONST_AND: u64 = 255 & 129;
pub static D09_STATIC_OR: u32 = 8 | 3;
pub static D10_STATIC_CMP: bool = 4 < 9;

// --- E: CLOSURES. Their own last segment is `{closure#0}`, which the typeck root removes. ---

#[inline(never)]
pub fn d11_closure_call(a: u32, b: u32) -> u32 {
    (|x: u32| x ^ b)(a)
}

#[inline(never)]
pub fn d12_closure_nested(a: u32) -> u32 {
    (|x: u32| (|y: u32| y & 7)(x ^ 1))(a)
}

#[inline(never)]
pub fn d13_closure_returned() -> impl Fn(u32) -> u32 {
    |x: u32| x | 4
}

#[inline(never)]
pub fn d14_closure_two_in_one_fn(a: u32) -> u32 {
    (|x: u32| x ^ 2)(a) ^ (|x: u32| x & 3)(a)
}

// --- F: GENERICS INSTANTIATED AT SEVERAL TYPES — one def path, several bodies. --------------

#[inline(never)]
pub fn d15_generic_id<T: Copy>(x: T) -> T {
    x
}

#[inline(never)]
pub fn d16_use_generic_u32(a: u32) -> u32 {
    d15_generic_id(a)
}

#[inline(never)]
pub fn d17_use_generic_u64(a: u64) -> u64 {
    d15_generic_id(a)
}

#[inline(never)]
pub fn d18_use_generic_char(a: char) -> char {
    d15_generic_id(a)
}

// --- G: A DERIVED IMPL — a compiler-generated body whose def path is the trait method. ------

#[derive(Clone, Copy, PartialEq)]
pub struct Der {
    pub x: u32,
    pub y: u32,
}

#[inline(never)]
pub fn d19_use_derived_eq(a: Der, b: Der) -> bool {
    a == b
}

#[inline(never)]
pub fn d20_use_derived_clone(a: Der) -> Der {
    a
}
