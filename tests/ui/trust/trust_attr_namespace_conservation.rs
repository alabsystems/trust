//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ check-fail
//! Trust (E5 CONSERVATION): a name in the reserved `trust::` tool namespace that no
//! consumer claims is a HARD ERROR naming the attribute — never silence.
//!
//! WHAT THIS FIXTURE PINS. rustc resolves `#[<tool>::<anything>]` to an INERT tool
//! attribute without ever inspecting `<anything>`. Measured on the sealed toolchain
//! `trust-e26541e3` BEFORE this rule: every attribute below compiled with zero
//! diagnostics, and the verification ledger of the annotated crate was identical —
//! row for row, solver for solver — to the same crate with no attribute at all. A
//! one-keystroke misspelling of a real annotation was silently nothing while its
//! author believed a property had been stated and checked.
//!
//! The companion fixture `trust_attr_namespace_conservation_accepts.rs` pins the
//! other half, and it is the half that matters for soundness of the CHECK: every
//! one of the twenty-four claimed names still compiles. A refusal that rejects
//! everything would pass this file and break every real program.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool, stmt_expr_attributes, proc_macro_hygiene)]
#![register_tool(trust)]

// The exact spelling measured to compile clean with a bit-identical ledger.
#[trust::totally_made_up_clause(whatever @@ nonsense)]
//~^ ERROR Trust: `#[trust::totally_made_up_clause]` is not a Trust attribute
pub fn invented(a: u32) -> u32 {
    a
}

// One keystroke from a real annotation. The diagnostic must NAME the intended one.
#[trust::assume_totall]
//~^ ERROR Trust: `#[trust::assume_totall]` is not a Trust attribute
pub fn typo(a: u32) -> u32 {
    a
}

// A deeper path inside the reserved namespace. No consumer reads one.
#[trust::a::b]
//~^ ERROR Trust: `#[trust::a::b]` is not a Trust attribute
pub fn deep(a: u32) -> u32 {
    a
}

// A CLAIMED name may not launder a longer path: `skip` is real, `skip::garbage`
// is not, and nothing reads a claimed name out of a three-segment `trust::` path.
#[trust::skip::garbage]
//~^ ERROR Trust: `#[trust::skip::garbage]` is not a Trust attribute
pub fn deep_over_claimed_name(a: u32) -> u32 {
    a
}

// NON-FUNCTION POSITIONS. The namespace rule is about the NAME, so it must fire on
// every item kind — these were all measured silent before it existed.
#[trust::made_up_on_struct]
//~^ ERROR Trust: `#[trust::made_up_on_struct]` is not a Trust attribute
pub struct S {
    #[trust::made_up_on_field]
    //~^ ERROR Trust: `#[trust::made_up_on_field]` is not a Trust attribute
    pub x: u32,
}

#[trust::made_up_on_impl]
//~^ ERROR Trust: `#[trust::made_up_on_impl]` is not a Trust attribute
impl S {
    pub fn g(&self) -> u32 {
        self.x
    }
}

#[trust::made_up_on_mod]
//~^ ERROR Trust: `#[trust::made_up_on_mod]` is not a Trust attribute
pub mod m {
    pub fn h() {}
}

#[trust::made_up_on_trait]
//~^ ERROR Trust: `#[trust::made_up_on_trait]` is not a Trust attribute
pub trait T {
    fn q(&self);
}

// Statement and expression positions.
pub fn positions(a: u32) -> u32 {
    #[trust::made_up_on_stmt]
    //~^ ERROR Trust: `#[trust::made_up_on_stmt]` is not a Trust attribute
    let b = a;
    let _c = #[trust::made_up_on_expr] (b);
    //~^ ERROR Trust: `#[trust::made_up_on_expr]` is not a Trust attribute
    b
}

// A macro-generated occurrence is still an occurrence.
macro_rules! annotate {
    ($n:ident) => {
        #[trust::made_up_from_macro]
        //~^ ERROR Trust: `#[trust::made_up_from_macro]` is not a Trust attribute
        pub fn $n() {}
    };
}
annotate!(from_macro);

// An ACTIVE `cfg_attr` branch reaches this compilation and is checked. (An
// INACTIVE branch is deliberately not: an attribute that is not part of this
// compilation states nothing about it.)
#[cfg_attr(all(), trust::made_up_via_cfg_attr)]
//~^ ERROR Trust: `#[trust::made_up_via_cfg_attr]` is not a Trust attribute
pub fn active_cfg_attr() {}

#[cfg_attr(any(), trust::never_reaches_this_compilation)]
pub fn inactive_cfg_attr() {}

// ANTI-VACUITY, in the same file as the refusals. A check that refused EVERY
// `trust::` name would satisfy every assertion above and be a worse defect than the
// silence it replaces. These four are CLAIMED and carry no expected-error
// annotation at all: if the rule ever rejects one, compiletest reports it as an
// unexpected error here. (Do not write the annotation marker in this prose —
// compiletest scans comments for it and will read the sentence as an assertion.)
#[trust::backing]
pub struct Buf {
    pub ptr: u32,
    pub len: usize,
}

#[trust::paired]
pub struct Pair {
    pub v: u32,
}

pub struct Machine {
    #[trust::var(name = "state", kind = "Int")]
    pub state: u64,
}

impl Machine {
    #[trust::action(name = "Step")]
    pub fn step(&mut self) {}
}

fn main() {}
