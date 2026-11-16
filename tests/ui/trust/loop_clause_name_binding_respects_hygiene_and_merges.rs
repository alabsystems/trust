//@ revisions: def_site_param def_site_const sroa_fragment_merge macro_rules_local inlined_loop_stamp
//@ revisions: metavariable_span param_shadow_ensures
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@[sroa_fragment_merge] compile-flags: -Zmir-opt-level=2 -Cdebuginfo=2
//@[inlined_loop_stamp] compile-flags: -Zinline-mir
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Review round 41 (2026-10-02), each PROVED and kernel-certified before.
//! `def_site_param`: a `pub macro` emits `fn f(lim: u8) .. invariant $inv`; the
//! call-site clause `lim <= 127` names the static (200), but name matching bound
//! the def-site parameter. `def_site_const`: a def-site block `const lim` was
//! replaced by a call-site `let lim` the macro's own clause cannot see. Source
//! contracts are matched by displayed name, so def-site (macros 2.0) hygiene now
//! leaves nothing bindable. `sroa_fragment_merge`: DestinationPropagation merged
//! `lim` with a tuple field whose row is an SROA fragment the name census does not
//! count; a verifying session no longer runs DestinationPropagation.
//! Review round 42: `macro_rules_local`: the macro's own `let lim = 200` was an
//! unsupported shadow that a narrower call-site `let lim` replaced, so the macro's
//! clause was proved about the call-site value; `macro_rules` local hygiene now
//! unbinds like def-site hygiene. `inlined_loop_stamp`: an inlined helper's loop
//! carried its own per-owner loop id, equal to the caller's `loop { break; }`, and
//! the caller's invariant was certified at the helper's loop head; an inlined
//! scope now names no loop of the caller.
//! Review round 47, against the identity lane (97a55c9d86f): `metavariable_span`:
//! a `macro_rules!` metavariable gives every expansion's binding the same span, so
//! the debug-row fallback (name + span) bound `one!(v, x)`'s row for the `v` of
//! `one!(v, 7)`; a row is now used only when no other HIR binding of the name
//! shares its span. `param_shadow_ensures`: a loop clause on a shadow of parameter
//! `n` handed the name `n` to the shadow, and the function's `ensures result == n`
//! was proved about it; a parameter's name now resolves only to the parameter.
#![cfg_attr(any(def_site_param, def_site_const), feature(decl_macro))]
#![allow(non_upper_case_globals, unused_variables, unused_assignments)]

#[cfg(def_site_param)]
pub static lim: u8 = 200;

#[cfg(def_site_param)]
mod mm {
    pub macro mk($name:ident, $inv:expr) {
        pub fn $name(lim: u8) -> u8
            requires lim <= 100
        {
            let mut i: u8 = 0;
            while i < 3
                invariant $inv
            {
                i += 1;
            }
            i
        }
    }
}
#[cfg(def_site_param)]
mm::mk!(f, lim <= 127);

#[cfg(def_site_const)]
mod mm {
    pub macro looper($($s:stmt;)*) {{
        const lim: u8 = 200;
        $($s;)*
        let mut i: u8 = 0;
        while i < 3
            invariant lim <= 127
        {
            i += 1;
        }
        i
    }}
}
#[cfg(def_site_const)]
pub fn f(a: u8) -> u8 {
    mm::looper!(let lim: u8 = a / 2; let _ = lim;)
}

#[cfg(sroa_fragment_merge)]
pub fn f(a: u8) -> u8 {
    let mut st: (u8, u8);
    let lim: u8 = a / 2;
    st = (lim, 0);
    st.0 |= 128;
    let mut i: u8 = 0;
    while i < 3
        invariant lim >= 128
    {
        i += 1;
    }
    st.0 + (i - i)
}

#[cfg(macro_rules_local)]
macro_rules! m {
    ($($b:tt)*) => {{
        let lim: u8 = 200;
        let mut i: u8 = 0;
        {
            $($b)*
            while i < 3
                invariant lim <= 127
            {
                i += 1;
            }
        }
        i
    }};
}
#[cfg(macro_rules_local)]
pub fn f(a: u8) -> u8 {
    m!(let lim: u8 = a / 4;)
}

#[cfg(inlined_loop_stamp)]
#[inline(always)]
fn helper(m: u8) -> u8 {
    let mut kk: u8 = 200;
    let mut j: u8 = 0;
    while j < m
        invariant j <= m
    {
        j = m;
    }
    j
}
#[cfg(inlined_loop_stamp)]
// Re-pinned 2026-10-15: since a39074ae82f (determinism T6, 2026-10-09) a proof session refuses
// `-Zinline-mir` outright, before any verification runs: the verified MIR, and so the verdict, must
// not depend on the caller's MIR options. The shape this revision built can no longer reach
// a verdict at all, which is the strongest form of the refusal it pinned.
//[inlined_loop_stamp]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zinline-mir would make the verified MIR
pub fn f(n: u8) -> u8 {
    let mut k: u8 = 200;
    let i: u8 = 0;
    loop
        invariant k == 0
    {
        break;
    }
    k = 0;
    let z = helper(n);
    z + k
}

#[cfg(metavariable_span)]
macro_rules! one {
    ($v:ident, $a:expr) => {
        let $v: u8 = $a;
    };
}
#[cfg(metavariable_span)]
pub fn f(p: u8) -> u8 {
    let x: u8 = p % 5;
    one!(v, x);
    one!(v, 7);
    let mut i: u8 = 0;
    while i < 3
        invariant v < 5
    {
        i += 1;
    }
    i
}

#[cfg(param_shadow_ensures)]
pub fn f(n: u8) -> u8 //[param_shadow_ensures]~ ERROR verification
    ensures result == n
{
    let m: u8 = n / 2;
    {
        let n: u8 = m | 1;
        let mut i: u8 = 0;
        while i < n
            invariant i <= n
        {
            i += 1;
        }
    }
    m | 1
}
