//@ needs-trust-verify
//@ edition: 2021
//@ revisions: overflow_arm index_arm div_arm rem_arm shift_arm mul_arm sub_arm neg_arm
//@ revisions: signed_local u8_local char_local moved_guard loop_body loop_carried option_guard
//@ revisions: nested_option user_enum array_holder generic_wrapper outer_field tuple_guard
//@ revisions: two_drops one_branch branch_built labeled_break closure_owner reassigned
//@ revisions: wildcard_temp double_ref noop_guard unrelated_drop other_local safe_arm
//@ revisions: fact_after_drop branch_after_drop
//@ revisions: scopeguard_closure usize_index
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[overflow_arm] check-fail
//@[index_arm] check-fail
//@[div_arm] check-fail
//@[rem_arm] check-fail
//@[shift_arm] check-fail
//@[mul_arm] check-fail
//@[sub_arm] check-fail
//@[neg_arm] check-fail
//@[signed_local] check-fail
//@[u8_local] check-fail
//@[char_local] check-fail
//@[moved_guard] check-fail
//@[loop_body] check-fail
//@[loop_carried] check-fail
//@[option_guard] check-fail
//@[nested_option] check-fail
//@[user_enum] check-fail
//@[array_holder] check-fail
//@[generic_wrapper] check-fail
//@[outer_field] check-fail
//@[tuple_guard] check-fail
//@[two_drops] check-fail
//@[one_branch] check-fail
//@[branch_built] check-fail
//@[labeled_break] check-fail
//@[closure_owner] check-fail
//@[reassigned] check-fail
//@[wildcard_temp] check-fail
//@[double_ref] check-fail
//@[noop_guard] check-fail
//@[scopeguard_closure] check-fail
//@[usize_index] check-fail
//@[unrelated_drop] check-pass
//@[other_local] check-pass
//@[safe_arm] check-pass
//@[fact_after_drop] check-pass
//@[branch_after_drop] check-pass
//! **Drop glue's write must reach the interval environment (trust-interval-drop-havoc,
//! 2026-10-08).**
//!
//! The interval fixpoint forgot tracked names at `Call`, `TailCall` and `Opaque`
//! terminators but not at a `Drop`. Drop glue runs user code with `&mut` to the dropped
//! value and to everything mut-reachable from it, so the interval of `c` established
//! before the drop survived it, and the discharge reads the post-drop SSA version of `c`
//! through its bare-name fallback. In every check-fail revision below the guard's `Drop`
//! stores into `c`, and `c`'s stale interval made the `match`'s other arm look dead: its
//! obligation was DISCHARGED at generation, withheld from ay, and published
//! `runtime_checked`.
//!
//! # Before (main `de6288dddf`, probe rounds `dh-r1` and `dh-r2`)
//!
//! Each check-fail revision built rc=0 under the default policy and its driver panicked
//! (exit 101): add / sub / mul / neg / shift overflow, index out of bounds, division and
//! remainder by zero. The same write through a `Call` (`set(&mut c, k)`) was refuted.
//! `usize_index` and `scopeguard_closure` are from the later round `dx-r3` (2026-10-09, also
//! on main `4e95b0c512`): `usize_index` built rc=0 and panicked; `scopeguard_closure` was
//! refused for its guard's drop glue (unproven panic-freedom), its overflow discharged and
//! `runtime_checked`, never refuted.
//!
//! # After
//!
//! The interval transfer havocs at every terminator that writes a place, with the formula
//! path's own list, so the arm is live in the interval lane, the obligation reaches ay,
//! and ay refutes it. The check-pass controls: a drop that cannot reach `c` (never
//! borrowed) keeps its interval and the arm stays dead; a drop that writes `c` before an
//! arm that cannot fail has nothing to refute; a fact established AFTER the drop holds.
//! `noop_guard` is the precision the fix costs: a guard that holds `&mut c` and never
//! writes it is refused like a call that might (the formula path has no drop-glue
//! write-set refinement).

#![allow(unused)]

pub struct Setter<'a> {
    r: &'a mut u32,
    v: u32,
}

impl Drop for Setter<'_> {
    #[inline(never)]
    fn drop(&mut self) {
        *self.r = self.v;
    }
}

pub struct SetterU<'a> {
    r: &'a mut usize,
    v: usize,
}

impl Drop for SetterU<'_> {
    #[inline(never)]
    fn drop(&mut self) {
        *self.r = self.v;
    }
}

// The base shape.
#[cfg(overflow_arm)]
pub fn f(k: u32) -> u32 {
    //[overflow_arm]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let _s = Setter { r: &mut c, v: k };
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// The dead-looking arm indexes out of bounds.
#[cfg(index_arm)]
pub fn f(k: u32) -> u32 {
    //[index_arm]~^ NOTE [bounds] FAILED
    let a = [1u32, 2, 3, 4];
    let mut c = 0u32;
    {
        let _s = Setter { r: &mut c, v: k };
    }
    match c {
        0 => a[0],
        n => a[n as usize],
    }
}

// The stale interval is `[1, 1]`; the drop stores 0 and the other arm divides.
#[cfg(div_arm)]
pub fn f(k: u32) -> u32 {
    //[div_arm]~^ NOTE [divzero] FAILED
    let mut c = 1u32;
    {
        let _s = Setter { r: &mut c, v: k };
    }
    match c {
        1 => 100,
        n => 100 / n,
    }
}

// As `div_arm`, a remainder.
#[cfg(rem_arm)]
pub fn f(k: u32) -> u32 {
    //[rem_arm]~^ NOTE [remzero] FAILED
    let mut c = 1u32;
    {
        let _s = Setter { r: &mut c, v: k };
    }
    match c {
        1 => 0,
        n => 100 % n,
    }
}

// The dead-looking arm shifts by `c`.
#[cfg(shift_arm)]
pub fn f(k: u32) -> u32 {
    //[shift_arm]~^ NOTE [shift:left] FAILED
    let mut c = 0u32;
    {
        let _s = Setter { r: &mut c, v: k };
    }
    match c {
        0 => 1,
        n => 1u32 << n,
    }
}

// The dead-looking arm multiplies.
#[cfg(mul_arm)]
pub fn f(k: u32) -> u32 {
    //[mul_arm]~^ NOTE [overflow:mul] FAILED
    let mut c = 0u32;
    {
        let _s = Setter { r: &mut c, v: k };
    }
    match c {
        0 => 0,
        n => n * u32::MAX,
    }
}

// The dead-looking arm subtracts below zero.
#[cfg(sub_arm)]
pub fn f(k: u32) -> u32 {
    //[sub_arm]~^ NOTE [overflow:sub] FAILED
    let mut c = 0u32;
    {
        let _s = Setter { r: &mut c, v: k };
    }
    match c {
        0 => 0,
        n => 3u32 - n,
    }
}

// A signed local: the drop stores `i32::MIN` and the arm negates.
#[cfg(neg_arm)]
pub struct SetI<'a> {
    r: &'a mut i32,
    v: i32,
}

#[cfg(neg_arm)]
impl Drop for SetI<'_> {
    #[inline(never)]
    fn drop(&mut self) {
        *self.r = self.v;
    }
}

#[cfg(neg_arm)]
pub fn f(k: i32) -> i32 {
    //[neg_arm]~^ NOTE [negation] FAILED
    let mut c = 0i32;
    {
        let _s = SetI { r: &mut c, v: k };
    }
    match c {
        0 => 0,
        n => -n,
    }
}

// An `i64` local: the drop stores `-k` and the arm subtracts.
#[cfg(signed_local)]
pub struct SetterI<'a> {
    r: &'a mut i64,
    v: u32,
}

#[cfg(signed_local)]
impl Drop for SetterI<'_> {
    #[inline(never)]
    fn drop(&mut self) {
        *self.r = -(self.v as i64);
    }
}

#[cfg(signed_local)]
pub fn f(k: u32) -> u32 {
    //[signed_local]~^ NOTE [overflow:sub] FAILED
    let mut c = 0i64;
    {
        let _s = SetterI { r: &mut c, v: k };
    }
    match c {
        0 => 0,
        n => (n - i64::MAX) as u32,
    }
}

// A `u8` local.
#[cfg(u8_local)]
pub struct Set8<'a> {
    r: &'a mut u8,
    v: u8,
}

#[cfg(u8_local)]
impl Drop for Set8<'_> {
    #[inline(never)]
    fn drop(&mut self) {
        *self.r = self.v;
    }
}

#[cfg(u8_local)]
pub fn f(k: u8) -> u8 {
    //[u8_local]~^ NOTE [overflow:add] FAILED
    let mut c = 0u8;
    {
        let _s = Set8 { r: &mut c, v: k };
    }
    match c {
        0 => 0,
        n => n + u8::MAX,
    }
}

// A `char` local; the arm indexes by it.
#[cfg(char_local)]
pub struct SetC<'a> {
    r: &'a mut char,
    v: char,
}

#[cfg(char_local)]
impl Drop for SetC<'_> {
    #[inline(never)]
    fn drop(&mut self) {
        *self.r = self.v;
    }
}

#[cfg(char_local)]
pub fn f(k: char) -> u32 {
    //[char_local]~^ NOTE [bounds] FAILED
    let t = [1u32, 2, 3];
    let mut c = 'a';
    {
        let _s = SetC { r: &mut c, v: k };
    }
    match c {
        'a' => t[0],
        x => t[x as usize],
    }
}

// The guard is moved into an inner scope and dropped at that scope's end.
#[cfg(moved_guard)]
pub fn f(k: u32) -> u32 {
    //[moved_guard]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let g = Setter { r: &mut c, v: k };
    {
        let _g2 = g;
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// The guard is dropped at the end of a loop iteration; the read follows the loop.
#[cfg(loop_body)]
pub fn f(k: u32) -> u32 {
    //[loop_body]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut i = 0u32;
    while i < 1 {
        let _s = Setter { r: &mut c, v: k };
        i += 1;
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// Loop-carried: the drop at the end of one iteration writes `c`, the next iteration reads it.
#[cfg(loop_carried)]
pub fn f(k: u32) -> u32 {
    //[loop_carried]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < 2 {
        acc = match c {
            0 => acc,
            n => n + u32::MAX,
        };
        {
            let _s = Setter { r: &mut c, v: k };
        }
        i += 1;
    }
    acc
}

// The guard sits in an `Option`; the enum's drop glue runs `Setter::drop`.
#[cfg(option_guard)]
pub fn f(k: u32) -> u32 {
    //[option_guard]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let _s = Some(Setter { r: &mut c, v: k });
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// Two levels of enum drop glue.
#[cfg(nested_option)]
pub fn f(k: u32) -> u32 {
    //[nested_option]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let _s = Some(Some(Setter { r: &mut c, v: k }));
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// The guard sits in one variant of a user enum.
#[cfg(user_enum)]
pub enum E<'a> {
    A(Setter<'a>),
    B,
}

#[cfg(user_enum)]
pub fn f(k: u32) -> u32 {
    //[user_enum]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let _e = if k > 3 { E::A(Setter { r: &mut c, v: k }) } else { E::B };
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// The guard sits in an array.
#[cfg(array_holder)]
pub fn f(k: u32) -> u32 {
    //[array_holder]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let _a = [Setter { r: &mut c, v: k }];
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// The guard sits in a generic wrapper: generic drop glue.
#[cfg(generic_wrapper)]
pub struct W<T>(T);

#[cfg(generic_wrapper)]
pub fn f(k: u32) -> u32 {
    //[generic_wrapper]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let _w = W(Setter { r: &mut c, v: k });
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// The guard is a field of an outer struct; the outer drop glue drops it.
#[cfg(outer_field)]
pub struct Outer<'a> {
    tag: u8,
    inner: Setter<'a>,
}

#[cfg(outer_field)]
pub fn f(k: u32) -> u32 {
    //[outer_field]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let _o = Outer { tag: 1, inner: Setter { r: &mut c, v: k } };
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// Two guards in a tuple, both dropped at scope end.
#[cfg(tuple_guard)]
pub fn f(k: u32) -> u32 {
    //[tuple_guard]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    {
        let _t = (Setter { r: &mut c, v: k }, Setter { r: &mut d, v: 1 });
    }
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// The read follows two drops.
#[cfg(two_drops)]
pub fn f(k: u32) -> u32 {
    //[two_drops]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut e = 3u32;
    {
        let _a = Setter { r: &mut e, v: 3 };
        let _b = Setter { r: &mut c, v: k };
    }
    match c {
        0 => e,
        n => n + u32::MAX,
    }
}

// The guard exists, and is dropped, on one branch only.
#[cfg(one_branch)]
pub fn f(k: u32) -> u32 {
    //[one_branch]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    if k > 3 {
        let _s = Setter { r: &mut c, v: k };
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// The guard is built in one of two arms and dropped after the join.
#[cfg(branch_built)]
pub fn f(k: u32) -> u32 {
    //[branch_built]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    {
        let _g = if k > 3 { Setter { r: &mut c, v: k } } else { Setter { r: &mut d, v: 1 } };
    }
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// The guard is dropped on two exits of a labeled block.
#[cfg(labeled_break)]
pub fn f(k: u32) -> u32 {
    //[labeled_break]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    'a: {
        let _s = Setter { r: &mut c, v: k };
        if k > 100 {
            break 'a;
        }
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// A move closure owns the guard; dropping the closure runs `Setter::drop`.
#[cfg(closure_owner)]
pub fn f(k: u32) -> u32 {
    //[closure_owner]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let s = Setter { r: &mut c, v: k };
        let _cl = move || {
            let _ = &s;
        };
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// Reassigning the guard drops the old value.
#[cfg(reassigned)]
pub fn f(k: u32) -> u32 {
    //[reassigned]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let mut d = 0u32;
    let mut g = Setter { r: &mut c, v: k };
    g = Setter { r: &mut d, v: 1 };
    let _ = &g;
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// `let _ = <guard>`: the temporary is dropped at the end of the statement.
#[cfg(wildcard_temp)]
pub fn f(k: u32) -> u32 {
    //[wildcard_temp]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    let _ = Setter { r: &mut c, v: k };
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// The guard holds `&mut &mut u32`; the drop writes two levels down.
#[cfg(double_ref)]
pub struct S2<'a, 'b> {
    r: &'a mut &'b mut u32,
    v: u32,
}

#[cfg(double_ref)]
impl Drop for S2<'_, '_> {
    #[inline(never)]
    fn drop(&mut self) {
        **self.r = self.v;
    }
}

#[cfg(double_ref)]
pub fn f(k: u32) -> u32 {
    //[double_ref]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let mut p = &mut c;
        let _s = S2 { r: &mut p, v: k };
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// PRECISION COST, pinned so a refinement is noticed: the guard holds `&mut c` and its `Drop` never
// writes it. The program is correct; the havoc cannot know.
#[cfg(noop_guard)]
pub struct Holder<'a> {
    r: &'a mut u32,
}

#[cfg(noop_guard)]
impl Drop for Holder<'_> {
    #[inline(never)]
    fn drop(&mut self) {
        let _ = &self.r;
    }
}

#[cfg(noop_guard)]
pub fn f(k: u32) -> u32 {
    //[noop_guard]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let _s = Holder { r: &mut c };
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// The scopeguard / `defer` pattern: a generic guard runs a closure in `Drop`, and the
// closure captured `&mut c`. (On main this revision was refused too, but for the guard:
// drop glue with unproven panic-freedom keeps the function fail-closed. The overflow
// below was DISCHARGED and published `runtime_checked`, never refuted. The pin is the
// refutation.)
#[cfg(scopeguard_closure)]
pub struct OnDrop<F: FnMut()>(F);

#[cfg(scopeguard_closure)]
impl<F: FnMut()> Drop for OnDrop<F> {
    #[inline(never)]
    fn drop(&mut self) {
        (self.0)()
    }
}

#[cfg(scopeguard_closure)]
pub fn f(k: u32) -> u32 {
    //[scopeguard_closure]~^ NOTE [overflow:add] FAILED
    let mut c = 0u32;
    {
        let _g = OnDrop(|| c = k);
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// A `usize` index into a caller's array: the dead-looking arm indexes with the value the
// drop stored.
#[cfg(usize_index)]
pub fn f(k: usize, a: &[u32; 4]) -> u32 {
    //[usize_index]~^ NOTE [bounds] FAILED
    let mut i = 0usize;
    {
        let _s = SetterU { r: &mut i, v: k };
    }
    match i {
        0 => a[0],
        n => a[n],
    }
}

// CONTROL: a `String` drop cannot reach `c` (never borrowed), so `c` keeps its interval.
#[cfg(unrelated_drop)]
pub fn f(k: u32) -> u32 {
    let c = 0u32;
    {
        let _s = String::new();
    }
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// CONTROL: the guard writes `d`; `c` is never borrowed, so the havoc does not name it.
#[cfg(other_local)]
pub fn f(k: u32) -> u32 {
    let c = 0u32;
    let mut d = 0u32;
    {
        let _s = Setter { r: &mut d, v: k };
    }
    match c {
        0 => d,
        n => n + u32::MAX,
    }
}

// CONTROL: the drop writes `c`, and every arm is safe.
#[cfg(safe_arm)]
pub fn f(k: u32) -> u32 {
    let mut c = 0u32;
    {
        let _s = Setter { r: &mut c, v: k };
    }
    match c {
        0 => 0,
        n => n / 2,
    }
}

// CONTROL: `c` is assigned again after the drop.
#[cfg(fact_after_drop)]
pub fn f(k: u32) -> u32 {
    let mut c = 0u32;
    {
        let _s = Setter { r: &mut c, v: k };
    }
    c = 0;
    match c {
        0 => 0,
        n => n + u32::MAX,
    }
}

// CONTROL: the bound is established by a branch after the drop.
#[cfg(branch_after_drop)]
pub fn f(k: usize) -> u32 {
    let a = [1u32, 2, 3, 4];
    let mut c = 0usize;
    {
        let _s = SetterU { r: &mut c, v: k };
    }
    if c < 4 { a[c] } else { 0 }
}
