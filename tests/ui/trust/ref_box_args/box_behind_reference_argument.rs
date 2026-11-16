//@ needs-trust-verify
//@ edition: 2021
//@ revisions: shared mut_ref field packed two zero_row opt node_next node_next_mut caller_spends zero_row_caller evil readdrop forge opt_lend node_next_lend node_next_copy double manually_drop maybe_uninit union raw lend refcell ref_addr_of_sink owned_addr_of_sink owned_nonnull ref_nonnull
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[caller_spends] compile-flags: -Ztrust-policy=certify
//@[zero_row_caller] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[shared] check-pass
//@[mut_ref] check-pass
//@[field] check-pass
//@[packed] check-pass
//@[two] check-pass
//@[zero_row] check-pass
//@[opt] check-pass
//@[node_next] check-pass
//@[node_next_mut] check-pass
//@[double] check-pass
//@[caller_spends] check-fail
//@[zero_row_caller] check-fail
//@[evil] check-fail
//@[readdrop] check-fail
//@[forge] check-fail
//@[opt_lend] check-fail
//@[node_next_lend] check-fail
//@[node_next_copy] check-fail
//@[manually_drop] check-fail
//@[maybe_uninit] check-fail
//@[union] check-fail
//@[raw] check-fail
//@[lend] check-fail
//@[refcell] check-fail
//@[ref_addr_of_sink] check-fail
//@[owned_addr_of_sink] check-fail
//@[owned_nonnull] check-fail
//@[ref_nonnull] check-fail
//@[evil] forbid-output: argument-validity premise
//@[readdrop] forbid-output: argument-validity premise
//@[forge] forbid-output: argument-validity premise
//@[opt_lend] forbid-output: argument-validity premise
//@[node_next_lend] forbid-output: argument-validity premise
//@[node_next_copy] forbid-output: argument-validity premise
//@[manually_drop] forbid-output: argument-validity premise
//@[maybe_uninit] forbid-output: argument-validity premise
//@[union] forbid-output: argument-validity premise
//@[raw] forbid-output: argument-validity premise
//@[lend] forbid-output: argument-validity premise
//@[refcell] forbid-output: argument-validity premise
//@[ref_addr_of_sink] forbid-output: argument-validity premise
//! D14 REFERENCE_ARG_BOX_VALID (2026-10-09): a `Box` stored in a reference
//! ARGUMENT's pointee is valid and live for the call, so the compiler-synthesized
//! `*box` of a copy of it is the `&T`-like deref it is and mints no
//! `[unsafe:sep:*]` rows. Before, each passing revision failed the default build on
//! those rows. The premise is not proved anywhere: it is disclosed, and no caller
//! spends the verdict (`caller_spends`, `zero_row_caller` under `certify` stay
//! refused). Unlike D15 the premise REMOVES rows, so a body left with no rows keeps
//! its marker (`zero_row_caller`). The rows it leaves are graded per row (2026-10-17,
//! gate RCA "premise"): a row whose VC the premise-free generation reproduces byte
//! for byte keeps its kernel certificate. Removing a deref's rows changes no other
//! row's VC, so every row of each passing revision is certified (the `of which N
//! kernel-certified` notes, N = every proved row); until 2026-10-17 every row of the
//! body was demoted (`forbid-output: kernel-certified`), which withheld proofs that
//! never used the premise.
//!
//! Every other revision must stay refused AND must not install the premise:
//! `evil` hands the box slot to a callee that `ptr::read`s a duplicate and drops
//! it (a real use-after-free with no write to `*b`); `readdrop` does it in the
//! body; `forge` writes an invalid box through a raw cast of a `&mut` argument; the
//! `ManuallyDrop`, `MaybeUninit`, union and raw-pointer shapes carry no validity
//! guarantee or reach the box through a call; `lend` is the disclosed
//! over-refusal (a shared hand-out of the box to a harmless callee is refused
//! because a duplicating callee looks the same from here); `refcell` reaches the
//! box through interior mutability.
//!
//! Review round 85: `ref_addr_of_sink` and `owned_addr_of_sink` hand a RAW
//! pointer to the box's allocation (it carries the box's own tag) to a callee that
//! `Box::from_raw`s and drops it; a LATER `*box` (its own pointer temp) then reads
//! freed memory. Every box root rests on a body-wide fence over all synthesized
//! box-pointer temps, so `f` must stay refused in both, the owned one included
//! (the parameter root dropped its rows before this round). `zero_row` is the
//! premise leaving no row at all (`**b` on `&Box<u32>`, whose debug UB-check
//! address comparisons the fence admits); it builds with the premise disclosed.
//! Review round 86: `owned_nonnull` and `ref_nonnull` pass `&mut *b` to a SAFE
//! sysroot callee (`NonNull::from`) whose RESULT carries the pointer out; the
//! callee's protector ends at its return, so `sink` frees the allocation with no
//! UB of its own. A `&mut` reborrow is admitted only when every derived pointer
//! stays contained.
//!
//! Sweep c67 (2026-10-11): a SHARED local reborrow of a part of the argument's
//! pointee (`if let Some(b) = o`, `match &n.next { Some(b) => b.val }`) names the
//! same box, and is admitted when every link of the chain is confined the way the
//! argument is (`sep_engine::shared_pointee_alias_is_confined`): `opt` (refused
//! before, as a shape limit) and the recursive `node_next`/`node_next_mut` pass.
//! The chain must not escape: `opt_lend` and `node_next_lend` hand the binding to
//! a callee that `ptr::read`s a duplicate of the box and drops it, and
//! `node_next_copy` copies the binding out of the chain.
//!
//! D100 (2026-10-14): main's 13c reference lane, merged on 2026-10-14, roots a box
//! through a reference argument by its own fences, and such a root rests on this
//! same premise (owner ruling R1: one premise, one grade). It is now admitted only
//! under the installed premise, so it is graded and disclosed like D14's shapes.
//! `double` (`&&Box`) was refused here as a D14 v1 shape limit (two `Deref`s); 13c
//! roots it, so its expectation moved from "refused, no premise" to "builds, premise
//! disclosed" (and, since 2026-10-17, its two remaining rows kernel-certified).

#[cfg(shared)]
pub fn f(b: &Box<[u32]>, i: usize) -> u32 {
    //[shared]~^ NOTE Trust argument-validity premise REFERENCE_ARG_BOX_VALID
    //[shared]~| NOTE of which 2 kernel-certified by the clean CIC kernel
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(mut_ref)]
pub fn f(b: &mut Box<[u32]>, i: usize) -> u32 {
    //[mut_ref]~^ NOTE of which 2 kernel-certified by the clean CIC kernel
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(field)]
pub struct S {
    pub n: usize,
    pub b: Box<[u32]>,
}

#[cfg(field)]
pub fn f(s: &S, i: usize) -> u32 {
    //[field]~^ NOTE of which 2 kernel-certified by the clean CIC kernel
    if i < s.b.len() { s.b[i] } else { s.n as u32 }
}

#[cfg(packed)]
#[repr(C, packed)]
pub struct P {
    pub a: u8,
    pub b: Box<[u32]>,
}

#[cfg(packed)]
pub fn f(p: &P, i: usize) -> u32 {
    //[packed]~^ NOTE of which 2 kernel-certified by the clean CIC kernel
    if i < p.b.len() { p.b[i] } else { 0 }
}

#[cfg(two)]
pub fn f(a: &Box<[u32]>, b: &Box<[u32]>, i: usize) -> u32 {
    //[two]~^ NOTE of which 5 kernel-certified by the clean CIC kernel
    if i < a.len() && i < b.len() { a[i] / 2 + b[i] / 2 } else { 0 }
}

#[cfg(caller_spends)]
fn g(b: &Box<[u32]>, i: usize) -> u32 {
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(caller_spends)]
pub fn h(b: &Box<[u32]>, i: usize) -> u32 {
    g(b, i)
}

#[cfg(zero_row_caller)]
fn g(b: &Box<u32>) -> u32 {
    **b
}

#[cfg(zero_row_caller)]
pub fn h(b: &Box<u32>) -> u32 {
    g(b)
}

#[cfg(evil)]
fn evil(b: &Box<[u32]>) {
    let dup: Box<[u32]> = unsafe { std::ptr::read(b) };
    drop(dup);
}

#[cfg(evil)]
pub fn f(b: &Box<[u32]>, i: usize) -> u32 {
    evil(b);
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(readdrop)]
pub fn f(b: &Box<[u32]>, i: usize) -> u32 {
    let dup: Box<[u32]> = unsafe { std::ptr::read(b) };
    drop(dup);
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(forge)]
pub fn f(b: &mut Box<[u32]>, i: usize) -> u32 {
    unsafe {
        *(b as *mut Box<[u32]> as *mut usize) = 8;
    }
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(opt)]
pub fn f(o: &Option<Box<[u32]>>, i: usize) -> u32 {
    //[opt]~^ NOTE of which 3 kernel-certified by the clean CIC kernel
    if let Some(b) = o {
        if i < b.len() {
            return b[i];
        }
    }
    0
}

#[cfg(opt_lend)]
fn evil(b: &Box<[u32]>) {
    let dup: Box<[u32]> = unsafe { std::ptr::read(b) };
    drop(dup);
}

#[cfg(opt_lend)]
pub fn f(o: &Option<Box<[u32]>>, i: usize) -> u32 {
    if let Some(b) = o {
        evil(b);
        if i < b.len() {
            return b[i];
        }
    }
    0
}

#[cfg(any(node_next, node_next_mut, node_next_lend, node_next_copy))]
pub struct Node {
    pub val: u32,
    pub next: Option<Box<Node>>,
}

#[cfg(node_next)]
pub fn second(n: &Node) -> Option<u32> {
    //[node_next]~^ NOTE of which 2 kernel-certified by the clean CIC kernel
    match &n.next {
        Some(b) => Some(b.val),
        None => None,
    }
}

#[cfg(node_next_mut)]
pub fn second(n: &mut Node) -> Option<u32> {
    //[node_next_mut]~^ NOTE of which 2 kernel-certified by the clean CIC kernel
    match &n.next {
        Some(b) => Some(b.val),
        None => None,
    }
}

#[cfg(node_next_lend)]
fn evil(b: &Box<Node>) {
    let dup: Box<Node> = unsafe { std::ptr::read(b) };
    drop(dup);
}

#[cfg(node_next_lend)]
pub fn second(n: &Node) -> Option<u32> {
    match &n.next {
        Some(b) => {
            evil(b);
            Some(b.val)
        }
        None => None,
    }
}

#[cfg(node_next_copy)]
pub fn second<'a>(n: &'a Node, out: &mut Option<&'a Box<Node>>) -> Option<u32> {
    match &n.next {
        Some(b) => {
            *out = Some(b);
            Some(b.val)
        }
        None => None,
    }
}

#[cfg(double)]
pub fn f(b: &&Box<[u32]>, i: usize) -> u32 {
    //[double]~^ NOTE Trust argument-validity premise REFERENCE_ARG_BOX_VALID
    //[double]~| NOTE of which 2 kernel-certified by the clean CIC kernel
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(manually_drop)]
pub fn f(b: &std::mem::ManuallyDrop<Box<[u32]>>, i: usize) -> u32 {
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(maybe_uninit)]
pub fn f(b: &std::mem::MaybeUninit<Box<[u32]>>, i: usize) -> u32 {
    let r = unsafe { b.assume_init_ref() };
    if i < r.len() { r[i] } else { 0 }
}

#[cfg(union)]
pub union U {
    pub b: std::mem::ManuallyDrop<Box<[u32]>>,
    pub x: usize,
}

#[cfg(union)]
pub fn f(u: &U, i: usize) -> u32 {
    let r: &Box<[u32]> = unsafe { &u.b };
    if i < r.len() { r[i] } else { 0 }
}

#[cfg(raw)]
pub unsafe fn f(p: *const Box<[u32]>, i: usize) -> u32 {
    unsafe { if i < (*p).len() { (*p)[i] } else { 0 } }
}

#[cfg(lend)]
fn look(_b: &Box<[u32]>) {}

#[cfg(lend)]
pub fn f(b: &Box<[u32]>, i: usize) -> u32 {
    look(b);
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(refcell)]
pub fn f(c: &std::cell::RefCell<Box<[u32]>>, i: usize) -> u32 {
    let b = c.borrow();
    if i < b.len() { b[i] } else { 0 }
}

#[cfg(zero_row)]
pub fn g(b: &Box<u32>) -> u32 {
    //[zero_row]~^ NOTE Trust argument-validity premise REFERENCE_ARG_BOX_VALID
    //[zero_row]~| NOTE of which 1 kernel-certified by the clean CIC kernel
    **b
}

#[cfg(any(ref_addr_of_sink, owned_addr_of_sink, owned_nonnull, ref_nonnull))]
fn sink(p: *const u32) {
    unsafe { drop(Box::from_raw(p as *mut u32)) }
}

#[cfg(ref_addr_of_sink)]
pub fn f(b: &Box<u32>) -> u32 {
    //[ref_addr_of_sink]~^ ERROR Trust strict verification failed for `box_behind_reference_argument::f`
    sink(std::ptr::addr_of!(**b));
    **b / 2
}

#[cfg(owned_addr_of_sink)]
pub fn f(b: Box<u32>) -> u32 {
    //[owned_addr_of_sink]~^ ERROR Trust strict verification failed for `box_behind_reference_argument::f`
    sink(std::ptr::addr_of!(*b));
    *b / 2
}

#[cfg(owned_nonnull)]
pub fn f(mut b: Box<u32>) -> u32 {
    //[owned_nonnull]~^ ERROR Trust strict verification failed for `box_behind_reference_argument::f`
    let n = core::ptr::NonNull::from(&mut *b);
    sink(n.as_ptr());
    *b / 2
}

#[cfg(ref_nonnull)]
pub fn f(b: &mut Box<u32>) -> u32 {
    //[ref_nonnull]~^ ERROR Trust strict verification failed for `box_behind_reference_argument::f`
    let n = core::ptr::NonNull::from(&mut **b);
    sink(n.as_ptr());
    **b / 2
}
