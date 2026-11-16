//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ edition: 2021
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (step 2 increment 4b residuals): THE PRODUCER PLACES THE DROPS 4b ELIDED. Every body here
//! has a drop rustc's elaboration performs that 4b's planner refused — a live temporary, a
//! by-value pattern binding (moving part of its scrutinee out), a drop-and-replace through a
//! pointer — and the direct trust-ir now carries it, at the same point, as the
//! effect-conservation gate checks against the drop oracle (`drop_oracle.rs`). Before this change
//! each body was `Abstracted(drop, ..)` and strict refused it — so this file compiling under
//! strict IS the check that fails before the change (measured: every body below was refused by
//! the 4b producer, naming the planner's reason).
//!
//! What stays refused is pinned with its reason in `trust_ir_effect_conservation_drop_elided.rs`.

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

pub struct Guard(pub i32);

impl Drop for Guard {
    fn drop(&mut self) {
        unsafe { close(self.0) };
    }
}

pub struct Pair {
    pub held: Guard,
    pub n: u32,
}

#[inline(never)]
pub fn mk(fd: i32) -> Guard {
    Guard(fd)
}

#[inline(never)]
pub fn peek(g: &Guard) -> i32 {
    g.0
}

// ---- (1) live temporaries ----

/// A discarded value: the statement's temporary, dropped at the statement's end.
pub fn discard(fd: i32) -> i32 {
    mk(fd);
    fd + 1
}

/// A field read out of a temporary: the temporary is dropped at the end of its scope (the
/// body's, for a tail expression in edition 2021).
pub fn field_of_temp(fd: i32) -> i32 {
    mk(fd).0
}

/// A borrowed temporary (`Drop` impl, address observed): dropped at the end of the statement,
/// through the slot the callee received — the shared-borrow snapshot lane hands `peek` a copy of
/// the borrow's slot, and the placement proves that copy is the object's only home (the 4b
/// residuals review, DROPS-RES-5).
pub fn borrow_temp_stmt(fd: i32) -> i32 {
    let n = peek(&mk(fd));
    n + 1
}

/// The same temporary, live across an early return: dropped at the statement's end, and the
/// return that follows drops nothing of it.
pub fn temp_then_return(fd: i32, c: bool) -> i32 {
    let n = peek(&mk(fd));
    if c {
        return n;
    }
    n + 1
}

/// A temporary extended to the `let`'s scope: dropped at the end of the block.
pub fn extended(fd: i32) -> i32 {
    let g = &mk(fd);
    g.0
}

/// An autoref receiver: `String::len(&s.clone())`.
pub fn len_of_clone(s: &String) -> usize {
    s.clone().len()
}

/// A temporary the callee MUTATES through the borrow (`Cell`): the destructor must see the bumped
/// value, so the drop goes through the slot `bump` received. The first cut dropped the borrow's
/// own slot — the stale original — and strict accepted it (the gate never reads a drop's pointer);
/// the dump's text is pinned in `tests/run-make/trust-effect-conservation` (`cell_temp`).
pub fn cell_temp(fd: i32) -> i32 {
    let n = bump(&mk_counter(fd));
    n
}

/// Explicit nested reborrows keep the same owned temporary and destructor home.
pub fn cell_temp_nested_reborrow(fd: i32) -> i32 {
    bump(&*(&*(&mk_counter(fd))))
}

/// The autoref receiver of a `&self` method: the callee receives the borrow's slot itself.
pub fn cell_method(fd: i32) -> i32 {
    mk_counter(fd).tick()
}

pub struct Counter {
    pub hits: std::cell::Cell<i32>,
}

impl Drop for Counter {
    fn drop(&mut self) {
        unsafe { close(self.hits.get()) };
    }
}

impl Counter {
    #[inline(never)]
    pub fn tick(&self) -> i32 {
        self.hits.set(self.hits.get() + 1);
        0
    }
}

#[inline(never)]
pub fn mk_counter(fd: i32) -> Counter {
    Counter { hits: std::cell::Cell::new(fd) }
}

#[inline(never)]
pub fn bump(c: &Counter) -> i32 {
    c.hits.set(c.hits.get() + 1);
    0
}

// ---- (2) by-value pattern bindings ----

/// The binding moves the payload out of the parameter: the parameter's drop is OPEN and drops
/// nothing (the payload moved, `None` carries nothing); the binding is dropped at the arm's end.
pub fn take_some(o: Option<Guard>) -> i32 {
    match o {
        Some(g) => g.0,
        None => 0,
    }
}

/// The same through `if let`: the binding is dropped at the then-branch's end.
pub fn if_let_some(o: Option<Guard>) -> i32 {
    if let Some(g) = o { g.0 } else { 0 }
}

/// A destructuring `let`: every needs-drop field moved out, so the struct's open drop is dead.
pub fn destructure(p: Pair) -> i32 {
    let Pair { held, n } = p;
    held.0 + n as i32
}

// ---- (3) drop-and-replace through a pointer ----

/// The old `Guard` is dropped through `slot`, then the new one stored.
pub fn overwrite(slot: &mut Guard, fd: i32) {
    *slot = Guard(fd);
}
