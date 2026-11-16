//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency built with verification OFF, as `targo` builds every dependency
//! unit. Each item CALLS the callable it is handed, in a body with no verdict here:
//! a caller that hands it a `requires`-carrying function has no call site that
//! charges the clause. `assume_total_does_not_cover_callee_requires.rs`'s `sink_*`
//! and `value_*` revisions hand them `add1` from a body carrying
//! `#[trust::assume_total]`.

/// Calls the fn pointer it is handed (a non-generic parameter: no call that names
/// `apply` carries the callable in a type argument).
pub fn apply(f: fn(u32) -> u32, y: u32) -> u32 {
    f(y)
}

pub trait Tr {
    fn m(&self, y: u32) -> u32;
}

/// A generic impl over the callable, reached through `dyn Tr`: the unsizing coercion
/// that instantiates it is not a call.
pub struct Wrap<F>(pub F);

impl<F: Fn(u32) -> u32> Tr for Wrap<F> {
    fn m(&self, y: u32) -> u32 {
        (self.0)(y)
    }
}

/// A struct whose field is a NON-generic fn pointer: a value of it names no callable
/// in its TYPE, so only the value shows what it holds (the `value_*` revisions build it
/// in a promoted, a `const` or a `static`).
pub struct H {
    pub f: fn(u32) -> u32,
}

/// Calls the field of the `H` it is handed.
pub fn run_h(h: &H, y: u32) -> u32 {
    (h.f)(y)
}

/// The same, with the `H` handed by value.
pub fn run_h_val(h: H, y: u32) -> u32 {
    (h.f)(y)
}

/// A trait whose associated constant holds a fn pointer, and a function generic over
/// it that calls it: this crate evaluates `T::H` itself, so a caller's call names only
/// the type `T` (the `value_assoc_*` revisions implement it for a local type).
pub trait HasH {
    const H: H;
}

/// Calls the field of `T::H`.
pub fn run_assoc<T: HasH>(y: u32) -> u32 {
    (T::H.f)(y)
}

/// The same with the associated constant itself a fn pointer.
pub trait HasF {
    const F: fn(u32) -> u32;
}

/// Calls `T::F`.
pub fn run_f<T: HasF>(y: u32) -> u32 {
    (T::F)(y)
}

/// A trait with no associated constant and a blanket impl that reads `T::H`, reached
/// through `&dyn Run` (the `value_assoc_dyn_certify` revision): the unsizing coercion,
/// not a call, instantiates it with the caller's type.
pub trait Run {
    fn run(&self, y: u32) -> u32;
}

impl<T: HasH> Run for T {
    fn run(&self, y: u32) -> u32 {
        (T::H.f)(y)
    }
}

/// Calls `r.run(y)`: a non-generic function, so a call to it names no type.
pub fn run_dyn(r: &dyn Run, y: u32) -> u32 {
    r.run(y)
}

/// A guard whose drop glue reads `T::H` (the `value_assoc_drop_certify` revision): a
/// `Drop` terminator is not a call.
pub struct Guard<T: HasH> {
    pub y: u32,
    pub t: core::marker::PhantomData<T>,
}

impl<T: HasH> Drop for Guard<T> {
    fn drop(&mut self) {
        core::hint::black_box((T::H.f)(self.y));
    }
}

thread_local! {
    /// A thread-local: `COUNTER.with(..)` reads a static `LocalKey` whose accessor is a
    /// closure this crate coerces to a fn pointer (the `thread_local_certify` revision).
    pub static COUNTER: std::cell::Cell<u32> = const { std::cell::Cell::new(7) };
}

/// A static table holding a closure this crate coerces to a fn pointer (the
/// `closure_table_certify` revision): the closure captures nothing and is no
/// `requires`-carrying function.
pub static TABLE: H = H { f: |x| x.wrapping_add(1) };

/// A closure coerced to a fn pointer inside a GENERIC impl's associated constant: its
/// parent's type argument `F` is what it was instantiated with (the
/// `closure_value_mutant_certify` revision instantiates it with a fn pointer).
pub struct G<F>(pub F);

impl<F> G<F> {
    pub const H: H = H { f: |x| x };
}

// Trust (2026-10-03, the minting-site seam): the METHOD routes and the generic hops of
// `assume_total_does_not_cover_callee_requires.rs` and
// `requires_value_minted_outside_verified_body.rs`. Each item hands on, or calls, what
// the caller's impl or type argument supplies.

/// A trait whose method returns a fn pointer, and a function generic over it that calls
/// it (`method_const_certify`, `method_static_certify`, `method_reify_certify`).
pub trait HasG {
    fn g() -> fn(u32) -> u32;
}

/// Calls `T::g()`.
pub fn run_g<T: HasG>(y: u32) -> u32 {
    T::g()(y)
}

/// The same with the method returning a `&'static H` (`method_promoted_certify`).
pub trait HasGH {
    fn g() -> &'static H;
}

/// Calls the field of `T::g()`.
pub fn run_gh<T: HasGH>(y: u32) -> u32 {
    (T::g().f)(y)
}

/// The same with the method returning an opaque type, an RPITIT
/// (`method_rpitit_certify`).
pub trait HasGI {
    fn g() -> impl Fn(u32) -> u32;
}

/// Calls the value `T::g()` returns.
pub fn run_gi<T: HasGI>(y: u32) -> u32 {
    T::g()(y)
}

/// Calls the zero-sized function item `F` without being handed one: it conjures the
/// value (`F` is zero-sized for a function item) and calls it. Its pointer is what
/// `mk_h` and `KH::V` mint for a caller's `F`.
pub fn tramp<F: Fn(u32) -> u32>(x: u32) -> u32 {
    let f: F = unsafe { core::mem::zeroed() };
    f(x)
}

/// A generic `const fn` that turns the callable it is handed into an `H` whose field
/// calls it (`const_call_hop_certify`: `static HH: sink::H = sink::mk_h(add1)`, rule 1
/// in an initializer).
pub const fn mk_h<F: Fn(u32) -> u32>(f: F) -> H {
    core::mem::forget(f);
    H { f: tramp::<F> }
}

/// A generic associated constant that mints the pointer for its type argument
/// (`generic_const_arg_certify`: `sink::KH::<_>::V` instantiated with `add1`, rule 4).
pub struct KH<F>(pub Option<F>, pub H);

impl<F: Fn(u32) -> u32> KH<F> {
    pub const V: KH<F> = KH(None, H { f: tramp::<F> });
}
