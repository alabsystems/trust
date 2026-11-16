//@ revisions: union tuple wrapper array reference slice static_value static_field static_closure
//@ revisions: returned
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Spawn census, typed LAUNDER route S (design §10): a fn pointer called at
//! another fn-pointer type of a matching shape reads the caller's arguments
//! at its parameter types and its return value at the caller's. `put` stores
//! `launch` through a `&mut Option<fn()>`; called as a `Reshaped`, whose first
//! parameter is a `&mut usize` (references are ABI-compatible whatever their
//! pointees, so the call is defined), it writes `launch`'s fn pointer into an
//! integer, with no cast in sight. Route S was recorded only for a transmute
//! of one fn-pointer type to another; it is structural now: wherever two
//! fn-pointer types of a matching shape share bytes, their argument and
//! return types are views of each other.
//!
//! * `union`: a union of the two fn-pointer types (route U);
//! * `tuple`, `wrapper`, `array`: a transmute of a tuple, a
//!   `repr(transparent)` wrapper or an array holding one (route V's types);
//! * `reference`, `slice`: a transmute of a reference to one, or of a slice
//!   of them (route P);
//! * `static_value`, `static_field`, `static_closure`: a static's bytes hold `put`
//!   (or a closure) at a `Reshaped` position (route C);
//! * `returned`: the return direction: `get` returns `&'static fn()`, called
//!   as returning `&'static usize`.
//!
//! The crate has no value LAUNDER, `hand` gives the integer to C, which may
//! call it back, and `launch` spawns: `hand` is INDIRECT in every revision.

#![allow(dead_code)]

extern "C" {
    fn c_call_back(n: usize);
}

fn launch() {
    let _handle = std::thread::spawn(|| {});
}

// Extra parameters give the reshaped call a shape no std callable has.
fn put(p: &mut Option<fn()>, _: i8, _: u128, _: i16) {
    *p = Some(launch)
}

type Put = fn(&mut Option<fn()>, i8, u128, i16);
type Reshaped = fn(&mut usize, i8, u128, i16);

#[cfg(union)]
union Either {
    put: Put,
    reshaped: Reshaped,
}

#[cfg(wrapper)]
#[repr(transparent)]
struct PutWrapper(Put);

#[cfg(wrapper)]
#[repr(transparent)]
struct ReshapedWrapper(Reshaped);

#[cfg(static_value)]
static RESHAPED: Reshaped = unsafe { std::mem::transmute::<Put, Reshaped>(put) };

#[cfg(static_field)]
struct Holder(Reshaped);

#[cfg(static_field)]
static HOLDER: Holder = Holder(unsafe { std::mem::transmute::<Put, Reshaped>(put) });

#[cfg(static_closure)]
static RESHAPED: Reshaped = unsafe {
    std::mem::transmute::<Put, Reshaped>(|p: &mut Option<fn()>, _: i8, _: u128, _: i16| {
        *p = Some(launch)
    })
};

#[cfg(not(returned))]
pub fn keep() -> usize {
    let mut n = 0usize;
    #[cfg(union)]
    let reshaped = unsafe { Either { put }.reshaped };
    #[cfg(tuple)]
    let reshaped = unsafe { std::mem::transmute::<(Put,), (Reshaped,)>((put,)) }.0;
    #[cfg(wrapper)]
    let reshaped = unsafe { std::mem::transmute::<PutWrapper, ReshapedWrapper>(PutWrapper(put)) }.0;
    #[cfg(array)]
    let [reshaped] = unsafe { std::mem::transmute::<[Put; 1], [Reshaped; 1]>([put]) };
    #[cfg(reference)]
    let reshaped = {
        let put: Put = put;
        unsafe { *std::mem::transmute::<&Put, &Reshaped>(&put) }
    };
    #[cfg(slice)]
    let reshaped = {
        let puts: [Put; 1] = [put];
        let reshaped = unsafe { std::mem::transmute::<&[Put], &[Reshaped]>(&puts[..]) };
        reshaped[0]
    };
    #[cfg(any(static_value, static_closure))]
    let reshaped = RESHAPED;
    #[cfg(static_field)]
    let reshaped = HOLDER.0;
    reshaped(&mut n, 0, 0, 0);
    n
}

#[cfg(returned)]
static FN: fn() = launch;

#[cfg(returned)]
fn get(_: i8, _: u128, _: i16) -> &'static fn() {
    &FN
}

#[cfg(returned)]
pub fn keep() -> usize {
    let (get_usize,) = unsafe {
        std::mem::transmute::<
            (fn(i8, u128, i16) -> &'static fn(),),
            (fn(i8, u128, i16) -> &'static usize,),
        >((get,))
    };
    *get_usize(0, 0, 0)
}

pub fn hand(n: usize) { //~ NOTE may spawn (indirect)
    unsafe { c_call_back(n) }
}
