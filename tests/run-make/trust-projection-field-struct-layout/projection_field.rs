#![feature(type_alias_impl_trait)]
#![allow(dead_code)]
use std::cell::UnsafeCell;
use std::ptr::NonNull;

// L1: a local struct whose field is a monomorphic associated-type projection
// (`core::sync::atomic::Atomic<T>`'s `UnsafeCell<T::Storage>`).
pub trait Prim { type Storage; }
#[repr(C, align(1))]
pub struct Align1<T>(T);
impl Prim for u8 { type Storage = Align1<u8>; }
impl Prim for bool { type Storage = Align1<u8>; }
pub struct Atomicish<T: Prim> { v: UnsafeCell<<T as Prim>::Storage> }
pub fn new_u8(v: u8) -> Atomicish<u8> { Atomicish { v: UnsafeCell::new(Align1(v)) } }
pub fn by_value(a: Atomicish<bool>) -> Atomicish<bool> { a }

// L3: a local ADT reached under a fn-pointer binder (`NonNull<fmt::rt::Argument<'_>>`).
pub struct Fm<'a> { buf: &'a mut u32, n: u32 }
pub struct Arg<'a> { f: fn(&mut Fm<'_>) -> u32, p: &'a u8 }
pub struct H<'a> { a: NonNull<Arg<'a>>, n: usize }
pub fn h(x: H<'_>) -> usize { x.n }

// The impl's value carries an unevaluated constant. fix11 (L2): a constant whose whole CTFE
// closure is leaf (`LEN`, a literal) is read as its value, so this one now lays out; the decline
// control is a constant that CALLS (`len2()`), whose evaluation would build a body from inside
// `mir_built`.
const LEN: usize = 2;
impl Prim for u16 { type Storage = [u8; LEN]; }
pub fn by_value_const(a: Atomicish<u16>) -> Atomicish<u16> { a }
const fn len2() -> usize { 2 }
impl Prim for i16 { type Storage = [u8; len2()]; }
pub fn by_value_call(a: Atomicish<i16>) -> Atomicish<i16> { a }

// Inside an opaque's defining scope: a projection selected over a local ADT whose field is the
// opaque, and a projection whose impl value IS the opaque. Neither may be read (a reveal of
// `Tait` there is `type_of(Tait)` -> borrowck of `define`, the body being built: E0391).
pub type Tait = impl Sized;
pub struct W { x: Tait }
impl Prim for W { type Storage = u8; }
impl Prim for u32 { type Storage = Tait; }
#[define_opaque(Tait)]
pub fn define() -> Tait {
    let c = |a: &Atomicish<W>, b: Atomicish<u32>| {
        let _ = b;
        a.v.get() as usize
    };
    let _ = c;
    0u32
}
