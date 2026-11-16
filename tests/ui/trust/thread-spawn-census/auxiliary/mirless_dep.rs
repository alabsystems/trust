//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency whose plain functions carry no MIR in its metadata (no
//! `-Zalways-encode-mir`): the consuming crate's census cannot walk them (R2).
//! Its `#[inline]` and generic code does carry MIR.

#[inline(never)]
pub fn make_string(n: usize) -> String {
    let mut s = String::with_capacity(n);
    for i in 0..n {
        s.push((b'a' + (i % 26) as u8) as char);
    }
    s
}

#[inline(never)]
pub fn checked(v: &[u8], i: usize) -> u8 {
    if i >= v.len() {
        panic!("out of range {i}")
    }
    v[i]
}

static mut SLOT: Option<fn()> = None;

#[inline(never)]
pub fn register(f: fn()) {
    unsafe { SLOT = Some(f) }
}

#[inline(never)]
pub fn run() {
    if let Some(f) = unsafe { SLOT } {
        f()
    }
}

#[inline]
pub fn inline_spawner() {
    let _handle = std::thread::spawn(|| {});
}

#[inline(never)]
pub fn get() -> fn() {
    inline_spawner
}

pub struct Gen<T>(pub T);

pub trait Tr {
    fn run(&self);
}

impl<T> Tr for Gen<T> {
    fn run(&self) {
        let _handle = std::thread::spawn(|| {});
    }
}

#[inline(never)]
pub fn get_dyn() -> Box<dyn Tr> {
    Box::new(Gen(0u8))
}
