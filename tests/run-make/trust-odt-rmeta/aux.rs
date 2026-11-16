// Trust: TG10 C1/C2 fixture; ordinary Rust remains valid for unsupported faces.
#![allow(dead_code)]

#[repr(i16)]
pub enum Decision {
    Zebra = -3,
    Alpha = if cfg!(changed) { 43 } else { 42 },
}

pub enum Empty {}
pub struct Unit;
pub struct Pair(pub u32, pub u32);
pub type Word = u32;
pub struct AllScalars {
    pub flag: bool,
    pub a: u8,
    pub b: u16,
    pub c: Word,
    pub d: u64,
    pub e: i8,
    pub f: i16,
    pub g: i32,
    pub h: i64,
    #[cfg(changed)]
    pub added: bool,
}

pub struct PointerWidth(pub usize);
pub struct SignedPointerWidth(pub isize);
pub struct Unicode(pub char);
pub struct Float32(pub f32);
pub struct Float64(pub f64);
pub struct WideUnsigned(pub u128);
pub struct WideSigned(pub i128);
pub struct Generic<T>(pub T);
pub enum Payload { A(u8) }
pub union Union { pub a: u8, pub b: u16 }
