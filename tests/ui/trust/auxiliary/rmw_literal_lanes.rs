//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! External fields keep the RMW builder on its actual placeholder-registration
//! path: the ordinary-registration preference applies only to local structs.

use std::collections::HashMap;

pub struct ExternalInstantiator {
    pub quantifier: u32,
    pub bound: HashMap<String, u32>,
    pub is_forall: bool,
}

pub struct ExternalBuffered {
    pub q: u32,
    pub items: Vec<u32>,
    pub open: bool,
}

pub struct ExternalBorrowing<'a> {
    pub n: u32,
    pub r: &'a u32,
}

pub struct ExternalNamed {
    pub n: u32,
    pub label: Option<String>,
}

pub struct ExternalBoxed {
    pub n: u32,
    pub b: Option<Box<u32>>,
}

pub struct ExternalZeroLen {
    pub n: u32,
    pub z: [String; 0],
}

pub enum ExternalDeclined {
    A((u8, u16)),
    B,
}

pub struct ExternalH {
    pub n: u32,
    pub e: ExternalDeclined,
}

pub struct ExternalG<T> {
    pub n: u32,
    pub t: T,
}

pub struct ExternalTagged {
    pub n: u32,
    pub o: Option<(u8, ExternalDeclined)>,
}
