#![allow(dead_code)]

pub struct Index {
    value: u32,
}

impl Index {
    pub fn value(&self) -> u32 {
        self.value
    }
}

// Either fat payload makes the containing enum enter the opaque match lane.
// The Unnamed arm still has a real &Index receiver in Rust.
pub enum SliceMember<'a> {
    Slice(&'a [u8]),
    Unnamed(Index),
}

pub fn fat_slice_read(member: &SliceMember<'_>) -> u32 {
    match member {
        SliceMember::Slice(_) => 0,
        SliceMember::Unnamed(index) => index.value(),
    }
}

pub enum DynMember<'a> {
    Display(&'a dyn core::fmt::Display),
    Unnamed(Index),
}

pub fn fat_dyn_read(member: &DynMember<'_>) -> u32 {
    match member {
        DynMember::Display(_) => 0,
        DynMember::Unnamed(index) => index.value(),
    }
}

pub enum ThinMember {
    Named(u32),
    Unnamed(Index),
}

pub fn thin_read(member: &ThinMember) -> u32 {
    match member {
        ThinMember::Named(value) => *value,
        ThinMember::Unnamed(index) => index.value(),
    }
}

pub fn accept_unit(_: ()) -> u32 {
    7
}

pub fn unit_argument() -> u32 {
    accept_unit(())
}
