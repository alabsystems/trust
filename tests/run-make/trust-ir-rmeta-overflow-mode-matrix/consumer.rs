extern crate mode_dep;

pub fn use_mix(x: u32) -> u32 { mode_dep::mix(x) }
pub fn use_identity(x: u32) -> u32 { mode_dep::identity(x) }
pub fn use_inherited(x: u32) -> u32 { mode_dep::inherited(x) }
