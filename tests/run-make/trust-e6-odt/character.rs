// Trust: the legacy model's integer carrier cannot admit a source char.
#![allow(dead_code)]
#[repr(u8)]
pub enum Phase { Ready = 42, Waiting = 3 }
pub fn kernel(p: Phase, c: char) -> u8 { match p { Phase::Ready => 1, Phase::Waiting => 0 } }
clean {
    theorem not_in_slice : trust_import_character__kernel = trust_import_character__kernel := rfl
}
