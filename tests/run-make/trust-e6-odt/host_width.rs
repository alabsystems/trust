// Trust: the legacy model's integer carrier cannot admit a source usize.
#![allow(dead_code)]
#[repr(u8)]
pub enum Phase { Ready = 42, Waiting = 3 }
pub fn kernel(p: Phase) -> usize { match p { Phase::Ready => 1, Phase::Waiting => 0 } }
clean {
    theorem not_in_slice : trust_import_host_width__kernel = trust_import_host_width__kernel := rfl
}
