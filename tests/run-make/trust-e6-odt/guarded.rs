// Trust: true guard is deliberately erased at -O; HIR must still refuse it.
#![allow(dead_code)]
#[repr(u8)]
pub enum Phase { Ready = 42, Waiting = 3 }
pub fn kernel(p: Phase) -> bool {
    match p { Phase::Ready if true => true, _ => false }
}
clean {
    theorem impossible : trust_import_guarded__kernel = trust_import_guarded__kernel := rfl
}
