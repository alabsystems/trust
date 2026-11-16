// Trust: ordinary Rust exhaustiveness is retained before E6 admission.
#[repr(u8)]
pub enum Phase { Ready = 42, Waiting = 3 }
pub fn kernel(p: Phase) -> bool { match p { Phase::Ready => true } }
