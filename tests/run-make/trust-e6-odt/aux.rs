// Trust: these faces cross rmeta before the local E6 consumer reads them.
#[repr(u8)]
pub enum Phase { Ready = 42, Waiting = 3 }
pub struct Row { pub right: bool, pub left: bool }
#[repr(u8)]
pub enum Single { Only = 13 }
