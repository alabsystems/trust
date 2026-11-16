pub enum St {
    A,
    B,
}
pub fn step(s: St) -> St {
    match s {
        St::A => St::B,
        St::B => St::A,
    }
}
