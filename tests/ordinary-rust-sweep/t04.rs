pub enum E {
    Io,
    Parse(u32),
}
pub fn code(e: &E) -> u32 {
    match e {
        E::Io => 1,
        E::Parse(n) => *n,
    }
}
