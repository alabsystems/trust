pub enum E { A(u32), B } pub fn f(e: &E) -> u32 { match e { E::A(v) => *v, E::B => 0 } }
