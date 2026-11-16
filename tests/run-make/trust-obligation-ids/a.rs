// The base program of trust-obligation-ids; b.rs is this program edited.

pub fn div_index(xs: &[u64], i: usize, d: u64) -> u64 {
    xs[i] / d
}

pub fn add3(a: u64, b: u64, c: u64) -> u64 {
    a + b + c
}

pub fn f(a: u64, b: u64) -> u64 {
    let x = a / b;
    let y = x * 3;
    let z = a * 5;
    y + a + z
}

macro_rules! halve {
    ($x:expr, $d:expr) => {
        $x / $d
    };
}

pub fn macro_div(a: u64, d: u64) -> u64 {
    halve!(a, d)
}
