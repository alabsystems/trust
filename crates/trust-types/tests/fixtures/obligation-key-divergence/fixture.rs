// Item-0.4 obligation-key divergence probe (tracks plan §3.2.1 / item 0.4).
// f1: authored contract (requires+ensures) AND two safety VCs (index + division).
pub fn contract_div_index(xs: &[u64], i: usize, d: u64) -> u64
    requires d > 0
    ensures result >= 0
{
    xs[i] / d
}

// f2: nested-`+` collision fixture (§3.2.1) — TWO `+` operators in one
// expression, which suffices for the same-kind-same-LO collision this probe
// measures. (The plan's list names "three `+`"; two already collide, and the
// third adds no new anchor class.)
pub fn add3(a: u64, b: u64, c: u64) -> u64 {
    a + b + c
}

// f3: a macro-expanded safety VC — measures the callsite-vs-raw span policy
// divergence ON an obligation (not just on debug info).
macro_rules! halve {
    ($x:expr, $d:expr) => {
        $x / $d
    };
}
pub fn macro_div(a: u64, d: u64) -> u64 {
    halve!(a, d)
}
