// Program-index fixture: hello world with an unguarded assertion obligation.
//
// The program prints the same runtime output as the good variant for the sample
// main input, but the helper is proof-flawed for unconstrained callers.

fn greeting() -> &'static str {
    "hello world"
}

fn require_nonnegative(x: i32) -> i32 {
    assert!(x >= 0);
    x
}

fn main() {
    println!("{}", greeting());
    let _ = require_nonnegative(4);
}
