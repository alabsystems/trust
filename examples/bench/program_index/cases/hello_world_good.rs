// Program-index fixture: hello world with a guarded assertion obligation.
//
// This keeps a real stdout surface in the corpus while the proof property stays
// a tiny scalar assertion the verifier can reason about independently.

fn greeting() -> &'static str {
    "hello world"
}

fn require_nonnegative_guarded(x: i32) -> i32 {
    if x >= 0 {
        assert!(x >= 0);
        x
    } else {
        0
    }
}

fn main() {
    println!("{}", greeting());
    let _ = require_nonnegative_guarded(4);
    let _ = require_nonnegative_guarded(-1);
}
