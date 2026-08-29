//@ dont-check-compiler-stderr
//! Trust: an `invariant`/`decreases` clause written where no clause position
//! exists must say so.
//!
//! Before the `loop`/`for` clause positions were added, EVERY unsupported
//! position produced vanilla rustc's generic "expected `{`, found `invariant`"
//! plus a block-recovery suggestion that rewrites the clause into
//! `{ invariant } n <= limit` -- a suggestion that names no fix, is never what
//! the author meant, and does not even hint that `invariant` is a Trust
//! keyword. `while`, `loop` and `for` now all have clause positions, so what
//! remains is the genuinely unsupported set: constructs that are not loops.
//! Those must fail closed with a Trust-aware message that names the construct
//! and lists the positions that do exist.
//!
//! Every block-expecting position routes through the one
//! `error_block_no_opening_brace_msg` helper, so `if` here stands for the
//! whole class.

fn if_is_not_a_loop(n: u32) -> u32 {
    if n > 0 invariant n > 0 {
        //~^ ERROR `invariant` is a Trust loop clause and is not allowed in this position
        n - 1
    } else {
        n
    }
}

fn unsafe_block_is_not_a_loop(n: u32) -> u32 {
    unsafe decreases n {
        //~^ ERROR `decreases` is a Trust loop clause and is not allowed in this position
        n
    }
}

fn main() {}
