//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-FR: the FAITHFUL RANGE `for` lane. `for <pat> in <a>..<b>` over a bare
// int/uint element, where the read-only-escape SUMMARY refuses (an effectful
// body), lowers as a real counting CFG instead of declining at the
// opaque-carrier gate:
//
//   pre:    %slot = alloca <int>; store <start>
//   header: %i = load %slot; %c = icmp {s,u}lt %i, <end>; condbr %c, body, exit
//   body:   store %slot, %i + 1   (the advance FIRST, so `continue` is correct
//           and `return`/`break` observe Range::next's own post-advance state);
//           <pat> binds %i; then the user body, visibly.
//
// The advance is emitted only on the payload edge, so `end + 1` is never
// computed — no overflow exists on this lane. `Range::next` semantics by the
// std definition (the same KB grade as the `Pin::new`/box peels); the
// hygienic iterator var is never bound because its only desugar use is the
// `next()` call this lane replaces. Bounds are lowered ONCE before the loop
// (Rust evaluates the Range ctor once). Fences: the literal `Range` lang-item
// ctor through the lang-item `into_iter` identity only — `a..=b`
// (RangeInclusive, done flag), `a..` (RangeFrom, unbounded), adapter chains
// (`.rev()`), char/float elements, and promoted/`&mut`-collected item vars
// all keep today's path. Read-only bodies keep the summary lane (it runs
// first); this lane owns the effectful residue.

// Effectful body (non-local write) — the summary refuses, wave-FR lowers.
pub fn fill(dst: &mut i64, n: i64) -> i64 {
    for i in 0..n {
        *dst = i;
    }
    *dst
}

// Early `return` of the item from inside the loop (issue-23611's
// `first_avail` shape): returns the PRE-advance item value.
pub fn find(n: u32, w: u32) -> u32 {
    for i in 3..n {
        if i == w {
            return i;
        }
    }
    0
}

// `continue` takes the back edge AFTER the advance (emitted at payload-block
// start), so it never loops on one value.
pub fn skip_odd(dst: &mut u64, n: u64) -> u64 {
    let mut c = 0;
    for i in 0..n {
        if i % 2 == 1 {
            continue;
        }
        *dst = i;
        c += 1;
    }
    c
}

// Nested range loops REFUSE today — the inner `loop` hits the pre-existing
// `Loop(nested)` wall, its inner match never arrives, and the leaked ctx is
// caught by the outer's unconsumed check (`ForDesugar(range ctx unconsumed)`,
// fail-closed). This pins two things: the ctx pairing is by inner-scrutinee
// ExprId (a leak can never be consumed by a parent's match), and a wiring
// failure refuses rather than miscompiles. Lifting `Loop(nested)` is a
// separate wave; when it lands, this body must start lowering with each inner
// match consuming ITS OWN ctx.
pub fn grid(dst: &mut i64, n: i64, m: i64) {
    for i in 0..n {
        for j in 0..m {
            *dst = i + j;
        }
    }
}

// NEGATIVE — `RangeInclusive` carries a done flag and misses the ctor fence:
// today's path (summary or refusal) is preserved.
pub fn inclusive(dst: &mut u32, n: u32) {
    for i in 0..=n {
        *dst = i;
    }
}
