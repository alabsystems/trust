//@ compile-flags: -Z trust-verify=off
//@ check-pass
//! FIRST-CLASS loop clauses (two-language design E4/E5, R3):
//! `while cond invariant P decreases e { .. }` as real grammar between the
//! loop condition and its body — a position vanilla Rust rejects, so no
//! vanilla program changes meaning. Predicates are verifier vocabulary
//! (span-only rather than Rust HIR), but the always-on contract query resolves
//! visible source bindings and checks their verifier-language sorts.

pub fn binary_search(xs: &[u32], key: u32) -> Option<usize> {
    let mut lo = 0usize;
    let mut hi = xs.len();
    while lo < hi
        invariant lo <= hi && hi <= xs.len()
        invariant forall i: usize, i < lo ==> xs[i] < key
        invariant forall i j: usize, i < j && j < lo ==> xs[i] <= xs[j]
        decreases hi - lo
    {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] < key {
            lo = mid + 1;
        } else if xs[mid] > key {
            hi = mid;
        } else {
            return Some(mid);
        }
    }
    None
}

// A single invariant, no decreases; labeled loop; nested while with its own
// clause inside a closure body (clauses attach to the closure's own body).
pub fn count_down(mut n: u32) -> u32 {
    let mut acc = 0u32;
    'outer: while n > 0
        invariant acc <= 1000
    {
        let f = || {
            let mut k = 0u8;
            while k < 3
                decreases 3 - k
            {
                k += 1;
            }
            k
        };
        acc = acc.saturating_add(u32::from(f()));
        n -= 1;
        if acc > 500 {
            break 'outer;
        }
    }
    acc
}

// Authored order is metadata: a leading decreases clause must stay ahead of
// the following invariant. Signature-clause words are ordinary verifier
// identifiers inside loop predicates and must not terminate the payload.
pub fn ordered_loop_clauses(mut n: u32, requires: u32, ensures: u32) {
    while n > 0
        decreases n
        invariant requires <= ensures
    {
        n -= 1;
    }
}

// Scalar references use the same explicit-dereference spelling as function
// contracts and the MIR place model; a bare reference is not an integer.
pub fn referenced_bound(mut n: u32, bound: &u32) {
    while n > 0
        invariant n <= *bound
        decreases n
    {
        n -= 1;
    }
}

// An attribute postcondition injects a hygienic `__ret` binding into HIR. It
// is compiler metadata, not a source binding visible to the native loop
// clause, and therefore must not trip the generated-name collision gate.
pub fn attributed_loop(mut n: u32) -> u32
    ensures result == 0
{
    while n > 0
        invariant n <= 100
        decreases n
    {
        n -= 1;
    }
    n
}

// Vanilla parity: `invariant` and `decreases` stay ordinary identifiers
// everywhere else.
#[allow(dead_code)]
fn invariant(x: u32) -> u32 {
    x
}

#[allow(dead_code, non_camel_case_types)]
struct decreases {
    invariant: bool,
}

fn main() {
    let _ = binary_search(&[1, 2, 3], 2);
    let _ = count_down(4);
    ordered_loop_clauses(2, 1, 2);
    referenced_bound(2, &4);
    let _ = attributed_loop(2);
    let _ = invariant(1);
    let _ = decreases { invariant: true };
}
