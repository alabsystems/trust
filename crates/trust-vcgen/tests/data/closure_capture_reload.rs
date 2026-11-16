// Fixture source for crates/trust-vcgen/tests/closure_capture_reload_realmir.rs.
//
// The real shape of trust-ir-conformance `CharCarriers::of` (preview3/preview4,
// `subset.rs:577-578`): a counter captured by a closure through its unique
// borrow, bumped and reread. In the closure body every use of `count` copies
// the captured `&mut usize` out of the closure environment into a FRESH
// temporary (`_7 = copy ((*_1).0); (*_7) = ...; _8 = copy ((*_1).0); _3 =
// copy (*_8)`), so the store and the reload go through two different locals
// that hold the same pointer.

/// SAFE: the reload reads `old + 1 >= 1`.
pub fn bump_reload(base: usize) -> usize {
    let mut count = base;
    let mut bump = || {
        count += 1;
        count - 1
    };
    bump()
}

/// SAFE: the `CharCarriers::of` numbering closure verbatim (a closure inside a
/// closure, each layer reborrowing the captured counter).
pub fn number_rows(rows: &std::collections::HashMap<u32, usize>, base: usize) -> usize {
    let mut count = base;
    let mut number = |rows: &std::collections::HashMap<u32, usize>| -> Vec<(u32, usize)> {
        rows.keys()
            .map(|&id| {
                count += 1;
                (id, count - 1)
            })
            .collect()
    };
    number(rows).len()
}

/// UNSAFE: `old + 1 - 2` underflows at `old = 0`.
pub fn bump_reload_sub_two(base: usize) -> usize {
    let mut count = base;
    let mut bump = || {
        count += 1;
        count - 2
    };
    bump()
}

/// UNSAFE: the second store replaces the bumped value with `v`; the reload is
/// `v - 1`, which underflows at `v = 0`.
pub fn bump_overwrite_reload(base: usize, v: usize) -> usize {
    let mut count = base;
    let mut bump = || {
        count += 1;
        count = v;
        count - 1
    };
    bump()
}

/// UNSAFE: the store goes through the captured pointer, but the reload reads a
/// DIFFERENT captured counter, which may be 0.
pub fn bump_other_reload(a: usize, b: usize) -> usize {
    let mut x = a;
    let mut y = b;
    let mut bump = || {
        x += 1;
        y - 1
    };
    bump()
}
