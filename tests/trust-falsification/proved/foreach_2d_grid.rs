#![crate_type = "lib"]
// 2D grid iteration: `for row in g { for &c in row { .. } }` over `&[[u32; 4]]` — a
// nested for-each where the outer yields `&[u32; 4]` (array reference) and the inner
// iterates it. Both iterator-modeled; `wrapping_add` is panic-free, so the whole
// matrix sum proves under the default strict policy.
pub fn foreach_2d_grid(g: &[[u32; 4]]) -> u32 {
    let mut t = 0u32;
    for row in g {
        for &c in row {
            t = t.wrapping_add(c);
        }
    }
    t
}
