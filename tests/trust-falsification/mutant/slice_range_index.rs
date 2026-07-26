#![crate_type = "lib"]
// MUTANT: `&s[a..b]` (exclusive Range<usize> SliceIndex on a runtime-length &[T])
// with NO bounds guard at all. `&s[0..9]` on a length-3 slice panics ("range end
// index out of range"). The `<[T] as Index<Range>>::index` call carries no
// caller-visible Projection::Index, so before the fix Trust emitted NO obligation
// and PROVED this vacuously (the Workflow-confirmed P0 false proof). Must be
// REFUSED: the `start > end ∨ end > s.len()` bounds VC is undischarged.
pub fn slice_range_index(s: &[u8], a: usize, b: usize) -> u8 {
    let t = &s[a..b];
    t.iter().copied().fold(0u8, |acc, x| acc.wrapping_add(x))
}
