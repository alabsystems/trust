//@ vec-lowering: verifies
//! THE OTHER `vec!` FORM, AND IT IS FINE. `vec![x; n]` takes a different path
//! (no `MaybeUninit` projection) and verifies. So the gap is the LIST form
//! specifically, not the macro.
fn main() { let v: Vec<u32> = vec![0u32; 4]; let _ = v.len(); }
