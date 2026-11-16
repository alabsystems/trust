// Two source files that a NON-INJECTIVE `--remap-path-prefix` pair renders as one name
// (`<cwd>/x=/src` and `<cwd>/y=/src` both give `/src/m.rs`). Their bodies DIFFER
// (`a + 1` vs `a + 2`): rustc keys loaded files on the remapped name, so without the
// load-time gate `y::m` is compiled from `x/m.rs`'s text. Under an injective remap the
// crate compiles and `both` sees two distinct files.
#[path = "x/m.rs"]
pub mod x;
#[path = "y/m.rs"]
pub mod y;

pub fn both(a: u64) -> u64 {
    x::m(a) + y::m(a)
}
