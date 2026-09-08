//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-AR (wave-full-0901 coverage tier): the irrefutable `let` array
// destructure WITH a `..` rest silently bound NOTHING — `build_bind_node`
// fail-closed on `slice: Some(..)`, the let routing fell to the
// "bind nothing" catch-all with no tag, and every later read failed
// `VarRef(unbound)` (34 sole-tag bodies; subslice-patterns-const-eval
// alone carries 12). `BindNode::ArrayRest` now models it: prefix
// subplans bind at `0..np`, suffix at `n-ns..n` (n resolved from the
// mapped arity at EMIT time — the pattern alone cannot know it), and a
// by-value `x @ ..` middle binds a fresh tuple built with the
// tuple-literal seed+InsertField machinery. `ref x @ ..` and an EMPTY
// bound middle stay fail-closed. TWO integration traps recorded: the
// `Action::LetDestructure` guard pattern-matched `BindNode::Fields`
// specifically (a new variant must join it or the whole lane is dead
// code), and the non-binding rest spells `PatKind::Wild`, not a Binding.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct N(pub u8);

// Suffix bind across a non-binding rest: must LOWER.
pub fn tail() -> N {
    let [_, .., x] = [N(1), N(2), N(3), N(4)];
    x
}

// Prefix + suffix binds: must LOWER.
pub fn both_ends() -> (N, N) {
    let [a, .., b] = [N(1), N(2), N(3), N(4)];
    (a, b)
}

// By-value bound middle, returned whole: must LOWER. A THIRD trap this
// shape found: `x @ ..` spells the rest as a Binding whose SUBPATTERN is
// the rest marker itself (`Some(..)`) — matching `subpattern: None`
// silently misses the entire `@`-bound population.
pub fn mid_pass_through() -> [N; 2] {
    let [_, x @ .., _] = [N(1), N(2), N(3), N(4)];
    x
}

fn main() {
    assert!(tail() == N(4));
    assert!(both_ends() == (N(1), N(4)));
    let _ = mid_pass_through();
}
