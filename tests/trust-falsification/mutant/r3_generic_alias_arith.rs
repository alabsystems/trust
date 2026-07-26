#![crate_type = "lib"]
// MUTANT of proved/r3_generic_alias_arith.rs: `k + 1` UNGUARDED — overflows at
// k == u32::MAX for every S. Must REFUTE; a pass would mean the R3 alias
// relaxation hid a genuine T-independent overflow obligation.
pub trait Src { type Item; }
pub fn r3_shift<S: Src>(pending: Option<S::Item>, k: u32) -> (Option<S::Item>, u32) {
    let bumped = k + 1;
    (pending, bumped)
}
