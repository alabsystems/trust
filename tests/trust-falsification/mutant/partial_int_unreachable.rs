#![crate_type = "lib"]
#![feature(core_intrinsics)]
// MUTANT: a plain-integer match whose otherwise arm is `unreachable()` but the cases
// {0,1} do NOT cover the full u8 space — x=2 reaches the Unreachable (genuine UB). The
// exhaustiveness assumption MUST NOT fire (selector is not an enum discriminant / cases
// != full tag set), so this MUST fail-closed (exit 1), not be proved dead.
pub fn classify(x: u8) -> u8 {
    match x {
        0 => 100,
        1 => 200,
        _ => unsafe { std::intrinsics::unreachable() },
    }
}
