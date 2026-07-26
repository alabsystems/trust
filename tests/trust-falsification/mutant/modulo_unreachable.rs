#![crate_type = "lib"]
// MUTANT of proved/modulo_unreachable.rs: weakens the guard to `k >= 3`. Since
// `n % 4` CAN equal 3, the `unreachable!()` is genuinely REACHABLE — the native
// lane must REFUSE to prove the branch dead.
pub fn modulo_unreachable(n: u32) -> u32 {
    let k = n % 4;
    if k >= 3 { unreachable!() } else { k }
}
