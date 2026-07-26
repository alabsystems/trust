#![crate_type = "lib"]
// `n % 4` is in [0, 4), so the `k >= 4` branch is DEAD — `unreachable!()` there is
// statically proven unreachable. The native lane PROVES the assert-unreachable
// obligation (the modulo range excludes the branch condition).
pub fn modulo_unreachable(n: u32) -> u32 {
    let k = n % 4;
    if k >= 4 { unreachable!() } else { k }
}
