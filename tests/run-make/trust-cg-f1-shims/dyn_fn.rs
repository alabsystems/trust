// `Shim(VTable(..))` and `Shim(ClosureOnce { .. })`: every `dyn Fn*` vtable carries a by-value
// `call_once` slot.
fn run(f: &dyn Fn(u64) -> u64, x: u64) -> u64 {
    f(x)
}

pub fn go(x: u64, y: u64) -> u64 {
    let c = move |v: u64| v ^ y;
    run(&c, x)
}
