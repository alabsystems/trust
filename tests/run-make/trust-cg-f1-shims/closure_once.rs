// `Shim(ClosureOnce { .. })`: an `Fn` closure called through `FnOnce::call_once`.
fn apply<F: FnOnce(u64) -> u64>(f: F, v: u64) -> u64 {
    f(v)
}

pub fn run(x: u64, v: u64) -> u64 {
    let c = move |v: u64| v ^ x;
    apply(c, v)
}
