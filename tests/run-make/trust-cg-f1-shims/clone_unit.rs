// `Shim(Clone(()))`: core has no `impl Clone for ()`, so `<() as Clone>::clone` is
// rustc-synthesized (a zero-field `tuple_like_shim`). The 4d.3 plumbing subject, never license
// evidence (it moves nothing).
fn dup<T: Clone>(t: &T) -> T {
    t.clone()
}

pub fn run() {
    let u = ();
    dup(&u)
}
