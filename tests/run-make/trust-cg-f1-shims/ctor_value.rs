// `CTOR_SUBJECT` of tests/run-make/trust-instance-producer-census/rmake.rs: constructors as
// codegen items, passed through `FnOnce` (`Option::map`) and coerced to fn pointers.
pub enum Wrapper {
    Fd(i32),
    Pipe(i32, i32),
    Closed,
}

pub struct Tagged(pub u64);

// An enum-variant ctor passed as a function: `Option::map` calls it through the `FnOnce` shim
// of its fn-item type, so codegen collects the ctor itself as an `InstanceKind::Item`.
pub fn wrap_fd(v: Option<i32>) -> Option<Wrapper> {
    v.map(Wrapper::Fd)
}

// Constructors used as VALUES: coerced to fn pointers and called through them.
pub fn ctor_values(a: i32, b: i32, n: u64) -> u64 {
    let pipe: fn(i32, i32) -> Wrapper = Wrapper::Pipe;
    let tag: fn(u64) -> Tagged = Tagged;
    let w = pipe(a, b);
    let t = tag(n);
    match w {
        Wrapper::Pipe(x, _) => t.0 + x as u64,
        _ => t.0,
    }
}
