// `Shim(FnPtrAsPtr(..))` (1.101 spelling; `FnPtrAddr` before), reached through core's
// `fn_addr_eq` over `fn()`.
fn a() {}

fn b() {}

pub fn same() -> bool {
    let x: fn() = a;
    let y: fn() = b;
    core::ptr::fn_addr_eq(x, y)
}
