// A `thread_local!` read. No `Shim(ThreadLocal(..))` on this target (`dll_tls_export`); F1
// fatals on the `#[thread_local]` static.
use std::cell::Cell;

thread_local! {
    static K: Cell<u64> = const { Cell::new(0) };
}

pub fn read() -> u64 {
    K.with(|k| k.get())
}
