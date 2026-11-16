//! The private-use shape: a library that derives from `pm_tcb_init` on a PRIVATE type
//! and exposes only a function. Its metadata still records `pm_tcb_init`, so every
//! compilation that depends on it loads `pm_tcb_init`.
#[derive(pm_tcb_init::Quiet)]
#[allow(dead_code)]
struct Hidden;

pub fn value() -> u8 {
    7
}
