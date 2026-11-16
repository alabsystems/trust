//! A DEPENDENCY's `Debug` impl. Provable in its own crate; an UNDECLARED
//! consumer must still refuse to format it (`user_fmt_dep`), because no
//! panic-freedom verdict crosses a crate boundary in rmeta, by decision (D4). A
//! consumer that DECLARES this crate re-derives the impl from its encoded MIR
//! instead (`user_fmt_dep_declared`).
#![crate_name = "libd"]
use core::fmt;
pub struct D;
impl fmt::Debug for D {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result { Ok(()) }
}
