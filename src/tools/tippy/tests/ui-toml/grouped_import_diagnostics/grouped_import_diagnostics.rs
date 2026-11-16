//@error-in-other-file: expected a macro, found a function
//@error-in-other-file: expected a macro, found a function
#![warn(clippy::disallowed_macros, clippy::missing_enforced_import_renames)]

mod definitions {
    pub fn policy() {}
    pub fn wrong_kind() {}
    pub fn allowed() {}
}

mod exports {
    pub use crate::definitions::{allowed, policy, wrong_kind};
    //~^ missing_enforced_import_renames
}

mod single {
    pub use crate::definitions::wrong_kind;
}

use exports::{allowed, policy as approved, wrong_kind};

fn main() {
    approved();
    wrong_kind();
    single::wrong_kind();
    allowed();
}
