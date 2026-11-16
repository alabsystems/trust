#![feature(decl_macro)]
#![warn(clippy::disallowed_macros, clippy::disallowed_methods)]

pub mod definitions {
    pub macro single_macro() {
        ()
    }
    pub macro grouped_macro() {
        ()
    }
    pub macro renamed_macro() {
        ()
    }
    pub macro module_macro() {
        ()
    }
    pub macro allowed_macro() {
        ()
    }

    pub fn single_function() {}
    pub fn grouped_function() {}
    pub fn renamed_function() {}
    pub fn module_function() {}
    pub fn allowed_function() {}

    pub mod deep {
        pub macro nested_macro() {
            ()
        }
        pub fn nested_function() {}
    }
}

// Preserve the import-tree shape: the controls must remain two single imports.
#[rustfmt::skip]
mod single {
    pub use crate::definitions::single_function;
    pub use crate::definitions::single_macro;
}

mod grouped {
    pub use crate::definitions::{grouped_function, grouped_macro};
}

#[rustfmt::skip]
mod nested {
    pub use crate::definitions::{
        allowed_function as nested_allowed,
        deep::{nested_function, nested_macro},
    };
}

mod aliases {
    pub use crate::definitions::{renamed_function as function_alias, renamed_macro as macro_alias};
}

#[rustfmt::skip]
mod bridge {
    pub use crate::{definitions as grouped_module, definitions::allowed_function as bridge_allowed};
}

fn main() {
    single::single_macro!();
    //~^ disallowed_macros
    grouped::grouped_macro!();
    //~^ disallowed_macros
    nested::nested_macro!();
    //~^ disallowed_macros
    aliases::macro_alias!();
    //~^ disallowed_macros
    bridge::grouped_module::module_macro!();
    //~^ disallowed_macros
    definitions::grouped_macro!();
    //~^ disallowed_macros

    single::single_function();
    //~^ disallowed_methods
    grouped::grouped_function();
    //~^ disallowed_methods
    nested::nested_function();
    //~^ disallowed_methods
    aliases::function_alias();
    //~^ disallowed_methods
    bridge::grouped_module::module_function();
    //~^ disallowed_methods
    definitions::grouped_function();
    //~^ disallowed_methods

    definitions::allowed_macro!();
    definitions::allowed_function();
    nested::nested_allowed();
    bridge::bridge_allowed();
}
