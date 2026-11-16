// tidy-alphabetical-start
#![allow(internal_features)]
#![feature(associated_type_defaults)]
#![feature(default_field_values)]
#![feature(deref_patterns)]
#![feature(macro_metavar_expr)]
#![feature(proc_macro_diagnostic)]
#![feature(proc_macro_internals)]
#![feature(try_blocks)]
#![feature(yeet_expr)]
// tidy-alphabetical-end
// Trust (D21): native equality controls and the exact ABI in worker duplex tests.
#![cfg_attr(
    test,
    feature(proc_macro_span, proc_macro_expand, proc_macro_tracked_env, proc_macro_tracked_path)
)]

mod build;
mod diagnostics;
mod mbe;
mod placeholders;
mod proc_macro_server;
mod stats;

pub use mbe::macro_rules::{MacroRulesMacroExpander, compile_declarative_macro};
pub mod base;
pub mod config;
pub mod expand;
pub mod module;
pub mod proc_macro;
