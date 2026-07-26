// tidy-alphabetical-start
#![feature(decl_macro)]
#![feature(file_buffered)]
#![feature(iter_intersperse)]
#![feature(try_blocks)]
// tidy-alphabetical-end

mod callbacks;
pub mod diagnostics;
pub mod interface;
mod limits;
pub mod passes;
mod queries;
pub mod util;

pub use callbacks::setup_callbacks;
pub use interface::{Config, NoTrustEvidence, run_compiler, run_compiler_with_no_trust_evidence};
pub use passes::{DEFAULT_QUERY_PROVIDERS, create_and_enter_global_ctxt, parse};
pub use queries::Linker;

#[cfg(test)]
mod tests;
