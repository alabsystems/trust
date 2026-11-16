// We need this feature as it changes `dylib` linking behavior and allows us to link to `rustc_driver`.
#![feature(rustc_private)]

extern crate rustc_data_structures;

use std::process::ExitCode;

fn main() -> ExitCode {
    // Trust: FIRST native-main operation, before the reusable rustdoc library.
    // SAFETY: no descriptor-opening operation has run in this native main.
    if let Err(error) = unsafe { rustc_data_structures::jobserver::capture_early() } {
        eprintln!("error: inherited compiler resource custody unavailable: {error}");
        return ExitCode::from(75);
    }

    rustdoc::main()
}
