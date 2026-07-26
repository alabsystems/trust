use cargo::ops;
use cargo::ops::RegistryOrIndex;

use crate::command_prelude::*;

pub fn cli() -> Command {
    subcommand("logout")
        .about("Remove an API token from the registry locally")
        .arg_registry("Registry to use")
        .arg_silent_suggestion()
        // Trust: the footer names the binary the user actually invoked; see
        // `command_help_footer` in `bin/cargo/main.rs`.
        .after_help(crate::command_help_footer("logout"))
}

pub fn exec(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    let reg = args.registry_or_index(gctx)?;
    assert!(
        !matches!(reg, Some(RegistryOrIndex::Index(..))),
        "must not be index URL"
    );

    ops::registry_logout(gctx, reg)?;
    Ok(())
}
