use crate::command_prelude::*;

use cargo::ops;

pub fn cli() -> Command {
    subcommand("init")
        .about("Create a new cargo package in an existing directory")
        .arg(
            Arg::new("path")
                .value_name("PATH")
                .action(ArgAction::Set)
                .default_value("."),
        )
        .arg_new_opts()
        .arg_registry("Registry to use")
        .arg_silent_suggestion()
        // Trust: the footer names the binary the user actually invoked; see
        // `command_help_footer` in `bin/cargo/main.rs`.
        .after_help(crate::command_help_footer("init"))
}

pub fn exec(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    let opts = args.new_options(gctx)?;
    ops::init(&opts, gctx)?;
    Ok(())
}
