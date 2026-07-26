use crate::cli;
use crate::command_prelude::*;

pub fn cli() -> Command {
    subcommand("version")
        .about("Show version information")
        .arg_silent_suggestion()
        // Trust: the footer names the binary the user actually invoked; see
        // `command_help_footer` in `bin/cargo/main.rs`.
        .after_help(crate::command_help_footer("version"))
}

pub fn exec(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    let verbose = args.verbose() > 0;
    let version = cli::get_version_string(verbose);
    cargo::drop_print!(gctx, "{}", version);
    Ok(())
}
