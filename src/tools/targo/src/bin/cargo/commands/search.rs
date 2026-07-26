use crate::command_prelude::*;

use std::cmp::min;

use cargo::ops;

pub fn cli() -> Command {
    subcommand("search")
        .about("Search packages in the registry. Default registry is crates.io")
        .arg(Arg::new("query").value_name("QUERY").num_args(0..))
        .arg(
            opt(
                "limit",
                "Limit the number of results (default: 10, max: 100)",
            )
            .value_name("LIMIT"),
        )
        .arg_index("Registry index URL to search packages in")
        .arg_registry("Registry to search packages in")
        .arg_silent_suggestion()
        // Trust: the footer names the binary the user actually invoked; see
        // `command_help_footer` in `bin/cargo/main.rs`.
        .after_help(crate::command_help_footer("search"))
}

pub fn exec(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    let reg_or_index = args.registry_or_index(gctx)?;
    let limit = args.value_of_u32("limit")?;
    let limit = min(100, limit.unwrap_or(10));
    let query: Vec<&str> = args
        .get_many::<String>("query")
        .unwrap_or_default()
        .map(String::as_str)
        .collect();
    let query: String = query.join("+");
    ops::search(&query, gctx, reg_or_index, limit)?;
    Ok(())
}
