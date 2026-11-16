use crate::command_prelude::*;
use targo::ops::cargo_config;

pub fn cli() -> Command {
    subcommand("config")
        .about("Inspect configuration values")
        // Trust: internal typed project-policy query, not verification activation.
        .subcommand(
            subcommand("trust-policy")
                .hide(true)
                .arg_target_tuple("Target whose effective project requirements are resolved"),
        )
        .subcommand_required(true)
        .arg_required_else_help(true)
        .subcommand(
            subcommand("get")
                .arg(
                    Arg::new("key")
                        .action(ArgAction::Set)
                        .help("The config key to display"),
                )
                .arg(
                    opt("format", "Display format")
                        .value_parser(cargo_config::ConfigFormat::POSSIBLE_VALUES)
                        .default_value("toml"),
                )
                .arg(flag(
                    "show-origin",
                    "Display where the config value is defined",
                ))
                .arg(
                    opt("merged", "Whether or not to merge config values")
                        .value_parser(["yes", "no"])
                        .default_value("yes"),
                ),
        )
}

pub fn exec(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    gctx.cli_unstable().fail_if_stable_command(
        gctx,
        "config",
        9301,
        "unstable-options",
        gctx.cli_unstable().unstable_options,
    )?;
    match args.subcommand() {
        Some(("trust-policy", args)) => {
            let targets = args
                .get_many::<String>("target")
                .into_iter()
                .flatten()
                .cloned()
                .collect::<Vec<_>>();
            cargo_config::trust_policy(gctx, &targets)?;
        }
        Some(("get", args)) => {
            let opts = cargo_config::GetOptions {
                key: args.get_one::<String>("key").map(String::as_str),
                format: args.get_one::<String>("format").unwrap().parse()?,
                show_origin: args.flag("show-origin"),
                merged: args.get_one::<String>("merged").map(String::as_str) == Some("yes"),
            };
            cargo_config::get(gctx, &opts)?;
        }
        Some((cmd, _)) => {
            unreachable!("unexpected command {}", cmd)
        }
        None => {
            unreachable!("unexpected command")
        }
    }
    Ok(())
}
