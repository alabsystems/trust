use anyhow::Context;
use cargo::ops::info;
use cargo::util::command_prelude::*;
use cargo_util_schemas::core::PackageIdSpec;

pub fn cli() -> Command {
    Command::new("info")
        .about("Display information about a package")
        .arg(
            Arg::new("package")
                .required(true)
                .value_name("SPEC")
                .help_heading(heading::PACKAGE_SELECTION)
                .help("Package to inspect"),
        )
        .arg_index("Registry index URL to search packages in")
        .arg_registry("Registry to search packages in")
        .arg_silent_suggestion()
        // Trust: the footer names the binary the user actually invoked; see
        // `command_help_footer` in `bin/cargo/main.rs`.
        .after_help(crate::command_help_footer("info"))
}

pub fn exec(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    let package = args
        .get_one::<String>("package")
        .map(String::as_str)
        .unwrap();
    let spec = PackageIdSpec::parse(package)
        .with_context(|| format!("invalid package ID specification: `{package}`"))?;

    // Check if --registry or --index was explicitly provided
    let explicit_registry = args._contains("registry") || args._contains("index");
    let reg_or_index = args.registry_or_index(gctx)?;
    info(&spec, gctx, reg_or_index, explicit_registry)?;
    Ok(())
}
