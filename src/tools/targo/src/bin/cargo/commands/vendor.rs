use crate::command_prelude::*;
use std::path::PathBuf;
use targo::ops;

pub fn cli() -> Command {
    subcommand("vendor")
        .about("Vendor all dependencies for a project locally")
        .arg(
            Arg::new("path")
                .action(ArgAction::Set)
                .value_parser(clap::value_parser!(PathBuf))
                .help("Where to vendor crates (`vendor` by default)"),
        )
        .arg(flag(
            "no-delete",
            "Don't delete older crates in the vendor directory",
        ))
        .arg(
            Arg::new("tomls")
                .short('s')
                .long("sync")
                .help("Additional `Cargo.toml` to sync and vendor")
                .value_name("TOML")
                .value_parser(clap::value_parser!(PathBuf))
                .action(clap::ArgAction::Append),
        )
        .arg(flag(
            "respect-source-config",
            "Respect `[source]` config in `.cargo/config`",
        ))
        .arg(flag(
            "versioned-dirs",
            "Always include version in subdir name",
        ))
        .arg(
            flag(
                "cohort-plan",
                "Print the Git-bound source cohort for explicit packages",
            )
            .long_help("Print the Git-bound source cohort for explicit packages, including owning-workspace optional, target and dev path dependencies. Requires committed manifests and lockfiles with --locked. Configured paths overrides and configuration-origin patches are unsupported.")
            .requires("package")
            .conflicts_with_all([
                "cohort-check",
                "path",
                "no-delete",
                "tomls",
                "versioned-dirs",
                "respect-source-config",
            ]),
        )
        .arg(
            Arg::new("cohort-check")
                .long("cohort-check")
                .value_name("RECORD")
                .value_parser(clap::value_parser!(PathBuf))
                .help("Check a source cohort record against the actual resolved source")
                .long_help("Check a source cohort record against the actual resolved source. Requires committed manifests and lockfiles with --locked. Configured paths overrides and configuration-origin patches are unsupported.")
                .conflicts_with_all([
                    "path",
                    "no-delete",
                    "tomls",
                    "versioned-dirs",
                    "respect-source-config",
                ]),
        )
        .arg(
            Arg::new("package")
                .short('p')
                .long("package")
                .value_name("SPEC")
                .action(ArgAction::Append)
                .requires("cohort-plan")
                .help("Explicit root package for source cohort planning"),
        )
        .arg(unsupported("no-merge-sources"))
        .arg(unsupported("relative-path"))
        .arg(unsupported("only-git-deps"))
        .arg(unsupported("disallow-duplicates"))
        .arg_manifest_path()
        // Trust: the footer names the binary the user actually invoked; see
        // `command_help_footer` in `bin/cargo/main.rs`.
        .after_help(crate::command_help_footer("vendor"))
}

fn unsupported(name: &'static str) -> Arg {
    // When we moved `cargo vendor` into Cargo itself we didn't stabilize a few
    // flags, so try to provide a helpful error message in that case to ensure
    // that users currently using the flag aren't tripped up.
    let value_parser = clap::builder::UnknownArgumentValueParser::suggest("the crates.io `cargo vendor` command has been merged into Cargo")
        .and_suggest(format!("and the flag `--{name}` isn't supported currently"))
        .and_suggest("to continue using the flag, execute `cargo-vendor vendor ...`")
        .and_suggest("to suggest this flag supported in Cargo, file an issue at <https://github.com/rust-lang/cargo/issues/new>");

    flag(name, "").value_parser(value_parser).hide(true)
}

pub fn exec(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    if args.flag("cohort-plan") {
        let ws = args.workspace(gctx)?;
        let packages = args
            .get_many::<String>("package")
            .expect("required cohort packages")
            .cloned()
            .collect::<Vec<_>>();
        let record = ops::vendor_cohort_plan(&ws, &packages)?;
        targo::drop_println!(gctx, "{}", record);
        return Ok(());
    }
    if let Some(input) = args.get_one::<PathBuf>("cohort-check") {
        let ws = args.workspace(gctx)?;
        let status = ops::vendor_cohort_check(&ws, &gctx.cwd().join(input))?;
        targo::drop_println!(gctx, "{}", status);
        return Ok(());
    }
    // We're doing the vendoring operation ourselves, so we don't actually want
    // to respect any of the `source` configuration in Cargo itself. That's
    // intended for other consumers of Cargo, but we want to go straight to the
    // source, e.g. crates.io, to fetch crates.
    let respect_source_config = args.flag("respect-source-config");
    if !respect_source_config {
        gctx.values_mut()?.remove("source");
    }

    let ws = args.workspace(gctx)?;
    let path = args
        .get_one::<PathBuf>("path")
        .cloned()
        .unwrap_or_else(|| PathBuf::from("vendor"));
    ops::vendor(
        &ws,
        &ops::VendorOptions {
            no_delete: args.flag("no-delete"),
            destination: &path,
            versioned_dirs: args.flag("versioned-dirs"),
            extra: args
                .get_many::<PathBuf>("tomls")
                .unwrap_or_default()
                .cloned()
                .collect(),
            respect_source_config,
        },
    )?;
    Ok(())
}
