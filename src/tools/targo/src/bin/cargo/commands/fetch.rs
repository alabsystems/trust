use crate::command_prelude::*;

use targo::ops;
use targo::ops::FetchOptions;
use targo::util::IntoUrl;

pub fn cli() -> Command {
    subcommand("fetch")
        .about("Fetch dependencies of a package from the network")
        .arg_silent_suggestion()
        .arg_target_tuple("Fetch dependencies for the target tuple")
        .arg_manifest_path()
        .arg(opt("local-cargo-data-cache", "Copy bounded stored Git and sparse crates.io cache DATA into a fresh Cargo home, then resolve normally (requires --locked --offline)")
            .value_name("PATH")
            .conflicts_with_all(["local-git-source-cache", "local-git-source-copy-budget", "local-git-source-preflight"]))
        .arg(opt("local-cargo-registry-data-cache", "Read only registry DATA from a separate original Cargo cache owner")
            .value_name("PATH").requires("local-cargo-data-cache"))
        .arg(opt("local-cargo-data-manifest", "Include another actual locked workspace in the same bounded DATA snapshot (no readiness claim)")
            .value_name("ABS_MANIFEST").action(clap::ArgAction::Append).requires("local-cargo-data-cache"))
        // Trust: opt-in source data only; normal fetching is unchanged.
        .arg(
            opt("local-git-source-cache", "Seed a fresh Cargo home from locked local Git objects (requires --locked --offline)")
                .value_name("PATH"),
        )
        .arg(
            opt("local-git-object-source", "Read locked Git object DATA for a URL from an explicit object directory (requires --locked --offline)")
                .value_names(["URL", "OBJECTS_DIR"])
                .num_args(2)
                .action(clap::ArgAction::Append),
        )
        .arg(
            opt("local-git-source-copy-budget", "Limit cumulative stream fallback bytes (0 requires native cloning; default 34359738368)")
                .value_name("BYTES")
                .value_parser(clap::value_parser!(u64)),
        )
        .arg(flag("local-git-source-preflight", "Validate and size the locked source closure as JSON without publishing a Cargo home or fetching"))
        // Trust: the footer names the binary the user actually invoked; see
        // `command_help_footer` in `bin/cargo/main.rs`.
        .after_help(crate::command_help_footer("fetch"))
}

pub fn exec(gctx: &mut GlobalContext, args: &ArgMatches) -> CliResult {
    let ws = args.workspace(gctx)?;

    let donor = args.get_one::<String>("local-git-source-cache");
    let mut objects = Vec::new();
    if let Some(values) = args.get_many::<String>("local-git-object-source") {
        let values = values.collect::<Vec<_>>();
        for pair in values.chunks_exact(2) {
            objects.push((
                pair[0].as_str().into_url()?,
                std::path::PathBuf::from(pair[1]),
            ));
        }
    }
    if let Some(cache) = args.get_one::<String>("local-cargo-data-cache") {
        let additional = args
            .get_many::<String>("local-cargo-data-manifest")
            .into_iter()
            .flatten()
            .map(std::path::PathBuf::from)
            .collect::<Vec<_>>();
        targo::sources::git::snapshot_locked_cache_data_workspaces(
            &ws,
            &additional,
            std::path::Path::new(cache),
            args.get_one::<String>("local-cargo-registry-data-cache")
                .map(std::path::Path::new),
            &objects,
        )?;
    } else if donor.is_some() || !objects.is_empty() {
        targo::sources::git::import_locked_source_data(
            &ws,
            donor.map(std::path::Path::new),
            &objects,
            args.get_one::<u64>("local-git-source-copy-budget").copied(),
            args.get_flag("local-git-source-preflight"),
        )?;
        if args.get_flag("local-git-source-preflight") {
            return Ok(());
        }
    } else if args.contains_id("local-git-source-copy-budget")
        || args.get_flag("local-git-source-preflight")
    {
        return Err(anyhow::anyhow!(
            "local Git source-data option requires a local Git source-data input"
        )
        .into());
    }

    let opts = FetchOptions {
        gctx,
        targets: args.targets()?,
    };
    let _ = ops::fetch(&ws, &opts)?;
    Ok(())
}
