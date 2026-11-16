// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use crate::command_prelude::*;

pub fn cli() -> Command {
    subcommand("source-check")
        .about("Read actual tracked-input bytes through the native landing protocol")
        .arg(flag("tracked-inputs", "Serve bounded tracked-input batches on stdin/stdout").required(true))
        .after_help("Observational data only. The caller must authenticate the original executable and retain source/index/history checks. Unsupported runtime profiles use the original landing reader.")
}

pub fn exec(_gctx: &mut GlobalContext, _args: &ArgMatches) -> CliResult {
    #[cfg(unix)]
    {
        let stdin = std::io::stdin();
        let stdout = std::io::stdout();
        targo::ops::checkout_inputs::serve_tracked_inputs(&mut stdin.lock(), &mut stdout.lock())?;
        Ok(())
    }
    #[cfg(not(unix))]
    Err(anyhow::anyhow!("native tracked-input runtime is unsupported on this host").into())
}
