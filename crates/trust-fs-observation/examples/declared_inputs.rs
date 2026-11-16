// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Measure the public observer over an original declared input graph.
//! No build action, cache admission, or proof authority is supplied here.

use std::path::PathBuf;

use anyhow::{Context as _, Result, ensure};
use serde::Deserialize;
use trust_fs_observation::observation::{observe_attempt, read_record, window_attempt};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DeclaredInputs {
    root: PathBuf,
    paths: Vec<PathBuf>,
    recursive: bool,
}

fn main() -> Result<()> {
    let mut args = std::env::args_os().skip(1);
    let input = PathBuf::from(args.next().context("usage: declared_inputs INPUTS.json")?);
    ensure!(args.next().is_none(), "usage: declared_inputs INPUTS.json");
    let input = serde_json::from_str::<DeclaredInputs>(&read_record(&input)?)?;

    let before = window_attempt(&input.root, &input.paths, input.recursive);
    let window_work = before.work;
    let before = before
        .result
        .with_context(|| format!("original execution window unavailable; work={window_work:?}"))?;
    let first = observe_attempt(&input.root, &input.paths, input.recursive);
    let first_work = first.work;
    let first = first
        .result
        .with_context(|| format!("first content observation unavailable; work={first_work:?}"))?;
    ensure!(
        before.covers(&first),
        "original window does not cover first observation"
    );
    let (snapshot, first_window) = first.into_parts();

    let repeated = observe_attempt(&input.root, &input.paths, input.recursive);
    let repeated_work = repeated.work;
    let repeated = repeated.result.with_context(|| {
        format!("repeated content observation unavailable; work={repeated_work:?}")
    })?;
    ensure!(
        before.covers(&repeated),
        "original window does not cover repeated observation"
    );
    ensure!(
        first_window.covers(&repeated),
        "first observation does not cover repeated observation"
    );
    ensure!(
        snapshot == repeated.into_snapshot(),
        "declared input content changed between observations"
    );

    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({
            "root": input.root,
            "declared_paths": input.paths.len(),
            "recursive": input.recursive,
            "snapshot": snapshot,
            "window_work": window_work,
            "first_content_work": first_work,
            "repeated_content_work": repeated_work,
            "original_window_covers_both": true,
            "repeated_content_equal": true,
        }))?
    );
    Ok(())
}
