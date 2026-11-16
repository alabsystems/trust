// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Execute the source-derived offline envelope in the SAME configured Targo.
//! The resident separately owns the authenticated envelope, source/config,
//! physical caller/private caches, seed, SDK, GNU loan and actual NoFork child.
//! This library consumer creates none of those owners or a readiness seal and
//! advertises no CLI, raw-Darwin override or online fallback. Its returned count
//! is DATA; only the actual native issuer can judge closure and all postchecks.

use crate::{
    context::homedir,
    ops::{FetchOptions, fetch},
    util::{CargoResult, GlobalContext},
    workspace::Workspace,
};
use cargo_util::EnvironmentInputs;
use cargo_util_terminal::Shell;
use std::{
    ffi::OsString,
    fs::Metadata,
    os::unix::{ffi::OsStringExt as _, fs::MetadataExt as _},
    path::{Path, PathBuf},
    time::Instant,
};
use trust_resource_controller::bootstrap_graph::offline_preparation::{Envelope, Request};

#[derive(PartialEq, Eq)]
struct ImageStamp {
    device: u64,
    inode: u64,
    bytes: u64,
    mode: u32,
    uid: u32,
    gid: u32,
    links: u64,
    modified: (i64, i64),
    changed: (i64, i64),
}
impl ImageStamp {
    fn of(item: &Metadata) -> CargoResult<Self> {
        anyhow::ensure!(
            item.is_file(),
            "configured preparation image is not regular"
        );
        Ok(Self {
            device: item.dev(),
            inode: item.ino(),
            bytes: item.len(),
            mode: item.mode(),
            uid: item.uid(),
            gid: item.gid(),
            links: item.nlink(),
            modified: (item.mtime(), item.mtime_nsec()),
            changed: (item.ctime(), item.ctime_nsec()),
        })
    }
}

fn path(bytes: &[u8]) -> PathBuf {
    PathBuf::from(OsString::from_vec(bytes.to_vec()))
}
fn before(end: Instant) -> CargoResult<()> {
    anyhow::ensure!(
        Instant::now() < end,
        "original preparation endpoint expired"
    );
    Ok(())
}
fn current_image(configured: &Path, expected: &ImageStamp) -> CargoResult<()> {
    anyhow::ensure!(
        ImageStamp::of(&configured.metadata()?)? == *expected
            && ImageStamp::of(&std::env::current_exe()?.metadata()?)? == *expected,
        "configured preparation image changed"
    );
    Ok(())
}

/// Perform every canonical row using the ordinary full `fetch` implementation.
/// Fresh contexts retain each ordinary invocation's config/warning/cache state.
/// Empty fetch targets preserve normal `fetch`'s ALL-platform dependency walk.
/// No manifest list, digest, path, environment or returned count creates an owner.
///
/// The resident supplies its ALREADY selected original endpoint, never a fresh
/// duration. The native custodian independently enforces that hard endpoint and
/// retains all input/child/loan owners through physical EOF and final ACK/closure.
/// These cooperative checks neither interrupt blocked IO nor settle any child.
///
/// # Errors
/// No actual installed dispatcher/original scheduler, unequal complete effective
/// environment, changed configured image/cwd/home, expired end or any ordinary
/// configuration/workspace/resolution/fetch error. No local process fallback.
pub fn execute_offline_envelope(
    request: &Request,
    envelope: &Envelope,
    original_end: Instant,
) -> CargoResult<usize> {
    // Strong borrow of the actual registered object BEFORE any project config.
    // A bool, decoded frame or successful-looking outcome constructs no owner.
    let executor = cargo_util::installed_process_executor().ok_or_else(|| {
        anyhow::anyhow!(
            "offline preparation requires the installed execution owner before configuration"
        )
    })?;
    let scheduler = crate::context::early_imported_preparation_jobserver()?;
    request.validate()?;
    envelope.validate()?;
    before(original_end)?;
    anyhow::ensure!(
        original_end
            .checked_duration_since(Instant::now())
            .is_some_and(|remaining| remaining.as_nanos() <= u128::from(request.budget_ns)),
        "preparation endpoint exceeds the request's restriction"
    );

    let environment = EnvironmentInputs::capture()?;
    let expected = EnvironmentInputs::from_variables(
        request
            .environment
            .iter()
            .map(|(k, v)| (OsString::from_vec(k.clone()), OsString::from_vec(v.clone()))),
    )?;
    anyhow::ensure!(
        environment.digest() == expected.digest(),
        "preparation complete effective environment differs from its original binding"
    );
    let cwd = std::env::current_dir()?;
    anyhow::ensure!(
        cwd == path(&request.source_root),
        "preparation cwd differs from original source"
    );
    let home =
        homedir(&cwd).ok_or_else(|| anyhow::anyhow!("preparation Cargo home unavailable"))?;
    anyhow::ensure!(
        home == path(&request.cargo_home),
        "preparation physical caller Cargo home differs"
    );
    let configured = path(&request.configured_targo);
    anyhow::ensure!(
        std::env::args_os().next().as_deref() == Some(configured.as_os_str()),
        "preparation configured Targo spelling differs from this invocation"
    );
    let image = ImageStamp::of(&std::env::current_exe()?.metadata()?)?;
    current_image(&configured, &image)?;

    let mut completed = 0;
    for index in 0..envelope.manifests.len() {
        before(original_end)?;
        current_image(&configured, &image)?;
        anyhow::ensure!(
            EnvironmentInputs::capture()?.digest() == environment.digest(),
            "preparation effective environment changed"
        );
        // Reuse the canonical codec's fixed fetch/locked/offline/manifest join,
        // rather than a second recipe list, caller argv or target projection.
        let arguments = envelope.fetch_arguments(request, index)?;
        let manifest = path(arguments.last().expect("fixed canonical manifest argument"));
        let mut context = GlobalContext::for_coordinator_queries(
            Shell::new(),
            cwd.clone(),
            home.clone(),
            configured.clone(),
            environment.clone(),
            scheduler.clone(),
            executor.clone(),
        )?;
        context.configure(0, false, None, false, true, true, &None, &[], &[])?;
        before(original_end)?;
        let workspace = Workspace::new(&manifest, &context)?;
        fetch(
            &workspace,
            &FetchOptions {
                gctx: &context,
                targets: Vec::new(),
            },
        )?;
        drop(workspace);
        drop(context);
        before(original_end)?;
        current_image(&configured, &image)?;
        anyhow::ensure!(
            EnvironmentInputs::capture()?.digest() == environment.digest(),
            "preparation effective environment changed"
        );
        completed += 1;
    }
    before(original_end)?;
    Ok(completed)
}

#[cfg(test)]
mod tests;
