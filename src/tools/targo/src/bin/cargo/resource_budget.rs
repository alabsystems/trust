//! Fresh native workload policy data before project configuration. No result
//! grants admission, work, GNU credit, CPU ownership or process control.

use super::*;
use std::collections::BTreeMap;
use trust_build_tree::admission::budget::{self, Outcome, Overlap, Request, Workload};

pub(super) fn cli() -> clap::Command {
    let plan = |name| {
        clap::Command::new(name)
            .arg(Arg::new("kind").required(true).value_parser([
                "rustc-build",
                "ui-test",
                "crates-test",
                "fast-lane",
            ]))
            .arg(
                Arg::new("max")
                    .long("max")
                    .value_parser(clap::value_parser!(NonZeroU32)),
            )
    };
    clap::Command::new("targo --unverified resource budget")
        .about("Observe native workload sizing policy; never an admission or capacity grant")
        .subcommand_required(true)
        .subcommand(clap::Command::new("measure"))
        .subcommand(plan("plan"))
        .subcommand(plan("jobs"))
        .subcommand(clap::Command::new("admit-overlap"))
        .subcommand(clap::Command::new("governor"))
}

struct Options {
    mode: String,
    request: Request,
}
fn options(args: &[OsString]) -> Result<Options> {
    let parsed = cli().try_get_matches_from(
        std::iter::once(OsString::from("resource budget")).chain(args.iter().cloned()),
    )?;
    let (mode, arguments) = parsed.subcommand().expect("required mode");
    let workload = if matches!(mode, "plan" | "jobs") {
        Workload::parse(
            arguments
                .get_one::<String>("kind")
                .expect("required workload"),
        )?
    } else {
        Workload::RustcBuild
    };
    let mut request = Request::new(workload);
    if matches!(mode, "plan" | "jobs") {
        request.maximum_jobs = arguments.get_one::<NonZeroU32>("max").copied();
    }
    Ok(Options {
        mode: mode.into(),
        request,
    })
}

fn gib_value(raw: &str) -> Result<NonZeroU64> {
    let value = raw
        .trim()
        .parse::<f64>()
        .context("workload memory override must be a number of GiB")?;
    let bytes = value * (1024_u64 * 1024 * 1024) as f64;
    ensure!(
        value.is_finite() && value > 0.0 && bytes.is_finite() && bytes < u64::MAX as f64,
        "workload memory override must be positive, finite and representable"
    );
    NonZeroU64::new(bytes as u64).context("workload memory override is below one byte")
}

fn unsupported_profile(mut present: impl FnMut(&str) -> bool) -> Result<()> {
    for key in [
        "BUILD_SLOT_HELD",
        "ATERM_RESOURCE_JOB_V3",
        "ATERM_SDK_LEASE_V3",
        "TRUST_CPU_HANDOFF",
        "TRUST_CPU_IMPLICIT_FD",
    ] {
        ensure!(
            !present(key),
            "native budget cannot infer an original owner from {key}"
        );
    }
    Ok(())
}

pub(super) fn dispatch(args: &[OsString], input: Option<NestedInput>) -> Result<i32> {
    if args.len() == 1 && (args[0] == "--help" || args[0] == "-h") {
        cli().print_help()?;
        writeln!(std::io::stdout().lock())?;
        return Ok(0);
    }
    let mut options = options(args)?;
    // Read the actual process environment once, without project configuration
    // overlays or repeated observations between profile/ceiling checks.
    #[expect(
        clippy::disallowed_methods,
        reason = "the native entry requires actual inherited environment before project overlays"
    )]
    let environment = std::env::vars_os().collect::<BTreeMap<_, _>>();
    unsupported_profile(|key| environment.contains_key(OsStr::new(key)))?;
    // Source slots were snapshotted at the FIRST native entry. Selected direct
    // or authenticated-courier failure never becomes an unmanaged policy.
    let original = match input {
        Some(NestedInput::Direct(pending)) => Some(pending.capture()?),
        Some(NestedInput::Courier(courier)) => {
            Some(trust_build_tree::admission::InheritedFixedClaim::from_descendant(&courier)?)
        }
        None => {
            ensure!(
                !environment
                    .contains_key(OsStr::new(trust_build_tree::admission::FIXED_HANDOFF_ENV))
                    && !environment.contains_key(OsStr::new(cargo_util::FIXED_CLAIM_HANDOFF_ENV)),
                "advertised original budget input was not captured at native entry"
            );
            None
        }
    };
    if let Some(original) = &original {
        let limit = original.limited_budget(
            environment
                .get(OsStr::new("CARGO_BUILD_JOBS"))
                .map(OsString::as_os_str),
        )?;
        options.request.maximum_jobs =
            Some(options.request.maximum_jobs.map_or(limit, |n| n.min(limit)));
    }
    let key = format!(
        "TRUST_HOST_{}",
        options
            .request
            .workload
            .name()
            .to_uppercase()
            .replace('-', "_")
    );
    let mut overrides = Vec::new();
    for (suffix, selected) in [
        ("WANT_GIB", &mut options.request.want_bytes),
        ("FLOOR_GIB", &mut options.request.floor_bytes),
    ] {
        let name = format!("{key}_{suffix}");
        if let Some(raw) = environment
            .get(OsStr::new(&name))
            .filter(|raw| !raw.is_empty())
        {
            let raw = raw
                .to_str()
                .context("workload memory override is not UTF8")?;
            *selected = Some(gib_value(raw)?);
            overrides.push((name, raw.to_owned()));
        }
    }
    let report = match budget::current(&options.request, original.as_ref()) {
        Ok(report) => report,
        Err(error) => {
            writeln!(
                std::io::stdout().lock(),
                "{}",
                serde_json::json!({
                    "protocol": "native-host-budget-v1", "authority": "policy_data_only_no_admission",
                    "outcome": "unavailable", "message": error.to_string(), "raw_os_error": error.raw_os_error()
                })
            )?;
            return Ok(3);
        }
    };
    writeln!(
        std::io::stderr().lock(),
        "native-budget: {} CPUs observed, {} bytes conservatively available; policy DATA only, no admission",
        report.host.cpus,
        report.host.available_memory_bytes
    )?;
    match options.mode.as_str() {
        "measure" => writeln!(
            std::io::stdout().lock(),
            "{}",
            serde_json::json!({
                "protocol": report.protocol, "authority": report.authority, "host": &report.host,
                "cpu_scope": &report.cpu_scope
            })
        )?,
        "plan" => writeln!(
            std::io::stdout().lock(),
            "{}",
            serde_json::json!({"report": &report, "overrides": overrides})
        )?,
        "jobs" => writeln!(std::io::stdout().lock(), "{}", report.plan.jobs)?,
        "admit-overlap" => {
            writeln!(
                std::io::stdout().lock(),
                "{}",
                serde_json::to_string(&report.overlap)?
            )?;
            return Ok(if report.overlap == Some(Overlap::FitsMeasuredMemory) {
                0
            } else {
                1
            });
        }
        "governor" => writeln!(
            std::io::stdout().lock(),
            "TRUST_GOV_CRITICAL_GIB={}\nTRUST_GOV_RESUME_GIB={}",
            report.governor.critical_gib,
            report.governor.resume_gib
        )?,
        _ => unreachable!("closed parser"),
    }
    Ok(
        if matches!(options.mode.as_str(), "plan" | "jobs")
            && report.plan.outcome != Outcome::FitsMeasuredMemory
        {
            3
        } else {
            0
        },
    )
}

#[cfg(test)]
#[path = "resource_budget/tests.rs"]
mod tests;
