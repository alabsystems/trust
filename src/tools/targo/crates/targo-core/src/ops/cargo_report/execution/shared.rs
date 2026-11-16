//! The planned native sharing frontier, with separately scoped owning-wait costs.

use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Context as _, bail};
use serde::Serialize;

use super::{UnitRow, compiler_unit};
use crate::CargoResult;
use crate::compiler::UnitIndex;
use crate::util::log_message::{SharedDependencyDecision, SharedDependencyExclusion};

#[derive(Serialize)]
pub(super) struct Frontier {
    scope: &'static str,
    pub(super) availability: &'static str,
    pub(super) eligible_units: Option<u64>,
    pub(super) dependency_blocked_units: Option<u64>,
    pub(super) excluded_units: Option<u64>,
    direct_exclusions: BTreeMap<SharedDependencyExclusion, u64>,
    // These are actual primary-process observations, not cache hits/misses.
    measured_compiler_commands: Option<Classes>,
}

#[derive(Default, Serialize)]
struct Classes {
    eligible: Cost,
    dependency_blocked: Cost,
    excluded: Cost,
}

#[derive(Default, Serialize)]
struct Cost {
    primary_processes: u64,
    successful_units_without_start: u64,
    owning_wait_user_ns: u64,
    owning_wait_system_ns: u64,
    max_single_primary_rss_bytes: Option<u64>,
}

pub(super) fn validate(
    units: &BTreeMap<UnitIndex, UnitRow>,
    policy: Option<bool>,
) -> CargoResult<()> {
    if policy != Some(true) {
        if units.values().any(|unit| unit.shared_dependency.is_some()) {
            bail!("shared dependency decisions lack an enabled policy");
        }
        return Ok(());
    }
    let requested_packages: BTreeSet<_> = units
        .values()
        .filter(|unit| unit.requested)
        .map(|unit| unit.package_id.as_str())
        .collect();
    for unit in units.values() {
        let decision = unit
            .shared_dependency
            .as_ref()
            .context("shared dependency policy lacks full unit coverage")?;
        if !matches!(decision, SharedDependencyDecision::Excluded { .. })
            && (unit.target.kind != "lib"
                || unit.mode.is_any_test()
                || !(unit.mode.is_check() || unit.mode == crate::compiler::CompileMode::Build)
                || requested_packages.contains(unit.package_id.as_str()))
        {
            bail!(
                "shared dependency candidate contradicts its registered target or requested package"
            );
        }
        let mut blocked: Vec<_> = unit
            .dependencies
            .iter()
            .copied()
            .filter(|index| {
                !matches!(
                    units
                        .get(index)
                        .and_then(|unit| unit.shared_dependency.as_ref()),
                    Some(SharedDependencyDecision::Eligible {})
                )
            })
            .collect();
        blocked.sort_unstable();
        blocked.dedup();
        match decision {
            SharedDependencyDecision::Eligible {} if !blocked.is_empty() => {
                bail!("eligible shared dependency lacks a closed eligible dependency set");
            }
            SharedDependencyDecision::DependencyBlocked { dependencies }
                if dependencies.is_empty() || dependencies != &blocked =>
            {
                bail!("shared dependency blockers do not match the original graph edges");
            }
            _ => {}
        }
    }
    // Cargo supplies a DAG, and the producer selects its LEAST dependency-
    // closed fixed point. Local closure alone accepts an all-Eligible cycle.
    let mut pending = BTreeMap::new();
    let mut dependents: BTreeMap<UnitIndex, Vec<UnitIndex>> = BTreeMap::new();
    let mut ready = Vec::new();
    for unit in units.values() {
        let dependencies: BTreeSet<_> = unit.dependencies.iter().copied().collect();
        pending.insert(unit.index, dependencies.len());
        if dependencies.is_empty() {
            ready.push(unit.index);
        }
        for dependency in dependencies {
            dependents.entry(dependency).or_default().push(unit.index);
        }
    }
    let mut reached = 0;
    while let Some(index) = ready.pop() {
        reached += 1;
        for parent in dependents.get(&index).into_iter().flatten() {
            let count = pending
                .get_mut(parent)
                .context("shared dependency parent is missing")?;
            *count = count
                .checked_sub(1)
                .context("shared dependency edge repeated")?;
            if *count == 0 {
                ready.push(*parent);
            }
        }
    }
    if reached != pending.len() {
        bail!("shared dependency frontier contains a cyclic original unit graph");
    }
    Ok(())
}

pub(super) fn summarize(
    units: &BTreeMap<UnitIndex, UnitRow>,
    policy: Option<bool>,
    complete_processes: bool,
) -> CargoResult<Frontier> {
    validate(units, policy)?;
    let mut frontier = Frontier {
        scope: "shared-dependency-planned-frontier-v1",
        availability: match policy {
            None => "unavailable",
            Some(false) => "disabled",
            Some(true) => "complete",
        },
        eligible_units: None,
        dependency_blocked_units: None,
        excluded_units: None,
        direct_exclusions: BTreeMap::new(),
        measured_compiler_commands: None,
    };
    if policy != Some(true) {
        return Ok(frontier);
    }
    let (mut eligible, mut blocked, mut excluded) = (0, 0, 0);
    let mut measured = complete_processes.then(Classes::default);
    for unit in units.values() {
        let decision = unit
            .shared_dependency
            .as_ref()
            .context("missing shared dependency decision")?;
        match decision {
            SharedDependencyDecision::Eligible {} => eligible += 1,
            SharedDependencyDecision::DependencyBlocked { .. } => blocked += 1,
            SharedDependencyDecision::Excluded { reason } => {
                excluded += 1;
                *frontier.direct_exclusions.entry(*reason).or_default() += 1;
            }
        }
        if compiler_unit(unit.mode) {
            if let Some(measured) = &mut measured {
                let cost = match decision {
                    SharedDependencyDecision::Eligible {} => &mut measured.eligible,
                    SharedDependencyDecision::DependencyBlocked { .. } => {
                        &mut measured.dependency_blocked
                    }
                    SharedDependencyDecision::Excluded { .. } => &mut measured.excluded,
                };
                if unit.process.command_started_seconds.is_none() {
                    if unit.outcome
                        == Some(crate::util::log_message::ExecutionUnitOutcome::Succeeded)
                    {
                        cost.successful_units_without_start += 1;
                    }
                } else {
                    let cpu = unit
                        .process
                        .owning_wait_cpu
                        .as_ref()
                        .context("complete compiler costs lack owning CPU")?;
                    let rss = unit
                        .process
                        .peak_rss_bytes
                        .context("complete compiler costs lack owning RSS")?;
                    cost.primary_processes += 1;
                    cost.owning_wait_user_ns = cost
                        .owning_wait_user_ns
                        .checked_add(cpu.user_ns)
                        .context("shared dependency CPU sum overflow")?;
                    cost.owning_wait_system_ns = cost
                        .owning_wait_system_ns
                        .checked_add(cpu.system_ns)
                        .context("shared dependency CPU sum overflow")?;
                    cost.max_single_primary_rss_bytes = Some(
                        cost.max_single_primary_rss_bytes
                            .map_or(rss, |previous| previous.max(rss)),
                    );
                }
            }
        }
    }
    frontier.eligible_units = Some(eligible);
    frontier.dependency_blocked_units = Some(blocked);
    frontier.excluded_units = Some(excluded);
    frontier.measured_compiler_commands = measured;
    Ok(frontier)
}
