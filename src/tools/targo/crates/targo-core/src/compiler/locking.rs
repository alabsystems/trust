//! This module handles the locking logic during compilation.

use crate::util::flock;
use crate::{
    CargoResult,
    compiler::{BuildRunner, Unit},
    util::{FileLock, Filesystem},
};

use crate::util::data_structures::{HashMap, HashSet};
use anyhow::bail;
use std::{
    fmt::{Display, Formatter},
    path::PathBuf,
    sync::RwLock,
};
use tracing::instrument;

/// A struct to store the lock handles for build units during compilation.
pub struct LockManager {
    held: RwLock<HeldLocks>,
}

#[derive(Default)]
struct HeldLocks {
    units: HashMap<LockKey, FileLock>,
    // Some marks a complete selected graph generation. Its rights never grow
    // after command preparation, and writers retain EX until retirement.
    graph_writers: Option<HashSet<LockKey>>,
}

struct Request {
    key: LockKey,
    message: String,
    exclusive: bool,
}

impl LockManager {
    pub fn new() -> Self {
        Self {
            held: RwLock::new(HeldLocks::default()),
        }
    }

    // Trust: acquire a complete read/write generation before any compiler
    // callback or publication Work. A partial acquisition is always dropped
    // BEFORE waiting on exactly one contested key, preventing cross-build
    // hold-and-wait. Independent read sets and disjoint writes still coexist.
    pub fn lock_selected_graph(
        &self,
        build_runner: &mut BuildRunner<'_, '_>,
        exec: &dyn super::Executor,
    ) -> CargoResult<()> {
        if !self.held.read().unwrap().units.is_empty() {
            bail!("selected graph lease preparation already has unit leases");
        }
        build_runner.lease_forces = None;
        build_runner.requested_forces = None;
        let mut pending = build_runner.bcx.roots.clone();
        let mut selected = HashSet::default();
        while let Some(unit) = pending.pop() {
            if selected.insert(unit.clone()) {
                pending.extend(
                    build_runner
                        .unit_deps(&unit)
                        .iter()
                        .map(|dep| dep.unit.clone()),
                );
            }
        }
        let mut units: Vec<_> = selected.into_iter().collect();
        units.sort_unstable();
        let roots: HashSet<_> = build_runner.bcx.roots.iter().cloned().collect();
        // Query each applicable original executor exactly once, as compile()
        // did. No-op/doc-test/custom-script paths do not invent that callback.
        let forces: HashMap<_, _> = units
            .iter()
            .map(|unit| {
                let force = !unit.skip_non_compile_time_dep
                    && !unit.mode.is_doc_test()
                    && !unit.mode.is_run_custom_build()
                    && (exec.force_rebuild(unit)
                        || (roots.contains(unit) && build_runner.bcx.build_config.force_rebuild));
                (unit.clone(), force)
            })
            .collect();
        let mtime_writes = build_runner.bcx.gctx.cli_unstable().mtime_on_use;
        loop {
            let read_requests = Self::requests(build_runner, &units, &HashSet::default(), false);
            let read_set = Self::acquire(&read_requests, build_runner.bcx.gctx)?;
            Self::refresh(build_runner)?;
            let writers = Self::compile_writers(build_runner, &units, &forces)?;
            if writers.is_empty() && !mtime_writes {
                build_runner.requested_forces = Some(forces.clone());
                build_runner.lease_forces = Some(forces);
                *self.held.write().unwrap() = read_set;
                return Ok(());
            }
            // Releasing the whole snapshot is mandatory: two invocations can
            // require opposite A/B upgrades even after both acquired all reads.
            drop(read_set);
            let requests = Self::requests(build_runner, &units, &writers, mtime_writes);
            let owned = Self::acquire(&requests, build_runner.bcx.gctx)?;
            Self::refresh(build_runner)?;
            let current = Self::compile_writers(build_runner, &units, &forces)?;
            if current.iter().any(|unit| {
                !owned
                    .graph_writers
                    .as_ref()
                    .unwrap()
                    .contains(&LockKey::from_unit(build_runner, unit))
            }) {
                drop(owned);
                continue;
            }
            // A producer can replace a dependency with different metadata even
            // when its logical fingerprint is identical. Reserve its dependent
            // closure for rebuilding too, never promote an inline Fresh job.
            build_runner.lease_forces = Some(
                units
                    .iter()
                    .map(|unit| (unit.clone(), forces[unit] || current.contains(unit)))
                    .collect(),
            );
            build_runner.requested_forces = Some(forces);
            *self.held.write().unwrap() = owned;
            return Ok(());
        }
    }

    fn refresh(build_runner: &mut BuildRunner<'_, '_>) -> CargoResult<()> {
        super::fingerprint::reset_plan_observations(build_runner);
        // These commands are derived planning data, not executed captures.
        // SourceInputs stay original and for_unit revalidates ensure_current.
        build_runner.action_commands.clear();
        // Re-read the SAME bounded receipt/control loader after a lease wait;
        // clearing fingerprint memoization alone cannot refresh cached scripts.
        super::custom_build::build_map(build_runner)
    }

    fn compile_writers(
        build_runner: &mut BuildRunner<'_, '_>,
        units: &[Unit],
        forces: &HashMap<Unit, bool>,
    ) -> CargoResult<HashSet<Unit>> {
        let mut writers = HashSet::default();
        let mut parents: HashMap<Unit, Vec<Unit>> = HashMap::default();
        for unit in units {
            if unit.skip_non_compile_time_dep || unit.mode.is_doc_test() {
                continue;
            }
            let bcx = build_runner.bcx;
            for dep in build_runner.unit_deps(unit).iter().filter(|dep| {
                unit.mode.is_run_custom_build()
                    || super::fingerprint::dependency_rebuilds(bcx, unit, dep)
            }) {
                parents
                    .entry(dep.unit.clone())
                    .or_default()
                    .push(unit.clone());
            }
            if super::fingerprint::lease_needs_write(build_runner, unit, forces[unit])? {
                writers.insert(unit.clone());
            }
        }
        let mut pending: Vec<_> = writers.iter().cloned().collect();
        while let Some(unit) = pending.pop() {
            if let Some(users) = parents.get(&unit) {
                for user in users {
                    if writers.insert(user.clone()) {
                        pending.push(user.clone());
                    }
                }
            }
        }
        Ok(writers)
    }

    fn requests(
        build_runner: &BuildRunner<'_, '_>,
        units: &[Unit],
        writers: &HashSet<Unit>,
        mtime_writes: bool,
    ) -> Vec<Request> {
        let mut keys: HashMap<LockKey, Request> = HashMap::default();
        for unit in units {
            let key = LockKey::from_unit(build_runner, unit);
            let exclusive = writers.contains(unit)
                || (mtime_writes && !unit.skip_non_compile_time_dep && !unit.mode.is_doc_test());
            keys.entry(key.clone())
                .and_modify(|request| request.exclusive |= exclusive)
                .or_insert_with(|| Request {
                    key,
                    message: format!(
                        "{} ({})",
                        unit.pkg.name(),
                        build_runner.files().unit_hash(unit)
                    ),
                    exclusive,
                });
        }
        let mut requests: Vec<_> = keys.into_values().collect();
        requests.sort_by(|a, b| a.key.0.cmp(&b.key.0));
        requests
    }

    fn acquire(requests: &[Request], gctx: &crate::util::GlobalContext) -> CargoResult<HeldLocks> {
        loop {
            let mut units = HashMap::default();
            let mut writers = HashSet::default();
            let mut contested = None;
            for request in requests {
                let fs = Filesystem::new(request.key.0.clone());
                let acquired = if request.exclusive {
                    fs.try_open_rw_exclusive_create(&request.key.0)?
                } else {
                    fs.try_open_ro_shared_create(&request.key.0)?
                };
                match acquired {
                    Some(lease) => {
                        if request.exclusive {
                            writers.insert(request.key.clone());
                        }
                        units.insert(request.key.clone(), lease);
                    }
                    None => {
                        contested = Some(request);
                        break;
                    }
                }
            }
            let Some(request) = contested else {
                return Ok(HeldLocks {
                    units,
                    graph_writers: Some(writers),
                });
            };
            drop(units);
            let fs = Filesystem::new(request.key.0.clone());
            let wait = if request.exclusive {
                fs.open_rw_exclusive_create(&request.key.0, gctx, &request.message)?
            } else {
                fs.open_ro_shared_create(&request.key.0, gctx, &request.message)?
            };
            drop(wait);
        }
    }

    #[instrument(skip_all, fields(key))]
    pub fn lock_shared(
        &self,
        build_runner: &BuildRunner<'_, '_>,
        unit: &Unit,
    ) -> CargoResult<LockKey> {
        let key = LockKey::from_unit(build_runner, unit);
        tracing::Span::current().record("key", key.0.to_str());
        let mut held = self.held.write().unwrap();
        if held.graph_writers.is_some() {
            if !held.units.contains_key(&key) {
                bail!("unit is outside the selected lease generation: {key}");
            }
            return Ok(key);
        }
        if let Some(lock) = held.units.get_mut(&key) {
            flock::lock_shared(lock.file())?;
        } else {
            let fs = Filesystem::new(key.0.clone());
            let message = format!(
                "{} ({})",
                unit.pkg.name(),
                build_runner.files().unit_hash(unit)
            );
            held.units.insert(
                key.clone(),
                fs.open_ro_shared_create(&key.0, build_runner.bcx.gctx, &message)?,
            );
        }
        Ok(key)
    }

    // Trust: called during planning, immediately after pure inspection and
    // before source validation, fingerprint truncation or Work/callback setup.
    pub(super) fn require_selected_write(
        &self,
        build_runner: &BuildRunner<'_, '_>,
        unit: &Unit,
    ) -> CargoResult<()> {
        let compilation_selected = build_runner
            .lease_forces
            .as_ref()
            .and_then(|selected| selected.get(unit))
            .copied()
            .unwrap_or(false);
        self.require_write_key(
            &LockKey::from_unit(build_runner, unit),
            compilation_selected,
        )
    }

    fn require_write_key(&self, key: &LockKey, compilation_selected: bool) -> CargoResult<()> {
        let held = self.held.read().unwrap();
        if compilation_selected
            && held
                .graph_writers
                .as_ref()
                .is_some_and(|writers| writers.contains(key))
            && held.units.contains_key(key)
        {
            Ok(())
        } else {
            bail!(
                "cache inputs changed after lease selection; dirty unit has no selected write lease: {key}"
            )
        }
    }

    #[instrument(skip(self))]
    pub fn lock(&self, key: &LockKey) -> CargoResult<()> {
        let held = self.held.read().unwrap();
        if let Some(writers) = &held.graph_writers {
            if !writers.contains(key) {
                bail!("unit has no selected write lease: {key}");
            }
            return Ok(());
        }
        if let Some(lock) = held.units.get(key) {
            flock::lock_exclusive(lock.file())?;
        } else {
            bail!("lock was not found in lock manager: {key}");
        }
        Ok(())
    }

    #[instrument(skip(self))]
    pub fn downgrade_to_shared(&self, key: &LockKey) -> CargoResult<()> {
        let held = self.held.read().unwrap();
        if held.graph_writers.is_some() {
            return Ok(());
        }
        let Some(lock) = held.units.get(key) else {
            bail!("lock was not found in lock manager: {key}");
        };
        flock::lock_shared(lock.file())?;
        Ok(())
    }

    #[instrument(skip(self))]
    pub fn unlock(&self, key: &LockKey) -> CargoResult<()> {
        let held = self.held.read().unwrap();
        if held.graph_writers.is_some() {
            return Ok(());
        }
        if let Some(lock) = held.units.get(key) {
            flock::unlock(lock.file())?;
        }
        Ok(())
    }

    /// Retire every actual unit right after all compiler workers joined.
    pub(crate) fn release_all(&self) {
        *self.held.write().unwrap() = HeldLocks::default();
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct LockKey(PathBuf);

impl LockKey {
    fn from_unit(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> Self {
        Self(build_runner.files().build_unit_lock(unit))
    }
}

impl Display for LockKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.display())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_generation_never_gains_dirty_publication_rights() {
        let root = tempfile::tempdir().unwrap();
        let key = LockKey(root.path().join("unit.lock"));
        let gctx = crate::util::GlobalContext::default().unwrap();
        let requests = |exclusive| {
            vec![Request {
                key: key.clone(),
                message: "actual unit right".into(),
                exclusive,
            }]
        };
        let manager = LockManager::new();
        *manager.held.write().unwrap() = LockManager::acquire(&requests(false), &gctx).unwrap();
        assert!(manager.require_write_key(&key, true).is_err());
        // Refusal must not silently upgrade the read lease. An independent
        // kernel read lease still succeeds while a writer remains excluded.
        let fs = Filesystem::new(root.path().to_path_buf());
        let sibling = fs.try_open_ro_shared_create(&key.0).unwrap().unwrap();
        assert!(fs.try_open_rw_exclusive_create(&key.0).unwrap().is_none());
        drop(sibling);
        manager.release_all();
        *manager.held.write().unwrap() = LockManager::acquire(&requests(true), &gctx).unwrap();
        // Mtime-on-use may own EX solely for timestamp metadata. That cannot
        // license a late compiler write outside the planned dependent closure.
        assert!(manager.require_write_key(&key, false).is_err());
        manager.require_write_key(&key, true).unwrap();
        assert!(fs.try_open_ro_shared_create(&key.0).unwrap().is_none());
        manager.release_all();
        assert!(
            manager.require_write_key(&key, true).is_err(),
            "a retired generation grants no write right"
        );
    }
}
