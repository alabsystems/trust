// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Provider-dispatch DATA controls; no cache, SDK or concurrency authority.

use super::*;
use crate::sources::IndexSummary;
use crate::sources::source::{QueryKind, Source};
use cargo_util_terminal::Shell;

struct Provider {
    id: SourceId,
    label: &'static str,
    packages: Vec<Package>,
    calls: Rc<RefCell<Vec<String>>>,
    invalidated: Cell<bool>,
    gate: Option<Rc<DownloadGate>>,
}

#[derive(Default)]
struct DownloadGate {
    open: Cell<bool>,
    entered: RefCell<Vec<PackageId>>,
    waiters: RefCell<Vec<std::task::Waker>>,
}

#[async_trait::async_trait(?Send)]
impl Source for Provider {
    fn source_id(&self) -> SourceId {
        self.id
    }
    fn supports_checksums(&self) -> bool {
        false
    }
    fn requires_precise(&self) -> bool {
        false
    }
    async fn query(
        &self,
        dependency: &Dependency,
        _: QueryKind,
        emit: &mut dyn FnMut(IndexSummary),
    ) -> CargoResult<()> {
        anyhow::ensure!(
            self.invalidated.get(),
            "{} still has stale index data",
            self.label
        );
        let package = self
            .packages
            .iter()
            .find(|package| package.name() == dependency.package_name())
            .ok_or_else(|| anyhow::anyhow!("{} does not supply queried package", self.label))?;
        self.calls
            .borrow_mut()
            .push(format!("{}:query:{}", self.label, package.name()));
        emit(IndexSummary::Yanked(package.summary().clone()));
        Ok(())
    }
    fn invalidate_cache(&self) {
        self.invalidated.set(true);
        self.calls
            .borrow_mut()
            .push(format!("{}:invalidate", self.label));
    }
    fn set_quiet(&mut self, _: bool) {}
    async fn download(&self, id: PackageId) -> CargoResult<MaybePackage> {
        if let Some(gate) = &self.gate {
            gate.entered.borrow_mut().push(id);
            std::future::poll_fn(|context| {
                if gate.open.get() {
                    std::task::Poll::Ready(())
                } else {
                    gate.waiters.borrow_mut().push(context.waker().clone());
                    std::task::Poll::Pending
                }
            })
            .await;
        }
        self.calls
            .borrow_mut()
            .push(format!("{}:download:{}", self.label, id.name()));
        let package = self
            .packages
            .iter()
            .find(|p| p.package_id() == id)
            .ok_or_else(|| anyhow::anyhow!("{} does not supply {id}", self.label))?;
        Ok(MaybePackage::Ready(package.clone()))
    }
    async fn finish_download(&self, _: PackageId, _: Vec<u8>) -> CargoResult<Package> {
        anyhow::bail!("unexpected remote download in provider-dispatch control")
    }
    fn fingerprint(&self, package: &Package) -> CargoResult<String> {
        let result = format!("{}:fingerprint:{}", self.label, package.name());
        self.calls.borrow_mut().push(result.clone());
        Ok(result)
    }
    fn verify(&self, id: PackageId) -> CargoResult<()> {
        anyhow::ensure!(
            self.packages.iter().any(|p| p.package_id() == id),
            "wrong provider for {id}"
        );
        self.calls
            .borrow_mut()
            .push(format!("{}:verify:{}", self.label, id.name()));
        Ok(())
    }
    fn describe(&self) -> String {
        self.label.to_owned()
    }
}

fn context(root: &Path) -> GlobalContext {
    let home = root.join("home");
    std::fs::create_dir_all(&home).unwrap();
    GlobalContext::new(
        Shell::from_write(Box::new(Vec::<u8>::new())),
        root.to_owned(),
        home,
    )
}

fn package(
    root: &Path,
    directory: &str,
    name: &str,
    source: SourceId,
    gctx: &GlobalContext,
) -> Package {
    let directory = root.join(directory);
    std::fs::create_dir_all(directory.join("src")).unwrap();
    std::fs::write(directory.join("src/lib.rs"), "").unwrap();
    let manifest = directory.join("Cargo.toml");
    std::fs::write(
        &manifest,
        format!("[package]\nname = '{name}'\nversion = '1.0.0'\nedition = '2021'\n"),
    )
    .unwrap();
    crate::ops::read_package(&manifest, source, gctx).unwrap()
}

fn map(
    source: SourceId,
    label: &'static str,
    packages: Vec<Package>,
    calls: &Rc<RefCell<Vec<String>>>,
) -> SourceMap<'static> {
    let mut map = SourceMap::new();
    map.insert(Box::new(Provider {
        id: source,
        label,
        packages,
        calls: Rc::clone(calls),
        invalidated: Cell::new(false),
        gate: None,
    }));
    map
}

fn check_dispatch(set: &PackageSet<'_>, id: PackageId, expected: &str) {
    let package = set.get_one(id).unwrap();
    let sources = set.sources();
    let provider = sources.package_source(id).unwrap();
    provider.verify(id).unwrap();
    assert_eq!(
        provider.fingerprint(package).unwrap(),
        format!("{expected}:fingerprint:{}", id.name())
    );
}

#[test]
fn merge_retains_left_resident_and_right_unique_provider_with_same_source_id() {
    let root = tempfile::tempdir().unwrap();
    let gctx = context(root.path());
    let source =
        SourceId::for_registry(&url::Url::parse("https://origin.invalid/index").unwrap()).unwrap();
    let left = package(root.path(), "left", "duplicate", source, &gctx);
    let right = package(root.path(), "right", "duplicate", source, &gctx);
    let unique = package(root.path(), "unique", "unique", source, &gctx);
    let calls = Rc::new(RefCell::new(Vec::new()));
    let mut a = PackageSet::new(
        &[left.package_id()],
        map(source, "left", vec![left.clone()], &calls),
        &gctx,
    )
    .unwrap();
    let b = PackageSet::new(
        &[right.package_id(), unique.package_id()],
        map(source, "right", vec![right.clone(), unique.clone()], &calls),
        &gctx,
    )
    .unwrap();
    a.packages[&left.package_id()]
        .set(left.clone())
        .ok()
        .unwrap();
    b.packages[&right.package_id()].set(right).ok().unwrap();
    b.packages[&unique.package_id()]
        .set(unique.clone())
        .ok()
        .unwrap();
    a.add_set(b);
    assert_eq!(
        a.get_one(left.package_id()).unwrap().manifest_path(),
        left.manifest_path()
    );
    check_dispatch(&a, left.package_id(), "left");
    check_dispatch(&a, unique.package_id(), "right");
    assert_eq!(
        &*calls.borrow(),
        &[
            "left:verify:duplicate",
            "left:fingerprint:duplicate",
            "right:verify:unique",
            "right:fingerprint:unique"
        ]
    );
}

#[test]
fn merge_keeps_left_empty_slot_origin_instead_of_discarded_right_resident() {
    let root = tempfile::tempdir().unwrap();
    let gctx = context(root.path());
    let source =
        SourceId::for_registry(&url::Url::parse("https://origin.invalid/index").unwrap()).unwrap();
    let left = package(root.path(), "left", "duplicate", source, &gctx);
    let right = package(root.path(), "right", "duplicate", source, &gctx);
    let calls = Rc::new(RefCell::new(Vec::new()));
    let mut a = PackageSet::new(
        &[left.package_id()],
        map(source, "left", vec![left.clone()], &calls),
        &gctx,
    )
    .unwrap();
    let b = PackageSet::new(
        &[right.package_id()],
        map(source, "right", vec![right.clone()], &calls),
        &gctx,
    )
    .unwrap();
    b.packages[&right.package_id()].set(right).ok().unwrap();
    a.add_set(b);
    assert!(a.packages[&left.package_id()].get().is_none());
    check_dispatch(&a, left.package_id(), "left");
    assert_eq!(
        a.get_one(left.package_id()).unwrap().manifest_path(),
        left.manifest_path()
    );
    assert_eq!(
        &*calls.borrow(),
        &[
            "left:download:duplicate",
            "left:verify:duplicate",
            "left:fingerprint:duplicate"
        ]
    );
}

#[test]
fn all_sources_invalidates_distinct_retained_wrappers_once() {
    let root = tempfile::tempdir().unwrap();
    let gctx = context(root.path());
    let source =
        SourceId::for_registry(&url::Url::parse("https://origin.invalid/index").unwrap()).unwrap();
    let left = package(root.path(), "left", "left", source, &gctx);
    let right = package(root.path(), "right", "right", source, &gctx);
    let calls = Rc::new(RefCell::new(Vec::new()));
    let left_id = left.package_id();
    let right_id = right.package_id();
    let mut a = PackageSet::new(
        &[left.package_id()],
        map(source, "left", vec![left], &calls),
        &gctx,
    )
    .unwrap();
    let b = PackageSet::new(
        &[right.package_id()],
        map(source, "right", vec![right], &calls),
        &gctx,
    )
    .unwrap();
    a.add_set(b);
    // Establish the stale baseline for BOTH selected provider wrappers.
    for id in [left_id, right_id] {
        let dependency = Dependency::parse(id.name(), Some("1.0.0"), source).unwrap();
        assert!(
            crate::util::block_on(
                a.sources()
                    .package_source(id)
                    .unwrap()
                    .query_vec(&dependency, QueryKind::Exact)
            )
            .is_err()
        );
    }
    for provider in a.sources().all_sources() {
        provider.invalidate_cache();
    }
    for id in [left_id, right_id] {
        let dependency = Dependency::parse(id.name(), Some("1.0.0"), source).unwrap();
        let result = crate::util::block_on(
            a.sources()
                .package_source(id)
                .unwrap()
                .query_vec(&dependency, QueryKind::Exact),
        )
        .unwrap();
        assert_eq!(result.len(), 1);
        match &result[0] {
            IndexSummary::Yanked(summary) => assert_eq!(summary.package_id(), id),
            _ => panic!("current provider must report its actual yanked summary"),
        }
    }
    let mut actual = calls.borrow().clone();
    actual.sort();
    assert_eq!(
        actual,
        [
            "left:invalidate",
            "left:query:left",
            "right:invalidate",
            "right:query:right"
        ]
    );
}

// Directory-at-lock-path is a genuine EISDIR refusal on these hosts.
// Windows may classify it as a tolerated read-only cache instead.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn resident_get_many_preserves_order_and_duplicates_without_download_lock() {
    let root = tempfile::tempdir().unwrap();
    let gctx = context(root.path());
    let source =
        SourceId::for_registry(&url::Url::parse("https://origin.invalid/index").unwrap()).unwrap();
    let a = package(root.path(), "a", "a", source, &gctx);
    let b = package(root.path(), "b", "b", source, &gctx);
    let calls = Rc::new(RefCell::new(Vec::new()));
    // This provider refuses every download: these packages are already loaded.
    let set = PackageSet::new(
        &[a.package_id(), b.package_id()],
        map(source, "no-download", Vec::new(), &calls),
        &gctx,
    )
    .unwrap();
    set.packages[&a.package_id()].set(a.clone()).ok().unwrap();
    set.packages[&b.package_id()].set(b.clone()).ok().unwrap();
    let obstruction = gctx.home().as_path_unlocked().join(".package-cache");
    std::fs::create_dir(&obstruction).unwrap();
    // Establish that the old Downloads path really cannot acquire this lock.
    assert!(
        gctx.acquire_package_cache_lock(CacheLockMode::DownloadExclusive)
            .is_err()
    );
    let result = set
        .get_many([b.package_id(), a.package_id(), b.package_id()])
        .unwrap();
    assert_eq!(
        result
            .iter()
            .map(|package| package.package_id())
            .collect::<Vec<_>>(),
        [b.package_id(), a.package_id(), b.package_id()]
    );
    assert_eq!(
        result
            .iter()
            .map(|package| package.manifest_path())
            .collect::<Vec<_>>(),
        [b.manifest_path(), a.manifest_path(), b.manifest_path()]
    );
    assert!(calls.borrow().is_empty());
    assert!(obstruction.is_dir());
}

#[test]
fn materialized_replaced_source_retains_mapping_for_verification() {
    let root = tempfile::tempdir().unwrap();
    let gctx = context(root.path());
    let canonical =
        SourceId::for_registry(&url::Url::parse("https://canonical.invalid/index").unwrap())
            .unwrap();
    let replacement =
        SourceId::for_registry(&url::Url::parse("https://replacement.invalid/index").unwrap())
            .unwrap();
    let inner = package(root.path(), "inner", "replaced", replacement, &gctx);
    let id = inner.package_id().with_source_id(canonical);
    let calls = Rc::new(RefCell::new(Vec::new()));
    let provider = Provider {
        id: replacement,
        label: "replacement",
        packages: vec![inner],
        calls: Rc::clone(&calls),
        invalidated: Cell::new(false),
        gate: None,
    };
    let mut sources = SourceMap::new();
    sources.insert(Box::new(crate::sources::replaced::ReplacedSource::new(
        canonical,
        replacement,
        Box::new(provider),
    )));
    let set = PackageSet::new(&[id], sources, &gctx).unwrap();
    check_dispatch(&set, id, "replacement");
    assert_eq!(set.get_one(id).unwrap().package_id(), id);
    assert_eq!(
        &*calls.borrow(),
        &[
            "replacement:download:replaced",
            "replacement:verify:replaced",
            "replacement:fingerprint:replaced"
        ]
    );
}

#[test]
fn unloaded_duplicates_share_one_in_flight_load_and_keep_requested_order() {
    use std::future::Future as _;
    use std::task::{Context, Poll};

    let root = tempfile::tempdir().unwrap();
    let gctx = context(root.path());
    let source =
        SourceId::for_registry(&url::Url::parse("https://origin.invalid/index").unwrap()).unwrap();
    let a = package(root.path(), "a", "a", source, &gctx);
    let b = package(root.path(), "b", "b", source, &gctx);
    let calls = Rc::new(RefCell::new(Vec::new()));
    let gate = Rc::new(DownloadGate::default());
    let mut sources = SourceMap::new();
    sources.insert(Box::new(Provider {
        id: source,
        label: "gated",
        packages: vec![a.clone(), b.clone()],
        calls: Rc::clone(&calls),
        invalidated: Cell::new(false),
        gate: Some(Rc::clone(&gate)),
    }));
    let set = PackageSet::new(&[a.package_id(), b.package_id()], sources, &gctx).unwrap();
    let requested = [b.package_id(), a.package_id(), b.package_id()];
    let mut loading = Box::pin(Downloads::download(&set, requested));
    let mut context = Context::from_waker(futures::task::noop_waker_ref());
    // Drive the actual download future until every source future is pending.
    // The closed gate cannot complete any slot and uses no thread or clock.
    assert!(matches!(loading.as_mut().poll(&mut context), Poll::Pending));
    let mut entered = gate.entered.borrow().clone();
    entered.sort();
    let mut unique = vec![a.package_id(), b.package_id()];
    unique.sort();
    assert_eq!(
        entered, unique,
        "a repeated unloaded ID started a second load"
    );
    assert!(set.packages.values().all(|slot| slot.get().is_none()));
    gate.open.set(true);
    for waiter in gate.waiters.borrow_mut().drain(..) {
        waiter.wake();
    }
    let loaded = crate::util::block_on(loading).unwrap();
    assert_eq!(
        loaded
            .iter()
            .map(|package| package.package_id())
            .collect::<Vec<_>>(),
        requested
    );
    assert_eq!(
        loaded
            .iter()
            .map(|package| package.manifest_path())
            .collect::<Vec<_>>(),
        [b.manifest_path(), a.manifest_path(), b.manifest_path()]
    );
    assert!(std::ptr::eq(loaded[0], loaded[2]));
    let mut actual = calls.borrow().clone();
    actual.sort();
    assert_eq!(actual, ["gated:download:a", "gated:download:b"]);
    check_dispatch(&set, a.package_id(), "gated");
    check_dispatch(&set, b.package_id(), "gated");
}
