// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

// Exact registry/proxy scheduling controls only, never authenticated NativeV3,
// actual compiler join, host loan, or implicit CPU grant fixtures.
use std::sync::mpsc;
use std::time::{Duration, Instant};

use super::super::{Client, Proxy};
use super::*;

fn proxy(registry: &Arc<Registry>, width: usize) -> Arc<Proxy> {
    Proxy::build_client(Client::new(width).unwrap(), Some(registry.clone()))
}
fn eligible(registry: &Registry) -> bool {
    Registry::eligible(&mut registry.enter().unwrap(), std::thread::current().id()).unwrap()
}
fn pending(proxy: &Proxy) {
    let end = Instant::now() + Duration::from_secs(60);
    while proxy.shared.data.lock().pending == 0 {
        assert!(Instant::now() < end, "worker did not request admission");
        std::thread::yield_now();
    }
}
#[test]
fn actual_thread_ownership_and_release_are_required_for_registry_eligibility() {
    let registry = Registry::new();
    let proxy = proxy(&registry, 1);
    assert!(eligible(&registry)); // actual creator is the assumed main
    let (entered, wait_entered) = mpsc::channel();
    let (release, wait_release) = mpsc::channel();
    let other = proxy.clone();
    let thread = std::thread::spawn(move || {
        other.acquire_thread();
        entered.send(()).unwrap();
        wait_release.recv().unwrap();
        other.release_thread();
    });
    wait_entered.recv_timeout(Duration::from_secs(60)).unwrap();
    assert!(!eligible(&registry));
    release.send(()).unwrap();
    thread.join().unwrap();
    assert!(eligible(&registry));
    proxy.release_thread();
    assert!(eligible(&registry)); // zero active is also admissible
}
#[test]
fn pending_and_reserved_work_cannot_be_mistaken_for_quiescence() {
    let registry = Registry::new();
    let proxy = proxy(&registry, 0);
    let other = proxy.clone();
    let thread = std::thread::spawn(move || {
        other.acquire_thread();
        other.release_thread();
    });
    pending(&proxy);
    assert!(!eligible(&registry));
    // The implicit handoff is serialized through the real release/dispatch
    // code. Its intermediate used-minus-active reservation cannot be parked.
    proxy.release_thread();
    thread.join().unwrap();
    assert!(eligible(&registry));
    {
        let _registry = registry.enter().unwrap();
        let mut data = proxy.shared.data.lock();
        data.used = 1; // private RESERVED-state negative, no CPU entitlement
        assert_eq!(reserved(&data).unwrap(), 1);
    }
    assert!(!eligible(&registry));
    proxy.shared.data.lock().used = 0;
}
#[test]
fn parked_registry_rejects_new_proxies_and_poison_wakes_pending_dispatch() {
    let registry = Registry::new();
    let proxy = proxy(&registry, 0);
    registry.state.lock().phase = Phase::Parked(1); // registry-only state fixture
    assert!(registry.enter().is_err());
    assert!(registry.register(&proxy.shared).is_err());
    registry.state.lock().phase = Phase::Running;
    let other = proxy.clone();
    let thread = std::thread::spawn(move || {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| other.acquire_thread())).is_err()
    });
    pending(&proxy);
    registry.poison();
    assert!(thread.join().unwrap());
    assert!(proxy.shared.data.lock().error.is_some());
    assert!(registry.enter().is_err());
}

#[test]
fn asynchronous_failure_publication_while_parked_poison_notifies_instead_of_panicking() {
    let registry = Registry::new();
    let proxy = proxy(&registry, 0);
    // Failed core acquisition already ended: zero extras can legitimately be
    // parked before its asynchronous callback. No grant/join proof is implied.
    registry.state.lock().phase = Phase::Parked(1);
    assert!(registry.callback(true).is_none());
    assert!(proxy.shared.data.lock().error.is_some());
    assert!(matches!(registry.state.lock().phase, Phase::Poisoned));
    // Even an impossible successful offer while parked is never published.
    let other = Registry::new();
    other.state.lock().phase = Phase::Parked(1);
    assert!(other.callback(false).is_none());
    assert!(other.enter().is_err());
}
