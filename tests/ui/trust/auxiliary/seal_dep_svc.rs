//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_async_trust.rs` and its `_holds`
//! twin: a service crate that keeps what it is handed, as plain fns and as
//! `async fn`s with the same bodies. Safe, and sound.
#![forbid(unsafe_code)]

pub fn record<T>(log: &mut Vec<T>, t: T) {
    log.push(t)
}
pub fn serve_sync<T>(t: T) -> Vec<T> {
    let mut log = Vec::new();
    record(&mut log, t);
    log
}
pub async fn serve<T>(t: T) -> Vec<T> {
    let mut log = Vec::new();
    record(&mut log, t);
    log
}
pub fn step<T>(t: T) -> T {
    t
}
pub fn relay_sync<T>(t: T, n: u32) -> T {
    let mut t = t;
    for _ in 0..n {
        t = step(t);
    }
    t
}
pub async fn relay<T>(t: T, n: u32) -> T {
    let mut t = t;
    for _ in 0..n {
        t = step(t);
    }
    t
}
