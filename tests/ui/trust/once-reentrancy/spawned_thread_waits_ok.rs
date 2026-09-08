//@ check-pass
//@ compile-flags: -Ztrust-verify=off
//
// Trust: aterm's live `QUARANTINE` shape (crates/aterm-gui/src/control.rs): the
// initializer SPAWNS a reaper thread that later waits on the same cell, and never
// joins it. The spawned thread parks only until the initializer returns, so this
// is benign — a `std::thread` spawn entry point is a thread boundary, not a
// synchronous edge, for both a fn item and a closure. (A spawn the initializer
// JOINS would deadlock and is a documented false negative of this rule.)

#![allow(dead_code)]

use std::sync::OnceLock;

struct Quarantine;

fn artifact_reply_quarantine() -> &'static Quarantine {
    static QUARANTINE: OnceLock<Quarantine> = OnceLock::new();
    QUARANTINE.get_or_init(|| {
        let _ = std::thread::Builder::new()
            .name("aterm-artifact-quarantine".into())
            .spawn(artifact_reply_quarantine_reaper);
        let _ = std::thread::spawn(|| {
            let _ = artifact_reply_quarantine();
        });
        Quarantine
    })
}

fn artifact_reply_quarantine_reaper() {
    let _quarantine = artifact_reply_quarantine();
}

fn main() {
    let _ = artifact_reply_quarantine();
}
