//! Step 2 increment 6, step 6.1 (review 2026-10-05): the entry builder's two guards that no test
//! reached before, end to end through rustc
//! (`docs/design/2026-10-02-step2-inc6-trust-ir-in-metadata.md` §2.2, §4).
//!
//! * THE RE-DERIVATION GUARD (`RustcNames::callee_symbol`, "re-derived, not trusted"): a callee
//!   is declared by the symbol of the instance its RAW call site resolves to, and only when that is
//!   the plain item the producer's ledger linked, at the instance the ledger keyed, and not the
//!   body itself. The producer links a free fn on its fast path WITHOUT resolving it, so an
//!   intrinsic (`core::intrinsics::bswap`) reaches the entry builder as a plain `Item` edge;
//!   re-resolved, it is `InstanceKind::Intrinsic`, with no symbol of its own. A recursive call
//!   resolves to the body itself. Both bodies are recorded `unnamed-callee`, each with the guard's
//!   own reason. A generic callee whose site re-resolves to the ledger's item at the ledger's
//!   concrete key is named: `core::ptr::drop_in_place::<String>` (a plain generic item in this
//!   toolchain; the drop-glue shim is `core::ptr::drop_glue`, which it calls), declared by the
//!   PRODUCING session's symbol of that instance (see `rmeta_entry`'s module doc). `call_mix` (a
//!   call to a plain local item) travels too.
//! * THE NOT-LOWERED WIRE (`record_candidate` -> `not_lowered_reasons`): a body that reads a local
//!   `const` carries a pending-const SENTINEL (the crate module resolves it at finalize, after the
//!   candidate was captured), and is recorded `not-lowered(pending-const sentinel)`, never written
//!   with the placeholder in it.
//!
//! * NO ICE WITHOUT A DIAGNOSTIC: run-make compiles with `TRUST_VANILLA_ANNOUNCED=1` (as bootstrap
//!   and targo do), so the dependency's build emits no diagnostic at all. The guard's refusal
//!   reason spells the resolved instance; spelled with trimmed paths, that ended the session in
//!   an internal compiler error ("`trimmed_def_paths` called, diagnostics were expected but none
//!   were emitted"), which this fixture first exposed (review 2026-10-05). The reason now spells
//!   it in full.
//!
//! The decisions themselves are unit-tested in `trust-thir-lower` (`rmeta_entry/tests.rs`); this
//! pins that the rustc half computes their inputs. Removing the guard's item check (the intrinsic
//! is then named, or the build fails), its self-edge check (the reason becomes "already
//! declared"), its key check over-refusing (`drop_it` loses its entry), or the pending-const
//! reason turns this red.
//@ ignore-cross-compile

use run_make_support::{rfs, rustc};

const DEP: &str = r#"#![crate_type = "lib"]
#![feature(core_intrinsics)]
#![allow(internal_features)]

#[inline]
pub fn mix(x: u32) -> u32 {
    x ^ 0x5a5a_5a5a
}

#[inline]
pub fn call_mix(x: u32) -> u32 {
    mix(x)
}

#[inline]
pub fn swapped(x: u32) -> u32 {
    core::intrinsics::bswap(x)
}

#[inline]
pub unsafe fn drop_it(p: *mut String) {
    unsafe { core::ptr::drop_in_place(p) }
}

#[inline]
pub fn rec(x: u32) -> u32 {
    if x < 2 { x } else { rec(x & 1) }
}

const KEY: u32 = 0x0f0f_0f0f;

#[inline]
pub fn keyed(x: u32) -> u32 {
    x ^ KEY
}
"#;

const USER: &str = r#"#![crate_type = "lib"]

pub fn use_all(x: u32) -> u32 {
    unsafe { dep::drop_it(core::ptr::null_mut()) };
    dep::mix(x) ^ dep::call_mix(x) ^ dep::swapped(x) ^ dep::rec(x) ^ dep::keyed(x)
}
"#;

fn row<'a>(stderr: &'a str, def: &str) -> &'a str {
    let rows: Vec<&str> = stderr
        .lines()
        .filter(|l| l.starts_with("TRUST-WALLA-PROBE C sym=") && l.contains(&format!(" def={def} ")))
        .collect();
    assert_eq!(rows.len(), 1, "one channel-C row for `{def}`:\n{stderr}");
    rows[0]
}

fn contains(haystack: &[u8], needle: &str) -> bool {
    haystack.windows(needle.len()).any(|w| w == needle.as_bytes())
}

/// Every trust-ir entry blob in an rmeta file (the framing `trust-ir-rmeta-entry-roundtrip`
/// documents): schema-5 magic/version/digest plus a length-framed owner/mode/module/evidence
/// payload. Mode is the actual producing session setting, not inferred from instructions.
fn entries(rmeta: &[u8]) -> Vec<Vec<u8>> {
    let u64_at = |at: usize| u64::from_le_bytes(rmeta[at..at + 8].try_into().unwrap()) as usize;
    let mut out = Vec::new();
    let mut at = 0;
    while let Some(found) = rmeta[at..].windows(8).position(|w| w == b"TRIRENTR") {
        let start = at + found;
        // Trust: entry schema 5 frames the complete owner/mode/module/evidence payload.
        assert_eq!(u32::from_le_bytes(rmeta[start + 8..start + 12].try_into().unwrap()), 5);
        let p = start + 56 + u64_at(start + 48);
        out.push(rmeta[start..p].to_vec());
        at = p;
    }
    out
}

/// The module bytes of a framed entry.
fn module_bytes(entry: &[u8]) -> &[u8] {
    let at = 56 + 16 + 1 + 32;
    let len = u64::from_le_bytes(entry[at..at + 8].try_into().unwrap()) as usize;
    &entry[at + 8..at + 8 + len]
}

fn main() {
    rfs::write("dep.rs", DEP);
    rfs::write("user.rs", USER);

    let out = rustc()
        .input("dep.rs")
        .crate_name("dep")
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ztrust-verify=off")
        .arg("--emit=metadata,link")
        .arg("-Zmeta-stats")
        .arg("-Ztrust-ir-lower")
        .out_dir("dep-out")
        .run();
    let stats = format!("{}{}", out.stdout_utf8(), out.stderr_utf8());
    assert!(
        stats.contains(
            "meta-stats trust-ir entries: 3 encoded; 3 unencoded: not-lowered=1 unnamed-callee=2"
        ),
        "three bodies travel; the guard refuses two, the sentinel one:\n{stats}"
    );

    // The recorded reasons, as the crate header carries them into rmeta.
    let rmeta = rfs::read("dep-out/libdep.rmeta");
    for (what, needle) in [
        (
            "the intrinsic",
            "bswap::<u32> - intrinsic`, which is not the plain item the ledger linked",
        ),
        ("the self edge", "`rec`: a self edge (a recursive call is linked by the body's own name)"),
        ("the sentinel", "not-lowered(pending-const sentinel)"),
    ] {
        assert!(contains(&rmeta, needle), "{what}: the header records `{needle}`");
    }
    // `drop_it` declares the generic callee by the symbol of the instance its site re-resolved
    // to (`drop_in_place::<String>`, instantiated in `dep`): the key check passed a non-empty
    // concrete key.
    let entries = entries(&rmeta);
    assert_eq!(entries.len(), 3, "three entries");
    let drop_it = entries
        .iter()
        .map(|e| module_bytes(e))
        .find(|m| contains(m, "3dep7drop_it"))
        .expect("`drop_it` carries an entry");
    assert!(
        contains(drop_it, "13drop_in_place") && contains(drop_it, "6string6String"),
        "`drop_it` declares `drop_in_place::<String>` by its symbol"
    );

    let out = rustc()
        .input("user.rs")
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-instance-flip-probe=*")
        .extern_("dep", "dep-out/libdep.rlib")
        .out_dir("user-out")
        .run();
    let stderr = out.stderr_utf8();
    assert!(!stderr.contains("internal compiler error"), "no ICE:\n{stderr}");
    for (def, functions) in [("dep::mix", 1), ("dep::call_mix", 2), ("dep::drop_it", 2)] {
        let r = row(&stderr, def);
        assert!(
            r.contains(&format!("rmeta=entry(digest-ok,functions={functions},")),
            "`{def}` travels: {r}"
        );
    }
    for def in ["dep::swapped", "dep::rec"] {
        let r = row(&stderr, def);
        assert!(
            r.contains("rmeta=absent(unnamed-callee)"),
            "a callee with no symbol of its own is never declared by one: {r}"
        );
    }
    let keyed = row(&stderr, "dep::keyed");
    assert!(
        keyed.contains("rmeta=absent(not-lowered)"),
        "a body holding a pending-const sentinel is never written: {keyed}"
    );
}
