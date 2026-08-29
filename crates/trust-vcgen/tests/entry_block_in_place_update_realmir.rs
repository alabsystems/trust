//! REAL-ARTIFACT precision guard for an in-place update in the FIRST block that
//! writes its place — the case where pinning the read at its establish point is
//! NOT ENOUGH, because that read is the parameter's ENTRY value.
//!
//! The fixture is the compiler's own extracted verification input for
//!
//! ```text
//! pub fn f(mut n: u32, a: &[u8; 10]) -> u8 { n /= 3; if n < 10 { a[n as usize] } else { 0 } }
//! ```
//!
//! captured with `trustc -Zt rust-dump=mir:<dir>`; source alongside as
//! `tests/data/entry_block_in_place_update.rs`. Every obligation in it is
//! discharge-able: the guard `n < 10` is read AFTER the division, so the index is
//! in bounds by construction.
//!
//! # The failure this pins
//!
//! `n /= 3` is `bb1[0]: _1 = Div(copy _1, 3)`. The cross-block definition thread
//! carries block defs BARE, so the consuming block renames the WHOLE fact at one
//! program point and both sides land on that point's token. Pinning the read at
//! the establishing statement (read-point `k = 0`) does not separate them here:
//! `version_token_at` returns `None` for an entry-valued read — by design, so
//! never-havoced parameter reads stay byte-identical across lanes — so the read
//! ships BARE, and bb2 (whose entry token for `n` IS `s1_0`) stamps it right back
//! onto the subject's token:
//!
//! ```text
//! Eq(Var("n#s1_0"), Div(Var("n#s1_0"), Int(3)))
//! ```
//!
//! `n == n / 3` forces `n == 0`; every obligation in reach is then vacuously
//! discharged, and the fail-closed `self_referential_definition` backstop in
//! `generate/entry.rs` degrades all of them to `UnsupportedMir`. MEASURED: 1 of 1
//! obligations demoted on safe code.
//!
//! The read must therefore carry the EXPLICIT entry token (`n#e`,
//! `ENTRY_VERSION_SENTINEL`) — the only spelling of "the value before this write"
//! that survives a consumer's rename.
//!
//! The backstop is untouched; this pins that it has nothing to catch here.

use trust_types::{Formula, VcKind, VerifiableFunction};

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
    let text = std::fs::read_to_string(format!("{path}{name}.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// Every `Eq(Var(v), rhs)` where `v` occurs free in `rhs` — a recurrence, not a
/// definition, and the shape the backstop degrades.
fn self_referential(f: &Formula, out: &mut Vec<String>) {
    if let Formula::Eq(l, r) = f
        && let Some(name) = l.var_name()
        && r.var_name() != Some(name)
        && r.free_variables().iter().any(|v| v.as_str() == name)
    {
        out.push(format!("{f:?}"));
    }
    for c in f.children() {
        self_referential(c, out);
    }
}

#[test]
fn entry_block_in_place_update_mints_no_recurrence() {
    let func = load("entry_block_in_place_update");
    let mut offenders = Vec::new();
    for vc in trust_vcgen::generate_vcs(&func) {
        let mut found = Vec::new();
        self_referential(&vc.formula, &mut found);
        for f in found {
            offenders.push(format!("{:?} @ {:?}: {f}", vc.kind, vc.location));
        }
    }
    assert!(
        offenders.is_empty(),
        "an in-place update in the first writing block still collapses its \
         pre- and post-write reads onto one symbol:\n  {}",
        offenders.join("\n  ")
    );
}

#[test]
fn entry_block_in_place_update_is_not_backstopped() {
    let func = load("entry_block_in_place_update");
    let vcs = trust_vcgen::generate_vcs(&func);
    let demoted: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "SelfReferentialDefinition")
        })
        .map(|vc| format!("{:?}", vc.location))
        .collect();
    assert!(
        demoted.is_empty(),
        "{} of {} obligations degraded to UnsupportedMir on SAFE code:\n  {}",
        demoted.len(),
        vcs.len(),
        demoted.join("\n  ")
    );
}

/// Laundering control: the recurrence must be REPAIRED, not deleted along with
/// the obligation it was poisoning. `a[n as usize]` must still raise a bounds row.
#[test]
fn entry_block_in_place_update_still_carries_its_bounds_obligation() {
    let func = load("entry_block_in_place_update");
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(
            vc.kind,
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck | VcKind::UnsupportedMir { .. }
        )),
        "`a[n as usize]` must still raise an obligation; dropping it would hide \
         the read the recurrence used to discharge: {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}
