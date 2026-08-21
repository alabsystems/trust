// T1 regression, inherent-method face: a plain Rust method literally named
// `write` (no unsafe, no FFI) must not bind the POSIX write(2) summary via
// last-segment name matching (the aterm-update-core `Sentinel::write` class —
// that method was renamed to dodge the false refutation; this fixture keeps
// the original shape provable so the rename can be reverted).
// This file must PROVE (exit 0).
//
// ============================================================================
// KNOWN RED, AND THE QUESTION IS CLOSED — do not re-open without new capability.
// ============================================================================
// This fixture's own subject (the name-binding regression) is FINE. What keeps it
// red is unrelated: a `[trust-drop-glue-assumption]` row for drop glue on
// `Result<(), io::Error>`, minted inside std's BUNDLED `unwrap_or_default` body at
// a Drop terminator and published under this function's obligation id.
//
// It is NOT an absent callee — `<Vec<u8> as io::Write>::write_all` is already
// modelled and discharged by the conditional Vec<u8>-grow summary in
// crates/trust-ir-bridge/src/lower.rs.
//
// THREE routes have been tried and measured. All fail:
//
//  1. Model `io::Error`'s drop glue as total on TYPE IDENTITY. Unsound: its repr can
//     transitively hold a `Box<dyn Error + Send + Sync>` whose `Drop` IS user code.
//
//  2. Prove the `Err` payload unreachable here because Vec<u8>'s `write_all` is
//     infallible, so the tag is provably `Ok`. Measured NO on both halves:
//     (a) lower.rs's "Havoc the result" step emits `Inst::Undef` over the WHOLE
//         Result — in this fixture's lowered module, `[49] Undef{ty:Struct 6}` in
//         BB6 — so the tag is entirely unconstrained. And it cannot be pinned FROM
//         THE LOWERED MODULE, because `write_all` is an absent callee and the module
//         holds no definition of its return value. Any Ok-pin would be a new modeled
//         fact about std's `impl io::Write for Vec<u8>` that the kernel cannot
//         re-check — the trusted-assumption class this campaign exists to remove.
//     (b) DECISIVE AND INDEPENDENT OF (a): a probe whose tag is a COMPILE-TIME
//         CONSTANT Ok — `let _r: Result<(), io::Error> = Ok(());` — lowers to
//         `InsertField(agg, field 0 /*__tag*/, Const I64 0)` and STILL mints the
//         byte-identical drop-glue row. The lane does not consult the tag at all, so
//         pinning it would not help even if it could be pinned.
//
//  3. Suppress or narrow the drop-glue obligation itself. That is the
//     silence-reads-as-success defect that `92b7a1fc52` was built to detect and that
//     cost a3d 95 unverified obligations. Not an option.
//
// WHAT WOULD ACTUALLY CLOSE IT: lowering std's drop glue for this chain so the
// obligation is discharged by a real proof rather than assumed away — i.e. the same
// answer as the wider "OCCT/std bodies the prover cannot see" problem. Until that
// exists, this row is an HONEST red: a real obligation, correctly unproved.
#![crate_type = "lib"]

pub struct Sentinel {
    state: u32,
}

impl Sentinel {
    #[must_use]
    pub fn new() -> Self {
        Self { state: 0 }
    }

    /// Inherent method named `write` — must verify as ordinary Rust code.
    pub fn write(&mut self, v: u32) {
        self.state = v;
    }

    #[must_use]
    pub fn read(&self) -> u32 {
        self.state
    }
}

impl Default for Sentinel {
    fn default() -> Self {
        Self::new()
    }
}

/// Trait-face twin: `io::Write`-style trait method resolution paths also end
/// in `::write` and must not bind the POSIX summary.
pub fn write_all_units(out: &mut Vec<u8>, n: usize) {
    use std::io::Write;
    // Vec<u8>'s io::Write is infallible; the unwrap is the documented contract.
    let bounded = n.min(64);
    for _ in 0..bounded {
        out.write_all(&[0u8]).unwrap_or_default();
    }
}
