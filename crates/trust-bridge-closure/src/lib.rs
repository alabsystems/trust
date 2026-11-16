//! Shared roots for the Lean↔Clean bridge and its closure audit utility.

mod snapshot;
pub mod source_reuse;

pub use snapshot::{export as export_snapshot, read_runtime_boundary_input};

/// The root module whose transitive `.olean` closure is vendored: trust-ir's
/// COMPARISON semantics (`semICmp`), which imports the arithmetic semantics
/// (`semIntBinOp`/`semIntUnOp`/`semOverflowOp` + their whole import cone). Was
/// `TrustIr.Semantics.Arith` through the OverflowOp increment; RETARGETED to
/// `TrustIr.Semantics.Compare` when the semICmp bridge was added — `Compare`
/// imports `Arith`, so its closure is a strict superset (11 TrustIr modules
/// vs. 9), at the SAME trust-ir pin (`26379f8`). Kept as a named constant
/// (rather than folded into [`BRIDGE_ROOT_MODULES`]) because several
/// diagnostics still cite it as "the" comparison root.
pub const BRIDGE_ROOT_MODULE: &str = "TrustIr.Semantics.Compare";

/// The FULL set of root modules whose UNION transitive `.olean` closure is
/// vendored. EXTENSION 4 (the semCast increment) adds `TrustIr.Semantics.Cast`
/// alongside [`BRIDGE_ROOT_MODULE`]: `Cast` imports `CastOp` + `Arith`, but —
/// unlike every prior extension — NEITHER `Compare` nor `Cast` imports the
/// other (`Compare` imports `Arith`; `Cast` imports `CastOp` + `Arith`), so a
/// single-root retarget cannot cover both. The two roots are loaded together
/// via `clean_olean::load_modules_with_deps` (the shared-`visited` multi-root
/// loader), whose closure is the UNION of both cones: the previous 11
/// TrustIr modules plus exactly 2 new ones (`CastOp`, `Semantics.Cast`) — 13
/// total, at the SAME trust-ir pin (`26379f8`). The vendored oleans +
/// manifest were regenerated (scripts/regen-trustir-oleans.sh --write) to
/// match this wider closure.
/// EXTENSION 6 (this increment) adds `TrustIr.Semantics.Eval` — the FIRST
/// WHOLE-BLOCK (`stepBlock`/`stepN`, terminator-inclusive) agreement, one
/// layer above `stepInst`. `Eval` `import`s `Step` directly, so its closure
/// is Step's closure PLUS `Eval` itself (a strict superset, 27 TrustIr
/// modules vs. 26) — no other root retarget is needed.
/// The byte-memory extension explicitly imports the canonical read/write,
/// non-aliasing and byte-encoding proofs. They are outside the execution roots'
/// import cone; a source pin alone would leave them absent from the package.
/// Every declaration in this extra module remains in the local kernel census.
pub const BRIDGE_ROOT_MODULES: &[&str] = &[
    BRIDGE_ROOT_MODULE,
    "TrustIr.Semantics.Cast",
    "TrustIr.Semantics.Step",
    "TrustIr.Semantics.Eval",
    "TrustIr.Proofs.ByteMemory",
];
