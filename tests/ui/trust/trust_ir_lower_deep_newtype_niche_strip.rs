//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//! STATUS ON MAIN (2026-09-24). Carried from the seal line (7dc02d605a). Of the two fuel
//! budgets this file pins, main repaired `declared_layout_resolvable` (the wave-LC strip) on its
//! own on 2026-09-22 (fixture: trust_ir_niche_descriptor_deep_payload_chain.rs); the other,
//! `struct_layout_resolvable`, still ran on `fuel = 8`, and on the sealed trust-7d5533b2 (main
//! of 2026-09-23) this file still WARNed `ConstTypeMismatch { location: "enum.4
//! (DomainConnectionInfo) layout", .. resolvable layout .. }`. The port that carries this file
//! replaces that budget with the cycle guard + memo. The prose below is the seal-line record.
//!
//! Trust (aterm `DomainConnectionInfo`, measured 2026-09-08 on seal trust-dac08891): the
//! wave-LC descriptor strip must terminate on a CYCLE GUARD, not on a depth budget — a
//! stripped `Niche` descriptor is not the absence of a claim, it is a DIFFERENT claim.
//!
//! THE DEFECT. `register_enum` fills `EnumLayoutDescriptor` from rustc's true layout, then the
//! wave-LC strip drops that fill when any declared payload's layout is not resolvable from the
//! module's own rows (`declared_layout_resolvable`). That walk carried `fuel: u32`, seeded `8`
//! at the call site, and answered `false` on exhaustion — filed as "conservative". It is not.
//! `trust_ir::shape` falls back to trust-ir's CANONICAL tagged-union layout for a
//! descriptor-less enum (a tag lane, then the payload aligned up), which is >= and routinely >
//! rustc's niche-optimised size, while every struct row holding that enum still declares
//! rustc's OWN size and offsets (`registered_struct_layout_fill` + `declared_field_offset_fill`).
//! The two halves then contradict each other, `ty_layout_shape`'s `Ty::Struct` arm reports
//! `StructLayoutIncoherent`, and the error surfaces on whichever enum descriptor had to bound a
//! field of that struct.
//!
//! IT IS PURE ARITHMETIC, and `std`'s own newtype chains overrun it. Counting one unit of fuel
//! per `Ty::Struct` hop and one for the scalar leaf, measured on the pre-fix seal:
//!
//!   `String`  = String > Vec<u8> > RawVec > RawVecInner > Unique > NonNull > ptr   — 7, fits
//!   `PathBuf` = PathBuf > OsString > Buf > (that same 7-hop String chain)           — 9, does not
//!
//! so `enum MuxTransport { LocalSocket(PathBuf), Ssh(SshConnectionConfig) }` — aterm's own
//! type, rustc size 56 via a niche, offsets `[[8], [0]]` — lost a faithful descriptor and fell
//! back to a canonical 64-byte image. `MuxConnectionConfig` is rustc size 112 with
//! `name@0, transport@24, protocol@80, max_panes@104`, so the canonical transport footprint
//! 24..88 overlaps `protocol` at 80 and the row is incoherent. Measured on seal
//! trust-dac08891, `aterm-types` (lib) under
//! `targo trust check --allow-l0-gaps --workspace --all-targets`, and reproduced standalone
//! with `trustc --crate-type lib --edition 2021 --emit=metadata -Ztrust-verify=off
//! -Ztrust-ir-lower=on`:
//!
//!   error: trust-ir-lower semantic finalization failed: final Trust-IR module validation
//!   failed [ConstTypeMismatch]: ConstTypeMismatch { location: "enum.101
//!   (DomainConnectionInfo) layout", expected: "variant 2 field 0 to have a resolvable layout
//!   (needed to bound it within size 120)", actual: "offset 8, layout UNRESOLVABLE for type
//!   struct.123: struct.123 has incoherent declared layout metadata" }
//!
//! (variant 3 repeats it; the enclosing `Option<DomainConnectionInfo>` then reports both the
//! same unresolvable bound and "the niche lane covered by a non-ZST field of the untagged
//! variant", because a lane it cannot size is a lane it cannot prove covered.)
//!
//! THERE ARE TWO SUCH BUDGETS AND THEY MUST MOVE TOGETHER. `struct_layout_resolvable` — the
//! transitive tuple hunt behind `enum_variant_field_admissible` — carried the identical
//! `fuel = 8` and runs FIRST: past its budget `register_enum` declines the def outright, so the
//! wave-LC strip is never reached. It sits ONE HOP further out, because it charges a unit per
//! `Ty::Struct` hop only while the wave-LC walk also charged the scalar leaf. Measured on the
//! pre-fix seal with a `Wk(...(String))` payload inside `struct H { e: E, tail: u64 }` inside
//! `enum Outer`, K = newtype hops:
//!
//!   K=0 exit 0   K=1 exit 0   K=2 exit 1 (1 ConstTypeMismatch)   K=3..8 exit 0
//!
//! The ladder is NON-MONOTONE, and K>=3 is green BY DECLINE, not by health: its dump carries
//! `struct @H { (), u64 }` — no `enum @E` row at all — with the body lowered to
//! `%3 = undef bool` and the coverage record "THIR crate module function unexpectedly carries
//! Inst::Undef (producer invariant violated)". So a single adjacent green/red pair does NOT by
//! itself isolate a cause here; what isolates it is that the fuel arithmetic predicts BOTH
//! boundaries exactly — the wave-LC walk at K=2, the sibling at K=3 — and each budget's own
//! removal moves its own boundary. Repairing only the wave-LC walk would leave every payload
//! past 8 struct hops silently declined; repairing only the sibling would turn those silent
//! declines into hard `ConstTypeMismatch`. Both are removed here.
//!
//! THE FIX. The budget's only job was TERMINATION, and `trust_ir::shape` already does that job
//! exactly, with a visiting stack: re-entering a struct already on the stack is
//! `StructLayoutIncoherent`. Both walks now mirror that stack instead of counting hops — `false`
//! on a genuine inline struct cycle (the same verdict as the validator, for the same reason, on
//! the same inputs) and depth left to the shape of the type. `Ty::Enum` does not recurse (it
//! reads descriptor PRESENCE on the registered def) and a `Ty` value is a finite tree, so the
//! struct stack is the only recursion needing a guard. Each walk carries a per-query memo, which
//! is a REQUIREMENT and not an optimisation: with no budget a struct DAG of fanout `k` and depth
//! `d` costs `k^d` visits (`fuel = 8` capped that at `2^8`), and a fanout-2 depth-40 DAG does not
//! terminate without it. Memoising is sound because a verdict here is context-free — a `true`
//! completed its subtree without meeting the guard, and a `false` produced under the guard is
//! also the standalone verdict, since a struct found on its own visiting stack is on a cycle.
//! `Ty::Array`/`Ty::Vector` also stop falling into `_ => true`: `shape.rs` resolves an element
//! layout for both, so `[DegradedStruct; 4]` is exactly as unresolvable as the bare field.
//!
//! WHY THIS DIRECTION IS THE SAFE ONE. The change strictly SHRINKS the descriptor-less corpus,
//! so it moves `to_mir.rs`'s recorded `enum_flip_direct_only` fail-open — `layout: None` read as
//! "Direct", which admits descriptor-less niche enums into the flip lane — in the closed
//! direction. No flip-admission census is owed. Nothing here loosens an admission gate: an enum
//! whose descriptor is genuinely unfaithful is still stripped, and `declared_niche_lane_covered`
//! still declines the enum outright.
//!
//! WHAT THIS PIN GUARDS, AND WHAT IT DOES NOT. Under `-Ztrust-ir-lower` (any mode, `on`
//! included) the crate finalizer runs final module validation and every validation error is
//! fatal — `crate_module.rs`'s `final_module_validation_errors` feeds `summary.errors`, and
//! rustc_mir_build's `trust_ir_crate_finalize` turns a non-empty list into `dcx().fatal`. The
//! guarded property is exactly that: the module the producer emits is VALID.
//!
//! The RED half is MEASURED. On seal trust-dac08891 this file is exit 1 with 6
//! `ConstTypeMismatch`, at `enum.4 (DomainConnectionInfo)` x2, `enum.5 (Option)` x2 and
//! `enum.7 (DeepOuter)` x2. The GREEN half is PREDICTED, not measured: the fix was authored
//! against a tree the fleet holds under a build lock, so no compiler carrying it has run. The
//! strongest available pre-build evidence that a KEPT descriptor makes this exact shape green —
//! rather than trading one error for another — is a surrogate with the deep chain swapped for a
//! rustc-identical shallow one (`struct ShallowPath(pub String)` for `PathBuf`: both 24/8, both
//! give `MuxTransport` 56/8), so the only difference is that the chain fits the PRE-fix budget
//! and the descriptor survives. That surrogate compiles exit 0 on the pre-fix seal. A rebuild
//! must confirm the prediction on this file itself.
//!
//! `check-pass` observes NOTHING ELSE — not that `MuxTransport` kept its descriptor, not that
//! `DeepE` got an `enum @` row at all rather than degrading to `()`, not which per-body tags
//! these functions record, and not that either walk still refuses a cycle. A change that made
//! every walk answer `true` would still pass this file; the cycle half has to be caught by the
//! validator's own `StructLayoutIncoherent` rule, which no producer edit can reach. What the
//! deep shapes below DO guard is the COUPLING: restore the wave-LC budget alone and they go
//! RED, because their payloads would then be stripped rather than declined.
//!
//! THE RESIDUE THIS DOES NOT REPAIR (stated, not waived). The general class is still open: ANY
//! descriptor-less enum used as a struct field pairs a canonical (larger) field image with
//! rustc-derived offsets, and the struct row is then incoherent whenever the extra bytes
//! collide. This fix removes the population that was descriptor-less BY ARITHMETIC ERROR — both
//! budgets — and nothing more. It does not touch the population that is descriptor-less because
//! `producer_enum_layout_descriptor` genuinely declined (an unmappable tag scalar, an uncoverable
//! niche interval). Closing that needs `register_struct`'s coherence gate to refuse rustc bytes
//! beside a field it cannot size — today that gate tests only `Ty::Unit` degradation, never a
//! descriptor-less enum field — and it is a fail-closed change that blanks struct layouts which
//! validate today, so it owes a clean-rate census and is deliberately not taken here.
//!
//! `declared_layout_resolvable` also still OVER-APPROVES relative to `shape.rs`: it tests
//! `sd.size.is_some()` where the validator additionally requires `sd.align`, per-field offsets
//! for non-ZSTs, alignment and containment, the packed clamp, pairwise non-overlap and the
//! `repr(transparent)` carrier rule. "Mirror" in this file describes the CYCLE GUARD, not the
//! whole rule, and every widening of a `true` here widens the population where a KEPT descriptor
//! meets one of those other rules. The counterweight is `declared_niche_lane_covered`, which
//! DECLINES rather than errors when a kept descriptor fails the lane rule.

#![allow(dead_code)]

// ---- the aterm shape, reduced: a niche-encoded enum with a `PathBuf` payload (9 hops) inside a
// ---- struct that is itself an enum payload. RED on the pre-fix seal.

use std::path::PathBuf;

pub struct SshConnectionConfig {
    pub user: Option<String>,
    pub host: String,
    pub port: u16,
}

pub enum MuxProtocol {
    Aterm,
    TmuxControl,
    Custom(String),
}

pub enum MuxTransport {
    LocalSocket(PathBuf),
    Ssh(SshConnectionConfig),
}

pub struct MuxConnectionConfig {
    pub name: String,
    pub transport: MuxTransport,
    pub protocol: MuxProtocol,
    pub max_panes: Option<u32>,
}

pub enum DomainConnectionInfo {
    Local,
    Ssh(SshConnectionConfig),
    Mux(MuxConnectionConfig),
    SshMultiplexer(MuxConnectionConfig),
}

pub fn is_local(i: &Option<DomainConnectionInfo>) -> bool {
    matches!(i, Some(DomainConnectionInfo::Local))
}

// ---- the same defect with `std` removed from the argument: `W2` is `String` plus TWO newtype
// ---- hops, which is exactly the one hop past the old wave-LC budget that `PathBuf` also was.
// ---- RED on the pre-fix seal. Its ONE-HOP-SHALLOWER twin below is GREEN there, and its
// ---- ONE-HOP-DEEPER twin (`W3`, further down) is green too — green BY DECLINE, at the SIBLING
// ---- budget. The ladder is not monotone, so this red/green pair is not on its own a cause;
// ---- see the header for why the arithmetic predicting both boundaries is.

pub struct W1(pub String);
pub struct W2(pub W1);
pub struct Pair {
    pub a: String,
    pub b: String,
}

pub enum DeepNewtype {
    A(W2),
    B(Pair),
}

pub struct DeepHolder {
    pub e: DeepNewtype,
    pub tail: u64,
}

pub enum DeepOuter {
    N,
    M(DeepHolder),
    O(DeepHolder),
}

pub fn deep_is_n(x: &DeepOuter) -> bool {
    matches!(x, DeepOuter::N)
}

// ---- the neighbour: identical in every respect except one newtype hop, so it fitted the old
// ---- budget and compiled clean before the fix. It rides along to pin that the repair does not
// ---- turn a working shape into a hard error.

pub enum ShallowNewtype {
    A(W1),
    B(Pair),
}

pub struct ShallowHolder {
    pub e: ShallowNewtype,
    pub tail: u64,
}

pub enum ShallowOuter {
    N,
    M(ShallowHolder),
    O(ShallowHolder),
}

pub fn shallow_is_n(x: &ShallowOuter) -> bool {
    matches!(x, ShallowOuter::N)
}

// ---- THE SIBLING BUDGET's own band: `W3` is one hop PAST `struct_layout_resolvable`'s old
// ---- `fuel = 8`, and `W8` is well past both. On the pre-fix seal these are green BY DECLINE —
// ---- `enum_variant_field_admissible` refuses the payload, `register_enum` declines `DeepE`,
// ---- the holder's field degrades to `()` and the body lowers to `undef`. After the fix they
// ---- are registered with a faithful descriptor, so a rebuild must show them still green FOR
// ---- THE OTHER REASON. They also pin the COUPLING: restoring the wave-LC budget alone turns
// ---- both RED, because a kept-then-stripped descriptor is what makes a holder row incoherent.

pub struct W3(pub W2);
pub struct W4(pub W3);
pub struct W5(pub W4);
pub struct W6(pub W5);
pub struct W7(pub W6);
pub struct W8(pub W7);

pub enum PastSiblingBudget {
    A(W3),
    B(Pair),
}

pub struct PastSiblingHolder {
    pub e: PastSiblingBudget,
    pub tail: u64,
}

pub enum PastSiblingOuter {
    N,
    M(PastSiblingHolder),
    O(PastSiblingHolder),
}

pub fn past_sibling_is_n(x: &PastSiblingOuter) -> bool {
    matches!(x, PastSiblingOuter::N)
}

pub enum FarPastBothBudgets {
    A(W8),
    B(Pair),
}

pub struct FarPastHolder {
    pub e: FarPastBothBudgets,
    pub tail: u64,
}

pub enum FarPastOuter {
    N,
    M(FarPastHolder),
    O(FarPastHolder),
}

pub fn far_past_is_n(x: &FarPastOuter) -> bool {
    matches!(x, FarPastOuter::N)
}

fn main() {}
