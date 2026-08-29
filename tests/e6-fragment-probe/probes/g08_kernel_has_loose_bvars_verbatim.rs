//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: CENSUS PROBE, not an isolation probe -- it fails for several reasons at
//@ probe-note: once (newtype field read, shift, cast, comparison-returned-as-value, `self`
//@ probe-note: receiver, same-unit call). Isolations are g01/g02/g03/g04/g07.
//@ probe-note: This is clean-kernel `ExprMeta::has_loose_bvars` + `loose_bvar_range`
//@ probe-note: VERBATIM (crates/clean-kernel/src/expr/meta.rs:130-138). It is one of the
//@ probe-note: TWO bodies passing the full ten-criteria crystal scorecard, i.e. the
//@ probe-note: strongest existing end-to-end result. The clause is written in Rust
//@ probe-note: (`>>`), so a refusal here is about the BODY, not about clause syntax. It answers one question: can the
//@ probe-note: fused route say anything about a body the crystal route has already closed?
clean { def nz_isl (x : UInt64) : Bool := x != 0 }
pub struct ExprMeta(pub u64);
impl ExprMeta {
    const BVAR_RANGE_SHIFT: u32 = 44;
    pub fn loose_bvar_range(self) -> u32 { (self.0 >> Self::BVAR_RANGE_SHIFT) as u32 }
    pub fn has_loose_bvars(self) -> bool
        ensures result == nz_isl(self.0 >> 44)
    { self.loose_bvar_range() > 0 }
}
