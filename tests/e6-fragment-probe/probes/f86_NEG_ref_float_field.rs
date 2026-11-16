//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: FLIPPED BY INCREMENT I2 (disposition R4, implementer-proposed), 2026-09-19, alongside `f80`. The
//@ probe-note: file name keeps its `NEG_` prefix so the flip stays legible in `git log`.
//@ probe-note: This was the CLEANEST D-REF-8 shape: every earlier condition admits
//@ probe-note: `Ratio`, and only the field's CARRIER refused it. `f64` is `Freeze`, sized,
//@ probe-note: non-generic and classified by K2's structural walk, so C1, C2, K2 and C3 all
//@ probe-note: pass and the pattern is a plain name — it is simply not a carrier this lane
//@ probe-note: types (`trust_e6_view_carrier` is `bool`, `u8`..`u128`, `i8`..`i128`).
//@ probe-note: I2 SKIPS such a field instead of refusing the pointee, so `num: u32` gets
//@ probe-note: its row and `scale` gets none. `scale` is thereafter unnameable: a clause
//@ probe-note: saying `self.scale` is an UNBOUND VARIABLE (`f90`), and a body that READS it
//@ probe-note: loses the whole view (`f89`) — it is not a binder that quietly defaults.
//@ probe-note: It stays the SIMPLER of the pair: `f80`'s `Vec<u8>` field also has to
//@ probe-note: survive K2's structural walk (it does, but only since K2 learned to walk a
//@ probe-note: pattern type's base — see `f80`'s header), while nothing but the carrier
//@ probe-note: rule ever stood between this one and a row.
//@ probe-note: Like every view row this is `Trusted`/`Constructive`, never `Certified`.
clean { def id32fl (x : UInt32) : UInt32 := x }
pub struct Ratio { pub num: u32, pub scale: f64 }
impl Ratio {
    pub fn num_of(&self) -> u32
        ensures result == id32fl(self.num)
    { self.num }
}
