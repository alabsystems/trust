//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. C2's GENERIC arm, and since I2 the sole net for
//@ probe-note: this shape. `tag: u32` is a perfectly good scalar field in the view
//@ probe-note: vocabulary, so with the all-or-nothing rule gone the ONLY reason
//@ probe-note: `&Tagged<T>` has no row is that `Freeze` for an uninstantiated `T` is not
//@ probe-note: decidable here — `has_non_region_param` refuses the pointee before anything
//@ probe-note: looks at a field. Under I1 `payload: T` also failed the carrier rule, so
//@ probe-note: which net held this shape was untested.
//@ probe-note: The POSITIVE control is `f88`: `&Wrapper<u32>` in a non-generic function IS
//@ probe-note: admitted, so "a generic" is not the refusal — an UNDECIDED one is. The pair
//@ probe-note: is what keeps this row from being read as "generics are out of the lane".
//@ probe-note: SOUNDNESS: admitting it would assume `Freeze` of a type this compilation has
//@ probe-note: not seen, at every future instantiation, `Tagged<Cell<u8>>` among them.
clean { def id32gp (x : UInt32) : UInt32 := x }
pub struct Tagged<T> { pub tag: u32, pub payload: T }
impl<T> Tagged<T> {
    pub fn tag_of(&self) -> u32
        ensures result == id32gp(self.tag)
    { self.tag }
}
