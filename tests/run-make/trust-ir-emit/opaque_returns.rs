// Trust: call-free opaque returns must retain declaration provenance after typeck reveals
// their THIR return types. Plain scalar and concrete-alias twins keep their ordinary lane.
type ScalarAlias = u32;

pub fn plain_scalar() -> u32 {
    7u32
}

pub fn concrete_alias() -> ScalarAlias {
    7u32
}

pub fn opaque_scalar() -> impl Copy {
    7u32
}

pub fn opaque_tuple() -> (impl Copy, bool) {
    (7u32, true)
}

pub struct Returner;
impl Returner {
    pub fn opaque_associated() -> impl Copy {
        9u32
    }
}

pub fn closure_control() -> u32 {
    let value = || 7u32;
    value()
}
