// MUST STAY REFUTED. The guard rail for the 2026-09-18 ledger-coverage change:
// the tolerance now covers a sysroot callee reached through a BUNDLED MEMBER,
// not just one called directly from the root. That must not extend to a sysroot
// routine handed a USER type, which dispatches into user code.
//
// `str::parse::<P>` calls this crate's `FromStr::from_str`, which panics. If the
// widened ledger ever tolerated this, the panic would be laundered through a
// std name. `P` is not foundational, so the verdict is `false` at every sighting.
pub struct P;
impl std::str::FromStr for P {
    type Err = ();
    fn from_str(s: &str) -> Result<P, ()> {
        if s.is_empty() {
            panic!("reachable user panic behind a std name")
        }
        Ok(P)
    }
}
fn inner(s: &str) -> bool {
    s.parse::<P>().is_ok()
}
pub fn outer(s: &str) -> bool {
    inner(s)
}
