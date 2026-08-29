// LANE SC (follow-on) — FAMILY F2: `<level::LevelArc as std::fmt::Debug>::fmt`, the two-call
// CHAIN whose corpus body carries a THIRD local. G25's `g1` probe measured the 2-local chain
// (`%2 = call f(%0); %3 = call g(%2, %1); ret %3`) as CONVERTING at 8 marker lines, and named the
// corpus body's THIRD local — minted by `&**self`, which derefs twice — as the refusal. G25 did
// not commit that probe; this file rebuilds both members of the pair.
#![allow(dead_code, clippy::all)]
use std::fmt;
use std::sync::Arc;

pub struct Lvl {
    n: u64,
}
impl fmt::Debug for Lvl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("l")
    }
}

// (a) THE 2-LOCAL CONTROL, G25's `g1` shape: a bare chain `g(f(%0), %1)`, no deref anywhere.
pub struct Two(Lvl);
impl Two {
    #[inline(never)]
    pub fn inner(&self) -> &Lvl {
        &self.0
    }
}
impl fmt::Debug for Two {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Lvl::fmt(self.inner(), f)
    }
}

// (b) THE CORPUS SPELLING: the same chain whose first link's result is DOUBLE-dereferenced and
//     re-borrowed — `&**x` — which mints the third local.
pub struct ArcNewtype(Arc<Lvl>);
impl ArcNewtype {
    #[inline(never)]
    pub fn inner(&self) -> &Arc<Lvl> {
        &self.0
    }
}
impl fmt::Debug for ArcNewtype {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Lvl::fmt(&**self.inner(), f)
    }
}
