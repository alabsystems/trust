//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-AFS2): a struct literal with a FUNCTION-POINTER field recovers that lane's
//! aggregate seed from the OPEN BLOCK, so the seed IS the value that immediately overwrites it.
//!
//! Neither seeder has a `Ty::Func` arm and that is deliberate: there is no null `FuncId`, and a
//! fabricated `FnDef` placeholder would name a REAL, callable function -- silently wrong rather
//! than loudly wrong. Measured, the intersection of validator and interpreter at `Ty::Func` for
//! any NON-identity placeholder is EMPTY: `Constant::Int(0)` is rejected by both, and
//! `Constant::PhantomData` is interpreter-accepted via a catch-all but validator-rejected, so it
//! would have rested on the `validate_module` tripwire that only runs under a debug tracing
//! filter.
//!
//! The class needs no placeholder at all, and the producer already knew that AT A DIFFERENT
//! SITE: `build_array_aggregate`'s wave-AFS arm recovers each element's own
//! `Inst::Const { ty: Ty::Func(sig), value: FnDef }` out of the same open block. This wave gives
//! that recovery a per-lane entry point so the `Adt` site can use it too. The measured asymmetry
//! on one file was `[a, b]` clean while `S { f: a }` refused -- a missing SPELLING at one call
//! site, not a missing carrier.
//!
//! The seed is therefore stronger than the thin/fat pointer placeholders beside it: those are
//! safe by LOUDNESS (a deref of a null faults), this one is safe by IDENTITY -- even if the
//! overwrite witness were ever weakened, reading the seed would read the CORRECT function
//! pointer. Both authorities already admit the `(Ty::Func, Constant::FnDef)` pair, so nothing
//! rests on a disabled instrument.
//!
//! FLIP CANNOT HAPPEN, by two independent already-live refusals that fire on the field VALUE
//! present before and after this change: the differential's reachability walk breaks on any
//! constant that materializes callable identity (`Constant::FnDef`, propagating through
//! `Constant::Aggregate`), and `to_mir`'s constant admission is an affirmative
//! `Int|U128|Float|Bool` allow-list with no `FnDef` arm at all.
//!
//! Not under `=strict`: the negative pin below must keep its tag.

#![allow(dead_code)]

extern "C" fn ext() {}
fn plain() {}

struct S {
    f: extern "C" fn(),
}

struct M {
    f: fn(),
    n: u8,
}

// THE LANE: the corpus shape (`tests/ui/consts/const-extern-function.rs`). The field value is a
// reified fn item, so its defining `Inst::Const { Ty::Func, FnDef }` sits in this very block.
static S1: S = S { f: ext };

// MIXED LANES: the recovery is PER LANE, not all-or-nothing. `n` takes the ordinary scalar seed
// and `f` takes the recovery, in the same aggregate. (`build_array_aggregate`'s wave-AFS arm is
// all-or-nothing over its element list, which is why this needed its own entry point.)
static M1: M = M { f: plain, n: 7 };

pub fn in_a_body() -> u8 {
    let m = M { f: plain, n: 3 };
    m.n
}

// FAIL-CLOSED, and this pin is the whole reason the gate is worth having: a fn pointer arriving
// from a PARAMETER has no defining `Inst::Const` in the open block, so the scan finds nothing
// and the literal keeps `Adt(non-scalar field seed)`. A future author "fixing" this by minting
// a placeholder `FnDef` reintroduces exactly the defect the recovery exists to avoid -- the
// placeholder would name a real, callable function. The gate is worthless the day this body
// starts lowering clean.
pub fn from_param(g: fn()) -> M {
    M { f: g, n: 1 }
}

fn main() {}
