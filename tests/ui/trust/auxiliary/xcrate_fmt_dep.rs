//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency with formatting impls, compiled exactly the way
//! `targo` compiles every dependency unit: `-Ztrust-verify=off` (NOTHING in this
//! file is verified by its own compilation) and `-Zalways-encode-mir` (its bodies
//! are readable by a caller). Consumed by `xcrate_fmt_dep.rs`; see that file for
//! what D4 increment A re-derives from these bodies and what must stay refused.
//!
//! The crate name is deliberately NOT `trust_`-prefixed: it classifies as an
//! ordinary external dependency (`PolicyBucket::ExternalDep`).
//!
//! `Bad`, `ErrE`, `Oob`, `ViaHelper`, `Exported`, `Drops`, `UnsafeNoop` and
//! `TmuteRegion` ARE THE ASSERTIONS. Do not make them total, error-transparent,
//! unexported, or free of `unsafe`.
#![crate_name = "xcfmt_dep"]
use std::fmt;

/// Panic-free and error-transparent: the one impl a consumer may credit, and
/// only by re-deriving it.
pub struct Good;
impl fmt::Debug for Good {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

/// Panics outright.
pub struct Bad;
impl fmt::Debug for Bad {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!("boom")
    }
}

/// PANIC-FREE but not error-transparent: `println!` of it panics inside std
/// (F1, cross-crate). Passing the panic-freedom bar is not enough at a sink.
pub struct ErrE;
impl fmt::Debug for ErrE {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Err(fmt::Error)
    }
}

/// Indexes a 3-array by its field: panics for any field >= 3.
pub struct Oob(pub usize);
impl fmt::Debug for Oob {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let a = [1u8, 2, 3];
        if a[self.0] == 9 {
            return Ok(());
        }
        Ok(())
    }
}

/// Panics in a NON-GENERIC helper of this crate, not in its own body: the
/// panic is a bundled member's, so the re-derived root must still be charged
/// with it.
pub struct ViaHelper(pub u32);
#[inline(never)]
pub fn helper(x: u32) -> u32 {
    if x == 7 {
        panic!("helper boom");
    }
    x
}
impl fmt::Debug for ViaHelper {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let _ = helper(self.0);
        Ok(())
    }
}

/// Body is `Good`'s, but its symbol is exported unmangled, so another object
/// can interpose it at link time: never credited from this MIR.
pub struct Exported;
impl fmt::Debug for Exported {
    #[unsafe(no_mangle)]
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

/// Body is `Good`'s plus a drop of a dependency type with a `Drop` impl. The
/// X1 rule: a dependency's `Drop` is never credited from its MIR, so the
/// drop-glue row in this re-derived body stays unproved.
pub struct Hollow;
impl Drop for Hollow {
    fn drop(&mut self) {}
}
pub struct Drops;
impl fmt::Debug for Drops {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let h = Hollow;
        drop(h);
        Ok(())
    }
}

/// Body is `Good`'s plus an `unsafe` block around a SAFE expression: its MIR
/// carries no unsafe operation at all, and a LOCAL copy of it verifies (rc=0 on
/// the stage-1 snapshot at `4e9fe36bf`). A consumer re-deriving it from this
/// crate's MIR must still decline it, on the user-`unsafe` SOURCE FACT this
/// crate's compiler encoded beside that MIR: the fact, not the MIR, is what can
/// see `unsafe`, and it is deliberately coarse (any user `unsafe` declines).
pub struct UnsafeNoop;
impl fmt::Debug for UnsafeNoop {
    #[allow(unused_unsafe)]
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let _n = unsafe { std::mem::size_of::<u8>() };
        Ok(())
    }
}

/// A lifetime-only `transmute::<&u32, &'static u32>`: InstSimplify erases it
/// to a plain copy, so this crate's ENCODED MIR carries no trace of it, and the
/// HIR half that charges it for a local body (`validity_transmute`) has no HIR
/// to read downstream. A LOCAL copy is refused (rc=1 on the stage-1 snapshot at
/// `4e9fe36bf`, "1 obligation(s) were not proved"); re-derived from this MIR
/// alone it would have cleared a weaker bar. The source fact declines it.
pub struct TmuteRegion(pub u32);
impl fmt::Debug for TmuteRegion {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let r: &u32 = &self.0;
        let _s: &'static u32 = unsafe { std::mem::transmute::<&u32, &'static u32>(r) };
        Ok(())
    }
}
