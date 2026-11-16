//! CLOSE NEGATIVE TWIN of `r29`: the same island, the same contracts, the same
//! `targo trust check main.rs` invocation — and ONE changed body. `min2` now
//! returns `a` unconditionally, which is not definitionally equal to `min_isl`
//! (`min2(41, 7)` is 41, `min_isl 41 7` is 7), so the uncited island-defeq lane
//! must refuse the clause and the authenticated lane must NOT report `Gate:
//! PASS`.
//!
//! Why the twin matters for the evidence change `r29` pins: that change makes
//! kernel-discharged rows PUBLISHABLE, so the failure to guard against is a
//! payload that rides along with a discharge the kernel never made. The
//! producer mints only after re-judging the whole surface under the full
//! certification audit, and a refused clause discharges nothing for the
//! function — so there is no row for a payload to attach to. This row keeps
//! that true end to end, through the same lane `r29` goes green on.
//!
//! `keep` is left honest on purpose: the refusal must come from the false
//! clause, not from collateral damage.

clean {
    def min_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn min2(a: u64, b: u64) -> u64
    ensures result == min_isl(a, b)
{
    a
}

pub fn keep(x: u64) -> u64
    ensures result >= x by u64_ge_refl
{
    x
}

fn main() {
    let m = min2(7, 41);
    let _k = keep(m);
}
