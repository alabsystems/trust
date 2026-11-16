//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E9-RESULT-CARRIER-4 (TG15 residual 1): an island definition whose RESULT is
//! spelled through a type alias. `island_return_domain` matched the codomain's
//! spelled constant name, so `def in_range_flag (a : BitVec 64) : Flag` with
//! `abbrev Flag := Bool` recorded no return domain, although its binders already
//! read through the alias (98559c747c), and the proposition-position arm refused
//! the call. The result is now read by the same alias-aware reader and recorded
//! only where its carrier has one preimage. This is row (3) of
//! `e9_comparison_bool_discharge.rs` with the result spelled `Flag`; the
//! fail-closed twin is `e9_island_alias_bool_result_fail_closed.rs`.

clean {
    abbrev Flag := Bool
    def in_range_flag (a : BitVec 64) : Flag := Bool.true
}

pub fn prop_position_flag(a: i64) -> bool
    ensures in_range_flag(a)
{
    true
}

fn main() {
    let _ = prop_position_flag(1);
}
