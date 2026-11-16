//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -O
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//! CLOSE NEGATIVE TWINS of `e9_cited_result_carrier_discharge`. Typing the
//! relation of `result == spec(..)` at the carrier the calls RETURN makes the
//! goal well-formed; it must not make a false clause true, and it must not
//! excuse an operand that really is of another carrier. Each function differs
//! from the positive `cursor` in one respect and each MUST stay a hard citation
//! error with its rows unproved.
//!
//! The island checks in full (no theorem here is false), so a refusal can never
//! be the incidental "an earlier Clean island was rejected" kind.
//!
//! `dont-require-annotations: ERROR` tolerates only the SECONDARY
//! strict-verification / Level-0 errors each function also raises; the primary
//! refusal of every twin is pinned by its own explicit ERROR annotation.

clean {
    def spec_cursor (has fresh same continues : Bool) : UInt8 :=
      if (has && fresh) = true then (if same = true then 1 else if continues = true then 2 else 0) else 0
    theorem spec_cursor_refl (a b c d : Bool) : spec_cursor a b c d = spec_cursor a b c d := rfl
    theorem spec_cursor_flag (flag a b c d : Bool) : spec_cursor a b c d = spec_cursor a b c d := rfl
    def spec_gate (o : Bool) (c : UInt8) : UInt8 := if o = true then c else 0
    def spec_pick (n : Bool) : BitVec 32 := if n = true then BitVec.ofNat 32 3 else BitVec.ofNat 32 5
    def bucket_spec (n : Nat) : UInt8 := ite (Nat.le 512 n) 1 0
    theorem bucket_spec_refl (n : Nat) : bucket_spec n = bucket_spec n := rfl
}

// TWIN 1 — MUTATED BODY: `2` and `1` the other way round, and a citation of a
// true theorem that states something else. The goal `∀ a b c d, @Eq UInt8
// (import a b c d) (spec_cursor a b c d)` is well-typed and false.
pub fn swapped(has: bool, fresh: bool, same: bool, continues: bool) -> u8
    //~^ ERROR Trust strict verification failed for
    ensures result == spec_cursor(has, fresh, same, continues) by spec_cursor_refl
    //~^ ERROR citation `spec_cursor_refl` failed the strict Clean statement/certification audit
{
    if has && fresh { if same { 2 } else if continues { 1 } else { 0 } } else { 0 }
}

// TWIN 2 — A GENUINELY MIXED COMPARISON. `flag` is a `bool` operand of the
// relation itself, not an argument of a typed call, so the `u8` that
// `spec_cursor` returns does not excuse it: the clause is refused by name, never
// built as an ill-typed goal and never retyped.
pub fn mixed(flag: bool, has: bool, fresh: bool, same: bool, continues: bool) -> bool
    //~^ ERROR Trust strict verification failed for
    ensures flag == spec_cursor(has, fresh, same, continues) by spec_cursor_flag
    //~^ ERROR declares its result at carrier `UInt8`, but the comparison is at carrier `Bool`
{
    flag && has && fresh && same && continues
}

// TWINS 3 AND 4 — MUTATED BODIES ON THE UNCITED ROUTE, at the other carrier
// mixes TG15 names (mixed `bool`/`u8` parameters with a `u8` result; a `bool`
// parameter with a signed result). Each body has its arms the other way round
// from the island definition, and no theorem is cited, so definitional
// equality is the only discharge left and it must refuse: the goal is
// well-typed at the result's carrier and false.
pub fn gate_swapped(open: bool, code: u8) -> u8
    //~^ ERROR Trust strict verification failed for
    ensures result == spec_gate(open, code)
{
    if open { 0 } else { code }
}

pub fn pick_swapped(neg: bool) -> i32
    //~^ ERROR Trust strict verification failed for
    ensures result == spec_pick(neg)
{
    if neg { 5 } else { 3 }
}

// TWIN 5 — THE CAST HALF, MUTATED BODY: `bucket` (`u16 -> u8`, a lifted
// argument inside the cited call) with its arms the other way round, citing a
// true theorem that states something else. The goal is well-typed at `UInt8`
// and false.
pub fn bucket_swapped(x: u16) -> u8
    //~^ ERROR Trust strict verification failed for
    ensures result == bucket_spec(x as nat) by bucket_spec_refl
    //~^ ERROR citation `bucket_spec_refl` failed the strict Clean statement/certification audit
{
    if 512 <= x { 0 } else { 1 }
}

fn main() {
    let _ = (swapped(true, true, false, true), mixed(true, true, true, true, true));
    let _ = (gate_swapped(true, 3), pick_swapped(false), bucket_swapped(600));
}
