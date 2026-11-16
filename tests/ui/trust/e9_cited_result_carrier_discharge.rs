//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -O
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9 POSITIVE fixture: a cited `ensures result == spec(..)` whose RESULT
//! carrier is not the carrier its parameters share.
//!
//! `cursor` is aterm's `relay_live::cursor` (crates/aterm-mesh-core): four
//! `bool` flags in, a `u8` code out. On Trust build 16387 it was the one kernel
//! of four in that file whose citation did not discharge: the goal builder
//! typed the relation of `result == spec_cursor(..)` by the variables in it,
//! all of them `bool` arguments of the two calls, and built `@Eq Bool` over two
//! `UInt8` terms, which the kernel refused ("the postcondition goal could not
//! be built (... TypeMismatch expected Bool, inferred UInt8 ...)"). The relation
//! now takes the result carrier the two typed calls declare. `code` is the same
//! bug at two machine widths (`u8` -> `u16`). `bool_to_int` is the same bug on
//! the UNCITED route (`e6_select_match_refusals` pinned it as a refusal until
//! this fix): its clause is closed by definitional equality alone.
//! `same_code` (`u8, u8 -> bool`), `gate` (`bool, u8 -> u8`), `admits`
//! (`bool, u8 -> bool`) and `pick` (`bool -> i32`) are the other carrier mixes
//! TG15 names: a `u8`-parameter kernel with a `bool` result, mixed `bool`/`u8`
//! parameters with each kind of result, and a signed result over a `bool`.
//! `bucket` (`u16 -> u8`) is the cast half: `bucket_spec(x as nat)` is a
//! `UInt8` result, so the lifted argument inside the call must not keep the
//! relation at the `UInt16` its variable has (TG15 verification, 2026-11-06:
//! on origin/main e88d030c4a it built `@Eq UInt16` over two `UInt8` terms).
//!
//! `check-pass` is NOT vacuous: `-Ztrust-verify=on` is strict, and a clause that
//! calls an island definition is outside every solver lane's vocabulary (its
//! rows are fail-closed `SpecEnsuresUnparseable` sentinels), so only a kernel
//! discharge (the citation, or definitional equality for `bool_to_int`) can
//! close these rows; with the old goal builder every one of them is a hard
//! error. The close negative twins live in `e9_cited_result_carrier_undischarged.rs`.

clean {
    def spec_cursor (has fresh same continues : Bool) : UInt8 :=
      if (has && fresh) = true then (if same = true then 1 else if continues = true then 2 else 0) else 0
    def spec_code (a : UInt8) : UInt16 := if a = 1 then 7 else 9
    def b2i_isl (c : Bool) : UInt8 := if c then 1 else 0
    -- `if .. then true else false` mints no `DefId`, so this carrier row does
    -- not depend on the Clean-origin gate. The minted `decide (a = b)` spelling
    -- with the same `rfl` citation is `e9_minted_spec_deferred_citation.rs`.
    def spec_same_code (a b : UInt8) : Bool := if a = b then true else false
    def spec_gate (o : Bool) (c : UInt8) : UInt8 := if o = true then c else 0
    def spec_admits (o : Bool) (c : UInt8) : Bool := o && decide (c = 1)
    def spec_pick (n : Bool) : BitVec 32 := if n = true then BitVec.ofNat 32 3 else BitVec.ofNat 32 5
    def bucket_spec (n : Nat) : UInt8 := ite (Nat.le 512 n) 1 0
}

pub fn cursor(has: bool, fresh: bool, same: bool, continues: bool) -> u8
    ensures result == spec_cursor(has, fresh, same, continues) by cursor_is_exact
    //~^ NOTE citation `cursor_is_exact` kernel-discharges this postcondition statement
{
    if has && fresh { if same { 1 } else if continues { 2 } else { 0 } } else { 0 }
}

pub fn code(a: u8) -> u16
    ensures result == spec_code(a) by code_is_exact
    //~^ NOTE citation `code_is_exact` kernel-discharges this postcondition statement
{
    if a == 1 { 7 } else { 9 }
}

pub fn bool_to_int(c: bool) -> u8
    ensures result == b2i_isl(c)
    //~^ NOTE island definition `b2i_isl` kernel-discharges this postcondition by definitional equality
{
    if c { 1 } else { 0 }
}

pub fn same_code(a: u8, b: u8) -> bool
    ensures result == spec_same_code(a, b) by same_code_is_exact
    //~^ NOTE citation `same_code_is_exact` kernel-discharges this postcondition statement
{
    a == b
}

pub fn gate(open: bool, code: u8) -> u8
    ensures result == spec_gate(open, code) by gate_is_exact
    //~^ NOTE citation `gate_is_exact` kernel-discharges this postcondition statement
{
    if open { code } else { 0 }
}

pub fn admits(open: bool, code: u8) -> bool
    ensures result == spec_admits(open, code) by admits_is_exact
    //~^ NOTE citation `admits_is_exact` kernel-discharges this postcondition statement
{
    open && code == 1
}

pub fn pick(neg: bool) -> i32
    ensures result == spec_pick(neg) by pick_is_exact
    //~^ NOTE citation `pick_is_exact` kernel-discharges this postcondition statement
{
    if neg { 3 } else { 5 }
}

pub fn bucket(x: u16) -> u8
    ensures result == bucket_spec(x as nat) by bucket_is_exact
    //~^ NOTE citation `bucket_is_exact` kernel-discharges this postcondition statement
{
    if 512 <= x { 1 } else { 0 }
}

clean {
    theorem cursor_is_exact (a b c d : Bool) :
        trust_import_e9_cited_result_carrier_discharge__cursor a b c d = spec_cursor a b c d := by
      cases a <;> cases b <;> cases c <;> cases d <;> rfl
    theorem code_is_exact (a : UInt8) :
        trust_import_e9_cited_result_carrier_discharge__code a = spec_code a := rfl
    theorem same_code_is_exact (a b : UInt8) :
        trust_import_e9_cited_result_carrier_discharge__same_code a b = spec_same_code a b := rfl
    theorem gate_is_exact (o : Bool) (c : UInt8) :
        trust_import_e9_cited_result_carrier_discharge__gate o c = spec_gate o c := by
      cases o <;> rfl
    theorem admits_is_exact (o : Bool) (c : UInt8) :
        trust_import_e9_cited_result_carrier_discharge__admits o c = spec_admits o c := by
      cases o <;> rfl
    theorem pick_is_exact (n : Bool) :
        trust_import_e9_cited_result_carrier_discharge__pick n = spec_pick n := by
      cases n <;> rfl
    theorem bucket_is_exact : forall (x : UInt16),
        Eq (trust_import_e9_cited_result_carrier_discharge__bucket x) (bucket_spec (UInt16.toNat x)) :=
        fun x => Eq.refl (trust_import_e9_cited_result_carrier_discharge__bucket x)
}

fn main() {
    let _ = (cursor(true, true, false, true), code(1), bool_to_int(true));
    let _ = (same_code(1, 2), gate(true, 3), admits(true, 1), pick(false), bucket(600));
}
