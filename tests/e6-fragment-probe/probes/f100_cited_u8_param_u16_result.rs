//@ probe-shape: none
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: f98's bug at two MACHINE widths: one `u8` parameter, a `u16` result.
//@ probe-note: MEASURED on Trust build 16387: `unproved`, the post-walk lane's
//@ probe-note: `ClauseOutsideFragment`: "TypeMismatch expected UInt8, inferred UInt16 at
//@ probe-note: [PiBody, AppFn, AppArg]" -- the relation
//@ probe-note: was typed by the parameter. Any uniform parameter carrier other than the
//@ probe-note: result's had it; mixed parameters (a `bool` and a `u8`) and a `bool`
//@ probe-note: result over `u8` parameters already discharged, through the mixed-domain
//@ probe-note: recovery and the decided-`bool` relation respectively.
clean {
    def spec_code (a : UInt8) : UInt16 :=
      if a = 1 then 7 else 9
}
clean {
    theorem code_is_exact (a : UInt8) :
        trust_import_probe__code a = spec_code a := rfl
}
pub fn code(a: u8) -> u16
    ensures result == spec_code(a) by code_is_exact
{ if a == 1 { 7 } else { 9 } }
