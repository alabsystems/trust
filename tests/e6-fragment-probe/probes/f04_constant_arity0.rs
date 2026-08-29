//@ probe-shape: ConstantUint
//@ probe-expect: discharged
//@ probe-note: WIDENED by a96eb1205d: a bare ZERO-ARITY citation now resolves through
//@ probe-note: the exact ambient admission, while bindings still shadow admissions,
//@ probe-note: parameterized definitions still require application, and unknown bare
//@ probe-note: identifiers still fail closed. Measured `discharged` at 4c8a1e19da.
clean { def forty_two_isl : UInt64 := 42 }
pub fn answer() -> u64
    ensures result == forty_two_isl
{
    42
}
