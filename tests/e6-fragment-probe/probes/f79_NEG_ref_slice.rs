//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. MEASURED on a stage-1 compiler carrying I1.
//@ probe-note: C3: the pointee must be a STRUCT. A slice is unsized, has no declared
//@ probe-note: fields to flatten, and would need a sequence carrier the E6 vocabulary
//@ probe-note: does not have. `&str`, `&dyn Tr`, `&&T`, `&Box<T>`, `&(A, B)`, `&Enum`
//@ probe-note: and a generic `&T` land on the same refusal, each for its own reason,
//@ probe-note: which the diagnostic enumerates.
clean { def id64s (x : UInt64) : UInt64 := x }
pub fn first_len(xs: &[u64]) -> u64
    ensures result == id64s(0)
{ xs.len() as u64 }
