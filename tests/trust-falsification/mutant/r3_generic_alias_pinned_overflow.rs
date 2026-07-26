#![crate_type = "lib"]
// Trust R3 TRAP T4: where-clause-PINNED assoc arithmetic — typeck normalizes
// `T::Out` to `u32` under the `T: W<Out = u32>` bound, so MIR spells the
// concrete type and the unguarded `x + 1` overflow REFUTES (x == u32::MAX).
// Pins the Land-1 scoping question empirically: NEVER proved. Must exit 1.
pub trait W {
    type Out;
}
pub fn r3_t_pinned<T: W<Out = u32>>(x: T::Out) -> u32 {
    x + 1
}
