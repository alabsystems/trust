//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//
// Trust (#197) regression: two facts about declarations minted at the assembly seam.
//
// (a) THE UNANIMOUS RETURN SURVIVES AMBIGUITY.
//
// wave-C puts two monomorphizations of one `DefId` under one `FuncId`, so `resolve_callee` hits
// its ambiguous arm and declares rather than links — which body to link genuinely is a guess.
// It also used to hardcode `ret: None`, on the claim that "their return types are not jointly
// attributable". The ledger had already answered that question: `emit_call` writes `ret_ty` to
// every entry sharing the `func_id` and poisons the whole set on the first disagreement, so a
// real conflict is `ret_ty_conflict` before `resolve_callee` ever runs. What the arm discarded
// was the ledger's own unanimous verdict.
//
// The minimal pair below is the proof: ONE instantiation of `size_of` declared
// `(...) -> (usize)` and validated; adding a SECOND identical-returning instantiation collapsed
// it to `(...) -> ()` and minted two `InstrResultArityMismatch`. `size_of::<T>()` returns
// `usize` at every instantiation — which body to call is ambiguous, the result type is not.
//
// (b) THE ARITY GUARD THAT MAKES (a) SAFE.
//
// `validate_instruction_result_arities` compares the declaration's `returns.len()` against the
// instruction's `results.len()`. One `FuncId` can cover sites that bind DIFFERENT counts — a
// unit-returning instantiation binds 0, a value-returning one binds 1 — and `emit_call` returns
// early on the unit path BEFORE its recording block while the value site still writes back to
// every entry sharing the `func_id`. So unanimity alone would relocate errors rather than clear
// them. The minted declaration therefore keys on the arity the site actually declares.
//
// `check-pass`: every function here is ordinary Rust and must compile identically.

use std::mem::size_of;

struct A(u8);
struct B(u64, u64);

// (a) TWO instantiations, one unanimous `usize` return.
pub fn two_instantiations() -> usize {
    let a = size_of::<A>();
    let b = size_of::<B>();
    a + b
}

// The control: one instantiation. Must keep declaring `(...) -> (usize)` exactly as before.
pub fn one_instantiation() -> usize {
    size_of::<A>()
}

// (b) One generic fn reached at a UNIT instantiation and a VALUE instantiation. The unit site
// binds 0 results, the value site binds 1, and both may share a `FuncId`.
fn ident<T>(t: T) -> T {
    t
}

pub fn mixed_arity_sites() -> u32 {
    ident(());
    ident(7u32)
}

// (c) THE ABI RIDES THE SAME UNANIMITY RULE. Giving the ambiguous declaration a real return type
// made a latent false claim observable: the arm hardcoded `rust_abi: false` and called it "the
// conservative foreign default", but `false` is a CLAIM — it says the callee uses the C ABI, and
// `is_foreign_abi_boundary` then holds `repr(Rust)` structs to FFI repr rules. It was inert only
// while the declaration had no type for the repr check to inspect. `Result::unwrap` at two
// instantiations returning a `repr(Rust)` struct is the case that surfaced it.
pub struct Payload {
    pub a: u32,
    pub b: u64,
}

fn get(v: u8) -> Result<Payload, ()> {
    Ok(Payload { a: v as u32, b: 0 })
}

fn get2(v: u8) -> Result<Payload, u8> {
    Ok(Payload { a: v as u32, b: 1 })
}

pub fn two_unwraps() -> u64 {
    let p = get(1).unwrap();
    let q = get2(2).unwrap();
    p.b + q.b
}

// (d) A `-> !` fn returns no VALUES, at the signature AND at both `Inst::Return` epilogues.
// Fixing only the signature traded one error class for another.
pub fn diverges_via_explicit_return(c: bool) -> ! {
    if c {
        panic!("a")
    }
    return panic!("b");
}

fn main() {}
