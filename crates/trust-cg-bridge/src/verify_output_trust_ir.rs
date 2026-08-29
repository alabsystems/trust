// trust-cg-bridge/verify_output_trust_ir.rs — the PROVEN-OUTPUT GATE for the
// F1 (source -> trust_ir_of -> object) frontend.
//
// WHY THIS FILE EXISTS. `verify_output.rs` proves, per function,
// `forall args. machine_ret(args) == ir_ret(args)`: the machine side by
// symbolically executing the EMITTED BYTES, the spec side by interpreting the
// IR. Its spec side reads a `trust_types::VerifiableFunction` — a MIR-SHAPED
// body (`locals` + `BasicBlock` + `Statement::Assign { place, rvalue }` +
// `Terminator`). Despite the name `trust_ir_semantics`, NOTHING in it consumes a
// `trust_ir::Function`. The F1 path never builds a `VerifiableFunction`, so the
// gate structurally could not run there.
//
// THIS MODULE IS THE MISSING SPEC SIDE, derived DIRECTLY from `trust_ir`:
//
//   * `trust_ir_function_semantics` walks a `trust_ir::Function`'s SSA blocks
//     (block params, `Inst::*`, block-argument branches) and produces the SAME
//     `trust_types::Formula` algebra over the SAME AAPCS64 argument-register
//     variables (`X{i}` / `W{i}`) that the machine side reads. Every Formula
//     constructor it uses (`eval_binop`, `eval_cast`, `pred_to_int`, `xn`, `wn`)
//     is the EXACT function the MIR-side interpreter uses — the two spec sides
//     agree on op semantics by construction, not by parallel re-derivation.
//   * the MACHINE side is `verify_output`'s `PathMergingExecutor`, UNCHANGED
//     except for the trap modeling described below. The bytes it executes come
//     from `lower_module_to_lir` — the SAME converter F1 ships through.
//
// THE SPEC IS NEVER DERIVED FROM THE LOWERING. `trust_ir_function_semantics`
// reads the PRODUCER's function as `trust_ir_of` emitted it, BEFORE
// `inline_local_pure_leaf_calls` and before any LIR exists. A bug in
// `module_to_lir` therefore shows up as a disagreement, which is the whole point.
//
// TRAPS AND THE `reach` PREDICATE (new obligation shape). A Rust `a / b` lowers
// to `assert b != 0; assert !(a == MIN && b == -1); sdiv`, and `Inst::Assert`
// lowers to `Brif(cond, cont, trap)` with a `bl <panic>; brk` tail. Such a path
// returns NO value. The gate therefore discharges the CONDITIONAL obligation
//
//     spec_reach(args)  =>  machine_reach(args) AND machine_ret == spec_ret
//
// where `spec_reach` is the conjunction of the IR's own `Inst::Assert`
// conditions along the path and `machine_reach` is the byte-level predicate
// "control reaches a RET" (false on a `brk` tail). Both halves are discharged:
// dropping the first would let a spuriously-trapping emission pass.
//
// VACUITY FIREWALL. A function whose `spec_reach` is UNSATISFIABLE would make
// the obligation vacuously true. That is checked and REJECTED (Unknown), never
// reported as Proven.
//
// FAIL-CLOSED EVERYWHERE. Any shape the interpreter does not model EXACTLY —
// memory, calls, aggregates, floats, overflow intrinsics, narrow SHIFTS,
// `bool` PARAMETERS, 128-bit ARITHMETIC, loops — returns `Err`, which the gate
// reports as `Unknown`. There is no arm that emits a function the gate did not
// look at.
//
// THE OBLIGATION IS AT THE DECLARED WIDTH. A narrow (8/16-bit) value is compared
// at 8 or 16 bits, not at 32, and the bits above are unconstrained on BOTH
// sides. That is a deliberately WEAKER equality than a register-width one, and
// it is weaker by exactly the amount the Rust ABI says is not part of the value:
// `arg_ext: None` on a Rust-ABI narrow slot means the callee owes the caller
// nothing above the declared width and the caller may read nothing above it.
// `scalar_reg_width` carries that derivation with its rustc source lines and the
// measured `lsr w0, w0, #3; ret` that proves LLVM leaves those bits dirty.
// A `bool` RESULT is the opposite case — rustc marks it `arg_ext: Zext`, so the
// callee owes a zero-extended 0/1 and the gate holds it to the full 32 bits.
//
// THE 128-BIT FRAGMENT IS MOVE-ONLY. An `i128`/`u128` is admitted as a CARRIED
// value — materialized by `Inst::Const`, bound from an argument register PAIR,
// `Copy`d, `Select`ed, and returned in `X0`/`X1` — because every one of those is
// a pure 128-bit transfer that the machine performs as two independent 64-bit
// register moves, making `concat(X1, X0)` on the byte side bit-for-bit the IR's
// value. It is NOT admitted into arithmetic, comparison, or width-changing
// casts: those lower to carry-coupled `adds`/`adcs`/`ccmp`/`umulh` pairs whose
// exact modeling is unmeasured, and a mismatch there would surface as a
// FABRICATED `Refuted`. See `reject_width_128`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{HashMap, HashSet};

use trust_ir::inst::{BinOp as IrBinOp, CastOp, ICmpOp, Inst, OverflowOp, UnOp as IrUnOp};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Constant, Module, Ty as IrTy};
use trust_types::{BinOp, Formula};

use crate::codegen_backend::{FunctionLinkage, TrustCgCodegenBackend, TrustCgTargetArch};
use crate::verify_output::{
    CertificationReport, Discharge, EmitPolicy, OutputVerdict, PreservedFunction, ProvenEvidence,
    VerifiedModuleObject, VerifyError, assert_merged_object_preserves_verified_text, b,
    discharge_equal_pre, discharge_valid, eval_binop, eval_cast, extract_text_from_object,
    pred_to_int, symbolic_machine_outcome_traps, try_kernel_recheckable_proof, wn, xn,
};

// ===========================================================================
// THE WORK ITEM
// ===========================================================================

/// One F1 function the gate must verify: the PRODUCER's `trust_ir::Module` plus
/// the id of the body function inside it, and the mangled symbol the object
/// emits it under.
///
/// The module is carried whole because `lower_module_to_lir` resolves the
/// function's `FuncTy` (and any inlinable callee) through it — the gate lowers
/// from EXACTLY the same input the shipping path lowers from.
#[derive(Debug, Clone)]
pub struct TrustIrGateSource {
    /// The mangled symbol this function is emitted under. It must already be the
    /// name on the `trust_ir::Function` (the frontend stamps it), because the
    /// object's symbol table and the merge obligation both key on it.
    pub symbol: String,
    /// The producer's module, with the body function renamed to `symbol`.
    pub module: Module,
    /// The body function's id inside `module`.
    pub func_id: FuncId,
}

// ===========================================================================
// PART 1 — THE SPEC SIDE: trust_ir::Function -> Formula
// ===========================================================================

/// A modeled SSA value: its Formula and the bit-width that Formula is at.
///
/// There is deliberately NO signedness field. trust-ir names the signed and
/// unsigned operations separately (`SDiv`/`UDiv`, `AShr`/`LShr`, `Slt`/`Ult`),
/// so every signedness decision is read off the OPCODE. That is strictly more
/// precise than the MIR-side interpreter's inference from operand types — and it
/// is the discriminator the original trust-cg signed-comparison miscompile got
/// wrong, so taking it from the opcode removes the failure mode rather than
/// re-implementing it.
#[derive(Clone)]
struct IrValue {
    f: Formula,
    width: u32,
}

/// What one evaluated path through the IR yields: the return-value Formula and
/// the conjunction of `Inst::Assert` conditions that had to hold to get there.
struct IrOutcome {
    value: Formula,
    reach: Formula,
}

/// The DECLARED BIT WIDTH of a scalar `trust_ir::Ty` — the number of bits that
/// carry the value, which is NOT in general the width of the register holding
/// it.
///
/// NARROW INTEGERS (i8/i16/u8/u16) ARE ADMITTED AT THEIR DECLARED WIDTH, and the
/// distinction above is the entire content of that decision. The machine
/// computes a narrow value in a 32-bit W register whose bits above the declared
/// width are NOT part of the value. Modeling such a value as 32-bit would assert
/// something about those bits that nothing guarantees; modeling it as `N`-bit
/// asserts nothing about them on EITHER side — the spec builds an `N`-bit
/// Formula, and the machine side reads `X0[N-1:0]` through
/// `PathMergingExecutor::read_int_return` / `MachineState::read_gpr(k, N)`. The
/// obligation is therefore an equality on the declared width only, with the
/// upper bits explicitly unconstrained on both sides.
///
/// THAT IS EXACTLY WHAT THE RUST ABI LICENSES, and here is the source rather
/// than an appeal to it. An extension contract exists iff rustc records
/// `ArgAttributes::arg_ext != ArgExtension::None` for the slot, and every write
/// of that field goes through `ArgAttributes::ext`
/// (`compiler/rustc_target/src/callconv/mod.rs:169`). That has SIX call sites,
/// not one, and enumerating them is the argument rather than a formality — the
/// one that actually fires on the Rust ABI is not the obvious one:
///
///   * `ArgAbi::extend_integer_width_to` (`callconv/mod.rs:518,520`) — the
///     target-callconv path. On AArch64 it is reached only from
///     `aarch64::classify_ret` / `classify_arg`
///     (`callconv/aarch64.rs:92,129`), and only under `AbiKind::DarwinPCS`,
///     which is selected only inside `FnAbi::adjust_for_foreign_abi`
///     (`callconv/mod.rs:688`) — the `extern "C"` path. The Rust ABI takes
///     `FnAbi::adjust_for_rust_abi` (`callconv/mod.rs:728`), whose AArch64 hook
///     `aarch64::compute_rust_abi_info` only fixes up softfloat and never
///     extends anything.
///   * `riscv.rs:410`, `mips64.rs:16`, `loongarch.rs:405` — other targets.
///   * `arg_attrs_for_rust_scalar` (`rustc_ty_utils/src/abi.rs:336`), which runs
///     for EVERY `ArgAbi` on EVERY ABI, Rust included — but sets `Zext` for
///     `bool` alone and returns immediately, contributing nothing for an
///     integer. (This is the writer that makes a bool signature `Zext` on the
///     Rust ABI; see [`signature_reg_width`].)
///
/// So a Rust-ABI `-> u8` has `arg_ext: None`: the callee owes the caller nothing
/// above bit 7, and the caller may read nothing above bit 7.
///
/// AND THAT IS NOT MERELY READ OFF THE SOURCE. `scalar_register_abi_ty_supported`
/// refusing every `arg_ext != None` slot is the SOLE reason this weaker
/// obligation is sound, so it is pinned by
/// `tests/run-make/trust-cg-abi-extension-refusal`: a Rust-ABI `-> u8` compiles
/// and is proved on both frontends, while its `extern "C"` twin is refused on
/// both with `arg_ext: Zext` in the message. Deleting that clause was measured to
/// make the gate report `1 [PROVED]` for the `extern "C"` narrow return — an
/// 8-bit obligation wearing a 32-bit contract — and the test catches it.
///
/// MEASURED, not merely read (aarch64-apple-darwin, rustc 1.97 `-O`):
/// `pub fn f(x: u32) -> u8 { (x >> 3) as u8 }` emits `lsr w0, w0, #3; ret` — the
/// high 24 bits of `W0` are left holding `x`'s bits. The same function written
/// `extern "C"` emits `ubfx w0, w0, #3, #8` instead, because THAT ABI does carry
/// `arg_ext: Zext`. And `pub fn g(x: u8) -> u32 { x as u32 + 1 }` emits
/// `and w8, w0, #0xff; add w0, w8, #1` — the callee masks its own parameter,
/// because it may not assume the caller extended it. Both directions of the
/// contract are visible in the bytes.
///
/// 128-BIT INTEGERS ARE ADMITTED, BUT ONLY AS A CARRIED VALUE. Unlike a narrow
/// integer, an `i128`/`u128` has NO unspecified bits: AAPCS64 gives it the full
/// register PAIR (`X{k}` low, `X{k+1}` high, and `X0`/`X1` for the result), and
/// both halves belong to the callee. Modeling it as one 128-bit `Formula` is
/// therefore exact — [`Formula`] carries its width, and `BvConcat` is the same
/// node the machine side reads the pair through. What is NOT admitted is
/// 128-bit ARITHMETIC: the machine lowers a 128-bit add/compare into a
/// carry-coupled `adds`/`adcs`/`ccmp` chain that this gate's fragment does not
/// model, and admitting it would risk a fabricated `Refuted`. See
/// [`reject_width_128`], which every arithmetic/compare/cast arm calls.
///
/// A THIN POINTER IS ADMITTED, BUT ONLY AS A CARRIED VALUE — the same
/// move-only discipline as the 128-bit case, for a different reason.
///
/// `Ty::Ptr` is trust-ir's THIN pointer, and trust-ir names the wide ones
/// separately (`Ty::FatPtr(FatPtrKind)`, whose `bit_width_with(64)` is 128 —
/// `trust-ir/src/ty.rs:286`). So a `Ty::Ptr` is one 64-bit value in one GPR:
/// `trust-cg-lower`'s adapter maps it to LIR `Type::I64` with the comment "All
/// pointers are 64-bit on AArch64" (`adapter.rs:1823`). Nothing about it is
/// unspecified the way a narrow integer's high bits are — all 64 bits are the
/// value — so the equality obligation over `X{k}` is exact, not weakened.
///
/// THIS IS NOT A NEW ABI CLAIM; IT IS THE ONE rustc'S OWN F1 FILTER ALREADY
/// MAKES. `scalar_register_abi_ty_supported`
/// (`compiler/rustc_codegen_trust_cg/src/lib.rs:1008`) admits
/// `ty::Ref(_, _, Mutability::Not)` at `BackendRepr::Scalar` with the comment
/// *"A THIN SHARED REFERENCE is one pointer-sized integer register, passed
/// exactly like a `usize`"*, after refusing every slot with
/// `arg_ext != ArgExtension::None`. A thin `&T` therefore ALREADY reaches the F1
/// compiler path, where this gate then refused it — the refusal was a gate gap
/// on the shipping path, not merely a corpus artifact.
///
/// WHAT IS NOT ADMITTED is any instruction that COMPUTES with a pointer. See
/// [`reject_ptr_compute`]: `BinOp`/`UnOp` on `Ty::Ptr` is pointer ARITHMETIC,
/// which `trust-cg-lower` scales by the pointee size for GEP and treats as a
/// raw byte add for `BinOp` (`adapter.rs:5876`) — two conventions this
/// interpreter does not model; `ICmp`/`Cast`/`Const` on a pointer are equally
/// unmeasured here. Loads, stores, GEP and `GlobalAddr` were never modeled and
/// still are not: they fall through `eval_ir_inst`'s catch-all. What remains —
/// bind a pointer parameter, pass it along a block edge, `Copy` it, `Select`
/// between two of them, return it — is a pure 64-bit register transfer, and the
/// machine performs exactly that.
///
/// A `bool` is a 0/1 carrier at 32 bits (see [`signature_reg_width`] for why
/// that width is the ABI's own obligation for a bool RESULT, and why a bool
/// PARAMETER is nevertheless refused).
fn scalar_reg_width(ty: &IrTy) -> Result<u32, String> {
    match ty {
        // Narrow integers: the DECLARED width is the whole value. Bits above it
        // are unconstrained on both sides — see the ABI derivation above.
        IrTy::I8 | IrTy::U8 => Ok(8),
        IrTy::I16 | IrTy::U16 => Ok(16),
        IrTy::I32 | IrTy::U32 | IrTy::Char => Ok(32),
        IrTy::I64 | IrTy::U64 | IrTy::Isize | IrTy::Usize => Ok(64),
        // A 128-bit integer occupies a register PAIR. Exact as a carried value;
        // arithmetic on it is refused separately by `reject_width_128`.
        IrTy::I128 | IrTy::U128 => Ok(128),
        // A boolean is a 0/1 carrier. `Opcode::Icmp` lowers to `cset`, which
        // writes exactly 0 or 1 into the whole register, so reading it at 32 bits
        // is exact.
        IrTy::Bool => Ok(32),
        // A THIN pointer occupies one whole 64-bit GPR (`Ty::Ptr` -> LIR
        // `Type::I64`). Exact as a carried value; computing with it is refused
        // separately by `reject_ptr_compute`. `Ty::FatPtr`/`Ref`/`RefMut`/
        // `PtrConst`/`PtrMut` are deliberately NOT listed: only the bare thin
        // `Ptr` was measured, and a `FatPtr` is 128 bits over TWO registers.
        IrTy::Ptr => Ok(64),
        other => Err(format!("type outside the modeled scalar fragment: {other:?}")),
    }
}

/// The IN-RANGE requirement a SHIFT narrower than a machine register carries.
///
/// THE PREVIOUS REFUSAL NAMED A CAUSE THAT MEASUREMENT DOES NOT SUPPORT. It read:
/// *"`eval_binop` masks the shift amount mod {width} while the machine's
/// W-register shift masks it mod 32"*, and refused every 8/16-bit shift on that
/// basis. The second half is false for the backend this gate actually verifies.
/// `AArch64ISel`'s shift lowering (`trust-cg-lower/src/isel.rs:10655`) masks the
/// amount to `width - 1` ITSELF before the 32-bit shift, saying so in its own
/// comment — *"trust-ir shift semantics are width-modular (i8 amount mod 8, i16
/// mod 16) … mask it to width-1 first so the 32-bit shift sees an in-[0,width)
/// amount matching the interpreter"* — and an out-of-range CONSTANT amount is
/// filtered out of the immediate form and routed to that same masked register
/// path. MEASURED in the emitted bytes of `<u8 as PrimInt>::unsigned_shl`:
/// `ubfx w2,w1,#0,#8` / `and w1,w2,#7` / `lsl w2,w0,w1` — word 9 is the mod-8
/// mask, not a mod-32 hardware reduction. So the two sides never disagreed.
///
/// THE REAL GAP IS ELSEWHERE, AND IT IS NARROWER. trust-ir's own reference
/// interpreter makes an over-wide shift **UB**, not width-modular: `shift_amount`
/// (`trust-ir/src/interpret.rs:5920`) returns `Err(ub(..))` when
/// `rhs >= bits`. Out of range there is therefore no IR semantics for the spec
/// to render, and `mask_shift`'s mod-width choice would be the gate inventing
/// one. Proving an equality over inputs the IR calls UB is not a proof about the
/// program, and if the ISel mask above were ever removed it would turn into a
/// FABRICATED `Refuted` on exactly those inputs.
///
/// So the honest closure is not "admit" and not "refuse": it is to **require**
/// what the IR itself already asserts. Every narrow shift in the 68-module
/// corpus is preceded by rustc's own shift-overflow check — `ICmp Ult(amt,
/// width)` + `Inst::Assert` — so the in-range fact is IN THE IR, waiting to be
/// discharged rather than assumed. This function returns that requirement as a
/// side condition; [`discharge_trust_ir_obligation`] proves
/// `spec_reach => requirement` VALID **after** the vacuity firewall (an
/// unsatisfiable `spec_reach` would otherwise make every side condition
/// trivially valid), and reports `Unknown` — never `Refuted` — if it does not
/// discharge. Under the requirement `mask_shift(r, width) == r`, so the spec
/// formula carries no masking convention at all.
///
/// Widths 32 and 64 need no condition: there `eval_binop`'s mod-width masking
/// and the hardware's own reduction are the same function.
fn narrow_shift_side_condition(
    op: IrBinOp,
    width: u32,
    amount: &Formula,
) -> Result<Option<Formula>, String> {
    if width >= 32 || !matches!(op, IrBinOp::Shl | IrBinOp::LShr | IrBinOp::AShr) {
        return Ok(None);
    }
    let bound = Formula::BitVec { value: i128::from(width), width };
    let in_range = eval_binop(BinOp::Lt, amount.clone(), bound, width, false)?;
    Ok(Some(in_range))
}

/// Refuse a 128-bit operand/result on an instruction that COMPUTES rather than
/// merely CARRIES its value.
///
/// The 128-bit fragment this gate models is MOVE-ONLY: a 128-bit value may be
/// materialized by `Inst::Const`, bound from a parameter or block parameter,
/// `Copy`d, `Select`ed and returned — every one of which is a pure transfer of
/// 128 bits that the machine performs as two independent 64-bit register moves,
/// so `concat(hi, lo)` on the byte side is bit-for-bit the IR's value.
///
/// Arithmetic is a different animal. `a + b` at 128 bits lowers to `adds`/`adcs`
/// (a CARRY-COUPLED pair), a compare to `cmp`/`ccmp` (a flag-coupled pair), a
/// multiply to `mul`/`umulh`. Whether this gate's machine semantics reproduces
/// those couplings EXACTLY is unmeasured, and a mismatch there would surface as
/// `Refuted` — a fabricated miscompile report against correct code, which is
/// strictly worse than an honest `Unknown`. So it fails closed, by construction,
/// at every arithmetic/compare/cast arm.
fn reject_width_128(width: u32, what: &str) -> Result<(), String> {
    if width == 128 {
        return Err(format!(
            "128-bit {what}: the modeled 128-bit fragment is MOVE-ONLY (const/copy/select/\
             parameter/return), because the machine lowers 128-bit arithmetic into a \
             carry-coupled register-pair sequence this gate does not model exactly \
             (fail-closed rather than risk a false Refuted)"
        ));
    }
    Ok(())
}

/// Refuse a POINTER-typed operand/result on an instruction that COMPUTES rather
/// than merely CARRIES its value.
///
/// The pointer fragment this gate models is MOVE-ONLY, exactly like the 128-bit
/// one and for the same kind of reason: a bind / block-edge / `Copy` / `Select` /
/// `Return` of a `Ty::Ptr` is a 64-bit register transfer that the machine
/// performs verbatim, whereas everything else about a pointer is a convention
/// this interpreter has not measured.
///
///   * `BinOp { op: Add | Sub, ty: Ptr }` is POINTER ARITHMETIC in trust-ir, and
///     `trust-cg-lower` handles it on a dedicated path that requires an integer
///     RHS (`adapter.rs:5876`) — modeling it as a plain `BvAdd` at 64 bits would
///     be a guess about scaling, and a wrong guess produces a FABRICATED
///     `Refuted` rather than an honest `Unknown`.
///   * `Cast` between `Ptr` and an integer is provenance-carrying in trust-ir and
///     is not a `Bitcast` this interpreter has checked.
///   * `ICmp` on pointers and a `Ptr`-typed `Const` are simply unmeasured: no
///     function in the 68-module corpus needs either, so admitting them would be
///     widening the trusted fragment past the evidence.
///
/// `Load`, `Store`, `Alloca`, `HeapAlloc`, `Gep` and `GlobalAddr` need no clause
/// here — they were never modeled and still fall through `eval_ir_inst`'s
/// catch-all, so no pointer this gate admits is ever dereferenced.
fn reject_ptr_compute(ty: &IrTy, what: &str) -> Result<(), String> {
    if matches!(ty, IrTy::Ptr) {
        return Err(format!(
            "pointer {what}: the modeled pointer fragment is MOVE-ONLY (parameter/block-arg/\
             copy/select/return), because pointer arithmetic, pointer-integer casts and \
             pointer comparison are lowering conventions this gate has not measured \
             (fail-closed rather than risk a false Refuted)"
        ));
    }
    Ok(())
}

/// The OVERFLOW FLAG of a checked ADD or SUB, as a Bool-sorted `Formula`.
///
/// WHY THIS ARM IS NOT A WIDENING OF THE VALUE FRAGMENT. `Inst::Overflow` binds
/// TWO results: a value and a flag. The value is the plain WRAPPING op and is
/// built by `eval_binop` — the same shared constructor `Inst::BinOp` uses, so it
/// is one term rather than a second derivation. The flag is the new thing, and
/// it is the reason this cannot be admitted by simply relaxing a type test: it
/// flows into `Inst::Assert`, hence into `spec_reach`, hence into BOTH gate
/// obligations. Getting it wrong is not a missed proof — a flag that is too
/// NARROW makes `spec_reach` too weak and turns obligation A into a FABRICATED
/// `Refuted` against correct code, and a flag that is too WIDE silently weakens
/// obligation B's precondition. Only an EXACT flag is admissible.
///
/// The four definitions are the standard ones and hold at every width:
///
///   * unsigned add — `a + b` carries out iff the wrapped sum dropped below `a`:
///     `s <u a`. (If it carried, `s = a + b - 2^w < a` because `b < 2^w`; if it
///     did not, `s = a + b >= a`.)
///   * unsigned sub — `a - b` borrows iff `a <u b`.
///   * signed add — overflow iff the operands share a sign and the sum does not:
///     the sign bit of `~(a^b) & (a^s)`.
///   * signed sub — overflow iff the operands differ in sign and the difference
///     takes the RHS's: the sign bit of `(a^b) & (a^d)`.
///
/// The two signed cases are the sign-bit idiom rather than the more obviously
/// correct "widen by one bit and compare" form, and that is a deliberate
/// concession to the exporter: a 64-bit checked add would need 65-bit terms,
/// which `ay-proof` will not take, so the definitional form would cost every
/// 64-bit verdict. `signed_overflow_bit_trick_matches_the_definition` pays the
/// difference back by PROVING the two encodings equivalent at a width where both
/// export, instead of asking the reader to accept the idiom.
///
/// MUL IS REFUSED. `translate_overflow` lowers a checked multiply through a
/// wide-multiply bit-pattern at narrow widths and an `SDIV`/`SMULH` identity at
/// 64 (`trust-cg-lower/src/adapter.rs:11288`), and the definitional form needs a
/// `2w`-bit product the exporter cannot carry at `w = 64`. Neither side of that
/// is measured here, so it fails closed — the same call the 128-bit fragment
/// makes, for the same reason.
fn overflow_flag_formula(
    op: OverflowOp,
    width: u32,
    signed: bool,
    lhs: &Formula,
    rhs: &Formula,
    wrapped: &Formula,
) -> Result<Formula, String> {
    let xor = |x: &Formula, y: &Formula| Formula::BvXor(b(x.clone()), b(y.clone()), width);
    let sign_bit_set =
        |f: Formula| Formula::BvSLt(b(f), b(Formula::BitVec { value: 0, width }), width);
    Ok(match (op, signed) {
        (OverflowOp::AddOverflow, false) => {
            Formula::BvULt(b(wrapped.clone()), b(lhs.clone()), width)
        }
        (OverflowOp::SubOverflow, false) => Formula::BvULt(b(lhs.clone()), b(rhs.clone()), width),
        (OverflowOp::AddOverflow, true) => sign_bit_set(Formula::BvAnd(
            b(Formula::BvNot(b(xor(lhs, rhs)), width)),
            b(xor(lhs, wrapped)),
            width,
        )),
        (OverflowOp::SubOverflow, true) => {
            sign_bit_set(Formula::BvAnd(b(xor(lhs, rhs)), b(xor(lhs, wrapped)), width))
        }
        (OverflowOp::MulOverflow, _) => {
            return Err(format!(
                "checked MULTIPLY at {width} bits: the lowering computes its flag through a \
                 wide-multiply bit pattern (narrow) or an SDIV/SMULH identity (64-bit) that \
                 this gate has not measured, and the definitional {}-bit product is outside \
                 what the exporter carries — fail-closed rather than risk a false Refuted \
                 on a flag that feeds `spec_reach`",
                width * 2
            ));
        }
    })
}

/// Which end of the signature a type sits at. The two ends are NOT symmetric for
/// `bool`, so the position has to be a parameter rather than an assumption.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SigPosition {
    /// A value the CALLER writes and the callee reads.
    Parameter,
    /// A value the CALLEE writes and its caller reads.
    Return,
}

/// The bit width of a type appearing in the function SIGNATURE.
///
/// This is [`scalar_reg_width`] MINUS `Ty::Bool` IN PARAMETER POSITION, and the
/// asymmetry is load-bearing — it is the whole reason this function takes a
/// [`SigPosition`].
///
/// A bool RESULT is admitted at 32 bits, and that is the ABI's own obligation
/// rather than a modeling convenience. rustc's `arg_attrs_for_rust_scalar`
/// (`compiler/rustc_ty_utils/src/abi.rs:334`) says it in one line —
/// *"Booleans are always a noundef i1 that needs to be zero-extended"* — and
/// sets `ArgExtension::Zext` for `bool` on the RUST ABI, not merely the foreign
/// one. So a bool result is a value the CALLEE is required to zero-extend across
/// the whole register slot, and its caller is entitled to read all of it and see
/// exactly 0 or 1. Comparing the full 32 bits is thus the STRONGEST form of the
/// obligation, not a weakened one; it is what the ABI demands. Internally the
/// producer of a bool is a `cset` (which writes exactly 0 or 1 into the whole
/// register) or a `const bool`, so the two sides meet.
///
/// A bool PARAMETER is REFUSED, and the reason is not symmetry-breaking for its
/// own sake. Its LIR carrier is `I8`; modeling it as an unconstrained 32-bit
/// value made the gate report REFUTED for six correct
/// `<bool as AsPrimitive<T>>::as_` functions in the 68-module corpus — a
/// fabricated miscompile. The `Zext` attribute above would license a `∈ {0,1}`
/// PRECONDITION on the incoming register instead, which is a different and
/// larger change: it moves the gate from an unconditional equality to one
/// conditioned on a caller-side promise the gate cannot see the caller keep.
/// Until that promise is modeled on both sides, refusing is the honest answer.
///
/// (rustc's ABI filter `scalar_register_abi_ty_supported`
/// (`compiler/rustc_codegen_trust_cg/src/lib.rs:1019`) refuses ANY slot with
/// `arg_ext != None`, so `bool` in either position never reaches the F1
/// compiler path at all — MEASURED: a `-> bool` function is rejected with
/// *"unsupported definition ABI: return value uses unsupported ABI type/pass
/// mode `bool` / Direct(ArgAttributes { .. arg_ext: Zext .. })"*. Admitting the
/// bool RESULT therefore costs the compiler path nothing and buys the corpus
/// census; it matters because the gate must be sound when called directly, and
/// because it is the shape that will be ready if that filter ever widens.
/// Narrow integers are the opposite case: `arg_ext: None` means they DO reach
/// the F1 path — measured, a `-> u8` function compiles and emits through
/// `-Ztrust-cg-frontend=trust-ir`.)
fn signature_reg_width(module: &Module, ty: &IrTy, position: SigPosition) -> Result<u32, String> {
    if matches!(ty, IrTy::Bool) && position == SigPosition::Parameter {
        return Err(
            "`bool` in PARAMETER position: its carrier is an i8 the CALLER wrote, and while \
             rustc marks a bool slot `arg_ext: Zext` (so the caller owes a zero-extended 0/1), \
             this gate does not yet model that promise as a precondition on both sides — an \
             unconstrained 32-bit model of it fabricated six Refuted verdicts once already \
             (fail-closed). A bool RETURN is admitted: that one the callee itself owes."
                .to_string(),
        );
    }
    scalar_reg_width_in(module, ty)
}

/// [`scalar_reg_width`] plus the FIELDLESS-ENUM carrier.
///
/// The carrier rule lives in ONE place — `module_to_lir::fieldless_enum_carrier`
/// — so the width this side reads a return/parameter/constant at is, by
/// construction, the SAME width the converter gave that slot in the LIR. Two
/// derivations of one convention is how the two sides drift; this is one.
///
/// Deliberately NOT applied at the arithmetic/cast/compare/memory sites: those
/// still call the module-blind [`scalar_reg_width`], which fails closed on an
/// enum type. Combined with the converter's identical restriction, an enum-typed
/// value in an admitted function is only ever a parameter, a checked declared
/// discriminant, or a block parameter merging those.
fn scalar_reg_width_in(module: &Module, ty: &IrTy) -> Result<u32, String> {
    match crate::module_to_lir::fieldless_enum_carrier(module, ty) {
        Some(carrier) => scalar_reg_width(&carrier),
        None => scalar_reg_width(ty),
    }
}

fn ty_is_signed(ty: &IrTy) -> bool {
    ty.is_signed()
}

/// What [`trust_ir_function_semantics`] derives from the producer's trust-ir.
///
/// `side_conditions` is the part that is NOT a claim about the machine: each
/// entry is a fact the gate needs to be TRUE for `value` to be a faithful
/// rendering of the IR's own semantics, and which the discharge step therefore
/// PROVES from `reach` rather than assuming. A side condition that does not
/// discharge yields `Unknown` — never `Refuted`, because failing to establish a
/// modeling precondition indicts the gate, not the emitted code.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SpecSemantics {
    /// Return value the producer's trust-ir computes, over `X{i}`/`W{i}`.
    pub value: Formula,
    /// Conjunction of the IR's own `Inst::Assert` guards along each path.
    pub reach: Formula,
    /// Bit width the return value is read at.
    pub out_width: u32,
    /// Modeling preconditions to discharge from `reach` before using `value`.
    pub side_conditions: Vec<Formula>,
}

/// Derive the intended-semantics Formula of `function`'s return value over the
/// AAPCS64 argument registers, plus the `spec_reach` predicate (the conjunction
/// of the IR's own `Inst::Assert` conditions along each path).
///
/// FAILS CLOSED (`Err`) on every shape outside the modeled fragment. The caller
/// reports that as `Unknown`, which the strict policy refuses.
pub fn trust_ir_function_semantics(
    module: &Module,
    func_id: FuncId,
) -> Result<SpecSemantics, String> {
    let function = module
        .function_by_id(func_id)
        .ok_or_else(|| format!("module carries no function with id {}", func_id.index()))?;
    let func_ty = module
        .func_types
        .get(function.ty.as_usize())
        .ok_or_else(|| format!("function `{}` names a FuncTy the module lacks", function.name))?;
    if func_ty.is_vararg {
        return Err("variadic functions are outside the modeled fragment".into());
    }
    if func_ty.returns.len() != 1 {
        return Err(format!(
            "expected exactly 1 return value, got {} (fail-closed)",
            func_ty.returns.len()
        ));
    }
    let out_width = signature_reg_width(module, &func_ty.returns[0], SigPosition::Return)?;

    let blocks: HashMap<u32, &trust_ir::Block> =
        function.blocks.iter().map(|blk| (blk.id.index(), blk)).collect();
    let entry = blocks
        .get(&function.entry.index())
        .ok_or_else(|| format!("function `{}` has no entry block", function.name))?;

    if entry.params.len() != func_ty.params.len() {
        return Err(format!(
            "entry block binds {} param(s) but the signature declares {} (fail-closed)",
            entry.params.len(),
            func_ty.params.len()
        ));
    }

    // ARGUMENT BINDING. Arguments are allocated GPR SLOTS in order: a scalar of
    // 64 bits or fewer takes one (`X{k}`, or its low `N` bits for a value of
    // declared width `N < 64`), a 128-bit integer takes the consecutive PAIR
    // `X{k}` (low) / `X{k+1}` (high) and is read as `concat(X{k+1}, X{k})` — the
    // identical registers `MachineState::symbolic()` seeds and the identical
    // convention the MIR-side interpreter uses.
    //
    // A NARROW parameter binds to `X{k}[N-1:0]` and NOTHING ELSE. That is the
    // whole of the `arg_ext: None` contract: the caller owes no extension, so
    // the bits above `N-1` are not part of the value and this side asserts
    // nothing about them. It is also bit-for-bit `MachineState::read_gpr(k, N)`,
    // the term the machine side would build for the same register — so the two
    // sides are not two derivations of one convention, they are one term.
    //
    // The SLOT INDEX is not the parameter index once a pair is in play, which is
    // why this is a running counter rather than `enumerate()`.
    let mut env: HashMap<ValueId, IrValue> = HashMap::new();
    let mut slot: u32 = 0;
    for (index, ((param_id, param_ty), sig_ty)) in
        entry.params.iter().zip(&func_ty.params).enumerate()
    {
        if param_ty != sig_ty {
            return Err(format!(
                "entry param {index} has type {param_ty:?} but the signature says {sig_ty:?}"
            ));
        }
        let width = signature_reg_width(module, param_ty, SigPosition::Parameter)?;
        let f = if width == 128 {
            // AAPCS64 as WRITTEN gives a 128-bit argument an EVEN-aligned pair;
            // `AppleAArch64ABI::classify_params` as IMPLEMENTED takes the next
            // two consecutive GPRs without realigning. Those two rules coincide
            // exactly when the pair already starts even — so the gate models the
            // aligned case and REFUSES the case where the two disagree, rather
            // than silently picking one and reporting a register-convention
            // disagreement as a miscompile.
            if !slot.is_multiple_of(2) {
                return Err(format!(
                    "128-bit argument {index} would start at the ODD register slot X{slot}, \
                     where the AAPCS64 even-alignment rule and the backend's \
                     next-two-consecutive allocation disagree; refusing to guess which \
                     register the caller wrote (fail-closed)"
                ));
            }
            if slot + 1 >= 8 {
                return Err(format!(
                    "128-bit argument {index} needs the register pair X{slot}/X{}, which is \
                     outside the 8 AAPCS64 integer argument registers this gate models \
                     (fail-closed)",
                    slot + 1
                ));
            }
            let pair = Formula::BvConcat(b(xn(slot + 1)), b(xn(slot)));
            slot += 2;
            pair
        } else {
            if slot >= 8 {
                return Err("more than 8 integer arguments is outside the AAPCS64 register \
                            fragment this gate models (fail-closed)"
                    .into());
            }
            let f = match width {
                64 => xn(slot),
                32 => wn(slot),
                // Narrow: the low `width` bits of the argument register, exactly
                // as `MachineState::read_gpr(slot, width)` would read them. No
                // claim is made about the bits above.
                n => Formula::BvExtract { inner: b(xn(slot)), high: n - 1, low: 0 },
            };
            slot += 1;
            f
        };
        env.insert(*param_id, IrValue { f, width });
    }

    let mut visited = Vec::new();
    let mut ev = SpecEval::new(&blocks);
    let outcome =
        eval_ir_block(module, &blocks, function.entry, &env, &mut visited, 0, out_width, &mut ev)?;
    Ok(SpecSemantics {
        value: outcome.value,
        reach: outcome.reach,
        out_width,
        side_conditions: ev.side,
    })
}

/// Evaluate block `id` under `env`, returning the reachable return-value Formula
/// and the accumulated assert guard. Branches merge as `Ite` over the branch
/// condition, mirroring the machine-side path merger.
///
/// Reconverging control flow is evaluated ONCE per distinct incoming
/// environment slice, not once per path — see the DAG-EVALUATION note above
/// `modeled_operands` for the memo key and why it is sound.
#[allow(clippy::too_many_arguments)]
fn eval_ir_block(
    module: &Module,
    blocks: &HashMap<u32, &trust_ir::Block>,
    id: BlockId,
    env: &HashMap<ValueId, IrValue>,
    visited: &mut Vec<u32>,
    depth: u32,
    out_width: u32,
    ev: &mut SpecEval,
) -> Result<IrOutcome, String> {
    if depth > MAX_IR_DEPTH {
        return Err("IR block-nesting budget exceeded (fail-closed)".into());
    }

    // MEMO HIT. Keyed on the incoming environment restricted to `live_in(id)`
    // and compared by value, so a hit is an environment the evaluation
    // provably cannot distinguish from the one that produced the entry.
    let memo_key = ev.key_for(id.index(), env);
    if let Some(key) = &memo_key {
        if let Some(hit) =
            ev.memo.get(&id.index()).and_then(|entries| entries.iter().find(|e| e.key == *key))
        {
            return Ok(IrOutcome { value: hit.value.clone(), reach: hit.reach.clone() });
        }
    }

    // WORK BUDGET. Counted per block EVALUATION (a memo hit above costs
    // nothing), so this bounds total work rather than any one dimension of it.
    ev.evals += 1;
    if ev.evals > MAX_IR_BLOCK_EVALS {
        return Err(format!(
            "IR evaluation budget exceeded after {MAX_IR_BLOCK_EVALS} block evaluations \
             (fail-closed)"
        ));
    }

    if visited.contains(&id.index()) {
        return Err(format!("loop/backedge at bb{} (fail-closed)", id.index()));
    }
    visited.push(id.index());

    let block = blocks
        .get(&id.index())
        .ok_or_else(|| format!("branch to bb{} which the function lacks", id.index()))?;

    let mut env = env.clone();
    // Assert conditions collected in THIS block, in order.
    let mut guards: Vec<Formula> = Vec::new();

    let Some((terminator, body)) = block.body.split_last() else {
        return Err(format!("bb{} is empty (fail-closed)", id.index()));
    };

    for node in body {
        match &node.inst {
            Inst::Assert { cond } => {
                let c = lookup(&env, *cond)?;
                guards.push(Formula::Not(b(Formula::Eq(
                    b(c.f.clone()),
                    b(Formula::BitVec { value: 0, width: c.width }),
                ))));
            }
            // CHECKED ARITHMETIC is the one modeled instruction that binds TWO
            // results, so it cannot go through the single-result path below.
            // `results[0]` is the wrapping value, `results[1]` the overflow flag
            // — a `bool` SSA value, hence the same 0/1-at-32-bits carrier an
            // `Inst::ICmp` result gets, because that is what it is fed to.
            Inst::Overflow { op, ty, lhs, rhs } => {
                if matches!(ty, IrTy::Bool) {
                    return Err(
                        "checked arithmetic on a bool carrier is not modeled (fail-closed)"
                            .to_string(),
                    );
                }
                reject_ptr_compute(ty, "checked arithmetic")?;
                let width = scalar_reg_width(ty)?;
                reject_width_128(width, "checked arithmetic")?;
                let signed = ty_is_signed(ty);
                let l = operand_at(&env, *lhs, width)?;
                let r = operand_at(&env, *rhs, width)?;
                let (mapped, mapped_signed) = map_ir_binop(
                    match op {
                        OverflowOp::AddOverflow => IrBinOp::Add,
                        OverflowOp::SubOverflow => IrBinOp::Sub,
                        OverflowOp::MulOverflow => IrBinOp::Mul,
                    },
                    signed,
                )?;
                let wrapped = eval_binop(mapped, l.clone(), r.clone(), width, mapped_signed)?;
                let flag = overflow_flag_formula(*op, width, signed, &l, &r, &wrapped)?;
                let [value_id, flag_id] = node.results.as_slice() else {
                    return Err(format!(
                        "`{}` binds {} result(s); the modeled checked-arithmetic shape is \
                         exactly (value, did_overflow) (fail-closed)",
                        inst_label(&node.inst),
                        node.results.len()
                    ));
                };
                env.insert(*value_id, IrValue { f: wrapped, width });
                env.insert(*flag_id, IrValue { f: pred_to_int(flag, 32), width: 32 });
            }
            other => {
                let value = eval_ir_inst(module, &env, other, &mut ev.side)?;
                let [result] = node.results.as_slice() else {
                    return Err(format!(
                        "instruction {} binds {} results; the modeled fragment is \
                         single-result (fail-closed)",
                        inst_label(other),
                        node.results.len()
                    ));
                };
                env.insert(*result, value);
            }
        }
    }

    let outcome =
        eval_ir_terminator(module, blocks, terminator, &env, &visited[..], depth, out_width, ev)?;
    let reach = conjoin(guards, outcome.reach);

    // Record ONLY a successful evaluation. An `Err` path is never memoized, so
    // a later visit re-derives it (and gets the same precise diagnostic).
    if let Some(key) = memo_key {
        ev.memo.entry(id.index()).or_default().push(MemoEntry {
            key,
            value: outcome.value.clone(),
            reach: reach.clone(),
        });
    }
    Ok(IrOutcome { value: outcome.value, reach })
}

#[allow(clippy::too_many_arguments)]
fn eval_ir_terminator(
    module: &Module,
    blocks: &HashMap<u32, &trust_ir::Block>,
    node: &trust_ir::node::InstrNode,
    env: &HashMap<ValueId, IrValue>,
    visited: &[u32],
    depth: u32,
    out_width: u32,
    ev: &mut SpecEval,
) -> Result<IrOutcome, String> {
    match &node.inst {
        Inst::Return { values } => {
            let [v] = values.as_slice() else {
                return Err(format!(
                    "`ret` carries {} value(s); exactly 1 is modeled (fail-closed)",
                    values.len()
                ));
            };
            let value = lookup(env, *v)?;
            if value.width != out_width {
                return Err(format!(
                    "returned value is {}-bit but the signature's return slot is {out_width}-bit \
                     (fail-closed)",
                    value.width
                ));
            }
            Ok(IrOutcome { value: value.f, reach: Formula::Bool(true) })
        }
        // A diverging terminator: this path yields no return value at all. Its
        // `reach` is FALSE, exactly as the machine side reports for the `brk`
        // tail it lowers to.
        Inst::Unreachable => Ok(IrOutcome {
            value: Formula::BitVec { value: 0, width: out_width },
            reach: Formula::Bool(false),
        }),
        Inst::Br { target, args } => {
            let next = bind_block_args(module, blocks, *target, args, env)?;
            let mut fork = visited.to_vec();
            eval_ir_block(module, blocks, *target, &next, &mut fork, depth + 1, out_width, ev)
        }
        Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
            let c = lookup(env, *cond)?;
            let taken = Formula::Not(b(Formula::Eq(
                b(c.f.clone()),
                b(Formula::BitVec { value: 0, width: c.width }),
            )));
            let then_env = bind_block_args(module, blocks, *then_target, then_args, env)?;
            let else_env = bind_block_args(module, blocks, *else_target, else_args, env)?;
            let mut then_visited = visited.to_vec();
            let mut else_visited = visited.to_vec();
            let t = eval_ir_block(
                module,
                blocks,
                *then_target,
                &then_env,
                &mut then_visited,
                depth + 1,
                out_width,
                ev,
            )?;
            let e = eval_ir_block(
                module,
                blocks,
                *else_target,
                &else_env,
                &mut else_visited,
                depth + 1,
                out_width,
                ev,
            )?;
            Ok(IrOutcome {
                value: Formula::Ite(b(taken.clone()), b(t.value), b(e.value)),
                reach: merge_reach(taken, t.reach, e.reach),
            })
        }
        Inst::Switch { value, default, default_args, cases, .. } => {
            // NO ARM CAP. The cap that used to sit here (8) was a guard against
            // the PATH-ENUMERATION blow-up, not a modeling limit: the cascade
            // below is the same nested `Ite` at any arm count, and each arm is
            // now evaluated ONCE (see the DAG-EVALUATION note above
            // `modeled_operands`). What bounds the work is
            // `MAX_IR_BLOCK_EVALS`, which counts the arms that are actually
            // evaluated instead of guessing an arm count that would be safe.
            let sel = lookup(env, *value)?;
            let default_env = bind_block_args(module, blocks, *default, default_args, env)?;
            let mut default_visited = visited.to_vec();
            let mut acc = eval_ir_block(
                module,
                blocks,
                *default,
                &default_env,
                &mut default_visited,
                depth + 1,
                out_width,
                ev,
            )?;
            // Fold LAST-to-FIRST so case 0 is tested outermost, matching the
            // comparison chain the backend emits.
            for case in cases.iter().rev() {
                let case_val = match &case.value {
                    Constant::Int(v) => *v,
                    Constant::Bool(v) => i128::from(*v),
                    other => {
                        return Err(format!("switch case constant {other:?} is not modeled"));
                    }
                };
                let is_case = Formula::Eq(
                    b(sel.f.clone()),
                    b(Formula::BitVec { value: case_val, width: sel.width }),
                );
                let arm_env = bind_block_args(module, blocks, case.target, &case.args, env)?;
                let mut arm_visited = visited.to_vec();
                let arm = eval_ir_block(
                    module,
                    blocks,
                    case.target,
                    &arm_env,
                    &mut arm_visited,
                    depth + 1,
                    out_width,
                    ev,
                )?;
                acc = IrOutcome {
                    value: Formula::Ite(b(is_case.clone()), b(arm.value), b(acc.value)),
                    reach: merge_reach(is_case, arm.reach, acc.reach),
                };
            }
            Ok(acc)
        }
        other => Err(format!(
            "terminator `{}` is outside the modeled fragment (fail-closed)",
            inst_label(other)
        )),
    }
}

/// Bind a branch edge's arguments to the target block's parameters.
fn bind_block_args(
    module: &Module,
    blocks: &HashMap<u32, &trust_ir::Block>,
    target: BlockId,
    args: &[ValueId],
    env: &HashMap<ValueId, IrValue>,
) -> Result<HashMap<ValueId, IrValue>, String> {
    let block = blocks
        .get(&target.index())
        .ok_or_else(|| format!("branch to bb{} which the function lacks", target.index()))?;
    if block.params.len() != args.len() {
        return Err(format!(
            "edge to bb{} passes {} arg(s) for {} param(s) (fail-closed)",
            target.index(),
            args.len(),
            block.params.len()
        ));
    }
    let mut next = env.clone();
    for ((param_id, param_ty), arg) in block.params.iter().zip(args) {
        let width = scalar_reg_width_in(module, param_ty)?;
        let value = lookup(env, *arg)?;
        if value.width != width {
            return Err(format!(
                "edge to bb{} passes a {}-bit value into a {width}-bit param (fail-closed)",
                target.index(),
                value.width
            ));
        }
        next.insert(*param_id, IrValue { f: value.f, width });
    }
    Ok(next)
}

fn lookup(env: &HashMap<ValueId, IrValue>, id: ValueId) -> Result<IrValue, String> {
    env.get(&id).cloned().ok_or_else(|| format!("read of undefined SSA value %{}", id.index()))
}

/// Evaluate ONE value-producing instruction into a modeled SSA value.
fn eval_ir_inst(
    module: &Module,
    env: &HashMap<ValueId, IrValue>,
    inst: &Inst,
    side: &mut Vec<Formula>,
) -> Result<IrValue, String> {
    match inst {
        Inst::Const { ty, value } => {
            reject_ptr_compute(ty, "constant")?;
            let width = scalar_reg_width_in(module, ty)?;
            let literal = match value {
                Constant::Int(v) => *v,
                Constant::Bool(v) => i128::from(*v),
                // A FIELDLESS-ENUM literal: the producer's canonical
                // `(Ty::Enum, Aggregate([Int(disc)]))` seed, whose one field is
                // the DISCRIMINANT at the def's canonical tag repr. The
                // discriminant must be one the def DECLARES — the same check the
                // converter makes before it emits the `Iconst`, so the two sides
                // model the same value or neither models one.
                Constant::Aggregate(fields)
                    if fields.len() == 1
                        && crate::module_to_lir::fieldless_enum_carrier(module, ty).is_some() =>
                {
                    match fields[0] {
                        Constant::Int(d)
                            if crate::module_to_lir::fieldless_enum_has_discriminant(
                                module, ty, d,
                            ) =>
                        {
                            d
                        }
                        ref other => {
                            return Err(format!(
                                "enum constant field 0 is {other:?}, which is not a DECLARED \
                                 discriminant of this def (fail-closed)"
                            ));
                        }
                    }
                }
                other => return Err(format!("constant {other:?} is not modeled (fail-closed)")),
            };
            Ok(IrValue { f: Formula::BitVec { value: literal, width }, width })
        }
        Inst::Copy { ty, operand } => {
            let width = scalar_reg_width(ty)?;
            let v = lookup(env, *operand)?;
            if v.width != width {
                return Err(format!(
                    "`copy` of a {}-bit value at declared type width {width} (fail-closed)",
                    v.width
                ));
            }
            Ok(IrValue { f: v.f, width })
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            if matches!(ty, IrTy::Bool) {
                return Err(
                    "integer BinOp on a bool carrier is not modeled (fail-closed)".to_string()
                );
            }
            reject_ptr_compute(ty, "BinOp (pointer arithmetic)")?;
            let width = scalar_reg_width(ty)?;
            reject_width_128(width, "integer BinOp")?;
            let signed = ty_is_signed(ty);
            let l = operand_at(env, *lhs, width)?;
            let r = operand_at(env, *rhs, width)?;
            // A narrow shift is admitted only against a DISCHARGED in-range
            // requirement; see `narrow_shift_side_condition`.
            if let Some(cond) = narrow_shift_side_condition(*op, width, &r)? {
                side.push(cond);
            }
            let (mapped, mapped_signed) = map_ir_binop(*op, signed)?;
            let f = eval_binop(mapped, l, r, width, mapped_signed)?;
            Ok(IrValue { f, width })
        }
        Inst::UnOp { op, ty, operand } => {
            if matches!(ty, IrTy::Bool) {
                return Err("UnOp on a bool carrier is not modeled (fail-closed)".to_string());
            }
            reject_ptr_compute(ty, "UnOp")?;
            let width = scalar_reg_width(ty)?;
            reject_width_128(width, "UnOp")?;
            let v = operand_at(env, *operand, width)?;
            let f = match op {
                // `Bnot` -> `MVN`: bitwise complement at the register width.
                IrUnOp::Not => Formula::BvNot(b(v), width),
                // `Ineg` -> `NEG`: wrapping `0 - x`.
                IrUnOp::Neg => Formula::BvSub(b(Formula::BitVec { value: 0, width }), b(v), width),
                other => {
                    return Err(format!("unary op {other:?} is not modeled (fail-closed)"));
                }
            };
            Ok(IrValue { f, width })
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            reject_ptr_compute(ty, "ICmp")?;
            let width = scalar_reg_width(ty)?;
            reject_width_128(width, "ICmp")?;
            let l = operand_at(env, *lhs, width)?;
            let r = operand_at(env, *rhs, width)?;
            let (mapped, signed) = map_ir_icmp(*op);
            let pred = eval_binop(mapped, l, r, width, signed)?;
            // A comparison result is the 0/1 the `cset` lowering materializes.
            Ok(IrValue { f: pred_to_int(pred, 32), width: 32 })
        }
        Inst::Cast { op, src_ty, dst_ty, operand } => {
            reject_ptr_compute(src_ty, "cast source")?;
            reject_ptr_compute(dst_ty, "cast destination")?;
            let src_width = scalar_reg_width(src_ty)?;
            let dst_width = scalar_reg_width(dst_ty)?;
            reject_width_128(src_width, "cast source")?;
            reject_width_128(dst_width, "cast destination")?;
            let v = operand_at(env, *operand, src_width)?;
            let f = match op {
                CastOp::Trunc => eval_cast(v, src_width, false, dst_width)?,
                CastOp::ZExt => eval_cast(v, src_width, false, dst_width)?,
                CastOp::SExt => eval_cast(v, src_width, true, dst_width)?,
                // `map_int_cast` lowers a SAME-WIDTH `Bitcast` to `Opcode::Copy`:
                // LIR integer types are width-only, so an equal-width integer
                // reinterpret is the identity on the bit pattern.
                CastOp::Bitcast if src_width == dst_width => v,
                other => {
                    return Err(format!(
                        "cast op {other:?} ({src_width} -> {dst_width}) is not modeled \
                         (fail-closed)"
                    ));
                }
            };
            Ok(IrValue { f, width: dst_width })
        }
        Inst::Select { ty, cond, then_val, else_val } => {
            let width = scalar_reg_width(ty)?;
            let c = lookup(env, *cond)?;
            let t = operand_at(env, *then_val, width)?;
            let e = operand_at(env, *else_val, width)?;
            // `Opcode::Select { cond: NotEqual }` -> `CMP c,#0; CSEL t,e,ne`.
            let taken = Formula::Not(b(Formula::Eq(
                b(c.f),
                b(Formula::BitVec { value: 0, width: c.width }),
            )));
            Ok(IrValue { f: Formula::Ite(b(taken), b(t), b(e)), width })
        }
        other => Err(format!(
            "instruction `{}` is outside the modeled fragment (fail-closed)",
            inst_label(other)
        )),
    }
}

/// Read an operand and require it to already be at `width`. The gate does NOT
/// silently widen or truncate: an unexpected width means the IR is outside the
/// shape this interpreter claims to model, and guessing would be exactly the
/// kind of quiet fixup that fabricates a proof.
fn operand_at(env: &HashMap<ValueId, IrValue>, id: ValueId, width: u32) -> Result<Formula, String> {
    let v = lookup(env, id)?;
    if v.width != width {
        return Err(format!(
            "operand %{} is {}-bit where the instruction declares {width}-bit (fail-closed)",
            id.index(),
            v.width
        ));
    }
    Ok(v.f)
}

/// Map a `trust_ir::BinOp` onto the `trust_types::BinOp` + signedness pair that
/// `verify_output::eval_binop` (the SHARED constructor) consumes.
///
/// The signedness is taken from the OPCODE (`SDiv` vs `UDiv`, `AShr` vs `LShr`),
/// not from the result type — trust-ir names the signed and unsigned operations
/// separately, which is strictly more precise than the MIR-side inference.
fn map_ir_binop(op: IrBinOp, ty_signed: bool) -> Result<(BinOp, bool), String> {
    Ok(match op {
        IrBinOp::Add => (BinOp::Add, ty_signed),
        IrBinOp::Sub => (BinOp::Sub, ty_signed),
        IrBinOp::Mul => (BinOp::Mul, ty_signed),
        IrBinOp::SDiv => (BinOp::Div, true),
        IrBinOp::UDiv => (BinOp::Div, false),
        IrBinOp::SRem => (BinOp::Rem, true),
        IrBinOp::URem => (BinOp::Rem, false),
        IrBinOp::And => (BinOp::BitAnd, ty_signed),
        IrBinOp::Or => (BinOp::BitOr, ty_signed),
        IrBinOp::Xor => (BinOp::BitXor, ty_signed),
        IrBinOp::Shl => (BinOp::Shl, ty_signed),
        IrBinOp::LShr => (BinOp::Shr, false),
        IrBinOp::AShr => (BinOp::Shr, true),
        other => {
            return Err(format!("binary op {other:?} is not modeled (fail-closed)"));
        }
    })
}

fn map_ir_icmp(op: ICmpOp) -> (BinOp, bool) {
    match op {
        ICmpOp::Eq => (BinOp::Eq, false),
        ICmpOp::Ne => (BinOp::Ne, false),
        ICmpOp::Ult => (BinOp::Lt, false),
        ICmpOp::Ule => (BinOp::Le, false),
        ICmpOp::Ugt => (BinOp::Gt, false),
        ICmpOp::Uge => (BinOp::Ge, false),
        ICmpOp::Slt => (BinOp::Lt, true),
        ICmpOp::Sle => (BinOp::Le, true),
        ICmpOp::Sgt => (BinOp::Gt, true),
        ICmpOp::Sge => (BinOp::Ge, true),
    }
}

fn conjoin(mut guards: Vec<Formula>, rest: Formula) -> Formula {
    if matches!(rest, Formula::Bool(true)) && guards.is_empty() {
        return Formula::Bool(true);
    }
    if guards.is_empty() {
        return rest;
    }
    if !matches!(rest, Formula::Bool(true)) {
        guards.push(rest);
    }
    if guards.len() == 1 {
        return guards.remove(0);
    }
    Formula::And(guards)
}

fn merge_reach(cond: Formula, then_reach: Formula, else_reach: Formula) -> Formula {
    if matches!(then_reach, Formula::Bool(true)) && matches!(else_reach, Formula::Bool(true)) {
        return Formula::Bool(true);
    }
    Formula::Ite(b(cond), b(then_reach), b(else_reach))
}

// ===========================================================================
// DAG EVALUATION — why the spec side memoizes, and why that is sound
// ===========================================================================
//
// `eval_ir_block` is a PATH ENUMERATOR: at every branch it evaluates BOTH
// successors and merges them into an `Ite`. When two branch arms RECONVERGE —
// which is what every `if` without an early return, and every range test
// `lo <= x && x <= hi`, compiles to — the block below the join is evaluated once
// PER PATH, not once. A cascade of `n` such tests is therefore evaluated 2^n
// times.
//
// That is not a hypothetical. `unicode-ccc`'s `get_canonical_combining_class`
// lowers to 710 blocks: a 245-case `Switch` whose default arm is a chain of 154
// range tests, each `lo <= x` / `x <= hi` with BOTH failing edges landing on the
// next test's first block. Enumerating it is 2^154 block evaluations. The
// `MAX_IR_DEPTH` and 8-arm `Switch` caps that used to sit here were guards
// against exactly that blow-up — they bounded the SYMPTOM. Memoizing the join
// removes the CAUSE, and the caps become a plain work budget.
//
// SOUNDNESS OF THE MEMO KEY. Reusing block `B`'s outcome across two different
// paths is sound exactly when the evaluation cannot observe the difference. The
// evaluation of `B` reads the incoming environment ONLY at values that are
// referenced somewhere in the sub-CFG reachable from `B` and NOT defined inside
// it — that is `live_in(B)`. So the memo is keyed on `(B, env restricted to
// live_in(B))`, compared by VALUE (`Formula` is `Eq`), never on the block id
// alone. Two paths that agree there cannot produce different outcomes; two that
// disagree get separate entries.
//
// `live_in` is computed by one backward pass in reverse topological order:
//
//     live_in(B) = (refs(B) ∪ ⋃ live_in(succ B)) \ defs(B)
//
// FAIL-CLOSED, THREE WAYS, so a gap in this analysis can only cost SPEED:
//   * a CYCLIC CFG has no topological order -> no memo at all (and the
//     evaluator's own per-path `visited` check still rejects the backedge);
//   * an instruction whose operands this module does not enumerate exactly
//     (`modeled_operands` returns `None`) -> no memo for any block that can
//     reach it;
//   * a block whose terminator's successors are not enumerable -> no memo.
// In every one of those cases the evaluator behaves EXACTLY as it did before
// this analysis existed. A memo that never fires cannot change a verdict; a
// memo that fires only on a key-equal environment cannot change one either.

/// The `ValueId` operands an instruction READS, or `None` when this module does
/// not enumerate that instruction exactly.
///
/// `None` DISABLES memoization rather than guessing. Under-reporting an operand
/// here would let two genuinely different environments share a memo entry, so
/// the arms are deliberately exhaustive-by-construction: every variant this
/// module's evaluator can actually evaluate is listed, and everything else —
/// including future variants — falls into the `None` arm.
fn modeled_operands(inst: &Inst) -> Option<Vec<ValueId>> {
    Some(match inst {
        Inst::Const { .. } | Inst::Undef { .. } | Inst::Unreachable => Vec::new(),
        Inst::BinOp { lhs, rhs, .. } | Inst::ICmp { lhs, rhs, .. } => vec![*lhs, *rhs],
        Inst::Overflow { lhs, rhs, .. } => vec![*lhs, *rhs],
        Inst::UnOp { operand, .. } => vec![*operand],
        Inst::Cast { operand, .. } => vec![*operand],
        Inst::Copy { operand, .. } => vec![*operand],
        Inst::Assert { cond } | Inst::Assume { cond } => vec![*cond],
        Inst::Select { cond, then_val, else_val, .. } => vec![*cond, *then_val, *else_val],
        Inst::Return { values } => values.clone(),
        Inst::Br { args, .. } => args.clone(),
        Inst::CondBr { cond, then_args, else_args, .. } => {
            let mut v = vec![*cond];
            v.extend(then_args.iter().copied());
            v.extend(else_args.iter().copied());
            v
        }
        Inst::Switch { value, default_args, cases, .. } => {
            let mut v = vec![*value];
            v.extend(default_args.iter().copied());
            for case in cases {
                v.extend(case.args.iter().copied());
            }
            v
        }
        // Every other instruction — memory, calls, aggregates, dialect ops —
        // is outside the evaluated fragment. Returning `None` costs the memo,
        // never correctness.
        _ => return None,
    })
}

/// The blocks a terminator can transfer to, or `None` if it is not one of the
/// modeled control-flow shapes.
fn modeled_successors(inst: &Inst) -> Option<Vec<BlockId>> {
    Some(match inst {
        Inst::Return { .. } | Inst::Unreachable => Vec::new(),
        Inst::Br { target, .. } => vec![*target],
        Inst::CondBr { then_target, else_target, .. } => vec![*then_target, *else_target],
        Inst::Switch { default, cases, .. } => {
            let mut v = vec![*default];
            v.extend(cases.iter().map(|c| c.target));
            v
        }
        _ => return None,
    })
}

/// `live_in` for every block, or `None` when the analysis cannot be completed
/// exactly (cyclic CFG, or an unenumerable instruction/terminator anywhere).
///
/// `None` means "do not memoize", which is always safe.
fn live_in_sets(blocks: &HashMap<u32, &trust_ir::Block>) -> Option<HashMap<u32, Vec<ValueId>>> {
    // refs / defs / succs per block, bailing on anything not enumerable.
    let mut refs: HashMap<u32, HashSet<ValueId>> = HashMap::new();
    let mut defs: HashMap<u32, HashSet<ValueId>> = HashMap::new();
    let mut succs: HashMap<u32, Vec<u32>> = HashMap::new();
    for (id, blk) in blocks {
        let mut r = HashSet::new();
        let mut d: HashSet<ValueId> = blk.params.iter().map(|(v, _)| *v).collect();
        let (terminator, body) = blk.body.split_last()?;
        for node in body {
            r.extend(modeled_operands(&node.inst)?);
            d.extend(node.results.iter().copied());
        }
        r.extend(modeled_operands(&terminator.inst)?);
        d.extend(terminator.results.iter().copied());
        let s: Vec<u32> =
            modeled_successors(&terminator.inst)?.into_iter().map(|b| b.index()).collect();
        // A successor the function lacks is a malformed CFG; the evaluator
        // reports it precisely, so bail out of the analysis rather than
        // silently treating it as a leaf.
        if s.iter().any(|t| !blocks.contains_key(t)) {
            return None;
        }
        refs.insert(*id, r);
        defs.insert(*id, d);
        succs.insert(*id, s);
    }

    // Reverse topological order via iterative DFS (no native recursion: these
    // CFGs are hundreds of blocks deep). `None` on any cycle.
    let mut order: Vec<u32> = Vec::with_capacity(blocks.len());
    let mut state: HashMap<u32, u8> = HashMap::new(); // 0/absent = new, 1 = on stack, 2 = done
    for &root in blocks.keys() {
        if state.get(&root).copied().unwrap_or(0) != 0 {
            continue;
        }
        let mut stack: Vec<(u32, usize)> = vec![(root, 0)];
        state.insert(root, 1);
        while let Some((node, idx)) = stack.pop() {
            let children = succs.get(&node)?;
            if idx < children.len() {
                stack.push((node, idx + 1));
                let child = children[idx];
                match state.get(&child).copied().unwrap_or(0) {
                    0 => {
                        state.insert(child, 1);
                        stack.push((child, 0));
                    }
                    // Back edge: cyclic. The evaluator rejects it anyway.
                    1 => return None,
                    _ => {}
                }
            } else {
                state.insert(node, 2);
                order.push(node);
            }
        }
    }

    // `order` is already reverse-topological (a node is pushed after all its
    // successors), so one forward pass over it suffices.
    let mut live: HashMap<u32, Vec<ValueId>> = HashMap::new();
    let mut live_set: HashMap<u32, HashSet<ValueId>> = HashMap::new();
    for id in &order {
        let mut acc = refs.get(id)?.clone();
        for s in succs.get(id)? {
            acc.extend(live_set.get(s)?.iter().copied());
        }
        for d in defs.get(id)? {
            acc.remove(d);
        }
        // Deterministic order so the memo key comparison is stable.
        let mut v: Vec<ValueId> = acc.iter().copied().collect();
        v.sort_by_key(|id| id.index());
        live.insert(*id, v);
        live_set.insert(*id, acc);
    }
    Some(live)
}

/// One memoized block evaluation: the environment slice it is valid for, and
/// the outcome it produced.
struct MemoEntry {
    /// `(value, formula, width)` for each `live_in` value, in `live_in` order.
    key: Vec<(ValueId, Formula, u32)>,
    value: Formula,
    reach: Formula,
}

/// Per-function evaluation state: the work budget and the block memo.
struct SpecEval {
    /// `live_in` per block, or `None` when memoization is disabled entirely.
    live_in: Option<HashMap<u32, Vec<ValueId>>>,
    memo: HashMap<u32, Vec<MemoEntry>>,
    /// Block evaluations performed so far, against [`MAX_IR_BLOCK_EVALS`].
    evals: u32,
    /// Side conditions, accumulated across the whole function.
    side: Vec<Formula>,
}

impl SpecEval {
    fn new(blocks: &HashMap<u32, &trust_ir::Block>) -> Self {
        SpecEval { live_in: live_in_sets(blocks), memo: HashMap::new(), evals: 0, side: Vec::new() }
    }

    /// The memo key for `id` under `env`, or `None` when `id` is not memoizable
    /// (analysis disabled, or a live value missing from `env` — the latter is a
    /// malformed-SSA case the evaluator itself reports precisely).
    fn key_for(
        &self,
        id: u32,
        env: &HashMap<ValueId, IrValue>,
    ) -> Option<Vec<(ValueId, Formula, u32)>> {
        let live = self.live_in.as_ref()?.get(&id)?;
        let mut key = Vec::with_capacity(live.len());
        for v in live {
            let iv = env.get(v)?;
            key.push((*v, iv.f.clone(), iv.width));
        }
        Some(key)
    }
}

/// Total block evaluations one function's spec derivation may perform.
///
/// This REPLACES the old `MAX_IR_DEPTH = 24` nesting cap and the 8-arm `Switch`
/// cap. Both were standing in for this: a bound on how much work the gate will
/// do before declaring the function undecided. Bounding the work directly is
/// both stricter (a wide-but-shallow function can no longer smuggle in
/// unbounded work) and far more permissive for the shapes real code has —
/// a 245-arm `Switch` is 245 evaluations, not 2^245 paths.
///
/// Exceeding it is `Unknown`, never `Proven`: an undecided function is refused.
const MAX_IR_BLOCK_EVALS: u32 = 250_000;

/// Native recursion guard. `eval_ir_block` recurses once per CFG edge on the
/// current path, so this bounds STACK depth, not work — the work bound is
/// [`MAX_IR_BLOCK_EVALS`]. It is high enough for the long reconverging cascades
/// real `match` statements produce (unicode-ccc's is ~310 deep) and low enough
/// that the frames cannot exhaust the re-check thread's stack.
const MAX_IR_DEPTH: u32 = 4096;

fn inst_label(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "BinOp",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::Alloca { .. } => "Alloca",
        Inst::GEP { .. } => "GEP",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::Return { .. } => "Return",
        Inst::ExtractField { .. } => "ExtractField",
        Inst::InsertField { .. } => "InsertField",
        Inst::Const { .. } => "Const",
        Inst::GlobalAddr { .. } => "GlobalAddr",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Unreachable => "Unreachable",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        _ => "<other>",
    }
}

// ===========================================================================
// PART 2 — THE PER-FUNCTION GATE
// ===========================================================================

/// Verify ONE F1 function: lower it through the SHIPPING converter, emit the
/// candidate object ONCE, derive the spec from the PRODUCER's trust-ir, and
/// discharge.
///
/// Returns the verdict plus the exact object bytes the verdict was computed
/// over (`None` only when lowering/emission itself failed, so there is nothing
/// to ship). This is the same shipped-==-verified discipline the MIR gate uses:
/// the caller ships THESE bytes, never a second emission.
pub fn verify_trust_ir_output_preserved(
    source: &TrustIrGateSource,
    backend: &TrustCgCodegenBackend,
) -> (OutputVerdict, Option<Vec<u8>>) {
    // (0) EMIT with the exact production backend, from the exact converter the
    // shipping path uses.
    let lir = match crate::lower_module_to_lir(&source.module, source.func_id) {
        Ok(lir) => lir,
        Err(e) => {
            return (
                OutputVerdict::Unknown { reason: format!("lower_module_to_lir failed: {e}") },
                None,
            );
        }
    };
    if lir.name != source.symbol {
        return (
            OutputVerdict::Unknown {
                reason: format!(
                    "lowered LIR carries the name `{}` but the gate was asked about `{}`; \
                     refusing to verify one function and ship another",
                    lir.name, source.symbol
                ),
            },
            None,
        );
    }
    let obj = match backend.emit_object(&[lir]) {
        Ok(obj) => obj,
        Err(e) => {
            return (OutputVerdict::Unknown { reason: format!("emit_object failed: {e:?}") }, None);
        }
    };

    let verdict = verify_trust_ir_bytes(source, &obj, backend.target_arch());
    (verdict, Some(obj))
}

/// Discharge a function's trust-ir specification against a GIVEN object's bytes.
///
/// This is the half of [`verify_trust_ir_output_preserved`] that touches no
/// emitter: hand it any object and it re-derives the machine side from THOSE
/// bytes. It is what makes the gate independently auditable — a corrupted or
/// substituted artifact can be checked against the same specification, and must
/// come back `Refuted`.
pub fn verify_trust_ir_bytes(
    source: &TrustIrGateSource,
    obj: &[u8],
    arch: TrustCgTargetArch,
) -> OutputVerdict {
    let obligation = match trust_ir_gate_obligation(source, obj, arch) {
        Ok(obligation) => obligation,
        Err(reason) => return OutputVerdict::Unknown { reason },
    };
    discharge_trust_ir_obligation(&source.symbol, &obligation)
}

/// The FOUR formulas the gate discharges, exposed so a verdict can be explained
/// rather than merely reported.
///
/// A gate whose obligation cannot be inspected is a gate nobody can audit; this
/// is the same data `verify_trust_ir_bytes` acts on, with nothing summarized.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct GateObligation {
    /// Return value the producer's trust-ir computes, over `X{i}`/`W{i}`.
    pub spec_value: Formula,
    /// Conjunction of the IR's own `Inst::Assert` guards along each path.
    pub spec_reach: Formula,
    /// Return value the EMITTED BYTES compute.
    pub machine_value: Formula,
    /// Predicate: do the bytes reach a `RET` at all (false on a `brk` tail)?
    pub machine_reach: Formula,
    /// Bit width both value formulas are read at.
    pub out_width: u32,
    /// Modeling preconditions the SPEC side carries (see [`SpecSemantics`]).
    /// Discharged from `spec_reach` after the vacuity firewall; a failure is
    /// `Unknown`, never `Refuted`.
    pub spec_side_conditions: Vec<Formula>,
}

/// TEMPORARY MEASUREMENT HOOK (not for commit): run ONLY the machine half of
/// the obligation over `obj`, so the machine-side budget can be measured
/// independently of whether the spec side is in-fragment.
#[doc(hidden)]
pub fn probe_machine_only(obj: &[u8], out_width: u32) -> Result<(Formula, Formula), String> {
    let (code, base) = extract_text_from_object(obj)?;
    let m = symbolic_machine_outcome_traps(&code, base, out_width, false)?;
    Ok((m.value, m.reach))
}

/// Build the gate's obligation for `source` against `obj`'s bytes.
pub fn trust_ir_gate_obligation(
    source: &TrustIrGateSource,
    obj: &[u8],
    arch: TrustCgTargetArch,
) -> Result<GateObligation, String> {
    // (1) THE SPEC — from the producer's trust-ir, never from the lowering.
    let spec = trust_ir_function_semantics(&source.module, source.func_id)?;
    let SpecSemantics { value: spec_value, reach: spec_reach, out_width, side_conditions } = spec;

    // (2) THE MACHINE SIDE — derived ONLY from the emitted bytes.
    if arch != TrustCgTargetArch::AArch64 {
        return Err(format!(
            "byte-level output preservation is wired for AArch64 machine semantics only; \
             emitted {arch:?} code is undecided (fail-closed)"
        ));
    }
    let (code, base) = extract_text_from_object(obj)?;
    if code.is_empty() {
        return Err("emitted text section is empty".into());
    }
    let machine = symbolic_machine_outcome_traps(&code, base, out_width, false)?;
    Ok(GateObligation {
        spec_value,
        spec_reach,
        machine_value: machine.value,
        machine_reach: machine.reach,
        out_width,
        spec_side_conditions: side_conditions,
    })
}

/// Discharge an already-built [`GateObligation`] into a verdict.
fn discharge_trust_ir_obligation(symbol: &str, obligation: &GateObligation) -> OutputVerdict {
    let GateObligation {
        spec_value,
        spec_reach,
        machine_value,
        machine_reach,
        spec_side_conditions,
        ..
    } = obligation;

    // (3) VACUITY FIREWALL. If `spec_reach` is unsatisfiable, every obligation
    // below is vacuously true. That is NOT a proof; it is a hole. Reject.
    if !matches!(spec_reach, Formula::Bool(true)) {
        match discharge_valid(&Formula::Not(b(spec_reach.clone()))) {
            Discharge::Proven => {
                return OutputVerdict::Unknown {
                    reason: format!(
                        "VACUOUS obligation for `{symbol}`: the IR's own assert guards are \
                         unsatisfiable, so no input reaches a return and the equality would \
                         hold for any bytes; refusing to report that as proven"
                    ),
                };
            }
            Discharge::CounterExample => {}
            Discharge::Unknown(reason) => {
                return OutputVerdict::Unknown {
                    reason: format!("vacuity check did not conclude: {reason}"),
                };
            }
        }
    }

    // (3b) SPEC-SIDE MODELING PRECONDITIONS. Each is a fact the spec formula
    // needed in order to be a faithful rendering of the IR's own semantics —
    // presently only the in-range requirement a narrow shift carries, so that
    // `mask_shift`'s mod-width convention is never the thing being proved and
    // the obligation never speaks about inputs trust-ir's interpreter calls UB.
    //
    // These are PROVED from `spec_reach`, not assumed. Order matters: this runs
    // AFTER the vacuity firewall above, because an unsatisfiable `spec_reach`
    // makes every implication out of it trivially valid, and a side condition
    // "discharged" that way would establish nothing.
    //
    // A failure here is `Unknown`, NEVER `Refuted`: it means the gate could not
    // justify its own model of the IR, which is not evidence against the bytes.
    for (index, condition) in spec_side_conditions.iter().enumerate() {
        let implication = Formula::Or(vec![Formula::Not(b(spec_reach.clone())), condition.clone()]);
        match discharge_valid(&implication) {
            Discharge::Proven => {}
            Discharge::CounterExample => {
                return OutputVerdict::Unknown {
                    reason: format!(
                        "spec-side modeling precondition #{index} for `{symbol}` is NOT implied \
                         by the IR's own assert guards (a narrow shift whose amount the IR does \
                         not prove in range): trust-ir makes an over-wide shift UB \
                         (`interpret.rs` `shift_amount`), so the gate has no IR semantics to \
                         render there and refuses to invent one (fail-closed)"
                    ),
                };
            }
            Discharge::Unknown(reason) => {
                return OutputVerdict::Unknown {
                    reason: format!(
                        "spec-side modeling precondition #{index} for `{symbol}` did not \
                         conclude: {reason}"
                    ),
                };
            }
        }
    }

    // (4) OBLIGATION A — the machine must RETURN wherever the IR returns. Without
    // this an emission that spuriously traps would pass, because its `reach` is
    // false exactly where the value obligation would have bitten.
    if !matches!(machine_reach, Formula::Bool(true)) {
        // `spec_reach -> machine_reach`, spelled as `NOT spec_reach OR
        // machine_reach` because that is the connective set `formula_to_term`
        // lowers into ay. Same claim, no new translator surface.
        let implication =
            Formula::Or(vec![Formula::Not(b(spec_reach.clone())), machine_reach.clone()]);
        match discharge_valid(&implication) {
            Discharge::Proven => {}
            Discharge::CounterExample => {
                return OutputVerdict::Refuted {
                    detail: format!(
                        "emitted bytes for fn `{symbol}` TRAP on an input the IR returns \
                         normally on (ay found a counterexample — the machine does not reach \
                         a RET where the IR does)"
                    ),
                };
            }
            Discharge::Unknown(reason) => {
                return OutputVerdict::Unknown {
                    reason: format!("reachability obligation did not conclude: {reason}"),
                };
            }
        }
    }

    // (5) OBLIGATION B — the values agree on every input the IR returns on.
    let pre = if matches!(spec_reach, Formula::Bool(true)) { None } else { Some(spec_reach) };
    match discharge_equal_pre(machine_value, spec_value, pre) {
        Discharge::Proven => OutputVerdict::Proven {
            evidence: try_kernel_recheckable_proof(machine_value, spec_value, pre)
                .unwrap_or(ProvenEvidence::AyValidated),
        },
        Discharge::CounterExample => OutputVerdict::Refuted {
            detail: format!(
                "emitted bytes do not equal the trust-ir semantics for fn `{symbol}` \
                 (ay found a counterexample input — miscompile)"
            ),
        },
        Discharge::Unknown(reason) => OutputVerdict::Unknown { reason },
    }
}

// ===========================================================================
// PART 3 — THE WHOLE-MODULE BUILD GATE
// ===========================================================================

/// THE F1 BUILD GATE: verify every function of a trust-ir codegen unit, then
/// emit ONE object and prove it carries each verified instruction stream
/// verbatim.
///
/// This mirrors `verify_output::emit_module_object_verified_reported_with_backend`
/// phase for phase — per-function proof, determinism re-emission, merge, and the
/// byte-preservation obligation read back from the SHIPPED symbol table — with
/// the spec side coming from trust-ir instead of from a `VerifiableFunction`.
///
/// FAIL-CLOSED: `Refuted` is refused under every policy; `Unknown` is refused
/// under [`EmitPolicy::StrictProvenOnly`]. There is NO arm that returns bytes
/// for a function the gate did not examine — an empty work list is
/// [`VerifyError::EmptyModule`], not a silent pass.
pub fn emit_trust_ir_module_object_verified(
    sources: &[TrustIrGateSource],
    linkage: &[FunctionLinkage],
    policy: EmitPolicy,
    backend: &TrustCgCodegenBackend,
) -> Result<(VerifiedModuleObject, CertificationReport), VerifyError> {
    if sources.is_empty() {
        return Err(VerifyError::EmptyModule);
    }
    let mut seen = HashSet::with_capacity(sources.len());
    for source in sources {
        if !seen.insert(source.symbol.as_str()) {
            return Err(VerifyError::DuplicateFunctionName { name: source.symbol.clone() });
        }
    }
    if !linkage.is_empty() && linkage.len() != sources.len() {
        return Err(VerifyError::ModuleEmitFailed {
            reason: format!(
                "{} linkage entries for {} functions; refusing to bind symbols against a \
                 mis-indexed vector",
                linkage.len(),
                sources.len()
            ),
        });
    }

    // PHASE 1 — GATE + CAPTURE.
    let mut verified: Vec<(String, Vec<u8>)> = Vec::with_capacity(sources.len());
    let mut report = CertificationReport::default();
    for source in sources {
        let (verdict, bytes) = verify_trust_ir_output_preserved(source, backend);
        match verdict {
            OutputVerdict::Proven { evidence } => match evidence {
                // [PROVED] — the clean kernel is the authority. The pair form is
                // the SAME grade with TWO kernel-accepted certificates (a 128-bit
                // AAPCS64 register pair, which cannot carry one); it is counted
                // as one PROVED FUNCTION, not as two.
                ProvenEvidence::KernelRecheckable(_)
                | ProvenEvidence::KernelRecheckablePair { .. }
                | ProvenEvidence::KernelInstantiated { .. } => report.proved += 1,
                // [CITED] — a wide `Mul` discharged by CITING the
                // kernel-checked structured theorem. Counted with the
                // [VALIDATED] surface and NOT with `proved`, deliberately: the
                // kernel never re-checked a term for THIS instance, and the
                // `AyBlastAgrees` residual is machine-checked rather than
                // proved. Under StrictProvenOnly it is therefore REFUSED on the
                // same footing as [VALIDATED] — a citation must never ship where
                // only kernel-[PROVED] may.
                ProvenEvidence::StructuralCitation { .. } | ProvenEvidence::AyValidated => {
                    if policy == EmitPolicy::StrictProvenOnly {
                        return Err(VerifyError::Unknown {
                            function: source.symbol.clone(),
                            reason: "function is [VALIDATED] (ay-only authority) but \
                                     StrictProvenOnly ships ONLY kernel-re-checkable \
                                     [PROVED] functions (certified-fragment mode)"
                                .to_string(),
                        });
                    }
                    report.validated += 1;
                }
            },
            OutputVerdict::Refuted { detail } => {
                return Err(VerifyError::Refuted { function: source.symbol.clone(), detail });
            }
            OutputVerdict::Unknown { reason } => {
                if policy == EmitPolicy::StrictProvenOnly {
                    return Err(VerifyError::Unknown { function: source.symbol.clone(), reason });
                }
                report.unknown += 1;
            }
        }
        match bytes {
            Some(bytes) => verified.push((source.symbol.clone(), bytes)),
            None => {
                return Err(VerifyError::EmitFailed {
                    function: source.symbol.clone(),
                    reason: "verification emission produced no shippable object bytes".to_string(),
                });
            }
        }
    }

    // PHASE 2 — DETERMINISM. Re-lower and re-emit each function and require the
    // bytes to be identical to the ones the gate verified. A backend that emits
    // different bytes when it is not being watched is caught here.
    for (index, (name, bytes)) in verified.iter().enumerate() {
        let source = &sources[index];
        let lir = crate::lower_module_to_lir(&source.module, source.func_id).map_err(|e| {
            VerifyError::EmitFailed {
                function: name.clone(),
                reason: format!("re-lower for the determinism check failed: {e}"),
            }
        })?;
        let reemit = backend.emit_object(&[lir]).map_err(|e| VerifyError::EmitFailed {
            function: name.clone(),
            reason: format!("re-emit emit_object failed: {e:?}"),
        })?;
        if &reemit != bytes {
            return Err(VerifyError::EmitFailed {
                function: name.clone(),
                reason: format!(
                    "RE-EMISSION DIVERGED from the verified bytes for fn `{name}` (verified \
                     {} bytes, re-emitted {} bytes) — the shipped artifact would not be the \
                     artifact the gate verified; refusing (fail-closed)",
                    bytes.len(),
                    reemit.len()
                ),
            });
        }
    }

    // PHASE 3a — MERGE into the ONE object this codegen unit ships.
    let mut lir_functions = Vec::with_capacity(sources.len());
    for source in sources {
        let lir = crate::lower_module_to_lir(&source.module, source.func_id).map_err(|e| {
            VerifyError::EmitFailed {
                function: source.symbol.clone(),
                reason: format!("lowering failed during whole-module emission: {e}"),
            }
        })?;
        lir_functions.push(lir);
    }
    let function_count = lir_functions.len();
    let module = crate::codegen_backend::CompiledModule {
        name: "trust_cg.verified_trust_ir_module".to_string(),
        lir_functions,
        object_path: None,
        function_count,
        source_functions: None,
        linkage: linkage.to_vec(),
    };
    let emitted = backend.emit_module_object(&module).map_err(|e| {
        VerifyError::ModuleEmitFailed { reason: format!("emit_module_object failed: {e:?}") }
    })?;

    // PHASE 3b — DISCHARGE THE BYTE-PRESERVATION OBLIGATION, using the SAME
    // read-back-from-the-shipped-object check the MIR gate uses.
    let preserved: Vec<PreservedFunction> =
        assert_merged_object_preserves_verified_text(&emitted, &verified)?;

    Ok((VerifiedModuleObject { bytes: emitted.bytes, preserved }, report))
}

// ===========================================================================
// PART 4 — THE 128-BIT REGISTER-PAIR FRAGMENT, PINNED
//
// These tests exist because a 128-bit return is the one shape where a gate can
// look like it is checking a value while checking only HALF of it: `X0` alone
// is a perfectly well-typed 64-bit answer, and every function that returns a
// small `i128` constant has `X1 == 0`, so an X0-only obligation would report
// `Proven` for all of them and never notice. Each test below therefore pins a
// verdict AND the mutation that must move it.
// ===========================================================================

#[cfg(test)]
mod tests_i128_pair {
    use trust_ir::inst::{BinOp as TirBinOp, Inst};
    use trust_ir::node::InstrNode;
    use trust_ir::ty::FuncTy;
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
    use trust_ir::{Block, Constant, Function as IrFunction, Module, Ty};

    use super::*;
    use crate::codegen_backend::BridgeOptimizationLevel;

    /// `movz x1, #7` — writes 7 into the HIGH half register of a 128-bit result.
    const MOVZ_X1_7: u32 = 0xd280_00e1;

    enum Body {
        Add,
        Param(u32),
        Const(i128),
    }

    fn build(name: &str, params: &[Ty], ret: Ty, body: Body) -> Module {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: params.to_vec(),
            returns: vec![ret.clone()],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        for (i, ty) in params.iter().enumerate() {
            block.params.push((ValueId::new(u32::try_from(i).expect("param index")), ty.clone()));
        }
        let next = u32::try_from(params.len()).expect("param count");
        let mut nodes: Vec<InstrNode> = Vec::new();
        let ret_val = match body {
            Body::Add => {
                nodes.push(
                    InstrNode::new(Inst::BinOp {
                        op: TirBinOp::Add,
                        ty: ret.clone(),
                        lhs: ValueId::new(0),
                        rhs: ValueId::new(1),
                    })
                    .with_result(ValueId::new(next)),
                );
                ValueId::new(next)
            }
            Body::Param(i) => ValueId::new(i),
            Body::Const(v) => {
                nodes.push(
                    InstrNode::new(Inst::Const { ty: ret.clone(), value: Constant::Int(v) })
                        .with_result(ValueId::new(next)),
                );
                ValueId::new(next)
            }
        };
        nodes.push(InstrNode::new(Inst::Return { values: vec![ret_val] }));
        block.body = nodes;
        f.blocks.push(block);
        module.functions.push(f);
        module
    }

    fn backend() -> TrustCgCodegenBackend {
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O0)
    }

    fn gate(module: Module, name: &str) -> (OutputVerdict, Option<Vec<u8>>) {
        let source =
            TrustIrGateSource { symbol: name.to_string(), module, func_id: FuncId::new(0) };
        verify_trust_ir_output_preserved(&source, &backend())
    }

    /// THE STRICT BUILD GATE, end to end: emit a whole module under
    /// `EmitPolicy::StrictProvenOnly` — which is `EmitPolicy::default()`, the
    /// policy `-Ztrust-cg-output-gate` resolves to by default
    /// (`rustc_session::options` sets that flag's default to `"strict"`).
    ///
    /// This is the ship/refuse decision, not just a verdict: under this policy a
    /// [VALIDATED] function is an `Err` and NO bytes come out.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn i128_constant_return_ships_under_the_default_strict_gate() {
        let module = build("k", &[], Ty::I128, Body::Const(1234));
        let source = TrustIrGateSource { symbol: "k".to_string(), module, func_id: FuncId::new(0) };
        let (object, report) = emit_trust_ir_module_object_verified(
            std::slice::from_ref(&source),
            &[],
            EmitPolicy::default(),
            &backend(),
        )
        .expect(
            "a 128-bit constant return must SHIP under the default strict gate; before the \
             register-pair split it was [VALIDATED] and this returned Err",
        );
        assert_eq!(EmitPolicy::default(), EmitPolicy::StrictProvenOnly, "the default IS strict");
        assert_eq!(report.proved, 1, "the function must be counted [PROVED]: {report}");
        assert_eq!(report.validated, 0, "nothing may ship as ay-only: {report}");
        assert_eq!(report.unknown, 0, "nothing may ship uncertified: {report}");
        assert_eq!(report.uncertified(), 0, "the uncertified surface must be empty: {report}");
        assert!(!object.bytes.is_empty(), "strict gate must produce real object bytes");
    }

    /// Mach-O `__text` file offset + size (LE 64-bit), so a test can corrupt an
    /// exact instruction word of the object the gate just verified.
    fn text_span(obj: &[u8]) -> Option<(usize, usize)> {
        let rd32 = |o: usize| -> Option<u32> {
            obj.get(o..o + 4).and_then(|s| s.try_into().ok()).map(u32::from_le_bytes)
        };
        if rd32(0)? != 0xfeed_facf {
            return None;
        }
        let ncmds = rd32(16)? as usize;
        let mut off = 32usize;
        for _ in 0..ncmds {
            let cmd = rd32(off)?;
            let cmdsize = rd32(off + 4)? as usize;
            if cmd == 0x19 {
                let nsects = rd32(off + 64)? as usize;
                let mut s = off + 72;
                for _ in 0..nsects {
                    if obj.get(s..s + 16)?.starts_with(b"__text\0") {
                        let size = u64::from_le_bytes(obj.get(s + 40..s + 48)?.try_into().ok()?);
                        return Some((rd32(s + 48)? as usize, size as usize));
                    }
                    s += 80;
                }
            }
            off += cmdsize;
        }
        None
    }

    #[test]
    fn i128_constant_return_is_proven() {
        let (v, _) = gate(build("k", &[], Ty::I128, Body::Const(1234)), "k");
        assert!(matches!(v, OutputVerdict::Proven { .. }), "expected Proven, got {v:?}");
    }

    /// THE GRADE, through the REAL BYTES. `Proven` alone was never the question
    /// for this fragment — it has been Proven all along. The question is whether
    /// it is Proven with a CLEAN-KERNEL certificate, because
    /// `EmitPolicy::StrictProvenOnly` (the compiler's default gate) ships only
    /// the kernel grade. Before the 128-bit register-pair split this was
    /// `AyValidated` and strict REFUSED it; it must now carry TWO kernel-accepted
    /// certificates, one per register of the pair.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn i128_constant_return_is_kernel_proved_as_a_pair() {
        let (v, _) = gate(build("k", &[], Ty::I128, Body::Const(1234)), "k");
        assert!(
            v.is_kernel_proved(),
            "a 128-bit constant return must be kernel-[PROVED], not merely Proven; got {v:?}"
        );
        assert!(
            matches!(
                v,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelRecheckablePair { .. } }
            ),
            "expected the two-certificate register-pair grade; got {v:?}"
        );
        assert_eq!(
            v.kernel_proofs().len(),
            2,
            "a 128-bit return rests on TWO certificates (X1 high, X0 low)"
        );
    }

    /// The 128-bit IDENTITY, through the real bytes, at the kernel grade. This is
    /// the shape whose halves are SYMBOLIC (`X1`/`X0` register reads) rather than
    /// constant, so it exercises leaf sharing across the split.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn i128_identity_is_kernel_proved_as_a_pair() {
        let (v, _) = gate(build("i", &[Ty::I128], Ty::I128, Body::Param(0)), "i");
        assert!(
            matches!(
                v,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelRecheckablePair { .. } }
            ),
            "the 128-bit identity must be kernel-[PROVED] as a pair; got {v:?}"
        );
    }

    /// THE LOAD-BEARING TEST. Corrupting the HIGH half alone must flip the
    /// verdict. Without the `X0`/`X1` pair model this mutation is invisible and
    /// the function still reports `Proven` — an X0-only check calling itself a
    /// 128-bit proof.
    #[test]
    fn i128_return_obligation_constrains_the_high_half() {
        let module = build("k", &[], Ty::I128, Body::Const(1234));
        let source = TrustIrGateSource { symbol: "k".to_string(), module, func_id: FuncId::new(0) };
        let (v, obj) = verify_trust_ir_output_preserved(&source, &backend());
        assert!(matches!(v, OutputVerdict::Proven { .. }), "baseline must be Proven, got {v:?}");
        let obj = obj.expect("verified bytes");
        let (off, size) = text_span(&obj).expect("__text");
        let words = size / 4;
        assert!(words >= 2, "need at least one instruction plus the ret");
        // Overwrite the last instruction before the trailing `ret` so the high
        // half becomes 7 (the true high half of 1234 is 0).
        let mut corrupted = obj.clone();
        let at = off + (words - 2) * 4;
        corrupted[at..at + 4].copy_from_slice(&MOVZ_X1_7.to_le_bytes());
        let v = verify_trust_ir_bytes(&source, &corrupted, TrustCgTargetArch::AArch64);
        assert!(
            matches!(v, OutputVerdict::Refuted { .. }),
            "a wrong HIGH half must be Refuted, got {v:?}"
        );
    }

    /// THE BYTE-LEVEL MUTATION CHECK, aimed at the KERNEL PATH specifically.
    ///
    /// `i128_return_obligation_constrains_the_high_half` above corrupts the high
    /// half and shows the GATE refuses (`Refuted`). That is a strictly earlier
    /// refusal — ay finds the counterexample and the kernel grade is never even
    /// requested — so on its own it does not show that the high half reaches the
    /// KERNEL. This test does: it takes the obligation derived from the SAME
    /// corrupted bytes and hands it straight to `try_kernel_recheckable_proof`,
    /// bypassing the discharge. The kernel path must return no evidence.
    ///
    /// The control at the end is what makes the result attributable: the
    /// UNcorrupted object's obligation, through the identical call, DOES produce
    /// the two-certificate pair grade. Same bytes but for one instruction word,
    /// same entry point, opposite answers.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn corrupting_the_high_half_refuses_the_kernel_recheck_path() {
        use crate::verify_output::try_kernel_recheckable_proof;

        let module = build("k", &[], Ty::I128, Body::Const(1234));
        let source = TrustIrGateSource { symbol: "k".to_string(), module, func_id: FuncId::new(0) };
        let (_, obj) = verify_trust_ir_output_preserved(&source, &backend());
        let obj = obj.expect("verified bytes");
        let (off, size) = text_span(&obj).expect("__text");
        let words = size / 4;
        assert!(words >= 2, "need at least one instruction plus the ret");

        // CONTROL FIRST: the pristine object's obligation IS kernel-[PROVED].
        let clean = trust_ir_gate_obligation(&source, &obj, TrustCgTargetArch::AArch64)
            .expect("obligation from pristine bytes");
        assert!(
            matches!(
                try_kernel_recheckable_proof(&clean.machine_value, &clean.spec_value, None),
                Some(ProvenEvidence::KernelRecheckablePair { .. })
            ),
            "control: the pristine 128-bit obligation must reach the kernel grade"
        );

        // MUTATE THE HIGH HALF ONLY: `movz x1, #7` where the true high half is 0.
        // X0 (the low half) is untouched, so a low-half-only check sees nothing.
        let mut corrupted = obj.clone();
        let at = off + (words - 2) * 4;
        corrupted[at..at + 4].copy_from_slice(&MOVZ_X1_7.to_le_bytes());
        let dirty = trust_ir_gate_obligation(&source, &corrupted, TrustCgTargetArch::AArch64)
            .expect("obligation from corrupted bytes");
        assert_ne!(
            dirty.machine_value, clean.machine_value,
            "the mutation must actually change the machine-side formula"
        );
        assert_eq!(
            dirty.spec_value, clean.spec_value,
            "the spec side is unchanged — only the bytes moved"
        );
        assert!(
            try_kernel_recheckable_proof(&dirty.machine_value, &dirty.spec_value, None).is_none(),
            "a corrupted HIGH half must be REFUSED by the kernel-recheck path; if this \
             passes, the high-half obligation never reached the kernel and the [PROVED] \
             grade on every 128-bit return is a claim about 64 of its 128 bits"
        );
    }

    /// The 128-bit fragment is MOVE-ONLY: arithmetic must stay `Unknown`. It may
    /// NOT become `Proven` (that would ship an unmodeled carry chain) and it may
    /// NOT become `Refuted` (that would be a fabricated miscompile report).
    #[test]
    fn i128_arithmetic_is_unknown_not_proven_and_not_refuted() {
        let (v, _) = gate(build("a", &[Ty::I128, Ty::I128], Ty::I128, Body::Add), "a");
        match v {
            OutputVerdict::Unknown { reason } => {
                assert!(reason.contains("MOVE-ONLY"), "unexpected reason: {reason}");
            }
            other => panic!("128-bit arithmetic must be Unknown, got {other:?}"),
        }
    }

    /// A 128-bit argument landing on an ODD register slot is the one case where
    /// the written AAPCS64 rule (even-aligned pair) and the backend's
    /// next-two-consecutive allocation disagree. The gate refuses rather than
    /// picking one and reporting the disagreement as a miscompile.
    #[test]
    fn i128_argument_at_an_odd_slot_is_refused() {
        let (v, _) = gate(build("o", &[Ty::I64, Ty::I128], Ty::I128, Body::Param(1)), "o");
        match v {
            OutputVerdict::Unknown { reason } => {
                assert!(reason.contains("ODD register slot"), "unexpected reason: {reason}");
            }
            other => panic!("odd-slot 128-bit argument must be Unknown, got {other:?}"),
        }
    }

    /// The slot allocator, not the parameter index, decides the register: a
    /// 128-bit first argument consumes X0 AND X1, so the trailing scalar is in
    /// X2. Reading it from X1 would disagree with the emitted bytes and Refute.
    #[test]
    fn scalar_after_a_128_bit_pair_is_read_from_x2() {
        let (v, _) = gate(build("s", &[Ty::I128, Ty::I64], Ty::I64, Body::Param(1)), "s");
        assert!(matches!(v, OutputVerdict::Proven { .. }), "expected Proven, got {v:?}");
    }

    /// A second 128-bit argument occupies the X2/X3 pair.
    #[test]
    fn second_128_bit_argument_is_the_x2_x3_pair() {
        let (v, _) = gate(build("p", &[Ty::I128, Ty::I128], Ty::I128, Body::Param(1)), "p");
        assert!(matches!(v, OutputVerdict::Proven { .. }), "expected Proven, got {v:?}");
    }

    /// The 128-bit identity: the spec is `concat(X1, X0)` from the argument pair
    /// and the machine leaves both halves in place.
    #[test]
    fn i128_identity_is_proven() {
        let (v, _) = gate(build("i", &[Ty::I128], Ty::I128, Body::Param(0)), "i");
        assert!(matches!(v, OutputVerdict::Proven { .. }), "expected Proven, got {v:?}");
    }

    /// Regression: the <=64-bit path is byte-identical to what it was before the
    /// pair model existed.
    #[test]
    fn narrower_returns_are_unaffected() {
        for (name, ty) in [("i32", Ty::I32), ("i64", Ty::I64)] {
            let (v, _) = gate(build(name, &[ty.clone(), ty.clone()], ty, Body::Add), name);
            assert!(matches!(v, OutputVerdict::Proven { .. }), "{name}: got {v:?}");
        }
    }
}

// ===========================================================================
// PART 5 — THE NARROW / BOOL FRAGMENT, PINNED
//
// A narrow return is the one shape where a gate can look like it is checking a
// value while checking a DIFFERENT NUMBER OF BITS than the value has. Reading
// too few bits would make a miscompile invisible; reading too many would
// fabricate a Refuted against code the ABI permits. The obligation therefore has
// to sit at the DECLARED width, and "declared" has to mean per-type, not a
// constant that happens to be right for one of them.
//
// Every test below pins a verdict AND the mutation that must (or must not) move
// it. The load-bearing pair is `narrow_obligation_sits_at_the_declared_width`:
// the SAME mutation must be invisible at 8 bits and fatal at 16, which no
// hard-coded width can satisfy.
// ===========================================================================

#[cfg(test)]
mod tests_narrow_and_bool {
    use trust_ir::inst::{BinOp as TirBinOp, CastOp, Inst};
    use trust_ir::node::InstrNode;
    use trust_ir::ty::FuncTy;
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
    use trust_ir::{Block, Constant, Function as IrFunction, Module, Ty};

    use super::*;
    use crate::codegen_backend::BridgeOptimizationLevel;

    /// `add w0, w0, #1` — perturbs bit 0, which lies INSIDE the declared width at
    /// every width this gate models. Verified against the system assembler
    /// (`as -arch arm64`): `add w0, w0, #0x1` = `00 04 00 11`.
    const ADD_W0_1: u32 = 0x1100_0400;
    /// `add w0, w0, #0x100` — perturbs only bits 8 and above. Verified the same
    /// way: `add w0, w0, #0x100` = `00 00 04 11`.
    const ADD_W0_256: u32 = 0x1104_0000;

    fn backend() -> TrustCgCodegenBackend {
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O0)
    }

    /// Build a one-block function: `params` in, `nodes` computed, `ret_val` out.
    fn build(params: &[Ty], ret: Ty, nodes: Vec<InstrNode>, ret_val: ValueId) -> TrustIrGateSource {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: params.to_vec(),
            returns: vec![ret],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        for (i, ty) in params.iter().enumerate() {
            block.params.push((ValueId::new(u32::try_from(i).expect("param index")), ty.clone()));
        }
        let mut body = nodes;
        body.push(InstrNode::new(Inst::Return { values: vec![ret_val] }));
        block.body = body;
        f.blocks.push(block);
        module.functions.push(f);
        TrustIrGateSource { symbol: "k".to_string(), module, func_id: FuncId::new(0) }
    }

    /// The identity `fn(x: T) -> T { x }` — the cleanest mutation bed there is,
    /// because the spec is exactly the argument register read at the declared
    /// width and nothing else.
    fn identity(ty: Ty) -> TrustIrGateSource {
        let params = vec![ty.clone()];
        build(&params, ty, Vec::new(), ValueId::new(0))
    }

    fn verdict(source: &TrustIrGateSource) -> (OutputVerdict, Option<Vec<u8>>) {
        verify_trust_ir_output_preserved(source, &backend())
    }

    /// Mach-O `__text` file offset + size, so a test can rewrite an exact word of
    /// the object the gate just verified.
    fn text_span(obj: &[u8]) -> Option<(usize, usize)> {
        let rd32 = |o: usize| -> Option<u32> {
            obj.get(o..o + 4).and_then(|s| s.try_into().ok()).map(u32::from_le_bytes)
        };
        if rd32(0)? != 0xfeed_facf {
            return None;
        }
        let ncmds = rd32(16)? as usize;
        let mut off = 32usize;
        for _ in 0..ncmds {
            let cmd = rd32(off)?;
            let cmdsize = rd32(off + 4)? as usize;
            if cmd == 0x19 {
                let nsects = rd32(off + 64)? as usize;
                let mut s = off + 72;
                for _ in 0..nsects {
                    if obj.get(s..s + 16)?.starts_with(b"__text\0") {
                        let size = u64::from_le_bytes(obj.get(s + 40..s + 48)?.try_into().ok()?);
                        return Some((rd32(s + 48)? as usize, size as usize));
                    }
                    s += 80;
                }
            }
            off += cmdsize;
        }
        None
    }

    /// Re-discharge the UNCHANGED spec against bytes whose last instruction
    /// before the trailing `ret` has been replaced by `insn`.
    fn verdict_after_mutation(source: &TrustIrGateSource, obj: &[u8], insn: u32) -> OutputVerdict {
        let (off, size) = text_span(obj).expect("__text");
        let words = size / 4;
        assert!(words >= 2, "need at least one instruction plus the ret");
        let mut corrupted = obj.to_vec();
        let at = off + (words - 2) * 4;
        corrupted[at..at + 4].copy_from_slice(&insn.to_le_bytes());
        verify_trust_ir_bytes(source, &corrupted, TrustCgTargetArch::AArch64)
    }

    /// THE LOAD-BEARING TEST. One mutation, three widths, three required answers.
    ///
    /// `add w0, w0, #0x100` touches bits 8 and above and nothing below. At a
    /// DECLARED width of 8 those bits are not part of the value — the Rust ABI
    /// gives a narrow slot `arg_ext: None`, so the caller may not read them — and
    /// the verdict must stay `Proven`. At 16 and at 32 bit 8 IS part of the value
    /// and the verdict must flip to `Refuted`.
    ///
    /// No hard-coded obligation width can pass this test: a fixed 8 fails the u16
    /// and u32 lines, a fixed 32 fails the u8 line. The width has to come from the
    /// type.
    #[test]
    fn narrow_obligation_sits_at_the_declared_width() {
        for (name, ty, high_bits_are_part_of_the_value) in [
            ("u8", Ty::U8, false),
            ("i8", Ty::I8, false),
            ("u16", Ty::U16, true),
            ("i16", Ty::I16, true),
            ("u32", Ty::U32, true),
        ] {
            let source = identity(ty);
            let (base, obj) = verdict(&source);
            assert!(matches!(base, OutputVerdict::Proven { .. }), "{name} baseline: {base:?}");
            let obj = obj.expect("verified bytes");

            let hi = verdict_after_mutation(&source, &obj, ADD_W0_256);
            if high_bits_are_part_of_the_value {
                assert!(
                    matches!(hi, OutputVerdict::Refuted { .. }),
                    "{name}: bit 8 is inside the declared width, so perturbing it must \
                     Refute; got {hi:?}"
                );
            } else {
                assert!(
                    matches!(hi, OutputVerdict::Proven { .. }),
                    "{name}: bits above the declared width are not part of the value \
                     (arg_ext: None), so perturbing them must NOT Refute; got {hi:?}"
                );
            }

            // Bit 0 is inside the declared width at every width. Always fatal.
            let lo = verdict_after_mutation(&source, &obj, ADD_W0_1);
            assert!(
                matches!(lo, OutputVerdict::Refuted { .. }),
                "{name}: perturbing bit 0 must Refute at every width; got {lo:?}"
            );
        }
    }

    /// The width the obligation is discharged at, read straight off the spec
    /// derivation. This pins the DECISION; the test above pins that the decision
    /// is acted on.
    #[test]
    fn obligation_width_is_the_declared_width() {
        for (ty, want) in [
            (Ty::U8, 8),
            (Ty::I8, 8),
            (Ty::U16, 16),
            (Ty::I16, 16),
            (Ty::U32, 32),
            (Ty::I64, 64),
            // A bool RESULT is `arg_ext: Zext` — the callee owes a zero-extended
            // 0/1 across the whole slot, so the gate holds it to all 32 bits.
            (Ty::Bool, 32),
            (Ty::I128, 128),
        ] {
            let source = build(
                &[],
                ty.clone(),
                vec![
                    InstrNode::new(Inst::Const { ty: ty.clone(), value: Constant::Int(1) })
                        .with_result(ValueId::new(0)),
                ],
                ValueId::new(0),
            );
            let spec =
                trust_ir_function_semantics(&source.module, source.func_id).expect("semantics");
            assert_eq!(spec.out_width, want, "{ty:?} must be discharged at {want} bits");
        }
    }

    /// Narrow constants and narrow moves.
    #[test]
    fn narrow_constant_returns_are_proven() {
        for (name, ty, value) in [
            ("u8", Ty::U8, 7i128),
            ("i8", Ty::I8, -1),
            ("u16", Ty::U16, 4097),
            ("i16", Ty::I16, -3),
        ] {
            let source = build(
                &[],
                ty.clone(),
                vec![
                    InstrNode::new(Inst::Const { ty, value: Constant::Int(value) })
                        .with_result(ValueId::new(0)),
                ],
                ValueId::new(0),
            );
            let (v, _) = verdict(&source);
            assert!(matches!(v, OutputVerdict::Proven { .. }), "{name}: got {v:?}");
        }
    }

    /// A narrow PARAMETER binds `X{k}[N-1:0]` and asserts nothing above. If it
    /// were modeled as the full `W{k}`, the emitted `uxtb`/`sxtb` would disagree
    /// with it and these would Refute rather than prove.
    #[test]
    fn narrow_parameter_widening_casts_are_proven() {
        for (name, src, dst, op) in [
            ("zext u8->u32", Ty::U8, Ty::U32, CastOp::ZExt),
            ("sext i8->i32", Ty::I8, Ty::I32, CastOp::SExt),
            ("zext u16->u64", Ty::U16, Ty::U64, CastOp::ZExt),
            ("sext i16->i64", Ty::I16, Ty::I64, CastOp::SExt),
            ("trunc u32->u8", Ty::U32, Ty::U8, CastOp::Trunc),
            ("trunc i64->i16", Ty::I64, Ty::I16, CastOp::Trunc),
        ] {
            let params = vec![src.clone()];
            let source = build(
                &params,
                dst.clone(),
                vec![
                    InstrNode::new(Inst::Cast {
                        op,
                        src_ty: src,
                        dst_ty: dst,
                        operand: ValueId::new(0),
                    })
                    .with_result(ValueId::new(1)),
                ],
                ValueId::new(1),
            );
            let (v, _) = verdict(&source);
            assert!(matches!(v, OutputVerdict::Proven { .. }), "{name}: got {v:?}");
        }
    }

    /// Narrow arithmetic. These are decided, not waved through: the machine
    /// computes them in a 32-bit W register and the gate reads the low N bits.
    #[test]
    fn narrow_arithmetic_is_proven() {
        for (name, ty, op) in [
            ("add u8", Ty::U8, TirBinOp::Add),
            ("sub i8", Ty::I8, TirBinOp::Sub),
            ("mul u16", Ty::U16, TirBinOp::Mul),
            ("and u8", Ty::U8, TirBinOp::And),
            ("or u16", Ty::U16, TirBinOp::Or),
            ("xor i16", Ty::I16, TirBinOp::Xor),
        ] {
            let source = build(
                &[ty.clone(), ty.clone()],
                ty.clone(),
                vec![
                    InstrNode::new(Inst::BinOp {
                        op,
                        ty,
                        lhs: ValueId::new(0),
                        rhs: ValueId::new(1),
                    })
                    .with_result(ValueId::new(2)),
                ],
                ValueId::new(2),
            );
            let (v, _) = verdict(&source);
            assert!(matches!(v, OutputVerdict::Proven { .. }), "{name}: got {v:?}");
        }
    }

    /// An UNGUARDED narrow shift must stay `Unknown`. It may NOT become `Proven`
    /// and it may NOT become `Refuted`.
    ///
    /// THE REASON THIS TEST GIVES CHANGED, AND THE CHANGE IS THE POINT. It used
    /// to assert the message said "masking convention", on the premise that the
    /// machine masks the amount mod 32 while the spec masks mod width. That
    /// premise is false for this backend — `isel.rs:10655` emits `and w, w,
    /// #(width-1)` itself, visible as word 9 of `<u8 as PrimInt>::unsigned_shl` —
    /// so the two sides never disagreed and the old justification was measuring
    /// nothing. The verdict is unchanged and the REASON is now the real one:
    /// trust-ir's interpreter makes an over-wide shift UB, so with no in-range
    /// assert the gate has no IR semantics to render. See
    /// `narrow_shift_is_proven_only_against_the_irs_own_range_assert` for the
    /// other half — the same shift, guarded, is now decided.
    #[test]
    fn narrow_shift_is_unknown_not_proven_and_not_refuted() {
        for (name, ty, op) in [
            ("shl u8", Ty::U8, TirBinOp::Shl),
            ("lshr u8", Ty::U8, TirBinOp::LShr),
            ("ashr i16", Ty::I16, TirBinOp::AShr),
        ] {
            let source = build(
                &[ty.clone(), ty.clone()],
                ty.clone(),
                vec![
                    InstrNode::new(Inst::BinOp {
                        op,
                        ty,
                        lhs: ValueId::new(0),
                        rhs: ValueId::new(1),
                    })
                    .with_result(ValueId::new(2)),
                ],
                ValueId::new(2),
            );
            match verdict(&source).0 {
                OutputVerdict::Unknown { reason } => {
                    assert!(reason.contains("modeling precondition"), "{name}: {reason}");
                }
                other => panic!("{name}: a narrow shift must be Unknown, got {other:?}"),
            }
        }
        // The SAME operation at a machine width is decided, so the refusal is
        // about the width and not about shifts.
        let source = build(
            &[Ty::U32, Ty::U32],
            Ty::U32,
            vec![
                InstrNode::new(Inst::BinOp {
                    op: TirBinOp::Shl,
                    ty: Ty::U32,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
            ],
            ValueId::new(2),
        );
        let (v, _) = verdict(&source);
        assert!(matches!(v, OutputVerdict::Proven { .. }), "32-bit shl must be Proven, got {v:?}");
    }

    /// A `bool` RESULT is admitted and held to the FULL 32-bit register — that is
    /// the `arg_ext: Zext` contract rustc records for every bool slot. A
    /// perturbation of bits 8 and above, which a narrow return is allowed to
    /// ignore, must therefore be fatal here.
    #[test]
    fn bool_return_is_proven_and_held_to_the_whole_register() {
        let source = build(
            &[],
            Ty::Bool,
            vec![
                InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                    .with_result(ValueId::new(0)),
            ],
            ValueId::new(0),
        );
        let (base, obj) = verdict(&source);
        assert!(matches!(base, OutputVerdict::Proven { .. }), "bool baseline: {base:?}");
        let obj = obj.expect("verified bytes");
        for (tag, insn) in [("high bits", ADD_W0_256), ("bit 0", ADD_W0_1)] {
            let v = verdict_after_mutation(&source, &obj, insn);
            assert!(
                matches!(v, OutputVerdict::Refuted { .. }),
                "bool: perturbing {tag} must Refute (the callee owes a zero-extended 0/1 \
                 across the whole slot); got {v:?}"
            );
        }
    }

    /// A `bool` PARAMETER stays refused. The prior finding stands: modeling it as
    /// an unconstrained 32-bit value fabricated six Refuted verdicts, and the
    /// `Zext` promise that would justify a `∈ {0,1}` precondition is not modeled
    /// on both sides yet.
    #[test]
    fn bool_parameter_stays_refused() {
        let source = build(
            &[Ty::Bool],
            Ty::U32,
            vec![
                InstrNode::new(Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::Bool,
                    dst_ty: Ty::U32,
                    operand: ValueId::new(0),
                })
                .with_result(ValueId::new(1)),
            ],
            ValueId::new(1),
        );
        match verdict(&source).0 {
            OutputVerdict::Unknown { reason } => {
                assert!(reason.contains("PARAMETER position"), "unexpected reason: {reason}");
            }
            other => panic!("a bool parameter must be Unknown, got {other:?}"),
        }
    }
}

// ===========================================================================
// TESTS — THE POINTER CARRIER AND THE NARROW-SHIFT SIDE CONDITION
//
// Both admissions in this block were opened by RE-MEASURING a stated cause and
// finding it did not survive:
//
//   * the pointer bucket's message said "type outside the modeled scalar
//     fragment: Ptr" as though pointer SEMANTICS were the obstacle; not one of
//     the 119 corpus functions it refused loads, stores or offsets a pointer.
//   * the narrow-shift refusal said "the machine's W-register shift masks it
//     mod 32"; the backend masks it mod WIDTH itself, in an instruction that is
//     visible in the emitted bytes.
//
// So each test below is written to fail if the admission is widened past what
// was measured, not merely to confirm the happy path.
// ===========================================================================

#[cfg(test)]
mod tests_ptr_carrier_and_shift_range {
    use trust_ir::inst::{BinOp as TirBinOp, ICmpOp, Inst};
    use trust_ir::node::InstrNode;
    use trust_ir::ty::{FatPtrKind, FuncTy};
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
    use trust_ir::{Block, Constant, Function as IrFunction, Module, Ty};

    use super::*;
    use crate::codegen_backend::BridgeOptimizationLevel;

    /// `add w0, w0, #1` — perturbs bit 0, inside every modeled width.
    const ADD_W0_1: u32 = 0x1100_0400;

    fn backend() -> TrustCgCodegenBackend {
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O0)
    }

    fn build(params: &[Ty], ret: Ty, nodes: Vec<InstrNode>, ret_val: ValueId) -> TrustIrGateSource {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: params.to_vec(),
            returns: vec![ret],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        for (i, ty) in params.iter().enumerate() {
            block.params.push((ValueId::new(u32::try_from(i).expect("param index")), ty.clone()));
        }
        let mut body = nodes;
        body.push(InstrNode::new(Inst::Return { values: vec![ret_val] }));
        block.body = body;
        f.blocks.push(block);
        module.functions.push(f);
        TrustIrGateSource { symbol: "k".to_string(), module, func_id: FuncId::new(0) }
    }

    fn text_span(obj: &[u8]) -> Option<(usize, usize)> {
        let rd32 = |o: usize| -> Option<u32> {
            obj.get(o..o + 4).and_then(|s| s.try_into().ok()).map(u32::from_le_bytes)
        };
        if rd32(0)? != 0xfeed_facf {
            return None;
        }
        let ncmds = rd32(16)? as usize;
        let mut off = 32usize;
        for _ in 0..ncmds {
            let cmd = rd32(off)?;
            let cmdsize = rd32(off + 4)? as usize;
            if cmd == 0x19 {
                let nsects = rd32(off + 64)? as usize;
                let mut s = off + 72;
                for _ in 0..nsects {
                    if obj.get(s..s + 16)?.starts_with(b"__text\0") {
                        let size = u64::from_le_bytes(obj.get(s + 40..s + 48)?.try_into().ok()?);
                        return Some((rd32(s + 48)? as usize, size as usize));
                    }
                    s += 80;
                }
            }
            off += cmdsize;
        }
        None
    }

    /// `fn(a: *T, b: *T) -> *T { b }` — a pointer carried through, with a real
    /// instruction (`mov x0, x1`) ahead of the `ret` so there is a word to
    /// corrupt.
    fn second_pointer_through() -> TrustIrGateSource {
        build(&[Ty::Ptr, Ty::Ptr], Ty::Ptr, Vec::new(), ValueId::new(1))
    }

    /// A pointer that is merely CARRIED is proved, AND the proof reads the bytes.
    ///
    /// The second half is the point. `Proven` for a register move is worth
    /// nothing unless corrupting the move flips it, so the same object is
    /// re-discharged with its `mov x0, x1` replaced by `add w0, w0, #1`.
    #[test]
    fn carried_pointer_is_proven_and_the_proof_has_teeth() {
        let source = second_pointer_through();
        let (base, obj) = verify_trust_ir_output_preserved(&source, &backend());
        assert!(matches!(base, OutputVerdict::Proven { .. }), "baseline: {base:?}");
        let obj = obj.expect("verified bytes");

        let (off, size) = text_span(&obj).expect("__text");
        let words = size / 4;
        assert!(words >= 2, "expected a move plus a ret, got {words} word(s)");
        let mut corrupted = obj.clone();
        let at = off + (words - 2) * 4;
        corrupted[at..at + 4].copy_from_slice(&ADD_W0_1.to_le_bytes());
        let mutated = verify_trust_ir_bytes(&source, &corrupted, TrustCgTargetArch::AArch64);
        assert!(
            matches!(mutated, OutputVerdict::Refuted { .. }),
            "corrupting the pointer move must Refute, else the pointer obligation is \
             vacuous; got {mutated:?}"
        );
    }

    /// POINTER ARITHMETIC IS NOT ADMITTED. `Ty::Ptr` becoming a scalar width must
    /// not silently turn `Inst::BinOp { ty: Ptr }` into a 64-bit `BvAdd` — the
    /// lowering scales and this interpreter does not, and a guessed convention
    /// fabricates verdicts.
    #[test]
    fn pointer_arithmetic_is_refused_by_the_derivation() {
        let source = build(
            &[Ty::Ptr, Ty::U64],
            Ty::Ptr,
            vec![
                InstrNode::new(Inst::BinOp {
                    op: TirBinOp::Add,
                    ty: Ty::Ptr,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
            ],
            ValueId::new(2),
        );
        let err = trust_ir_function_semantics(&source.module, source.func_id)
            .expect_err("pointer arithmetic must not derive a spec");
        assert!(err.contains("MOVE-ONLY"), "unexpected reason: {err}");
    }

    /// A pointer COMPARISON is equally unmeasured, and equally refused.
    #[test]
    fn pointer_comparison_is_refused_by_the_derivation() {
        let source = build(
            &[Ty::Ptr, Ty::Ptr],
            Ty::Bool,
            vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::Ptr,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
            ],
            ValueId::new(2),
        );
        let err = trust_ir_function_semantics(&source.module, source.func_id)
            .expect_err("pointer comparison must not derive a spec");
        assert!(err.contains("MOVE-ONLY"), "unexpected reason: {err}");
    }

    /// ONLY THE THIN POINTER IS ADMITTED. A `Ty::FatPtr` is 128 bits across TWO
    /// registers (`trust-ir` `bit_width_with(64) == 128`); admitting it under the
    /// same 64-bit slot rule would misread the caller's registers.
    #[test]
    fn fat_pointer_is_not_admitted() {
        let source = build(&[Ty::FatPtr(FatPtrKind::Str)], Ty::U64, Vec::new(), ValueId::new(0));
        let err = trust_ir_function_semantics(&source.module, source.func_id)
            .expect_err("a fat pointer must not derive a spec");
        assert!(err.contains("outside the modeled scalar fragment"), "unexpected reason: {err}");
    }

    /// `fn(x: u8, n: u8) -> u8 { x << n }`, with the IR's shift-overflow assert
    /// present iff `guarded`.
    fn narrow_shift(guarded: bool) -> TrustIrGateSource {
        let mut nodes = Vec::new();
        if guarded {
            nodes.push(
                InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(8) })
                    .with_result(ValueId::new(2)),
            );
            nodes.push(
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ult,
                    ty: Ty::U8,
                    lhs: ValueId::new(1),
                    rhs: ValueId::new(2),
                })
                .with_result(ValueId::new(3)),
            );
            nodes.push(InstrNode::new(Inst::Assert { cond: ValueId::new(3) }));
        }
        nodes.push(
            InstrNode::new(Inst::BinOp {
                op: TirBinOp::Shl,
                ty: Ty::U8,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(4)),
        );
        build(&[Ty::U8, Ty::U8], Ty::U8, nodes, ValueId::new(4))
    }

    /// THE LOAD-BEARING PAIR. The SAME 8-bit shift must be `Proven` when the IR
    /// carries its own `amount < 8` assert and `Unknown` when it does not.
    ///
    /// Deleting the side condition makes the second half pass as `Proven` — the
    /// backend masks mod 8, so the bytes really do agree — which is exactly the
    /// mutant this pins. Agreement is not the standard: trust-ir's interpreter
    /// makes an over-wide shift UB (`shift_amount` returns `Err(ub(..))`), so
    /// with no assert there is no IR semantics for the spec to render, and a
    /// `Proven` there would be a claim about inputs the IR refuses to define.
    #[test]
    fn narrow_shift_is_proven_only_against_the_irs_own_range_assert() {
        let guarded = verify_trust_ir_output_preserved(&narrow_shift(true), &backend()).0;
        assert!(
            matches!(guarded, OutputVerdict::Proven { .. }),
            "a guarded 8-bit shift must be Proven; got {guarded:?}"
        );

        let unguarded = verify_trust_ir_output_preserved(&narrow_shift(false), &backend()).0;
        match unguarded {
            OutputVerdict::Unknown { reason } => assert!(
                reason.contains("modeling precondition"),
                "unguarded shift must be Unknown for the RANGE reason; got {reason}"
            ),
            other => panic!(
                "an 8-bit shift the IR does not prove in range must stay Unknown, got {other:?}"
            ),
        }
    }

    /// THE BOUNDARY. The requirement is `amount < width`, and `amount <= width`
    /// is not good enough: at `amount == width` `mask_shift` folds to a shift by
    /// ZERO while trust-ir's interpreter calls the same input UB, so admitting
    /// the equal case would re-open exactly the invented-semantics hole the
    /// condition exists to close.
    ///
    /// This is the test that kills a `Lt`->`Le` mutant in
    /// `narrow_shift_side_condition`; the guarded/unguarded pair above does not,
    /// because both of its cases answer the same either way.
    #[test]
    fn a_shift_guarded_only_to_the_width_ITSELF_is_not_enough() {
        let source = build(
            &[Ty::U8, Ty::U8],
            Ty::U8,
            vec![
                InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(8) })
                    .with_result(ValueId::new(2)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ule,
                    ty: Ty::U8,
                    lhs: ValueId::new(1),
                    rhs: ValueId::new(2),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Assert { cond: ValueId::new(3) }),
                InstrNode::new(Inst::BinOp {
                    op: TirBinOp::Shl,
                    ty: Ty::U8,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(4)),
            ],
            ValueId::new(4),
        );
        match verify_trust_ir_output_preserved(&source, &backend()).0 {
            OutputVerdict::Unknown { reason } => assert!(
                reason.contains("modeling precondition"),
                "expected the range precondition to be the blocker; got {reason}"
            ),
            other => panic!(
                "`amount <= 8` does not establish `amount < 8`; the shift must stay \
                 Unknown, got {other:?}"
            ),
        }
    }

    /// The side condition is discharged, not assumed: the derivation emits one
    /// for a narrow shift and none for a 32-bit shift, where `eval_binop`'s
    /// mod-width masking already IS the hardware's reduction.
    #[test]
    fn side_conditions_are_emitted_only_where_the_width_needs_them() {
        let narrow =
            trust_ir_function_semantics(&narrow_shift(true).module, narrow_shift(true).func_id)
                .expect("narrow spec");
        assert_eq!(narrow.side_conditions.len(), 1, "an 8-bit shift owes one range obligation");

        let wide = build(
            &[Ty::U32, Ty::U32],
            Ty::U32,
            vec![
                InstrNode::new(Inst::BinOp {
                    op: TirBinOp::Shl,
                    ty: Ty::U32,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
            ],
            ValueId::new(2),
        );
        let wide = trust_ir_function_semantics(&wide.module, wide.func_id).expect("wide spec");
        assert!(
            wide.side_conditions.is_empty(),
            "a 32-bit shift owes nothing: mod-32 IS the hardware reduction"
        );
    }
}

// ===========================================================================
// TESTS — THE CHECKED-ARITHMETIC OVERFLOW FLAG
//
// This flag is the only thing in the modeled fragment that flows into
// `spec_reach` rather than into the returned value, which inverts the usual
// risk: a flag that is too NARROW does not lose a proof, it manufactures a
// `Refuted` against correct code. So these tests are aimed at EXACTNESS, not at
// coverage — the equivalence proof below is the one that would have caught a
// mis-transcribed sign-bit idiom before the corpus ever ran.
// ===========================================================================

#[cfg(test)]
mod tests_checked_arithmetic {
    use trust_ir::inst::{Inst, OverflowOp};
    use trust_ir::node::InstrNode;
    use trust_ir::ty::FuncTy;
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
    use trust_ir::{Block, Constant, Function as IrFunction, Module, Ty};

    use super::*;
    use crate::codegen_backend::BridgeOptimizationLevel;

    fn backend() -> TrustCgCodegenBackend {
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O0)
    }

    fn bv(name: &str, width: u32) -> Formula {
        Formula::Var(name.to_string(), trust_types::Sort::BitVec(width))
    }

    fn iff(left: Formula, right: Formula) -> Formula {
        Formula::And(vec![
            Formula::Or(vec![Formula::Not(b(left.clone())), right.clone()]),
            Formula::Or(vec![Formula::Not(b(right)), left]),
        ])
    }

    /// THE EXACTNESS PROOF. The shipped flag uses the sign-bit idiom so that a
    /// 64-bit checked add stays inside the exporter's 64-bit ceiling. That is a
    /// performance concession, and this test pays for it: at a width where BOTH
    /// encodings export, the idiom is PROVED equivalent to the definitional
    /// "widen by one bit and see whether the exact result still fits".
    ///
    /// All four arms are checked. A transcription slip in any of them — a `~`
    /// dropped from the signed-add mask, `lhs`/`rhs` swapped in the signed-sub
    /// one — makes the corresponding line fail here rather than surface as a
    /// fabricated miscompile report against the backend.
    #[test]
    fn overflow_flag_matches_the_widen_by_one_bit_definition() {
        const W: u32 = 8;
        let a = bv("a", W);
        let c = bv("c", W);

        for (op, signed, label) in [
            (OverflowOp::AddOverflow, false, "unsigned add"),
            (OverflowOp::SubOverflow, false, "unsigned sub"),
            (OverflowOp::AddOverflow, true, "signed add"),
            (OverflowOp::SubOverflow, true, "signed sub"),
        ] {
            let is_add = matches!(op, OverflowOp::AddOverflow);
            let wrapped = if is_add {
                Formula::BvAdd(b(a.clone()), b(c.clone()), W)
            } else {
                Formula::BvSub(b(a.clone()), b(c.clone()), W)
            };
            let shipped = overflow_flag_formula(op, W, signed, &a, &c, &wrapped)
                .unwrap_or_else(|e| panic!("{label}: {e}"));

            // Definitional form: extend both operands by ONE bit, do the exact
            // arithmetic there, and ask whether the w-bit result is faithful.
            let ext = |f: &Formula| {
                if signed {
                    Formula::BvSignExt(b(f.clone()), 1)
                } else {
                    Formula::BvZeroExt(b(f.clone()), 1)
                }
            };
            let wide = if is_add {
                Formula::BvAdd(b(ext(&a)), b(ext(&c)), W + 1)
            } else {
                Formula::BvSub(b(ext(&a)), b(ext(&c)), W + 1)
            };
            let definitional = Formula::Not(b(Formula::Eq(b(ext(&wrapped)), b(wide))));

            match discharge_valid(&iff(shipped, definitional)) {
                Discharge::Proven => {}
                other => panic!(
                    "{label} overflow flag is NOT equivalent to the widen-by-one \
                     definition: {other:?}"
                ),
            }
        }
    }

    /// A checked MULTIPLY stays refused, and refused for the stated reason.
    #[test]
    fn checked_multiply_is_refused() {
        let a = bv("a", 32);
        let c = bv("c", 32);
        let wrapped = Formula::BvMul(b(a.clone()), b(c.clone()), 32);
        let err = overflow_flag_formula(OverflowOp::MulOverflow, 32, false, &a, &c, &wrapped)
            .expect_err("checked multiply must not be modeled");
        assert!(err.contains("checked MULTIPLY"), "unexpected reason: {err}");
    }

    /// `fn(a: u64, b: u64) -> u64 { a + b }` as rustc's frontend emits it:
    /// `add.overflow`, `assert(!did_overflow)`, return the wrapping value.
    fn checked_add_u64() -> TrustIrGateSource {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::U64, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::U64));
        block.params.push((ValueId::new(1), Ty::U64));
        block.body = vec![
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ty: Ty::U64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2))
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Select {
                ty: Ty::Bool,
                cond: ValueId::new(3),
                then_val: ValueId::new(4),
                else_val: ValueId::new(5),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Assert { cond: ValueId::new(6) }),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        f.blocks.push(block);
        module.functions.push(f);
        TrustIrGateSource { symbol: "k".to_string(), module, func_id: FuncId::new(0) }
    }

    /// THE FLAG IS LOAD-BEARING ON BOTH OBLIGATIONS, and this is what shows it.
    ///
    /// The IR's guard is `!did_overflow`, so `spec_reach` is a real predicate and
    /// the vacuity firewall has something to reject if it were not satisfiable.
    /// The baseline must be `Proven` — the emitted `adds`/`b.cs` check and the
    /// modeled flag have to agree exactly, or obligation A ("the machine returns
    /// wherever the IR returns") reports a miscompile that is not there.
    #[test]
    fn checked_add_is_proven_against_a_nontrivial_reach() {
        let source = checked_add_u64();
        let spec = trust_ir_function_semantics(&source.module, source.func_id)
            .expect("checked add must derive a spec");
        assert!(
            !matches!(spec.reach, Formula::Bool(true)),
            "the assert must make `spec_reach` a real predicate, else this proves nothing"
        );
        let verdict = verify_trust_ir_output_preserved(&source, &backend()).0;
        assert!(
            matches!(verdict, OutputVerdict::Proven { .. }),
            "checked add must be Proven; got {verdict:?}"
        );
    }

    /// And the VALUE half still bites: corrupt the returned register and the same
    /// obligation flips, so `Proven` above is not riding on a vacuous reach.
    #[test]
    fn checked_add_proof_is_not_vacuous() {
        /// `movz x0, #0x5a5a` — the whole return value replaced by a constant.
        const MOVZ_X0_5A5A: u32 = 0xd280_0000 | (0x5a5a << 5);
        let source = checked_add_u64();
        let (base, obj) = verify_trust_ir_output_preserved(&source, &backend());
        assert!(matches!(base, OutputVerdict::Proven { .. }), "baseline: {base:?}");
        let obj = obj.expect("verified bytes");

        let rd32 = |o: usize| u32::from_le_bytes(obj[o..o + 4].try_into().expect("word"));
        let ncmds = rd32(16) as usize;
        let mut off = 32usize;
        let mut span = None;
        for _ in 0..ncmds {
            if rd32(off) == 0x19 {
                let nsects = rd32(off + 64) as usize;
                let mut s = off + 72;
                for _ in 0..nsects {
                    if obj[s..s + 16].starts_with(b"__text\0") {
                        let size =
                            u64::from_le_bytes(obj[s + 40..s + 48].try_into().expect("size"));
                        span = Some((rd32(s + 48) as usize, size as usize));
                    }
                    s += 80;
                }
            }
            off += rd32(off + 4) as usize;
        }
        let (base_off, size) = span.expect("__text");
        let mut best = None;
        for i in 0..size / 4 {
            if rd32(base_off + i * 4) == 0xd65f_03c0 {
                best = Some(i);
            }
        }
        let ret = best.expect("a ret");
        assert!(ret >= 1, "need an instruction before the ret");
        let mut corrupted = obj.clone();
        let at = base_off + (ret - 1) * 4;
        corrupted[at..at + 4].copy_from_slice(&MOVZ_X0_5A5A.to_le_bytes());
        let mutated = verify_trust_ir_bytes(&source, &corrupted, TrustCgTargetArch::AArch64);
        assert!(
            matches!(mutated, OutputVerdict::Refuted { .. }),
            "returning a constant instead of the sum must Refute; got {mutated:?}"
        );
    }
}

/// THE GATE SIDE OF THE FIELDLESS-ENUM ADMISSION.
///
/// The converter's half is pinned in `module_to_lir::tests`; this half pins that
/// the SPEC side reads the same slot at the same width, refuses the same
/// constants, and that the resulting `Proven` has teeth against a tag rewrite.
///
/// The fixtures are the producer's real shapes, read back out of a
/// `-Ztrust-ir-lower --emit=trust-ir` module for the corresponding Rust source
/// (see `module_to_lir::tests::fieldless_enum`), and all three of them ship
/// `3 [PROVED]` through `-Ztrust-cg-frontend=trust-ir` at HEAD+this-change.
#[cfg(test)]
mod tests_fieldless_enum {
    use trust_ir::inst::Inst;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::{EnumTagRepr, FuncTy};
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
    use trust_ir::{Block, Constant, Function as IrFunction, Module, Ty};

    use super::*;
    use crate::codegen_backend::BridgeOptimizationLevel;

    fn backend() -> TrustCgCodegenBackend {
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O0)
    }

    /// The producer's fieldless-enum def: explicit discriminants, a `repr` hint
    /// only where `widen_enum_repr_to_rustc_tag_lane` had to move the lane, and
    /// a `Direct { tag_offset: 0 }` descriptor whose size is the tag's.
    fn fieldless_enum(discs: &[i128], repr: Option<EnumTagRepr>, size: u64) -> trust_ir::EnumDef {
        let variants = (0..discs.len())
            .map(|i| trust_ir::EnumVariant {
                name: format!("V{i}"),
                fields: Vec::new(),
                field_names: Vec::new(),
            })
            .collect();
        let mut def = trust_ir::EnumDef::new(trust_ir::EnumId::new(0), "E", variants);
        def.discriminants = discs.iter().map(|d| Some(*d)).collect();
        def.repr = repr;
        def.layout = Some(trust_ir::EnumLayoutDescriptor {
            encoding: trust_ir::EnumTagEncoding::Direct { tag_offset: 0 },
            size,
            align: size,
            variant_field_offsets: vec![Vec::new(); discs.len()],
        });
        def
    }

    /// `enum Three { X, Y, Z }`, verbatim.
    fn three_variant_enum() -> trust_ir::EnumDef {
        fieldless_enum(&[0, 1, 2], None, 1)
    }

    /// `fn k() -> E { <disc> }` — the shape `pub fn three_z() -> Three
    /// { Three::Z }` really lowers to: one `Inst::Const` at the enum type whose
    /// single aggregate field is the discriminant, then a `Return`.
    fn enum_const_source(def: trust_ir::EnumDef, disc: i128) -> TrustIrGateSource {
        let mut module = Module::new("t");
        module.enums.push(def);
        let ety = Ty::Enum(trust_ir::EnumId::new(0));
        module.func_types.push(FuncTy {
            params: Vec::new(),
            returns: vec![ety.clone()],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body = vec![
            InstrNode::new(Inst::Const {
                ty: ety,
                value: Constant::Aggregate(vec![Constant::Int(disc)]),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
        ];
        f.blocks.push(block);
        module.functions.push(f);
        TrustIrGateSource { symbol: "k".to_string(), module, func_id: FuncId::new(0) }
    }

    /// `fn k(e: E) -> E { e }` — an enum-typed PARAMETER, the other half of the
    /// signature rule (`pub fn three_id(t: Three) -> Three { t }`).
    fn enum_identity_source(def: trust_ir::EnumDef) -> TrustIrGateSource {
        let mut module = Module::new("t");
        module.enums.push(def);
        let ety = Ty::Enum(trust_ir::EnumId::new(0));
        module.func_types.push(FuncTy {
            params: vec![ety.clone()],
            returns: vec![ety.clone()],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), ety));
        block.body = vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] })];
        f.blocks.push(block);
        module.functions.push(f);
        TrustIrGateSource { symbol: "k".to_string(), module, func_id: FuncId::new(0) }
    }

    /// ONE derivation, not two. The width the SPEC reads an enum-typed return at
    /// is the same width the CONVERTER gave that slot in the LIR — asserted
    /// against each other on the same module, at every real producer width, so
    /// a change to either side that does not move the other fails here.
    #[test]
    fn spec_and_converter_read_an_enum_slot_at_the_same_width() {
        for (name, discs, repr, size, tag, bits) in [
            ("Three (u8)", &[0i128, 1, 2][..], None, 1u64, 2i128, 8u32),
            ("Wide (repr u32)", &[0, 1, 2][..], Some(EnumTagRepr::U32), 4, 2, 32),
            ("Big (u16 by value)", &[0, 300][..], None, 2, 300, 16),
            ("Neg (i8, signed)", &[-1, 0][..], None, 1, -1, 8),
        ] {
            let source = enum_const_source(fieldless_enum(discs, repr, size), tag);
            let spec = trust_ir_function_semantics(&source.module, source.func_id)
                .unwrap_or_else(|e| panic!("{name}: spec must derive, got {e}"));
            assert_eq!(spec.out_width, bits, "{name}: spec width");

            let lir = crate::lower_module_to_lir(&source.module, source.func_id)
                .unwrap_or_else(|e| panic!("{name}: converter must lower, got {e:?}"));
            let converter_bits = match &lir.signature.returns[0] {
                trust_cg_lower::types::Type::I8 => 8,
                trust_cg_lower::types::Type::I16 => 16,
                trust_cg_lower::types::Type::I32 => 32,
                trust_cg_lower::types::Type::I64 => 64,
                other => panic!("{name}: unexpected LIR carrier {other:?}"),
            };
            assert_eq!(
                converter_bits, spec.out_width,
                "{name}: the converter and the gate must read ONE derivation of the \
                 carrier width"
            );
        }
    }

    /// The value-validity check is on the SPEC side too, not only in the
    /// converter — otherwise the two sides could disagree about which constants
    /// exist. The declared half is the control that only passes with the change.
    #[test]
    fn spec_refuses_an_undeclared_discriminant() {
        for disc in [0i128, 1, 2] {
            let source = enum_const_source(three_variant_enum(), disc);
            trust_ir_function_semantics(&source.module, source.func_id)
                .unwrap_or_else(|e| panic!("declared discriminant {disc} must model: {e}"));
        }
        for disc in [3i128, 7, 255, -1] {
            let source = enum_const_source(three_variant_enum(), disc);
            let err = trust_ir_function_semantics(&source.module, source.func_id)
                .expect_err(&format!("tag {disc} is not declared and must fail closed"));
            assert!(
                err.contains("DECLARED discriminant"),
                "tag {disc} must be refused FOR NOT BEING A DECLARED DISCRIMINANT, \
                 not for some other reason; got {err}"
            );
        }
    }

    /// A def the descriptor does not pin has no carrier on the spec side either,
    /// so the gate refuses the whole function rather than inventing a width.
    #[test]
    fn spec_fails_closed_on_an_unpinned_enum_def() {
        trust_ir_function_semantics(
            &enum_const_source(three_variant_enum(), 2).module,
            FuncId::new(0),
        )
        .expect("control: the pinned def must model");

        let mut no_layout = three_variant_enum();
        no_layout.layout = None;
        let mut payload = three_variant_enum();
        payload.variants[1].fields.push(Ty::I32);

        for (why, def) in [("no layout descriptor", no_layout), ("a payload variant", payload)] {
            let source = enum_const_source(def, 0);
            assert!(
                trust_ir_function_semantics(&source.module, source.func_id).is_err(),
                "{why}: the spec must fail closed"
            );
        }
    }

    /// END TO END: a fieldless-enum constant and a fieldless-enum parameter both
    /// compile through the real converter and backend and are certified
    /// `Proven` against their own emitted bytes.
    #[test]
    fn fieldless_enum_functions_are_proven_end_to_end() {
        for (name, discs, repr, size, tag) in [
            ("Three (u8)", &[0i128, 1, 2][..], None, 1u64, 2i128),
            ("Wide (repr u32)", &[0, 1, 2][..], Some(EnumTagRepr::U32), 4, 2),
            ("Big (u16 by value)", &[0, 300][..], None, 2, 300),
            ("Neg (i8, signed)", &[-1, 0][..], None, 1, -1),
        ] {
            let source = enum_const_source(fieldless_enum(discs, repr, size), tag);
            let (v, _) = verify_trust_ir_output_preserved(&source, &backend());
            assert!(matches!(v, OutputVerdict::Proven { .. }), "{name} constant: got {v:?}");

            let source = enum_identity_source(fieldless_enum(discs, repr, size));
            let (v, _) = verify_trust_ir_output_preserved(&source, &backend());
            assert!(matches!(v, OutputVerdict::Proven { .. }), "{name} identity: got {v:?}");
        }
    }

    /// THE TAG-REWRITE TEETH. Take the bytes the backend emitted for one
    /// DECLARED discriminant and re-discharge a DIFFERENT declared
    /// discriminant's spec against them. Nothing here is a hand-built encoding:
    /// both byte images are real emitter output, so this is exactly "the tag
    /// immediate was rewritten to another declared discriminant" with no
    /// opportunity to mutate into something the decoder would reject for an
    /// unrelated reason.
    ///
    /// If the tag were not part of the obligation — if the enum return were
    /// modeled as an opaque or a fixed value — every one of these pairs would
    /// stay `Proven`.
    #[test]
    fn rewriting_a_tag_to_another_declared_discriminant_is_refuted() {
        let objs: Vec<(i128, Vec<u8>)> = [0i128, 1, 2]
            .into_iter()
            .map(|disc| {
                let source = enum_const_source(three_variant_enum(), disc);
                let (v, obj) = verify_trust_ir_output_preserved(&source, &backend());
                assert!(matches!(v, OutputVerdict::Proven { .. }), "tag {disc}: got {v:?}");
                (disc, obj.expect("verified bytes"))
            })
            .collect();

        let mut checked = 0;
        for (spec_disc, _) in &objs {
            let source = enum_const_source(three_variant_enum(), *spec_disc);
            for (byte_disc, obj) in &objs {
                if byte_disc == spec_disc {
                    continue;
                }
                let v = verify_trust_ir_bytes(&source, obj, TrustCgTargetArch::AArch64);
                assert!(
                    matches!(v, OutputVerdict::Refuted { .. }),
                    "spec says tag {spec_disc} but the bytes return tag {byte_disc}: \
                     must Refute, got {v:?}"
                );
                checked += 1;
            }
        }
        assert_eq!(checked, 6, "every ordered pair of distinct declared tags must be tried");
    }
}
