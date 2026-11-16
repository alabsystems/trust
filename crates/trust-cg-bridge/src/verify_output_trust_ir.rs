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
//     except for the trap modeling described below (it also reads the O0 ABI
//     locations, as it does for the MIR gate). The bytes it executes come
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
// THE ABI GUARANTEE (O0, increment-5 step 5.0). Every caller of an F1 function
// is LLVM-built code that relies on AAPCS64, so the bytes must also hand back
// X19-X29, SP and D8-D15 unchanged, return to the entry X30, and (on Darwin)
// never write X18. The executor reads those locations at every reachable exit
// (`verify_output::AbiExit`); what its structural reading cannot reduce to the
// entry values is `GateObligation::abi_residue`, discharged FIRST.
//
// EVIDENCE GRADE. The kernel certificate currently covers the value equality
// only. Additional modeling conditions, nontrivial machine reachability, a
// source/ambient precondition, or an O0 residue the solver had to discharge cap
// the complete verdict at AyValidated, even when all solver checks succeed.
// StrictProvenOnly refuses that grade until every necessary obligation has
// exact, composed kernel evidence.
//
// MODULE-LOCAL CALLS (WS7.12). `Inst::Call` to a callee DEFINED IN THIS MODULE
// is modeled by interpreting the CALLEE'S OWN trust-ir with its entry-block
// parameters bound to the caller's argument formulas, and conjoining the
// callee's `reach` into the caller's path. The callee's semantics are read from
// the producer's IR, never from `inline_local_pure_leaf_calls`' splice — so the
// inliner stays the thing under test and the obligation stays non-tautological.
// The admission is deliberately narrow and every miss is `Unknown`: a non-local
// or body-less callee, a `Producer::Clean` callee (refused by the
// `CleanOriginBelowCodegenGate` name until WS7.15's shared predicate replaces
// it), recursion, a chain deeper than `MAX_IR_CALL_DEPTH`, or a callee that
// does not return exactly one value. `Inst::CallIndirect` is never modeled.
//
// `bool` PARAMETERS (WS7.13). A bool parameter arrives in a register the
// CALLER wrote, and an unconstrained model of it fabricated six `Refuted`
// verdicts against correct code once. It is modeled ONLY under the extension
// contract the ABI makes the caller owe — rustc marks every bool slot
// `arg_ext: Zext`, and Apple AArch64 makes the caller extend a small argument
// to 32 bits — spelled as the AMBIENT precondition `W{k}[31:1] == 0` over the
// shared input variable both sides read, with the spec value `W{k}[0:0]`. The
// facts are attested by the attached `AbiPassModeCrossCheck`
// (`AbiParamExtensions`), never inferred here; without them, with an
// extension other than `Zext`, or on a target that makes no caller-side
// promise, the parameter stays `Unknown`. The precondition is a trust
// assumption on every caller (C callers included): it caps the verdict at
// `AyValidated` and appears in the obligation's assumption list.
//
// LOOPS (WS7.14). A loop header is a CUT POINT. The spec is cut into acyclic
// segments — entry -> first header, header -> {next header, return} — and for
// each the machine is run from the header's claimed address with the header's
// SHARED VARIABLES (its block params and every other live-in) in their
// claimed registers and everything else havoc. Each segment proves
// `spec_reach => machine_reach AND agreement` (the return value, or the next
// header's shared variables); by induction over cut points that is lockstep
// PARTIAL correctness — nothing is claimed about non-termination, and the
// verdict is capped at `AyValidated`. The header addresses and registers are
// an UNTRUSTED map, inferred from the bytes here because the emitter exports
// none (see PART 2b); a wrong map can only fail to prove. Irreducible control
// flow, a callee's loop, a loop beside a stack-passed or `bool` parameter,
// and a live-in the map cannot locate stay `Unknown`.
//
// FAIL-CLOSED EVERYWHERE. Any shape the interpreter does not model EXACTLY —
// memory, non-local or indirect calls, aggregates, floats, overflow intrinsics,
// narrow SHIFTS, un-attested `bool` PARAMETERS, 128-bit ARITHMETIC, irreducible
// or callee-side loops — returns `Err`, which the gate reports as `Unknown`.
// There is no arm that emits a function the gate did not look at.
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

use trust_cg_lower::abi::{AArch64AbiVariant, AppleAArch64ABI, ArgLocation};
use trust_cg_lower::types::Type as ClassifierTy;
use trust_ir::inst::{BinOp as IrBinOp, CastOp, ICmpOp, Inst, OverflowOp, UnOp as IrUnOp};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Constant, Module, Ty as IrTy};
use trust_machine_sem::{Flags, MachineState};
use trust_types::{BinOp, Formula, Sort};

use crate::codegen_backend::{
    CompiledModule, EmittedModuleObject, FunctionLinkage, TrustCgCodegenBackend, TrustCgTargetArch,
    assembled_internal_object_globals,
};
use crate::verify_output::{
    AbiConjunct, AbiDischarge, CertificationReport, Discharge, EmitPolicy, OutputVerdict,
    PathOutcome, PreservedFunction, ProvenEvidence, VerifiedModuleObject, VerifyError,
    abi_arrival_invariant, abi_guarantee_residue, assert_merged_object_preserves_verified_text, b,
    backward_branch_targets, discharge_abi_guarantee, discharge_abi_loop_conjuncts,
    discharge_equal_pre, discharge_valid, eval_binop, eval_cast, extract_text_from_object,
    normalize_sp_selects, platform_reserves_x18, pred_to_int, seed_abi_entry_invariant,
    symbolic_machine_outcome_traps, symbolic_machine_segment, try_kernel_recheckable_proof, wn, xn,
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
    ///
    /// SHARED (`Arc`), not owned: the F1 frontend lowers every function of a
    /// crate against the SAME crate module, and owning it meant one full clone
    /// per admitted function, O(functions x module size) in time and memory
    /// (plan item K; measured 2026-10-01: 3,200 one-line functions took 23.6 GB
    /// RSS and 38 s). Every reader takes `&Module` through `Deref`.
    pub module: std::sync::Arc<Module>,
    /// The body function's id inside `module`.
    pub func_id: FuncId,
    /// The PASS-MODE CROSS-CHECK the shipping path attached when it lowered this
    /// module, carried so the gate's own re-lowerings are admitted on exactly the
    /// same evidence — never on a weaker one.
    ///
    /// The gate EMITS the object it verifies (`verify_trust_ir_output_preserved`
    /// lowers, emits, and returns the bytes the caller ships), so it is itself a
    /// codegen boundary: it must clear the same `struct_passing` admission the
    /// shipping converter does. `None` means no cross-check was attached, and an
    /// `Unclassified` module with an aggregate call edge is then refused by name
    /// (`ModuleLirError::UnclassifiedAggregateAbi`) here as well.
    ///
    /// The in-tree producer of a `Some` is `rustc_codegen_trust_cg`'s F1
    /// frontend, which mints it from the `validate_codegen_instance_abi_trust_ir`
    /// check it runs against rustc's `FnAbi` immediately before lowering.
    pub abi_cross_check: Option<crate::AbiPassModeCrossCheck>,
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
pub(crate) struct IrValue {
    pub(crate) f: Formula,
    pub(crate) width: u32,
}

/// What one evaluated path through the IR yields: the return-value Formula and
/// the conjunction of `Inst::Assert` conditions that had to hold to get there.
struct IrOutcome {
    value: Formula,
    reach: Formula,
    /// NO CHECK FAILS: the predicate under which no `Inst::Assert` (this
    /// function's or a callee's) fails on any path from here. It is computed
    /// like `reach` except that a path ending in `Inst::Unreachable` (undefined
    /// behaviour, which the producer emits only where reaching it is UB) and a
    /// path after a callee that reached one count as not failing, and a
    /// cut-point arrival counts as failing (its continuation is not evaluated
    /// here). `reach` implies `ok`. Read by the call-event gate for an inlined
    /// callee, so an `Unreachable` arm of the callee is not a failed check.
    ok: Formula,
    /// CUT-POINT ARRIVALS (WS7.14): the loop headers this evaluation reached
    /// instead of returning, each with its own reach predicate and the values
    /// of the header's shared variables at that edge. Empty for a loop-free
    /// function.
    arrivals: Vec<IrArrival>,
}

/// One arrival of a spec SEGMENT at a cut point (WS7.14): the header block,
/// the predicate under which this path reaches it, and the header's shared
/// variables (block params, then every other live-in) in `SpecEval::shared`
/// order.
#[derive(Clone)]
struct IrArrival {
    block: u32,
    reach: Formula,
    values: Vec<IrValue>,
}

/// Merge two arms' arrival lists under `cond`, pairing by header block.
fn merge_ir_arrivals(
    cond: &Formula,
    taken: Vec<IrArrival>,
    fall: Vec<IrArrival>,
) -> Vec<IrArrival> {
    let mut merged: Vec<IrArrival> = Vec::new();
    let mut fall: Vec<Option<IrArrival>> = fall.into_iter().map(Some).collect();
    for t in taken {
        let partner = fall
            .iter_mut()
            .find(|f| f.as_ref().is_some_and(|f| f.block == t.block))
            .and_then(Option::take);
        merged.push(match partner {
            Some(f) => IrArrival {
                block: t.block,
                reach: merge_reach(cond.clone(), t.reach, f.reach),
                values: t
                    .values
                    .into_iter()
                    .zip(f.values)
                    .map(|(a, e)| IrValue {
                        f: if a.f == e.f {
                            a.f
                        } else {
                            Formula::Ite(b(cond.clone()), b(a.f), b(e.f))
                        },
                        width: a.width,
                    })
                    .collect(),
            },
            None => IrArrival {
                block: t.block,
                reach: merge_reach(cond.clone(), t.reach, Formula::Bool(false)),
                values: t.values,
            },
        });
    }
    for f in fall.into_iter().flatten() {
        merged.push(IrArrival {
            block: f.block,
            reach: merge_reach(cond.clone(), Formula::Bool(false), f.reach),
            values: f.values,
        });
    }
    merged
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
pub(crate) fn scalar_reg_width(ty: &IrTy) -> Result<u32, String> {
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

/// Kernel evidence for an unconditional value obligation together with its
/// spec-side modeling conditions, or `None` if any part lacks it.
///
/// With no side conditions this is exactly the value's own evidence. Otherwise
/// each condition `c` is exported as the 1-bit equality `ite(c, 1, 0) == 1`,
/// which holds for every input iff `c` is valid, and must earn kernel evidence
/// of its own; a condition outside the exportable fragment leaves the function
/// at solver authority. The caller has already discharged every condition with
/// ay, so this only decides the grade.
fn kernel_value_and_side_conditions(
    machine_value: &Formula,
    spec_value: &Formula,
    side_conditions: &[Formula],
) -> Option<ProvenEvidence> {
    let value = try_kernel_recheckable_proof(machine_value, spec_value, None)?;
    if side_conditions.is_empty() {
        return Some(value);
    }
    let one = Formula::BitVec { value: 1, width: 1 };
    let side_conditions = side_conditions
        .iter()
        .map(|condition| {
            try_kernel_recheckable_proof(&pred_to_int(condition.clone(), 1), &one, None)
        })
        .collect::<Option<Vec<_>>>()?;
    // Trust: every part must be kernel evidence; a wide multiply's citation is not
    // (DECISION_QUEUE AGG-SSA-2).
    ProvenEvidence::with_side_conditions(value, side_conditions)
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
/// here — they fall through `eval_ir_inst`'s catch-all, so no pointer this gate
/// admits is ever dereferenced. The one exception is a block-local slot
/// ([`LocalSlots`]): its `Alloca`, `Load` and `Store` are evaluated before the
/// catch-all, and its address never becomes an SSA value of the spec.
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

/// The OVERFLOW FLAG of a checked ADD, SUB, or MUL, as a Bool-sorted `Formula`.
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
/// The six definitions are the standard ones and hold at every width:
///
///   * unsigned add — `a + b` carries out iff the wrapped sum dropped below `a`:
///     `s <u a`. (If it carried, `s = a + b - 2^w < a` because `b < 2^w`; if it
///     did not, `s = a + b >= a`.)
///   * unsigned sub — `a - b` borrows iff `a <u b`.
///   * signed add — overflow iff the operands share a sign and the sum does not:
///     the sign bit of `~(a^b) & (a^s)`.
///   * signed sub — overflow iff the operands differ in sign and the difference
///     takes the RHS's: the sign bit of `(a^b) & (a^d)`.
///   * unsigned mul — zero-extend both operands to `2w`, multiply there, and
///     overflow iff the high `w` bits of the exact product are nonzero.
///   * signed mul — sign-extend both operands to `2w`, multiply there, and
///     overflow iff that exact product differs from the sign-extension of the
///     wrapped low-`w` result.
///
/// The two signed cases are the sign-bit idiom rather than the more obviously
/// correct "widen by one bit and compare" form, and that is a deliberate
/// concession to the exporter: a 64-bit checked add would need 65-bit terms,
/// which `ay-proof` will not take, so the definitional form would cost every
/// 64-bit verdict. `signed_overflow_bit_trick_matches_the_definition` pays the
/// difference back by PROVING the two encodings equivalent at a width where both
/// export, instead of asking the reader to accept the idiom.
///
/// Multiplication is admitted only for nonzero widths through 32. Its `2w`-bit
/// term is a SOURCE-semantics definition, not a claim that the target performs
/// one register-wide operation: the independently decoded machine formula is
/// still compared against it by the output gate. The cap is the exporter's, not
/// the definition's: a 64-bit checked multiply needs a 128-bit exact product,
/// and `ay-proof` will not take terms wider than 64 bits (the same limit that
/// forces the sign-bit idiom above), so admitting `w = 64` would build a term
/// no verdict could discharge. 64-bit and wider multiplies, and width zero,
/// stay fail-closed here before any term is constructed.
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
        (OverflowOp::MulOverflow, signed) => {
            if width == 0 || width > 32 {
                return Err(format!(
                    "checked MULTIPLY at {width} bits: the exact modeled fragment supports \
                     only nonzero scalar widths through 32, because the definitional {}-bit \
                     product is outside the 64-bit terms the ay-proof exporter carries; \
                     64-bit, wider, and zero-width multiplication remains fail-closed",
                    width.saturating_mul(2)
                ));
            }

            let wide_width = width * 2;
            let extend = |f: &Formula| {
                if signed {
                    Formula::BvSignExt(b(f.clone()), width)
                } else {
                    Formula::BvZeroExt(b(f.clone()), width)
                }
            };
            let exact = Formula::BvMul(b(extend(lhs)), b(extend(rhs)), wide_width);

            if signed {
                Formula::Not(b(Formula::Eq(
                    b(exact),
                    b(Formula::BvSignExt(b(wrapped.clone()), width)),
                )))
            } else {
                let high = Formula::BvExtract { inner: b(exact), high: wide_width - 1, low: width };
                Formula::Not(b(Formula::Eq(b(high), b(Formula::BitVec { value: 0, width }))))
            }
        }
    })
}

/// Which end of the signature a type sits at. The two ends are NOT symmetric for
/// `bool`, so the position has to be a parameter rather than an assumption.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SigPosition {
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
/// A bool PARAMETER is REFUSED HERE, and the reason is not symmetry-breaking
/// for its own sake. Its LIR carrier is `I8`; modeling it as an unconstrained
/// 32-bit value made the gate report REFUTED for six correct
/// `<bool as AsPrimitive<T>>::as_` functions in the 68-module corpus — a
/// fabricated miscompile. The `Zext` attribute above licenses a PRECONDITION on
/// the incoming register instead, which moves the gate from an unconditional
/// equality to one conditioned on a caller-side promise the gate cannot see
/// the caller keep. That precondition is modeled by ONE site only —
/// [`bind_bool_parameter`], the ROOT function's entry binding, under the
/// attested extension facts of the attached cross-check (WS7.13) — so this
/// width function, which also serves the stack-placement classifier and the
/// module-local callee binding (WS7.12), keeps refusing: a stack-passed bool
/// and a local callee's bool parameter are not modeled.
///
/// (rustc's ABI filter `scalar_register_abi_ty_supported`
/// (`compiler/rustc_codegen_trust_cg/src/lib.rs`) refuses ANY slot with
/// `arg_ext != None`; the F1 lane admits the bool RETURN through
/// `zext_bool_return_abi_supported` and, since WS7.13, the bool PARAMETER
/// through `zext_bool_param_abi_supported`, minting the extension facts this
/// gate consumes. Narrow integers are the opposite case: `arg_ext: None` means
/// they reach the F1 path with no extension contract at all — measured, a
/// `-> u8` function compiles and emits through `-Ztrust-cg-frontend=trust-ir`.)
pub(crate) fn signature_reg_width(
    module: &Module,
    ty: &IrTy,
    position: SigPosition,
) -> Result<u32, String> {
    if matches!(ty, IrTy::Bool) && position == SigPosition::Parameter {
        return Err(
            "`bool` in PARAMETER position: its carrier is an i8 the CALLER wrote, and the \
             `arg_ext: Zext` promise that makes it a 0/1 is modeled only for the ROOT function's \
             register-passed parameters under an attested cross-check (WS7.13) — a stack-passed \
             bool or a module-local callee's bool parameter is not modeled; an unconstrained \
             32-bit model of it fabricated six Refuted verdicts once already (fail-closed). A \
             bool RETURN is admitted: that one the callee itself owes."
                .to_string(),
        );
    }
    scalar_reg_width_in(module, ty)
}

/// The precondition width this gate models for a caller-extended `bool`: the
/// `W` register. Apple AArch64 makes the caller extend a small argument to 32
/// bits, and the machine side reads bools as 32-bit 0/1 carriers everywhere
/// else (`scalar_reg_width`), so this is the ONE width under which the
/// `W{k}[31:1] == 0` precondition and the rest of the interpreter agree.
const BOOL_CALLER_EXTENSION_BITS: u32 = 32;

/// WS7.13 — bind a ROOT-function `bool` parameter at register slot `slot` under
/// the caller-owed zero-extension precondition, or refuse by name.
///
/// Returns `(value, ambient)`: the spec value `zext32(X{slot}[0:0])` and the
/// AMBIENT precondition `X{slot}[31:1] == 0` — i.e. `W{slot}[31:1] == 0`, the
/// WHOLE extension width the target makes the caller owe, not merely bits 7:1.
/// A `[7:1]` precondition would leave bits 31:8 free, so emitted code that
/// tests the whole `w` register (`cbz w0`) would be "refuted" on an input with
/// bit 0 clear and bit 8 set — the fabricated-Refuted class this arm exists to
/// retire. The ambient is over the SHARED input variable both sides read, so it
/// conditions the machine formula exactly as it conditions the spec; it is
/// never a spec-side-only fact.
///
/// ADMISSION is by attested fact, never inferred: the cross-check must carry
/// [`crate::AbiParamExtensions`] stating `Zext` for THIS parameter index and
/// `caller_extends_to_bits == Some(32)`. Every other case is `Err` (the gate's
/// `Unknown`): no cross-check, no recorded extensions, an unrecorded slot, an
/// extension other than `Zext`, a target that makes no caller-side promise
/// (generic AAPCS64, where the callee may not assume the caller extended), or
/// a promise at a width this gate does not model.
fn bind_bool_parameter(
    index: usize,
    slot: u32,
    cross_check: Option<&crate::AbiPassModeCrossCheck>,
) -> Result<(Formula, Formula), String> {
    let refuse = |why: &str| -> String {
        format!(
            "`bool` in PARAMETER position (parameter {index}, register slot W{slot}): its \
             carrier is a register the CALLER wrote, and it is modeled only under the \
             caller-owed zero-extension precondition `W{slot}[31:1] == 0` that an attested \
             `arg_ext: Zext` cross-check licenses — {why}; an unconstrained 32-bit model of it \
             fabricated six Refuted verdicts once already (fail-closed)"
        )
    };
    let Some(cross_check) = cross_check else {
        return Err(refuse("no ABI pass-mode cross-check is attached"));
    };
    let Some(extensions) = cross_check.param_extensions() else {
        return Err(refuse("the attached cross-check records no parameter-extension facts"));
    };
    match extensions.extension_of(index) {
        Some(crate::AbiArgExtension::Zext) => {}
        Some(other) => {
            return Err(refuse(&format!(
                "the cross-check records `arg_ext: {other:?}` for this slot, not `Zext`"
            )));
        }
        None => {
            return Err(refuse("the cross-check records no extension for this slot"));
        }
    }
    match extensions.caller_extends_to_bits {
        Some(BOOL_CALLER_EXTENSION_BITS) => {}
        Some(bits) => {
            return Err(refuse(&format!(
                "the target makes the caller extend to {bits} bits, and only a \
                 {BOOL_CALLER_EXTENSION_BITS}-bit caller extension is modeled"
            )));
        }
        None => {
            return Err(refuse(
                "the target makes NO caller-side extension promise (the callee may not assume \
                 the caller extended, as on generic AAPCS64)",
            ));
        }
    }
    let bit0 = Formula::BvExtract { inner: b(xn(slot)), high: 0, low: 0 };
    let value = Formula::BvZeroExt(b(bit0), BOOL_CALLER_EXTENSION_BITS - 1);
    let ambient = Formula::Eq(
        b(Formula::BvExtract { inner: b(xn(slot)), high: BOOL_CALLER_EXTENSION_BITS - 1, low: 1 }),
        b(Formula::BitVec { value: 0, width: BOOL_CALLER_EXTENSION_BITS - 1 }),
    );
    Ok((value, ambient))
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
pub(crate) fn scalar_reg_width_in(module: &Module, ty: &IrTy) -> Result<u32, String> {
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
    ///
    /// With a non-empty `cut_points` (WS7.14) this is the ENTRY SEGMENT's
    /// return value only — the paths that return without entering a loop.
    /// It is NOT the function's semantics on its own: a consumer must also
    /// discharge every entry of `segments`, as the gate does.
    pub value: Formula,
    /// Conjunction of the IR's own `Inst::Assert` guards along each path
    /// (with cut points: along each path of the entry segment that returns).
    pub reach: Formula,
    /// Bit width the return value is read at.
    pub out_width: u32,
    /// Modeling preconditions to discharge from `reach` before using `value`.
    pub side_conditions: Vec<Formula>,
    /// AMBIENT machine-environment assumptions the obligation is conditioned
    /// on — the WELL-FORMED-STACK bounds a stack-passed argument needs (`SP`
    /// bounded away from both wrap edges, so the prologue's frame stores
    /// provably do not alias the caller's incoming-argument slots in array
    /// theory), and (WS7.13) the CALLER-OWED ZERO-EXTENSION `W{k}[31:1] == 0`
    /// of each attested `bool` parameter. Unlike `side_conditions` these are
    /// NOT discharged from `reach`: they are assumptions about the execution
    /// environment (AAPCS guarantees a valid stack; the ABI makes the caller
    /// extend a bool), spelled into BOTH obligations so the proof claim is
    /// "for every well-formed stack and every ABI-conforming caller", never an
    /// unconditional claim the wrap corner or a non-0/1 register would falsify.
    /// A non-empty list caps the verdict at `AyValidated`, and the vacuity
    /// firewall checks the list is jointly satisfiable with `reach`.
    pub ambient_pre: Vec<Formula>,
    /// CUT POINTS (WS7.14): the root function's loop headers, each with its
    /// shared variables. EMPTY for a loop-free function, in which case
    /// `value`/`reach` are the whole spec exactly as before and `segments` is
    /// the single entry segment.
    pub cut_points: Vec<SpecCutPoint>,
    /// The acyclic SEGMENTS of the spec: the entry segment first (its `value`
    /// and `reach` are the fields above), then one per cut point REACHED, in
    /// discovery order. A cut point no segment arrives at is dead code and has
    /// no segment.
    pub segments: Vec<SpecSegment>,
}

/// A cut point of the spec (WS7.14): a loop header and its SHARED VARIABLES —
/// every SSA value live into the header (its block params and every
/// dominating definition the loop reads), each bound on BOTH sides of the
/// obligation to the same symbolic name at the header's segment start.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SpecCutPoint {
    /// The header block (index of its `BlockId`).
    pub block: u32,
    /// The shared variables, block params first, then the other live-ins, each
    /// group sorted by value id.
    pub shared: Vec<SharedVar>,
}

/// One shared variable of a cut point (WS7.14).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SharedVar {
    /// The SSA value (index of its `ValueId`).
    pub value: u32,
    /// The symbolic name both sides bind it to at the segment start.
    pub name: String,
    /// Its declared width in bits.
    pub width: u32,
}

impl SharedVar {
    /// The symbolic variable itself.
    pub fn formula(&self) -> Formula {
        Formula::Var(self.name.clone(), Sort::BitVec(self.width))
    }
}

/// One acyclic segment of the spec (WS7.14): from the entry (`start: None`)
/// or from a cut point's fresh shared variables, to a return or to the next
/// cut point.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SpecSegment {
    /// The cut point this segment starts at, or `None` for the entry segment.
    pub start: Option<u32>,
    /// Return value on the paths that return.
    pub value: Formula,
    /// Under which inputs the segment returns.
    pub reach: Formula,
    /// The cut points the segment arrives at instead of returning.
    pub arrivals: Vec<SpecArrival>,
}

/// One arrival of a spec segment at a cut point (WS7.14).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SpecArrival {
    /// The header arrived at.
    pub block: u32,
    /// Under which inputs of the segment this arrival happens.
    pub reach: Formula,
    /// The header's shared variables on this edge, in `SpecCutPoint::shared`
    /// order.
    pub values: Vec<Formula>,
}

/// The backend's OWN placement of this signature's arguments, for the
/// stack-passed binding. Every parameter must be a scalar the register
/// fragment already models (widths 8/16/32/64) — a 128-bit or non-scalar
/// parameter in an overflowing signature stays fail-closed, so the register
/// slot accounting of the binding loop and the classifier's cannot diverge
/// on the shapes this is consulted for.
fn classify_stack_offsets(
    module: &Module,
    func_ty: &trust_ir::ty::FuncTy,
) -> Result<Vec<ArgLocation>, String> {
    let mut tys = Vec::with_capacity(func_ty.params.len());
    for p in &func_ty.params {
        // A `bool` takes one register slot as its byte-wide LIR carrier
        // (`module_to_lir::map_scalar_int_ty`: `Ty::Bool` -> `LirType::I8`),
        // so it is classified as an I8 here — placement only. Whether the
        // bool VALUE is modeled is decided by `bind_bool_parameter`, and a
        // stack-passed bool is refused there before this placement is read.
        if matches!(p, IrTy::Bool) {
            tys.push(ClassifierTy::I8);
            continue;
        }
        let width = signature_reg_width(module, p, SigPosition::Parameter)?;
        tys.push(match width {
            8 => ClassifierTy::I8,
            16 => ClassifierTy::I16,
            32 => ClassifierTy::I32,
            64 => ClassifierTy::I64,
            other => {
                return Err(format!(
                    "stack-argument placement is modeled for 8/16/32/64-bit scalars only \
                     (parameter width {other}; fail-closed)"
                ));
            }
        });
    }
    Ok(AppleAArch64ABI::classify_params_with(AArch64AbiVariant::Darwin, &tys))
}

/// Derive the intended-semantics Formula of `function`'s return value over the
/// AAPCS64 argument registers, plus the `spec_reach` predicate (the conjunction
/// of the IR's own `Inst::Assert` conditions along each path).
///
/// FAILS CLOSED (`Err`) on every shape outside the modeled fragment. The caller
/// reports that as `Unknown`, which the strict policy refuses.
///
/// This form carries NO ABI cross-check, so a `bool` parameter is refused
/// (see [`trust_ir_function_semantics_with`]).
pub fn trust_ir_function_semantics(
    module: &Module,
    func_id: FuncId,
) -> Result<SpecSemantics, String> {
    trust_ir_function_semantics_with(module, func_id, None)
}

/// [`trust_ir_function_semantics`] with the ABI pass-mode cross-check the
/// shipping path attached (WS7.13): its attested parameter-extension facts are
/// the ONLY thing that admits a `bool` parameter, and only for the ROOT
/// function's register-passed slots — see [`bind_bool_parameter`]. The
/// cross-check is consulted for nothing else here; `None` keeps every
/// pre-WS7.13 answer.
pub fn trust_ir_function_semantics_with(
    module: &Module,
    func_id: FuncId,
    cross_check: Option<&crate::AbiPassModeCrossCheck>,
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
    let mut stack_placements: Option<Result<Vec<ArgLocation>, String>> = None;
    let mut needs_stack_ambient = false;
    // WS7.13: the caller-owed zero-extension precondition of each attested
    // `bool` parameter, one per bool slot, in parameter order.
    let mut bool_ambient: Vec<Formula> = Vec::new();
    for (index, ((param_id, param_ty), sig_ty)) in
        entry.params.iter().zip(&func_ty.params).enumerate()
    {
        if param_ty != sig_ty {
            return Err(format!(
                "entry param {index} has type {param_ty:?} but the signature says {sig_ty:?}"
            ));
        }
        // A `bool` PARAMETER (WS7.13): admitted at a REGISTER slot only, under
        // the attested caller-owed zero-extension; see `bind_bool_parameter`.
        // A stack-passed bool is refused by name — the stack-argument binding
        // below reads the caller's outgoing slot at the declared width, and
        // what a caller owes ABOVE a stack-passed bool's byte is not modeled.
        if matches!(param_ty, IrTy::Bool) {
            if slot >= 8 {
                return Err(format!(
                    "`bool` in PARAMETER position (parameter {index}) is STACK-PASSED: the \
                     caller-owed extension is modeled for register slots only (fail-closed)"
                ));
            }
            let (f, ambient) = bind_bool_parameter(index, slot, cross_check)?;
            bool_ambient.push(ambient);
            env.insert(*param_id, IrValue { f, width: BOOL_CALLER_EXTENSION_BITS });
            slot += 1;
            continue;
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
                // STACK-PASSED scalar argument. The AArch64 backend places it
                // via `AppleAArch64ABI::classify_params_with` (DarwinPCS packs
                // narrow fixed args at natural size/alignment), and the callee
                // loads it from the caller's outgoing area at [SP0 + offset] —
                // SP0 being the symbolic entry stack pointer the machine
                // walker seeds (`Var("SP")`). Binding the spec parameter to
                // the SAME little-endian byte read of the SAME initial memory
                // makes the two sides one term, exactly as the register
                // binding above is one term with `read_gpr`. The offsets come
                // from the CLASSIFIER ITSELF (single source of truth), never
                // re-derived here; any disagreement between this loop's slot
                // accounting and the classifier fails closed.
                let placement =
                    stack_placements.get_or_insert_with(|| classify_stack_offsets(module, func_ty));
                let placement = placement.as_ref().map_err(|e| e.clone())?;
                let Some(ArgLocation::Stack { offset, .. }) = placement.get(index).cloned() else {
                    return Err(format!(
                        "argument {index} overflowed the 8 GPR slots but the ABI classifier \
                         did not place it on the stack; refusing to guess (fail-closed)"
                    ));
                };
                let addr = Formula::BvAdd(
                    b(Formula::Var("SP".into(), Sort::BitVec(64))),
                    b(Formula::BitVec { value: offset as i128, width: 64 }),
                    64,
                );
                let mem0 = crate::verify_output::mem_array_var();
                let f =
                    crate::verify_output::load_bytes_le_formula(&mem0, &addr, width.div_ceil(8));
                needs_stack_ambient = true;
                env.insert(*param_id, IrValue { f, width });
                continue;
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

    // The well-formed-stack ambient assumptions (see `SpecSemantics::
    // ambient_pre`): SP0 at least 1 MiB from either wrap edge, so the frame's
    // own stores (at SP0 - frame) and the incoming argument slots (at
    // SP0 + offset) are provably distinct addresses in array theory. Every
    // real AAPCS stack satisfies this by orders of magnitude.
    let mut ambient_pre: Vec<Formula> = if needs_stack_ambient {
        let mib = 1_i128 << 20;
        vec![
            // SP >= 2^20  ==  NOT (SP < 2^20)
            Formula::Not(b(Formula::BvULt(
                b(Formula::Var("SP".into(), Sort::BitVec(64))),
                b(Formula::BitVec { value: mib, width: 64 }),
                64,
            ))),
            // SP < 2^64 - 2^20
            Formula::BvULt(
                b(Formula::Var("SP".into(), Sort::BitVec(64))),
                b(Formula::BitVec { value: (u64::MAX as i128) - mib, width: 64 }),
                64,
            ),
        ]
    } else {
        Vec::new()
    };
    // The bool preconditions follow the stack bounds, so a reader of the
    // assumption list sees the environment facts first and the per-caller
    // ABI promises after them.
    ambient_pre.extend(bool_ambient);

    let mut visited = Vec::new();
    // The root function is SEEDED onto the call stack, so a direct self-call is
    // recursion by the same rule a `f -> g -> f` cycle is (see `eval_ir_call`).
    let mut ev = SpecEval::new(func_id);

    // CUT POINTS (WS7.14). The root function's loop headers, each with its
    // shared-variable list (block params first, then the other live-ins).
    // An irreducible CFG is refused here by name. A loop-free function has
    // none, and everything below then reduces to the single entry segment.
    let headers = loop_headers(&blocks, function.entry.index())?;
    if !headers.is_empty() {
        let live = live_in_sets(&blocks).ok_or_else(|| {
            "loop live-in analysis could not be completed exactly (fail-closed)".to_string()
        })?;
        for h in &headers {
            let blk = blocks.get(h).ok_or_else(|| format!("bb{h} missing"))?;
            let mut shared: Vec<ValueId> = blk.params.iter().map(|(p, _)| *p).collect();
            shared.sort_by_key(|v| v.index());
            let mut others: Vec<ValueId> = live
                .get(h)
                .ok_or_else(|| format!("bb{h} has no live-in set"))?
                .iter()
                .copied()
                .filter(|v| !shared.contains(v))
                .collect();
            others.sort_by_key(|v| v.index());
            shared.extend(others);
            ev.shared.insert(*h, shared);
        }
    }

    let entry_outcome = eval_ir_block(
        module,
        func_id,
        &blocks,
        function.entry,
        &env,
        &mut visited,
        0,
        out_width,
        &mut ev,
    )?;

    // SEGMENTS. The entry segment first; then, in discovery order, one per
    // cut point some segment arrives at. A header's shared variables get
    // their widths from the FIRST arrival (every arrival must agree — SSA
    // gives each value one type) and are then bound to fresh symbolic
    // variables named `CUT_bb{H}_v{id}` on both sides of the obligation.
    let mut cut_points: Vec<SpecCutPoint> = Vec::new();
    let mut segments: Vec<SpecSegment> = Vec::new();
    let mut pending: Vec<IrArrival> = entry_outcome.arrivals.clone();
    segments.push(spec_segment(None, &entry_outcome, &mut cut_points, &ev)?);
    let mut done: Vec<u32> = Vec::new();
    while let Some(arrival) = pending.pop() {
        if done.contains(&arrival.block) {
            continue;
        }
        done.push(arrival.block);
        let shared_ids = ev
            .shared
            .get(&arrival.block)
            .ok_or_else(|| format!("arrival at bb{} which is not a cut point", arrival.block))?
            .clone();
        let cut = cut_point_for(&arrival, &shared_ids, &cut_points)?;
        let mut seg_env: HashMap<ValueId, IrValue> = HashMap::new();
        for sv in &cut.shared {
            seg_env.insert(ValueId::new(sv.value), IrValue { f: sv.formula(), width: sv.width });
        }
        let header = BlockId::new(arrival.block);
        let mut seg_visited = Vec::new();
        let outcome = eval_ir_block(
            module,
            func_id,
            &blocks,
            header,
            &seg_env,
            &mut seg_visited,
            0,
            out_width,
            &mut ev,
        )?;
        pending.extend(outcome.arrivals.iter().cloned());
        segments.push(spec_segment(Some(arrival.block), &outcome, &mut cut_points, &ev)?);
    }
    // Every header a segment arrives at got its cut point; sort them by block
    // for a stable record.
    cut_points.sort_by_key(|c| c.block);

    Ok(SpecSemantics {
        value: entry_outcome.value,
        reach: entry_outcome.reach,
        out_width,
        side_conditions: ev.side,
        ambient_pre,
        cut_points,
        segments,
    })
}

/// The `SpecCutPoint` record for `arrival.block`, minted from this arrival's
/// value widths on first sight and checked against it afterwards.
fn cut_point_for(
    arrival: &IrArrival,
    shared_ids: &[ValueId],
    cut_points: &[SpecCutPoint],
) -> Result<SpecCutPoint, String> {
    if let Some(existing) = cut_points.iter().find(|c| c.block == arrival.block) {
        return Ok(existing.clone());
    }
    if arrival.values.len() != shared_ids.len() {
        return Err(format!(
            "arrival at bb{} carries {} value(s) for {} shared variable(s) (fail-closed)",
            arrival.block,
            arrival.values.len(),
            shared_ids.len()
        ));
    }
    Ok(SpecCutPoint {
        block: arrival.block,
        shared: shared_ids
            .iter()
            .zip(&arrival.values)
            .map(|(v, iv)| SharedVar {
                value: v.index(),
                name: format!("CUT_bb{}_v{}", arrival.block, v.index()),
                width: iv.width,
            })
            .collect(),
    })
}

/// Project an evaluated segment into its `SpecSegment` record, minting the
/// cut-point records of the headers it arrives at (their widths come from
/// the arrival) and checking every later arrival against the minted widths.
fn spec_segment(
    start: Option<u32>,
    outcome: &IrOutcome,
    cut_points: &mut Vec<SpecCutPoint>,
    ev: &SpecEval,
) -> Result<SpecSegment, String> {
    let mut arrivals = Vec::with_capacity(outcome.arrivals.len());
    for a in &outcome.arrivals {
        let shared_ids = ev
            .shared
            .get(&a.block)
            .ok_or_else(|| format!("arrival at bb{} which is not a cut point", a.block))?;
        let cut = cut_point_for(a, shared_ids, cut_points)?;
        for (sv, iv) in cut.shared.iter().zip(&a.values) {
            if sv.width != iv.width {
                return Err(format!(
                    "loop header bb{} live-in %{} arrives as {}-bit here but {}-bit elsewhere \
                     (fail-closed)",
                    a.block, sv.value, iv.width, sv.width
                ));
            }
        }
        if !cut_points.iter().any(|c| c.block == cut.block) {
            cut_points.push(cut);
        }
        arrivals.push(SpecArrival {
            block: a.block,
            reach: a.reach.clone(),
            values: a.values.iter().map(|v| v.f.clone()).collect(),
        });
    }
    Ok(SpecSegment { start, value: outcome.value.clone(), reach: outcome.reach.clone(), arrivals })
}

/// Evaluate block `id` under `env`, returning the reachable return-value Formula
/// and the accumulated assert guard. Branches merge as `Ite` over the branch
/// condition, mirroring the machine-side path merger.
///
/// Reconverging control flow is evaluated ONCE per distinct incoming
/// environment slice, not once per path — see the DAG-EVALUATION note above
/// `modeled_operands` for the memo key and why it is sound.
///
/// `func` is the function `blocks` belongs to. It is NOT decoration: a
/// module-local `Inst::Call` evaluates the CALLEE's own blocks (WS7.12), and
/// block ids are per-function, so `bb0` of the caller and `bb0` of the callee
/// are different blocks that must never share a memo entry or collide in the
/// backedge `visited` set. Both are therefore keyed on `(func, block)`.
#[allow(clippy::too_many_arguments)]
fn eval_ir_block(
    module: &Module,
    func: FuncId,
    blocks: &HashMap<u32, &trust_ir::Block>,
    id: BlockId,
    env: &HashMap<ValueId, IrValue>,
    visited: &mut Vec<(u32, u32)>,
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
    let site = (func.index(), id.index());
    let memo_key = ev.key_for(func, blocks, id.index(), env);
    if let Some(key) = &memo_key {
        if let Some(hit) =
            ev.memo.get(&site).and_then(|entries| entries.iter().find(|e| e.key == *key))
        {
            return Ok(IrOutcome {
                value: hit.value.clone(),
                reach: hit.reach.clone(),
                ok: hit.ok.clone(),
                arrivals: hit.arrivals.clone(),
            });
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

    // A block already on this path is a backedge that no cut point caught:
    // a loop inside a CALLEE (cut points are the root's only, WS7.14), or a
    // header the cut-point set does not carry. Refused, never unrolled.
    if visited.contains(&site) {
        return Err(format!("loop/backedge at bb{} (fail-closed)", id.index()));
    }
    visited.push(site);

    let block = blocks
        .get(&id.index())
        .ok_or_else(|| format!("branch to bb{} which the function lacks", id.index()))?;

    let mut env = env.clone();
    // Assert conditions collected in THIS block, in order.
    let mut guards: Vec<Formula> = Vec::new();
    // The same block, read for `IrOutcome::ok`: each check, and each call with
    // its callee's `(ok, reach)`, in order.
    let mut checks: Vec<(Formula, Option<Formula>)> = Vec::new();

    let Some((terminator, body)) = block.body.split_last() else {
        return Err(format!("bb{} is empty (fail-closed)", id.index()));
    };

    let mut slots = LocalSlots::default();

    for node in body {
        if let Some(step) = slots.step(module, func, blocks, id.index(), &mut env, node) {
            step?;
            continue;
        }
        match &node.inst {
            // A sited assert (trust-ir v54) calls its entry on failure, which
            // this model does not: it falls to `eval_ir_inst`, which refuses
            // it as outside the modeled fragment. The kind (v52) names the
            // panic, not whether the check fails.
            Inst::Assert { cond, kind: _, site: None } => {
                let c = lookup(&env, *cond)?;
                let g = Formula::Not(b(Formula::Eq(
                    b(c.f.clone()),
                    b(Formula::BitVec { value: 0, width: c.width }),
                )));
                checks.push((g.clone(), None));
                guards.push(g);
            }
            // CHECKED ARITHMETIC is the one modeled instruction that binds TWO
            // results, so it cannot go through the single-result path below.
            // `results[0]` is the wrapping value, `results[1]` the overflow flag
            // — a `bool` SSA value, hence the same 0/1-at-32-bits carrier an
            // `Inst::ICmp` result gets, because that is what it is fed to.
            Inst::Overflow { op, ty, lhs, rhs } => {
                for (id, value) in eval_ir_overflow(&env, &node.inst, *op, ty, *lhs, *rhs, &node.results)? {
                    env.insert(id, value);
                }
            }
            // MODULE-LOCAL CALL (WS7.12). Like `Inst::Overflow` this cannot go
            // through the single-value `eval_ir_inst` path, for two reasons:
            // it evaluates a DIFFERENT function's CFG (so it needs `blocks`,
            // `depth` and the shared evaluator state), and it contributes to
            // the caller's `reach` as well as to its environment.
            //
            // THE SPEC IS STILL NEVER DERIVED FROM THE LOWERING (file header,
            // "THE SPEC IS NEVER DERIVED FROM THE LOWERING"). The callee's
            // semantics are read from the callee's OWN trust-ir body, exactly
            // as the caller's are; `inline_local_pure_leaf_calls` is not
            // consulted and its splice is not trusted. A splice that binds the
            // wrong argument, drops a callee guard, or routes the wrong result
            // therefore shows up as a disagreement — which is the whole point
            // of the gate.
            Inst::Call { callee, args } => {
                let (value, reach, ok) = eval_ir_call(module, *callee, args, &env, depth, ev)?;
                let [result] = node.results.as_slice() else {
                    return Err(format!(
                        "`call` binds {} result(s); the modeled fragment is single-result \
                         (fail-closed)",
                        node.results.len()
                    ));
                };
                // THE CALLEE'S GUARDS BECOME THE CALLER'S. A callee `Assert`
                // that fails traps, and the trap is taken on THIS path — which
                // is precisely what the inliner's splice does on the machine
                // side, so conjoining the callee's `reach` here keeps the two
                // sides talking about the same set of returning inputs. The
                // vacuity firewall in `discharge_trust_ir_obligation` runs over
                // the conjunction, so a callee that can never return still
                // yields `Unknown`, never `Proven`.
                checks.push((ok, Some(reach.clone())));
                if !matches!(reach, Formula::Bool(true)) {
                    guards.push(reach);
                }
                env.insert(*result, value);
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

    let outcome = eval_ir_terminator(
        module,
        func,
        blocks,
        terminator,
        &env,
        &visited[..],
        depth,
        out_width,
        ev,
    )?;
    // THIS BLOCK'S GUARDS CONDITION EVERY WAY OUT OF IT — the return AND each
    // cut-point arrival (WS7.14): a failed `Assert` traps before the latch is
    // taken exactly as it traps before the `ret`.
    let reach = conjoin(guards.clone(), outcome.reach);
    // No check fails from here: a failing check is a failure whatever follows
    // it, and after a call only the callee's normal return continues (a callee
    // that reached `Unreachable` is undefined behaviour, not a failure).
    let mut ok = outcome.ok;
    for (check, call_reach) in checks.into_iter().rev() {
        ok = match call_reach {
            None => conjoin(vec![check], ok),
            Some(r) if matches!(r, Formula::Bool(true)) || matches!(ok, Formula::Bool(true)) => {
                conjoin(vec![check], ok)
            }
            Some(r) => conjoin(vec![check], Formula::Or(vec![Formula::Not(b(r)), ok])),
        };
    }
    let arrivals: Vec<IrArrival> = outcome
        .arrivals
        .into_iter()
        .map(|a| IrArrival {
            block: a.block,
            reach: conjoin(guards.clone(), a.reach),
            values: a.values,
        })
        .collect();

    // Record ONLY a successful evaluation. An `Err` path is never memoized, so
    // a later visit re-derives it (and gets the same precise diagnostic).
    if let Some(key) = memo_key {
        ev.memo.entry(site).or_default().push(MemoEntry {
            key,
            value: outcome.value.clone(),
            reach: reach.clone(),
            ok: ok.clone(),
            arrivals: arrivals.clone(),
        });
    }
    Ok(IrOutcome { value: outcome.value, reach, ok, arrivals })
}

/// Admit `slot`, the result of an `Alloca { ty, count, align }` in block `home`,
/// as a BLOCK-LOCAL SLOT, or refuse it.
///
/// An admitted slot is modeled as what it is in trust-ir's semantics: a fresh
/// cell that a `Store` writes and a `Load` reads. No value is ever read from
/// memory the evaluator does not model, so the slot needs no memory model:
///
///   * Its type is a scalar of the modeled fragment, neither a pointer nor 128
///     bits wide, and it has no `count` and no explicit `align` (so it is
///     naturally aligned, as trust-ir reads `align: None`). One cell of one
///     type means the bytes a load reads are exactly the bytes the latest store
///     wrote.
///   * Every use of `slot` in the WHOLE function (by `Inst`'s exhaustive operand
///     walk, terminators included) is the `ptr` operand of a non-volatile `Load`
///     or `Store` of exactly `ty` with no explicit `align`, in `home`, and never
///     the stored value. So the address never escapes: no call, GEP, cast,
///     store-as-value, block argument or return sees it, and no other block
///     reads or writes the cell. Within one block the evaluator visits the
///     accesses in program order, so the cell's value at each `Load` is the
///     latest `Store` before it.
///   * Each stored value's DECLARED SSA type is the slot's type
///     ([`LocalSlots::step`]), as trust-ir's `eval_store` requires; a
///     same-width value of another type (a `u32` into a `bool` slot, a pointer
///     into a `u64` slot) is refused, not reinterpreted.
///   * A `Load` before any `Store` reads an uninitialized cell, which trust-ir
///     makes poison; the evaluator refuses it rather than give it a value.
///
/// Anything else is refused, fail-closed, as `Alloca` was before.
///
/// Both spec evaluators (this file's `eval_ir_block` and the call-event gate's
/// `SpecCx::block`) model slots through [`LocalSlots::step`], so they agree.
fn admit_local_slot(
    blocks: &HashMap<u32, &trust_ir::Block>,
    home: u32,
    slot: ValueId,
    ty: &IrTy,
    count: Option<&ValueId>,
    align: Option<u64>,
) -> Result<(), String> {
    let refuse = |why: &str| {
        Err(format!("`Alloca` %{} is not a block-local slot: {why} (fail-closed)", slot.index()))
    };
    if count.is_some() || align.is_some() {
        return refuse("it has a count or an explicit alignment");
    }
    reject_ptr_compute(ty, "slot")?;
    reject_width_128(scalar_reg_width(ty)?, "slot")?;
    // In block order, so a refusal names the same use on every run.
    let mut order: Vec<(&u32, &&trust_ir::Block)> = blocks.iter().collect();
    order.sort_by_key(|(bid, _)| **bid);
    for (bid, blk) in order {
        for node in &blk.body {
            if !node.inst.uses_value(slot) {
                continue;
            }
            if *bid != home {
                return refuse(&format!("bb{bid} uses it"));
            }
            let admitted = match &node.inst {
                // A `Load`'s only SSA operand is its address, so `*ptr == slot`
                // holds whenever `uses_value` led here; it guards a future
                // operand.
                Inst::Load { ty: t, ptr, volatile: false, align: None } => *ptr == slot && t == ty,
                Inst::Store { ty: t, ptr, value, volatile: false, align: None } => {
                    *ptr == slot && *value != slot && t == ty
                }
                _ => false,
            };
            if !admitted {
                return refuse(&format!(
                    "`{}` uses it other than as the address of a plain load or store of its type",
                    inst_label(&node.inst)
                ));
            }
        }
    }
    Ok(())
}

/// One block evaluation's BLOCK-LOCAL SLOTS (see [`admit_local_slot`]): each
/// `Alloca` the block defines, with the value its latest `Store` wrote (`None`
/// until the first one). Each evaluator builds a new `LocalSlots` per
/// evaluation of a block: that is a fresh cell per execution of its `alloca`,
/// as trust-ir's semantics has it, and it keeps a caller's slots apart from an
/// inlined callee's, whose `ValueId`s may coincide. An `Alloca` stepped again
/// on the same `LocalSlots` also resets its cell.
#[derive(Default)]
pub(crate) struct LocalSlots {
    cells: HashMap<ValueId, Option<IrValue>>,
    /// The function's declared SSA types, read once on the first slot store.
    declared: Option<HashMap<ValueId, IrTy>>,
}

impl LocalSlots {
    /// Evaluate `node` (in block `home` of function `func` of `module`, whose
    /// blocks are `blocks`) if it is a slot instruction: every `Alloca`,
    /// admitted or refused, and a `Load` or `Store` whose address is an
    /// admitted slot. `None` leaves `node` to the caller; any other `Load` or
    /// `Store` is not touched here.
    pub(crate) fn step(
        &mut self,
        module: &Module,
        func: FuncId,
        blocks: &HashMap<u32, &trust_ir::Block>,
        home: u32,
        env: &mut HashMap<ValueId, IrValue>,
        node: &trust_ir::node::InstrNode,
    ) -> Option<Result<(), String>> {
        match &node.inst {
            Inst::Alloca { ty, count, align } => {
                Some(self.alloca(blocks, home, node, ty, count.as_ref(), *align))
            }
            Inst::Store { ty, ptr, value, .. } if self.cells.contains_key(ptr) => {
                Some(self.store(module, func, env, node, ty, *ptr, *value))
            }
            Inst::Load { ty, ptr, .. } if self.cells.contains_key(ptr) => {
                Some(self.load(env, node, ty, *ptr))
            }
            _ => None,
        }
    }

    fn alloca(
        &mut self,
        blocks: &HashMap<u32, &trust_ir::Block>,
        home: u32,
        node: &trust_ir::node::InstrNode,
        ty: &IrTy,
        count: Option<&ValueId>,
        align: Option<u64>,
    ) -> Result<(), String> {
        let [slot] = node.results.as_slice() else {
            return Err(format!("`alloca` binds {} results (fail-closed)", node.results.len()));
        };
        admit_local_slot(blocks, home, *slot, ty, count, align)?;
        self.cells.insert(*slot, None);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn store(
        &mut self,
        module: &Module,
        func: FuncId,
        env: &HashMap<ValueId, IrValue>,
        node: &trust_ir::node::InstrNode,
        ty: &IrTy,
        ptr: ValueId,
        value: ValueId,
    ) -> Result<(), String> {
        if !node.results.is_empty() {
            return Err("`store` binds a result (fail-closed)".into());
        }
        if self.declared.is_none() {
            let function = module
                .function_by_id(func)
                .ok_or("slot store in a function the module lacks (fail-closed)")?;
            self.declared = Some(
                function.typed_values(module).into_iter().map(|m| (m.value, m.ty)).collect(),
            );
        }
        let declared = self.declared.as_ref().and_then(|types| types.get(&value));
        if declared != Some(ty) {
            return Err(format!(
                "store to slot %{} of %{} declared {declared:?}, not the slot's type {ty:?} \
                 (fail-closed)",
                ptr.index(),
                value.index()
            ));
        }
        let width = scalar_reg_width(ty)?;
        let f = operand_at(env, value, width)?;
        self.cells.insert(ptr, Some(IrValue { f, width }));
        Ok(())
    }

    fn load(
        &self,
        env: &mut HashMap<ValueId, IrValue>,
        node: &trust_ir::node::InstrNode,
        ty: &IrTy,
        ptr: ValueId,
    ) -> Result<(), String> {
        let [result] = node.results.as_slice() else {
            return Err(format!("`load` binds {} results (fail-closed)", node.results.len()));
        };
        let Some(Some(v)) = self.cells.get(&ptr) else {
            return Err(format!(
                "load of slot %{} before any store to it: the slot is uninitialized \
                 (fail-closed)",
                ptr.index()
            ));
        };
        if v.width != scalar_reg_width(ty)? {
            return Err(format!(
                "load of slot %{} at a width its store did not write (fail-closed)",
                ptr.index()
            ));
        }
        env.insert(*result, v.clone());
        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
fn eval_ir_terminator(
    module: &Module,
    func: FuncId,
    blocks: &HashMap<u32, &trust_ir::Block>,
    node: &trust_ir::node::InstrNode,
    env: &HashMap<ValueId, IrValue>,
    visited: &[(u32, u32)],
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
            Ok(IrOutcome {
                value: value.f,
                reach: Formula::Bool(true),
                ok: Formula::Bool(true),
                arrivals: Vec::new(),
            })
        }
        // A diverging terminator: this path yields no return value at all. Its
        // `reach` is FALSE, exactly as the machine side reports for the `brk`
        // tail it lowers to.
        Inst::Unreachable => Ok(IrOutcome {
            value: Formula::BitVec { value: 0, width: out_width },
            reach: Formula::Bool(false),
            // Undefined behaviour, not a failed check.
            ok: Formula::Bool(true),
            arrivals: Vec::new(),
        }),
        Inst::Br { target, args } => {
            enter_block(module, func, blocks, *target, args, env, visited, depth, out_width, ev)
        }
        Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
            let c = lookup(env, *cond)?;
            let taken = Formula::Not(b(Formula::Eq(
                b(c.f.clone()),
                b(Formula::BitVec { value: 0, width: c.width }),
            )));
            let t = enter_block(
                module,
                func,
                blocks,
                *then_target,
                then_args,
                env,
                visited,
                depth,
                out_width,
                ev,
            )?;
            let e = enter_block(
                module,
                func,
                blocks,
                *else_target,
                else_args,
                env,
                visited,
                depth,
                out_width,
                ev,
            )?;
            let arrivals = if t.arrivals.is_empty() && e.arrivals.is_empty() {
                Vec::new()
            } else {
                merge_ir_arrivals(&taken, t.arrivals, e.arrivals)
            };
            Ok(IrOutcome {
                value: Formula::Ite(b(taken.clone()), b(t.value), b(e.value)),
                reach: merge_reach(taken.clone(), t.reach, e.reach),
                ok: merge_reach(taken, t.ok, e.ok),
                arrivals,
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
            let mut acc = enter_block(
                module,
                func,
                blocks,
                *default,
                default_args,
                env,
                visited,
                depth,
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
                let arm = enter_block(
                    module,
                    func,
                    blocks,
                    case.target,
                    &case.args,
                    env,
                    visited,
                    depth,
                    out_width,
                    ev,
                )?;
                let arrivals = if arm.arrivals.is_empty() && acc.arrivals.is_empty() {
                    Vec::new()
                } else {
                    merge_ir_arrivals(&is_case, arm.arrivals, acc.arrivals)
                };
                acc = IrOutcome {
                    value: Formula::Ite(b(is_case.clone()), b(arm.value), b(acc.value)),
                    reach: merge_reach(is_case.clone(), arm.reach, acc.reach),
                    ok: merge_reach(is_case, arm.ok, acc.ok),
                    arrivals,
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

/// Take the CFG edge to `target` with `args`: bind the edge, then either
/// ARRIVE (when `target` is a cut point of the root function — WS7.14) or
/// evaluate the block.
///
/// An arrival is the whole content of cut-point simulation on the spec side:
/// instead of following the edge into the loop header (which the per-path
/// `visited` set would refuse as a backedge on the way round), the segment
/// ends here with the header's shared variables as they stand on this edge.
/// The header's own body is evaluated ONCE, as its own segment, from fresh
/// symbolic shared variables (`trust_ir_function_semantics_with`).
#[allow(clippy::too_many_arguments)]
fn enter_block(
    module: &Module,
    func: FuncId,
    blocks: &HashMap<u32, &trust_ir::Block>,
    target: BlockId,
    args: &[ValueId],
    env: &HashMap<ValueId, IrValue>,
    visited: &[(u32, u32)],
    depth: u32,
    out_width: u32,
    ev: &mut SpecEval,
) -> Result<IrOutcome, String> {
    let next = bind_block_args(module, blocks, target, args, env)?;
    if func == ev.root
        && let Some(shared) = ev.shared.get(&target.index())
    {
        let mut values = Vec::with_capacity(shared.len());
        for v in shared {
            values.push(lookup(&next, *v).map_err(|e| {
                format!(
                    "live-in of loop header bb{} on the edge from this block: {e}",
                    target.index()
                )
            })?);
        }
        return Ok(IrOutcome {
            value: Formula::BitVec { value: 0, width: out_width },
            reach: Formula::Bool(false),
            // The loop body after the header is not evaluated on this path, so
            // nothing here says no check fails in it.
            ok: Formula::Bool(false),
            arrivals: vec![IrArrival { block: target.index(), reach: Formula::Bool(true), values }],
        });
    }
    let mut fork = visited.to_vec();
    eval_ir_block(module, func, blocks, target, &next, &mut fork, depth + 1, out_width, ev)
}

/// Bind a branch edge's arguments to the target block's parameters.
pub(crate) fn bind_block_args(
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

/// Evaluate a MODULE-LOCAL `Inst::Call` into the callee's returned value and
/// the callee's own `reach` predicate (WS7.12).
///
/// WHAT THIS IS AND IS NOT. It is the CALLEE's trust-ir, interpreted by the
/// same evaluator that derives the caller's spec, with the callee's entry-block
/// parameters bound to the caller's argument formulas. It is NOT a reading of
/// what `inline_local_pure_leaf_calls` spliced into the caller: the inliner is
/// the thing under test on the machine side, and deriving the spec from it
/// would make the obligation a tautology (file header, `:24-28`).
///
/// FAIL-CLOSED ADMISSION — every one of these is `Err`, i.e. `Unknown`:
///   * a NON-LOCAL callee (no `Function` in this `Module`): there is no IR to
///     read, and the machine side would carry a real `bl` this gate does not
///     compose. `Inst::CallIndirect` never reaches here at all — it has no
///     `FuncId`, so `eval_ir_inst`'s fallback refuses it by name.
///   * a BODY-LESS declaration, for the same reason.
///   * a `Producer::Clean` callee. The refusal names
///     `CleanOriginBelowCodegenGate`, the same gate
///     `module_to_lir::inline_local_pure_leaf_calls_one_pass` states by name,
///     because a Clean row's carrier faithfulness is not established below
///     tier `gate`. WS7.15 replaces this with the shared `admit_clean_body`
///     predicate; until then the gate refuses every Clean callee, so it can
///     never be the gate that first admits one.
///   * RECURSION: a callee already on the evaluation call stack (direct or
///     mutual). The interpreter has no fixed-point machinery, and unrolling a
///     recursive call to the budget would model a DIFFERENT function.
///   * a call NESTING deeper than [`MAX_IR_CALL_DEPTH`].
///   * a callee whose signature is variadic, or does not return exactly one
///     value, or whose entry block does not bind its declared parameters.
///
/// The work budget ([`MAX_IR_BLOCK_EVALS`]) and the side-condition list are
/// SHARED with the caller through `ev`, so a call cannot buy itself a fresh
/// allowance and a callee's narrow-shift precondition is discharged with the
/// caller's.
fn eval_ir_call(
    module: &Module,
    callee: FuncId,
    args: &[ValueId],
    env: &HashMap<ValueId, IrValue>,
    depth: u32,
    ev: &mut SpecEval,
) -> Result<(IrValue, Formula, Formula), String> {
    let function = module.function_by_id(callee).ok_or_else(|| {
        format!(
            "call to function id {} which this module does not define: a non-local callee has \
             no trust-ir body the gate could read, and the emitted `bl` is not composed here \
             (fail-closed)",
            callee.index()
        )
    })?;
    if function.blocks.is_empty() {
        return Err(format!(
            "callee `{}` is a body-less declaration: there is no trust-ir to derive a \
             specification from (fail-closed)",
            function.name
        ));
    }
    // Trust: the affirmative producer gate, stated here by the SAME name the
    // converter states it by (`ModuleLirError::CleanOriginBelowCodegenGate`).
    if function.producer == Some(trust_ir::Producer::Clean) {
        return Err(format!(
            "callee `{}` is a Clean-origin trust-ir function and is not admitted to codegen \
             (CleanOriginBelowCodegenGate): the proven-output gate refuses every \
             `Producer::Clean` body fail-closed, so it can never be the component that first \
             admits one (fail-closed)",
            function.name
        ));
    }
    if ev.call_stack.contains(&callee) {
        return Err(format!(
            "recursive call to `{}` (it is already on the evaluation call stack): the gate's \
             interpreter has no fixed point for it, and unrolling to the budget would model a \
             different function (fail-closed)",
            function.name
        ));
    }
    if ev.call_stack.len() > MAX_IR_CALL_DEPTH {
        return Err(format!(
            "call nesting deeper than {MAX_IR_CALL_DEPTH} at `{}` (fail-closed)",
            function.name
        ));
    }

    let func_ty = module
        .func_types
        .get(function.ty.as_usize())
        .ok_or_else(|| format!("callee `{}` names a FuncTy the module lacks", function.name))?;
    if func_ty.is_vararg {
        return Err(format!(
            "callee `{}` is variadic, which is outside the modeled fragment (fail-closed)",
            function.name
        ));
    }
    if func_ty.returns.len() != 1 {
        return Err(format!(
            "callee `{}` returns {} value(s); exactly 1 is modeled (fail-closed)",
            function.name,
            func_ty.returns.len()
        ));
    }
    let out_width = signature_reg_width(module, &func_ty.returns[0], SigPosition::Return)?;

    let blocks: HashMap<u32, &trust_ir::Block> =
        function.blocks.iter().map(|blk| (blk.id.index(), blk)).collect();
    let entry = blocks
        .get(&function.entry.index())
        .ok_or_else(|| format!("callee `{}` has no entry block", function.name))?;
    if entry.params.len() != func_ty.params.len() {
        return Err(format!(
            "callee `{}`'s entry block binds {} param(s) but its signature declares {} \
             (fail-closed)",
            function.name,
            entry.params.len(),
            func_ty.params.len()
        ));
    }
    if args.len() != func_ty.params.len() {
        return Err(format!(
            "call to `{}` passes {} arg(s) for {} declared param(s) (fail-closed)",
            function.name,
            args.len(),
            func_ty.params.len()
        ));
    }

    // A FRESH ENVIRONMENT. The callee is a different SSA namespace: reusing the
    // caller's map would let a callee `%3` read the caller's `%3`, which is a
    // silently wrong spec rather than a refusal.
    let mut callee_env: HashMap<ValueId, IrValue> = HashMap::new();
    for (index, (((param_id, param_ty), sig_ty), arg)) in
        entry.params.iter().zip(&func_ty.params).zip(args).enumerate()
    {
        if param_ty != sig_ty {
            return Err(format!(
                "callee `{}` entry param {index} has type {param_ty:?} but its signature says \
                 {sig_ty:?}",
                function.name
            ));
        }
        let width = signature_reg_width(module, param_ty, SigPosition::Parameter)?;
        let value = lookup(env, *arg)?;
        if value.width != width {
            return Err(format!(
                "call to `{}` passes a {}-bit value into a {width}-bit param {index} \
                 (fail-closed)",
                function.name, value.width
            ));
        }
        callee_env.insert(*param_id, IrValue { f: value.f, width });
    }

    ev.call_stack.push(callee);
    // A FRESH `visited`: the callee's blocks are its own, and the `(func,
    // block)` keying above already keeps the two namespaces apart. Call CYCLES
    // are caught by `call_stack`, not by this.
    let mut visited = Vec::new();
    let outcome = eval_ir_block(
        module,
        callee,
        &blocks,
        function.entry,
        &callee_env,
        &mut visited,
        depth + 1,
        out_width,
        ev,
    );
    ev.call_stack.pop();
    let outcome = outcome?;
    Ok((IrValue { f: outcome.value, width: out_width }, outcome.reach, outcome.ok))
}

/// Trust (increment 5, step 5.2): interpret a call site that trust-cg's OPT-4
/// ACTUALLY INLINED, for the call-event gate (`call_event`).
///
/// This is [`eval_ir_call`] — the callee's OWN producer trust-ir, with every
/// one of its fail-closed admissions (local, bodied, not Clean-origin,
/// non-recursive, at most [`MAX_IR_CALL_DEPTH`] deep, single-result, in the
/// modeled fragment) — with the callee's parameters bound to `args`. `root`
/// is the CALLER when it lives in the same module, so a callee that calls back
/// into it is recursion by the same rule as everywhere else.
///
/// It is never used to discharge a `bl`: the call-event gate calls it only for
/// a site whose callee has no machine call anywhere in the caller's extent.
/// Returns the result, the callee's own `reach`, the predicate under which
/// none of its checks fails (`IrOutcome::ok`: an `Unreachable` arm is not a
/// failure), and its side conditions.
pub(crate) fn interpret_inlined_call(
    module: &Module,
    root: Option<FuncId>,
    callee: FuncId,
    args: &[IrValue],
) -> Result<(IrValue, Formula, Formula, Vec<Formula>), String> {
    // Synthetic argument ids from the top of the id space: the callee's own
    // environment is fresh (`eval_ir_call` builds it), so these names are seen
    // only by the binding loop that reads them.
    let ids: Vec<ValueId> = (0..args.len())
        .map(|i| ValueId::new(u32::MAX - u32::try_from(i).unwrap_or(u32::MAX)))
        .collect();
    let env: HashMap<ValueId, IrValue> = ids.iter().copied().zip(args.iter().cloned()).collect();
    let mut ev = SpecEval::new(root.unwrap_or(callee));
    if root.is_none() {
        ev.call_stack.clear();
    }
    let (value, reach, ok) = eval_ir_call(module, callee, &ids, &env, 0, &mut ev)?;
    Ok((value, reach, ok, ev.side))
}

/// CHECKED ARITHMETIC: the one modeled instruction that binds TWO results.
/// `results[0]` is the wrapping value, `results[1]` the overflow flag — a
/// `bool` SSA value, hence the same 0/1-at-32-bits carrier an `Inst::ICmp`
/// result gets, because that is what it is fed to. Shared by the F1 gate's
/// spec side and the call-event gate's (`call_event`).
pub(crate) fn eval_ir_overflow(
    env: &HashMap<ValueId, IrValue>,
    inst: &Inst,
    op: OverflowOp,
    ty: &IrTy,
    lhs: ValueId,
    rhs: ValueId,
    results: &[ValueId],
) -> Result<[(ValueId, IrValue); 2], String> {
    if matches!(ty, IrTy::Bool) {
        return Err("checked arithmetic on a bool carrier is not modeled (fail-closed)".to_string());
    }
    reject_ptr_compute(ty, "checked arithmetic")?;
    let width = scalar_reg_width(ty)?;
    reject_width_128(width, "checked arithmetic")?;
    let signed = ty_is_signed(ty);
    let l = operand_at(env, lhs, width)?;
    let r = operand_at(env, rhs, width)?;
    let (mapped, mapped_signed) = map_ir_binop(
        match op {
            OverflowOp::AddOverflow => IrBinOp::Add,
            OverflowOp::SubOverflow => IrBinOp::Sub,
            OverflowOp::MulOverflow => IrBinOp::Mul,
        },
        signed,
    )?;
    let wrapped = eval_binop(mapped, l.clone(), r.clone(), width, mapped_signed)?;
    let flag = overflow_flag_formula(op, width, signed, &l, &r, &wrapped)?;
    let [value_id, flag_id] = results else {
        return Err(format!(
            "`{}` binds {} result(s); the modeled checked-arithmetic shape is exactly (value, \
             did_overflow) (fail-closed)",
            inst_label(inst),
            results.len()
        ));
    };
    Ok([
        (*value_id, IrValue { f: wrapped, width }),
        (*flag_id, IrValue { f: pred_to_int(flag, 32), width: 32 }),
    ])
}

pub(crate) fn lookup(env: &HashMap<ValueId, IrValue>, id: ValueId) -> Result<IrValue, String> {
    env.get(&id).cloned().ok_or_else(|| format!("read of undefined SSA value %{}", id.index()))
}

/// Evaluate ONE value-producing instruction into a modeled SSA value.
pub(crate) fn eval_ir_inst(
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

pub(crate) fn conjoin(mut guards: Vec<Formula>, rest: Formula) -> Formula {
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

pub(crate) fn merge_reach(cond: Formula, then_reach: Formula, else_reach: Formula) -> Formula {
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
// evaluation of `B` reads the incoming environment at (1) values referenced
// somewhere in the sub-CFG reachable from `B` and NOT defined inside it — that
// is `live_in(B)` — and (2) `B`'s OWN BLOCK PARAMS, whose bound formulas are
// supplied by the in-edge and can differ per predecessor even though the
// params are SSA defs of `B`. So the memo is keyed on `(B, env restricted to
// live_in(B) ∪ params(B))`, compared by VALUE (`Formula` is `Eq`), never on
// the block id alone. Two paths that agree there cannot produce different
// outcomes; two that disagree get separate entries. (Omitting (2) was a WRONG
// SPEC generator: every param-carrying join collapsed to its first edge's
// binding — pinned by tests/trust_ir_gate_diamond_shapes.rs.)
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
        Inst::Assume { cond } => vec![*cond],
        // The evaluator reads only the condition; a kind's operands (trust-ir
        // v52) are listed too, which can only withhold a memo. A sited assert
        // (v54) is not evaluated, so it is not enumerated.
        Inst::Assert { cond, kind, site: None } => {
            let mut v = vec![*cond];
            v.extend(kind.operands().into_iter().flatten());
            v
        }
        Inst::Select { cond, then_val, else_val, .. } => vec![*cond, *then_val, *else_val],
        // A module-local call reads exactly its arguments (WS7.12). The callee
        // is resolved from the module and its body is fixed, so two evaluations
        // of this block with key-equal arguments cannot produce different
        // callee outcomes — which is the property the memo needs.
        Inst::Call { args, .. } => args.clone(),
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
/// exactly (an unenumerable instruction/terminator anywhere, or a nesting the
/// fixpoint does not settle in 64 passes).
///
/// `None` means "do not memoize" (and, for a function with loops, "no cut
/// points" — the evaluator then refuses the backedge as before), which is
/// always safe.
pub(crate) fn live_in_sets(
    blocks: &HashMap<u32, &trust_ir::Block>,
) -> Option<HashMap<u32, Vec<ValueId>>> {
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

    // Reverse post-order via iterative DFS (no native recursion: these CFGs
    // are hundreds of blocks deep). A CYCLE no longer disables the analysis
    // (WS7.14): the equations below are iterated to a FIXPOINT, which for an
    // acyclic CFG converges in the single reverse-post-order pass this used to
    // be, and for a cyclic one in as many passes as the loop nesting needs.
    // The memo key built from a fixpoint live-in set is sound by the same
    // argument as before — `live_in(B)` is a superset of what any acyclic
    // segment through `B` reads — and a segment's cut-point arrivals read
    // only `live_in(B) ∪ defs(B)` (a header's live-ins are its predecessor's
    // live-ins or defs, by the equation itself).
    let mut order: Vec<u32> = Vec::with_capacity(blocks.len());
    let mut state: HashMap<u32, u8> = HashMap::new(); // 0/absent = new, 1 = on stack, 2 = done
    let mut roots: Vec<u32> = blocks.keys().copied().collect();
    roots.sort_unstable();
    for root in roots {
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
                if state.get(&child).copied().unwrap_or(0) == 0 {
                    state.insert(child, 1);
                    stack.push((child, 0));
                }
            } else {
                state.insert(node, 2);
                order.push(node);
            }
        }
    }

    // `order` is post-order (a node is pushed after all its successors), so
    // one forward pass over it is the reverse-post-order sweep; repeat until
    // nothing changes.
    let mut live_set: HashMap<u32, HashSet<ValueId>> = HashMap::new();
    let mut passes = 0u32;
    loop {
        let mut changed = false;
        for id in &order {
            let mut acc = refs.get(id)?.clone();
            for s in succs.get(id)? {
                if let Some(l) = live_set.get(s) {
                    acc.extend(l.iter().copied());
                }
            }
            for d in defs.get(id)? {
                acc.remove(d);
            }
            if live_set.get(id) != Some(&acc) {
                live_set.insert(*id, acc);
                changed = true;
            }
        }
        passes += 1;
        if !changed {
            break;
        }
        if passes > 64 {
            // Nesting deeper than any real function; refuse the memo rather
            // than spend unbounded time here.
            return None;
        }
    }
    let mut live: HashMap<u32, Vec<ValueId>> = HashMap::new();
    for id in &order {
        let acc = live_set.get(id)?;
        // THE MEMO KEY additionally carries the block's OWN params. A block
        // param is an SSA def of this block, so the dataflow above rightly
        // removes it from the set propagated to predecessors (each
        // predecessor's key already covers the edge ARG values via its
        // terminator's `modeled_operands`) — but its BOUND FORMULA is
        // edge-supplied observable input to THIS block's evaluation, and it
        // differs across in-edges. Omitting it collapsed every param-carrying
        // join to the first edge's outcome: the diamond
        // `if c { b } else { a }` memoized its join at the `b` binding and
        // reused it on the `a` edge, producing an `Ite` with the SAME value in
        // both arms — a wrong spec the solver then honestly "refuted" against
        // correct machine code (see tests/trust_ir_gate_diamond_shapes.rs).
        // `eval_ir_block` is always entered with the POST-binding environment,
        // so the params are present in `env` when the key is built.
        let mut v: Vec<ValueId> = acc.iter().copied().collect();
        if let Some(blk) = blocks.get(id) {
            v.extend(blk.params.iter().map(|(p, _)| *p));
        }
        // Deterministic order so the memo key comparison is stable.
        v.sort_by_key(|id| id.index());
        v.dedup_by_key(|id| id.index());
        live.insert(*id, v);
    }
    Some(live)
}

// ===========================================================================
// CUT POINTS (WS7.14) — loop headers of a reducible CFG
// ===========================================================================

/// The loop headers of the root function's CFG — the targets of its
/// back-edges — or `Err` when the CFG is IRREDUCIBLE or not enumerable.
///
/// A back-edge is a DFS edge `u -> v` with `v` on the DFS stack. The CFG is
/// reducible iff every such `v` DOMINATES its `u`; an irreducible CFG has no
/// single-entry loops, so a header would not be a cut that every iteration
/// passes through, and the induction over cut points would not hold. That
/// case is refused by name.
///
/// Headers are returned in ascending block-id order.
pub(crate) fn loop_headers(
    blocks: &HashMap<u32, &trust_ir::Block>,
    entry: u32,
) -> Result<Vec<u32>, String> {
    let mut succs: HashMap<u32, Vec<u32>> = HashMap::new();
    for (id, blk) in blocks {
        let Some(terminator) = blk.body.last() else {
            return Err(format!("bb{id} is empty (fail-closed)"));
        };
        let s = modeled_successors(&terminator.inst).ok_or_else(|| {
            format!(
                "terminator `{}` is outside the modeled fragment (fail-closed)",
                inst_label(&terminator.inst)
            )
        })?;
        succs.insert(*id, s.into_iter().map(|b| b.index()).collect());
    }

    // DFS from the entry: back-edges and the reachable set.
    let mut state: HashMap<u32, u8> = HashMap::new();
    let mut back_edges: Vec<(u32, u32)> = Vec::new();
    let mut reachable: Vec<u32> = Vec::new();
    let mut stack: Vec<(u32, usize)> = vec![(entry, 0)];
    state.insert(entry, 1);
    reachable.push(entry);
    while let Some((node, idx)) = stack.pop() {
        let children = succs
            .get(&node)
            .ok_or_else(|| format!("branch to bb{node} which the function lacks"))?;
        if idx < children.len() {
            stack.push((node, idx + 1));
            let child = children[idx];
            match state.get(&child).copied().unwrap_or(0) {
                0 => {
                    state.insert(child, 1);
                    reachable.push(child);
                    stack.push((child, 0));
                }
                1 => back_edges.push((node, child)),
                _ => {}
            }
        } else {
            state.insert(node, 2);
        }
    }
    if back_edges.is_empty() {
        return Ok(Vec::new());
    }

    // Dominators over the reachable blocks: dom(n) = {n} ∪ ⋂ dom(pred n),
    // iterated to a fixpoint from "everything".
    let all: HashSet<u32> = reachable.iter().copied().collect();
    let mut preds: HashMap<u32, Vec<u32>> = HashMap::new();
    for &n in &reachable {
        for &s in &succs[&n] {
            preds.entry(s).or_default().push(n);
        }
    }
    let mut dom: HashMap<u32, HashSet<u32>> = reachable.iter().map(|&n| (n, all.clone())).collect();
    dom.insert(entry, HashSet::from([entry]));
    loop {
        let mut changed = false;
        for &n in &reachable {
            if n == entry {
                continue;
            }
            let mut acc: Option<HashSet<u32>> = None;
            for p in preds.get(&n).into_iter().flatten() {
                let dp = &dom[p];
                acc = Some(match acc {
                    None => dp.clone(),
                    Some(a) => a.intersection(dp).copied().collect(),
                });
            }
            let mut next = acc.unwrap_or_default();
            next.insert(n);
            if dom[&n] != next {
                dom.insert(n, next);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut headers: Vec<u32> = Vec::new();
    for (u, v) in &back_edges {
        if !dom[u].contains(v) {
            return Err(format!(
                "IRREDUCIBLE control flow: the back-edge bb{u} -> bb{v} enters a loop whose \
                 header does not dominate its latch, so no cut point is passed by every \
                 iteration (fail-closed)"
            ));
        }
        if !headers.contains(v) {
            headers.push(*v);
        }
    }
    headers.sort_unstable();
    Ok(headers)
}

/// One memoized block evaluation: the environment slice it is valid for, and
/// the outcome it produced.
struct MemoEntry {
    /// `(value, formula, width)` for each `live_in` value, in `live_in` order.
    key: Vec<(ValueId, Formula, u32)>,
    value: Formula,
    reach: Formula,
    ok: Formula,
    arrivals: Vec<IrArrival>,
}

/// Evaluation state for ONE spec derivation: the work budget, the block memo,
/// and (since WS7.12) the module-local call stack.
///
/// Everything here is shared across the call tree — a callee does not get a
/// fresh work budget, a fresh side-condition list, or a memo of its own.
struct SpecEval {
    /// `live_in` per (function, block), computed LAZILY per function because a
    /// callee's blocks are not known until its call is evaluated. The inner
    /// `None` is "memoization disabled for this function", which is always
    /// safe (see the DAG-EVALUATION note).
    live_in: HashMap<u32, Option<HashMap<u32, Vec<ValueId>>>>,
    /// Keyed on `(function, block)`: block ids are per-function, so a caller's
    /// `bb0` and a callee's `bb0` must never share an entry.
    memo: HashMap<(u32, u32), Vec<MemoEntry>>,
    /// Block evaluations performed so far, against [`MAX_IR_BLOCK_EVALS`].
    evals: u32,
    /// Side conditions, accumulated across the whole call tree.
    side: Vec<Formula>,
    /// The functions currently being evaluated, root first. A callee already on
    /// it is recursion and is refused (`eval_ir_call`).
    call_stack: Vec<FuncId>,
    /// The ROOT function: the only one whose loop headers are cut points
    /// (WS7.14). A callee's loop is still refused by the backedge check.
    root: FuncId,
    /// The root function's cut points: loop header block -> its SHARED
    /// VARIABLES (block params first, then every other live-in, each sorted by
    /// id). Empty for a loop-free root, in which case nothing here changes.
    shared: HashMap<u32, Vec<ValueId>>,
}

impl SpecEval {
    fn new(root: FuncId) -> Self {
        SpecEval {
            live_in: HashMap::new(),
            memo: HashMap::new(),
            evals: 0,
            side: Vec::new(),
            call_stack: vec![root],
            root,
            shared: HashMap::new(),
        }
    }

    /// The memo key for `func`'s block `id` under `env`, or `None` when it is
    /// not memoizable (analysis disabled for `func`, or a live value missing
    /// from `env` — the latter is a malformed-SSA case the evaluator itself
    /// reports precisely).
    fn key_for(
        &mut self,
        func: FuncId,
        blocks: &HashMap<u32, &trust_ir::Block>,
        id: u32,
        env: &HashMap<ValueId, IrValue>,
    ) -> Option<Vec<(ValueId, Formula, u32)>> {
        let live = self
            .live_in
            .entry(func.index())
            .or_insert_with(|| live_in_sets(blocks))
            .as_ref()?
            .get(&id)?;
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

/// How deep a chain of module-local `Inst::Call`s the spec side will follow
/// (WS7.12). The root function is depth 0, so 8 admits a chain of eight nested
/// callees.
///
/// This is a SOLVER-COST bound, not a modeling one: each level multiplies the
/// callee's formula into the caller's, and the emitted bytes it is compared
/// against are the inliner's splice of the same chain. Exceeding it is
/// `Unknown` — an undecided function is refused, never proven.
const MAX_IR_CALL_DEPTH: usize = 8;

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
    let lir = match crate::lower_module_to_lir_maybe_cross_checked(
        &source.module,
        source.func_id,
        source.abi_cross_check.as_ref(),
    ) {
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
    let obj = match backend.emit_object_with_trust_ir_globals(&[lir], &source.module) {
        Ok(obj) => obj,
        Err(e) => {
            return (
                OutputVerdict::Unknown {
                    reason: format!("globals-aware emit_object failed: {e:?}"),
                },
                None,
            );
        }
    };

    if let Err(reason) = backend.require_object_target(&obj) {
        return (OutputVerdict::Unknown { reason }, None);
    }
    let verdict = verify_trust_ir_bytes(source, &obj, backend.target_arch());
    (verdict, Some(obj))
}

/// MUTATION-CONTROL HOOK (WS7.12): [`verify_trust_ir_output_preserved`] with
/// the LOWERING supplied by the caller.
///
/// It exists so a test can inject a DELIBERATELY WRONG lowering — an inliner
/// that swaps a callee's arguments, a `brif` with its targets exchanged, a
/// switch arm whose constant moved — and demand that the gate answers
/// `Refuted`. A gate that only ever sees correct bytes has not been shown to
/// refuse incorrect ones, and a negative twin built by hand-editing an object
/// tests the disassembler rather than the obligation.
///
/// It is NOT a production entry point and grants no authority: the SPEC side is
/// unchanged and still comes from `source.module`, so the only thing a caller
/// can do with it is make the machine side disagree. It is `#[doc(hidden)]` and
/// behind the non-default `test-hooks` feature because integration tests cannot
/// see `cfg(test)` items; nothing in the compiler path enables that feature.
#[cfg(feature = "test-hooks")]
#[doc(hidden)]
pub fn verify_trust_ir_output_preserved_with_lowering(
    source: &TrustIrGateSource,
    backend: &TrustCgCodegenBackend,
    lower: fn(&Module, FuncId) -> Result<trust_cg_lower::function::Function, String>,
) -> (OutputVerdict, Option<Vec<u8>>) {
    let lir = match lower(&source.module, source.func_id) {
        Ok(lir) => lir,
        Err(e) => {
            return (
                OutputVerdict::Unknown { reason: format!("injected lowering failed: {e}") },
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
    let obj = match backend.emit_object_with_trust_ir_globals(&[lir], &source.module) {
        Ok(obj) => obj,
        Err(e) => {
            return (
                OutputVerdict::Unknown {
                    reason: format!("globals-aware emit_object failed: {e:?}"),
                },
                None,
            );
        }
    };
    if let Err(reason) = backend.require_object_target(&obj) {
        return (OutputVerdict::Unknown { reason }, None);
    }
    let verdict = verify_trust_ir_bytes(source, &obj, backend.target_arch());
    (verdict, Some(obj))
}

/// Discharge a function's trust-ir specification against a GIVEN object's bytes.
///
/// This is the half of [`verify_trust_ir_output_preserved`] that touches no
/// emitter: hand it any object and it re-derives the machine side from THOSE
/// bytes. It is what makes the gate independently auditable — a corrupted or
/// substituted artifact can be checked against the same specification, and must
/// come back `Refuted` for modeled byte changes, or `Unknown` for an object
/// whose target header cannot be bound to the requested machine model.
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

/// The formulas the gate discharges, exposed so a verdict can be explained
/// rather than merely reported.
///
/// A gate whose obligation cannot be inspected is a gate nobody can audit; this
/// is the same data `verify_trust_ir_bytes` acts on, with nothing summarized.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
#[serde(deny_unknown_fields)]
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
    /// Ambient machine-environment assumptions (see
    /// [`SpecSemantics::ambient_pre`]) conditioning BOTH obligations.
    pub ambient_pre: Vec<Formula>,
    /// Trust (O0, increment-5 step 5.0): the ABI guarantee the bytes owe their
    /// LLVM-built caller — callee-saved X19-X29, SP and D8-D15, the return
    /// target equal to the entry X30, and (on Darwin) X18 never written. Only
    /// the conjuncts the executor's structural reading could NOT reduce to
    /// their entry values are listed; each `claim` must be valid under
    /// `ambient_pre`. EMPTY means O0 was discharged structurally, which is the
    /// common case. A legacy serialized obligation without this field reads as
    /// EMPTY and therefore no longer matches a reconstruction that has residue.
    #[serde(default)]
    pub abi_residue: Vec<AbiConjunct>,
    /// CUT-POINT SEGMENTS (WS7.14). EMPTY for a loop-free function, whose
    /// obligation is then exactly the four formulas above. For a function
    /// with loops the four formulas above are the ENTRY segment's return
    /// half, and this carries the entry segment's arrivals plus one segment
    /// per reached loop header (its return half and its arrivals). The
    /// conjunction of all of them, by induction over cut points, is LOCKSTEP
    /// PARTIAL CORRECTNESS: every terminating spec execution is matched by a
    /// machine execution with the same result. It says nothing about
    /// non-termination, and a verdict built from a non-empty list is capped
    /// at `AyValidated` (see `discharge_trust_ir_obligation`).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub segments: Vec<SegmentObligation>,
}

/// One acyclic segment's obligation (WS7.14): a spec segment paired with the
/// machine segment that starts at the cut address claimed for its header.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SegmentObligation {
    /// The spec header this segment starts at (`None` = the entry segment).
    pub start: Option<u32>,
    /// The claimed machine address of that header (`None` = the entry).
    pub machine_addr: Option<u64>,
    /// The registers the header's shared variables are located in, one per
    /// `SpecCutPoint::shared` entry (empty for the entry segment). These are
    /// the seeds of the machine segment: `X{r}[w-1:0] = shared var`, every
    /// other bit of the machine state HAVOC.
    pub locations: Vec<u8>,
    /// Return value the spec computes on the segment's returning paths.
    pub spec_value: Formula,
    /// Under which segment inputs the spec returns.
    pub spec_reach: Formula,
    /// Return value the machine segment computes.
    pub machine_value: Formula,
    /// Under which segment inputs the machine segment reaches a `RET`.
    pub machine_reach: Formula,
    /// The cut points the spec segment arrives at, each paired with the
    /// machine arrival at the corresponding claimed address.
    pub arrivals: Vec<ArrivalObligation>,
    /// STRAY ARRIVALS: cut-candidate addresses the machine segment stops at
    /// that no located spec header claims (a backward-branch target that is
    /// not a loop header — e.g. a block the emitter merely laid out before
    /// its predecessor). A path that stops there contributes neither a
    /// return nor a matched arrival, so a failed obligation of a segment
    /// with strays may indict the untrusted MAP rather than the bytes; the
    /// discharge reports it `Unknown`, never `Refuted`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub stray_arrivals: Vec<u64>,
    /// O0 x WS7.14: the ABI residue of THIS segment's `RET`s and X18 writes,
    /// as `GateObligation::abi_residue` is for a loop-free function. Empty for
    /// the entry segment, whose residue IS `GateObligation::abi_residue` (it
    /// starts from the true entry state and keeps O0's ordinary verdicts). A
    /// header segment's residue rests on the seeded ABI invariant, so it is
    /// discharged as `Unknown` on any failure, never `Refuted`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub abi_residue: Vec<AbiConjunct>,
    /// O0 x WS7.14: the inductive step of the ABI invariant — for every
    /// machine arrival of this segment at a LOCATED loop header, each O0
    /// location the header does not hold a live-in in must be its entry
    /// value (`reach => location == entry`). Only the conjuncts the
    /// structural reading could not reduce are listed. Discharged BEFORE any
    /// segment verdict; any failure is `Unknown`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub abi_invariant: Vec<AbiConjunct>,
}

/// One arrival obligation (WS7.14): `spec_reach => machine_reach AND every
/// located shared variable holds the spec's value`.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArrivalObligation {
    /// The header arrived at.
    pub block: u32,
    /// Its claimed machine address.
    pub machine_addr: u64,
    /// Under which segment inputs the spec arrives here.
    pub spec_reach: Formula,
    /// Under which segment inputs the machine segment stops here
    /// (`Bool(false)` when it never does).
    pub machine_reach: Formula,
    /// `(spec value, machine register value)` per shared variable, both at
    /// the variable's declared width.
    pub values: Vec<(Formula, Formula)>,
}

/// MEASUREMENT PROBE, not part of the gate: run ONLY the machine half of the
/// obligation over `obj`, so the machine-side budget can be measured
/// independently of whether the spec side is in-fragment.
///
/// No verdict is derived from it. [`trust_ir_gate_obligation`] does not call it
/// (it runs the same `symbolic_machine_outcome_traps` step inline), and its only
/// caller is the `ccc_probe` developer example. It is `pub` only so that example
/// can reach it, and `#[doc(hidden)]` because it is not API.
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
    trust_ir_gate_obligation_impl(source, obj, arch, None)
}

/// CLAIMED-MAP HOOK (WS7.14): [`verify_trust_ir_bytes`] with the cut-point
/// map (header addresses AND shared-variable registers) supplied by the
/// caller instead of inferred from the bytes. A test injects a LYING map — a
/// wrong header address, or the honest registers over bytes that clobber one
/// — and demands the verdict is never `Proven`. Grants no authority: a
/// supplied map is exactly as untrusted as the inferred one, and the
/// obligation checks it the same way. It is also the shape an emitter export
/// would arrive in.
#[cfg(feature = "test-hooks")]
#[doc(hidden)]
pub fn verify_trust_ir_bytes_with_claimed_cut_points(
    source: &TrustIrGateSource,
    obj: &[u8],
    arch: TrustCgTargetArch,
    claimed: &[ClaimedCutPoint],
) -> OutputVerdict {
    let obligation = match trust_ir_gate_obligation_impl(source, obj, arch, Some(claimed)) {
        Ok(obligation) => obligation,
        Err(reason) => return OutputVerdict::Unknown { reason },
    };
    discharge_trust_ir_obligation(&source.symbol, &obligation)
}

/// TEST HOOK: the emitted `__text` bytes and their base address, so a test can
/// patch one instruction of an object and hand it back to
/// [`verify_trust_ir_bytes`].
#[cfg(feature = "test-hooks")]
#[doc(hidden)]
pub fn emitted_text(obj: &[u8]) -> Result<(Vec<u8>, u64), String> {
    extract_text_from_object(obj)
}

fn trust_ir_gate_obligation_impl(
    source: &TrustIrGateSource,
    obj: &[u8],
    arch: TrustCgTargetArch,
    claimed: Option<&[ClaimedCutPoint]>,
) -> Result<GateObligation, String> {
    // (1) THE SPEC — from the producer's trust-ir, never from the lowering.
    // The cross-check contributes ONLY the attested bool-parameter extension
    // facts (WS7.13); the spec formula itself is still read off the IR.
    let spec = trust_ir_function_semantics_with(
        &source.module,
        source.func_id,
        source.abi_cross_check.as_ref(),
    )?;
    // (2) THE MACHINE SIDE — derived ONLY from the emitted bytes.
    if arch != TrustCgTargetArch::AArch64 {
        return Err(format!(
            "byte-level output preservation is wired for AArch64 machine semantics only; \
             emitted {arch:?} code is undecided (fail-closed)"
        ));
    }
    crate::codegen_backend::require_object_architecture(obj, arch)?;
    crate::verify_output::require_exact_elf_function_bindings(
        obj,
        &[(source.symbol.as_str(), FunctionLinkage::External)],
    )?;
    let (code, base) = extract_text_from_object(obj)?;
    if code.is_empty() {
        return Err("emitted text section is empty".into());
    }

    // LOOPS (WS7.14): cut-point simulation. The entry segment's return half
    // takes the four top-level slots; everything else is `segments`.
    if !spec.cut_points.is_empty() {
        if !spec.ambient_pre.is_empty() {
            return Err("a function with loops AND an ambient precondition (stack-passed or bool \
                 parameters) is not modeled: the cut-point seeding havocs the memory and \
                 register bits those preconditions speak about (fail-closed)"
                .into());
        }
        let mut segments =
            build_segment_obligations(&spec, &code, base, claimed, platform_reserves_x18(obj))?;
        let entry = segments.first_mut().ok_or("no entry segment")?;
        // O0 of the ENTRY segment is the function's ordinary O0 residue: that
        // segment runs from the true entry state, so its verdicts stand as
        // for a loop-free function (a header segment's rest on the invariant).
        let abi_residue = std::mem::take(&mut entry.abi_residue);
        let (machine_value, machine_reach) =
            (entry.machine_value.clone(), entry.machine_reach.clone());
        return Ok(GateObligation {
            spec_value: spec.value.clone(),
            spec_reach: spec.reach.clone(),
            machine_value,
            machine_reach,
            out_width: spec.out_width,
            spec_side_conditions: spec.side_conditions.clone(),
            ambient_pre: Vec::new(),
            abi_residue,
            segments,
        });
    }

    let SpecSemantics {
        value: spec_value,
        reach: spec_reach,
        out_width,
        side_conditions,
        ambient_pre,
        ..
    } = spec;
    let machine = symbolic_machine_outcome_traps(&code, base, out_width, false)?;
    // O0 — read off the SAME execution of the SAME bytes, before the value and
    // reach formulas are moved out of it.
    let abi_residue = abi_guarantee_residue(&machine, platform_reserves_x18(obj));
    // STACK-ADDRESS NORMALIZATION. When the obligation carries the
    // well-formed-stack ambient, resolve `Select(Store(m, SP0+c1, v),
    // SP0+c2)` structurally before handing the formulas to ay: under the
    // ambient bounds, `SP0+c1 == SP0+c2 <=> c1 == c2` for the small frame/
    // argument offsets these chains carry, so a differing constant makes the
    // store provably irrelevant and an equal constant makes the read the
    // stored value. ay's QF_ABV lane was MEASURED not to converge on the raw
    // chains (Unknown at 120s and 480s); after this rewrite it is handed only
    // the trivial residue. The rewrite fires ONLY under the ambient that
    // justifies it and ONLY on SP0-plus-constant addresses — anything else is
    // left for the solver, so a shape outside the argument stays exactly as
    // hard (and as sound) as before.
    let (machine_value, machine_reach) = if ambient_pre.is_empty() {
        (machine.value, machine.reach)
    } else {
        (normalize_sp_selects(&machine.value), normalize_sp_selects(&machine.reach))
    };
    Ok(GateObligation {
        spec_value,
        spec_reach,
        machine_value,
        machine_reach,
        out_width,
        spec_side_conditions: side_conditions,
        ambient_pre,
        abi_residue,
        segments: Vec::new(),
    })
}

// ===========================================================================
// PART 2b — CUT-POINT SIMULATION (WS7.14): the machine side of a loop
// ===========================================================================
//
// THE IDEA. A loop header H is a CUT POINT. The spec is cut into acyclic
// segments — entry -> first header, and header -> {next header, return} — and
// for each segment the machine is run from the header's claimed ADDRESS in a
// state where the header's SHARED VARIABLES sit in their claimed REGISTERS and
// EVERYTHING ELSE is havoc (fresh, unconstrained). Proving every segment's
// `spec_reach => machine_reach AND agreement (return value, or the next
// header's shared variables)` is, by induction over the cut points, lockstep
// partial correctness. The havoc is what makes the induction sound: a header
// segment's proof holds for EVERY state the machine could be in at the header,
// so it holds for the state the previous segment actually left it in.
//
// THE MAP IS UNTRUSTED, AND HERE IT IS INFERRED. The roadmap's design has the
// emitter export each header's address and each live-in's location. MEASURED
// 2026-09-20 on this tree: the object path exports neither. `ModuleEmission`
// carries `text_extents` only; block offsets exist inside trust-cg's encoder
// (`encode_function_with_fixups_and_blocks`) on a path that is not the object
// path; and the only value->location machinery is the DWARF `ProvenanceVar`
// slice, keyed on single-origin instructions and documented as not populated
// by the adapter. Exporting them is a trust-cg companion. What lands here is
// the whole gate WITH THE MAP AS AN INPUT, plus an in-tree UNTRUSTED
// derivation of that input from the bytes: header candidates are the targets
// of backward branches, and a live-in's register is found by STRUCTURAL
// matching of the spec's arrival value against the register file at the
// machine's arrival (`locate_cut_registers`). Soundness never depends on the
// map: a wrong address makes a segment stop where the spec did not predict
// (or run into its own backedge, `Err`), and a wrong register makes an arrival
// check fail. Neither can produce `Proven`; the companion export would only
// make more correct code provable, never more code provable.
//
// WHAT A COUNTEREXAMPLE MEANS UNDER HAVOC. A machine formula that mentions a
// havoc variable depends on state the map did not relate to the spec — a
// spilled live-in read back from havoc memory, the upper bits of a narrow
// register. A counterexample to such a formula indicts the MAP, not the
// bytes, so it is reported `Unknown` ("could not locate"), never `Refuted`. A
// counterexample to a formula over shared variables alone is a real
// disagreement and is `Refuted`. `mentions_havoc` is that test.
//
// WHAT A HEADER-SEGMENT `Refuted` CLAIMS. It names a header state — shared
// variables with arbitrary values — from which the machine's loop body
// disagrees with the IR's. Both sides are deterministic in those variables, so
// the disagreement is real for that state; whether a run from the entry can
// reach it is not established (no invariant is inferred). `Refuted` there is a
// verdict on the loop BODY the bytes implement, which is what a stale latch or
// a clobbered live-in is.
//
// STRAY CUT CANDIDATES. An inferred candidate that is no loop header (a
// backward branch into a block the emitter merely laid out early) makes the
// machine segment stop where neither a return nor a matched arrival is: a path
// that looks like a trap. That indicts the MAP, so any `Refuted` from a segment
// with a stray arrival is demoted to `Unknown` (`demote_if_stray`). A wrong
// map therefore can yield neither `Proven` nor a fabricated `Refuted`.

/// The bit width of a bit-vector `Formula`, for the shapes this module builds.
fn bv_width(f: &Formula) -> Option<u32> {
    Some(match f {
        Formula::Var(_, Sort::BitVec(w)) => *w,
        Formula::BitVec { width, .. } => *width,
        Formula::BvAdd(_, _, w)
        | Formula::BvSub(_, _, w)
        | Formula::BvMul(_, _, w)
        | Formula::BvUDiv(_, _, w)
        | Formula::BvSDiv(_, _, w)
        | Formula::BvURem(_, _, w)
        | Formula::BvSRem(_, _, w)
        | Formula::BvAnd(_, _, w)
        | Formula::BvOr(_, _, w)
        | Formula::BvXor(_, _, w)
        | Formula::BvNot(_, w)
        | Formula::BvShl(_, _, w)
        | Formula::BvLShr(_, _, w)
        | Formula::BvAShr(_, _, w) => *w,
        Formula::BvExtract { high, low, .. } => high - low + 1,
        Formula::BvConcat(a, c) => bv_width(a)? + bv_width(c)?,
        Formula::BvZeroExt(a, k) | Formula::BvSignExt(a, k) => bv_width(a)? + k,
        Formula::Ite(_, t, _) => bv_width(t)?,
        Formula::Select(..) => 8,
        _ => return None,
    })
}

/// STRUCTURAL NORMALIZER for register reads: folds the extract/zero-extend/
/// concat wrappers the machine model puts around a value (`W`-writes
/// zero-extend into `X`, `read_gpr(r, w)` extracts back out) so that a
/// register holding the spec's value compares EQUAL to the spec's formula by
/// `==`. Pure syntax, every rule an identity of bit-vector arithmetic; a shape
/// no rule covers is left alone (and then simply fails to match).
fn norm(f: &Formula) -> Formula {
    let f = f.clone().map_children(&mut |c| norm(&c));
    match f {
        Formula::BvExtract { inner, high, low } => {
            let width = high - low + 1;
            match *inner {
                Formula::BitVec { value, width: _ } => {
                    let shifted = ((value as u128) >> low) as i128;
                    let mask: i128 = if width >= 128 { -1 } else { (1i128 << width) - 1 };
                    Formula::BitVec { value: shifted & mask, width }
                }
                Formula::BvZeroExt(x, _) if bv_width(&x).is_some_and(|wx| high < wx) => {
                    norm(&Formula::BvExtract { inner: x, high, low })
                }
                Formula::BvConcat(hi, lo) => match bv_width(&lo) {
                    Some(wlo) if high < wlo => norm(&Formula::BvExtract { inner: lo, high, low }),
                    Some(wlo) if low >= wlo => {
                        norm(&Formula::BvExtract { inner: hi, high: high - wlo, low: low - wlo })
                    }
                    _ => Formula::BvExtract { inner: b(Formula::BvConcat(hi, lo)), high, low },
                },
                Formula::BvExtract { inner: x, high: _, low: l2 } => {
                    norm(&Formula::BvExtract { inner: x, high: l2 + high, low: l2 + low })
                }
                other => {
                    if low == 0 && bv_width(&other) == Some(width) {
                        other
                    } else {
                        Formula::BvExtract { inner: b(other), high, low }
                    }
                }
            }
        }
        Formula::BvZeroExt(x, k) => match *x {
            Formula::BitVec { value, width } => Formula::BitVec { value, width: width + k },
            other => Formula::BvZeroExt(b(other), k),
        },
        // `mov wd, ws` is `orr wd, wzr, ws` and `mov wd, #k` may arrive as
        // `add`/`orr` with a zero operand: an identity is dropped, and two
        // constants fold.
        Formula::BvOr(a, c, _) | Formula::BvAdd(a, c, _) | Formula::BvXor(a, c, _)
            if is_zero(&a) =>
        {
            *c
        }
        Formula::BvOr(a, c, _) | Formula::BvAdd(a, c, _) | Formula::BvXor(a, c, _)
            if is_zero(&c) =>
        {
            *a
        }
        Formula::BvOr(a, c, w) => fold_const_pair(a, c, w, |x, y| x | y, Formula::BvOr),
        Formula::BvXor(a, c, w) => fold_const_pair(a, c, w, |x, y| x ^ y, Formula::BvXor),
        Formula::BvAdd(a, c, w) => fold_const_pair(a, c, w, i128::wrapping_add, Formula::BvAdd),
        other => other,
    }
}

/// `op` over two constant operands, masked to the width `w`; any other
/// operand pair is rebuilt unchanged by `rebuild` (the variant's own
/// constructor), exactly as `norm` leaves a shape no rule covers.
fn fold_const_pair(
    a: Box<Formula>,
    c: Box<Formula>,
    w: u32,
    op: fn(i128, i128) -> i128,
    rebuild: fn(Box<Formula>, Box<Formula>, u32) -> Formula,
) -> Formula {
    match const_pair(&a, &c) {
        Some((x, y)) => Formula::BitVec { value: op(x, y) & bv_mask(w), width: w },
        None => rebuild(a, c, w),
    }
}

fn is_zero(f: &Formula) -> bool {
    matches!(f, Formula::BitVec { value: 0, .. })
}

fn const_pair(a: &Formula, c: &Formula) -> Option<(i128, i128)> {
    match (a, c) {
        (Formula::BitVec { value: x, .. }, Formula::BitVec { value: y, .. }) => Some((*x, *y)),
        _ => None,
    }
}

fn bv_mask(w: u32) -> i128 {
    if w >= 128 { -1 } else { (1i128 << w) - 1 }
}

/// The low `width` bits of a 64-bit register formula, normalized.
fn read_reg(gpr: &Formula, width: u32) -> Formula {
    if width >= 64 {
        norm(gpr)
    } else {
        norm(&Formula::BvExtract { inner: b(gpr.clone()), high: width - 1, low: 0 })
    }
}

/// Does `f` mention a havoc variable of a cut state?
fn mentions_havoc(f: &Formula) -> bool {
    f.free_variables().iter().any(|v| v.contains("_HAVOC"))
}

/// Replace every free variable named in `map` by its formula.
fn substitute_vars(f: &Formula, map: &HashMap<String, Formula>) -> Formula {
    f.clone().map(&mut |node| match node {
        Formula::Var(ref name, _) => map.get(name).cloned().unwrap_or(node),
        other => other,
    })
}

/// The register file candidates a live-in may be located in: `X0..=X28`
/// (`X29`/`X30` are the frame and link registers, never a value's home).
const CUT_CANDIDATE_REGS: std::ops::RangeInclusive<u8> = 0..=28;

/// A machine state at a claimed cut address: EVERYTHING havoc under `tag`,
/// except the seeded registers.
fn cut_state(tag: &str, seeds: &[(u8, Formula)]) -> MachineState {
    let mut st = MachineState::symbolic();
    for (i, g) in st.gpr.iter_mut().enumerate() {
        *g = Formula::Var(format!("{tag}_HAVOC_X{i}"), Sort::BitVec(64));
    }
    for (i, v) in st.fpr.iter_mut().enumerate() {
        *v = Formula::Var(format!("{tag}_HAVOC_V{i}"), Sort::BitVec(128));
    }
    st.sp = Formula::Var(format!("{tag}_HAVOC_SP"), Sort::BitVec(64));
    st.flags = Flags::symbolic(&format!("{tag}_HAVOC"));
    st.memory = Formula::Var(
        format!("{tag}_HAVOC_MEM"),
        Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
    );
    for (r, f) in seeds {
        st.gpr[*r as usize] = f.clone();
    }
    st
}

/// The 64-bit seed of register `r` holding shared variable `sv`: the variable
/// in the low bits, havoc above them (the machine is promised NOTHING about a
/// narrow value's upper register bits, and the arrival check reads none).
fn seed_for(tag: &str, r: u8, sv: &SharedVar) -> Formula {
    if sv.width >= 64 {
        sv.formula()
    } else {
        Formula::BvConcat(
            b(Formula::Var(format!("{tag}_HAVOC_HI_X{r}"), Sort::BitVec(64 - sv.width))),
            b(sv.formula()),
        )
    }
}

/// A header whose machine address and register locations have been fixed.
struct LocatedCut {
    block: u32,
    addr: u64,
    /// One register per `SpecCutPoint::shared` entry.
    regs: Vec<u8>,
}

/// Cap on the register assignments tried when several registers hold a
/// live-in's value at the first arrival.
const MAX_LOCATION_ASSIGNMENTS: usize = 256;

/// LOCATE the shared variables of header `cut` in the register file of a
/// machine arrival, and pick among the candidates by a PROBE run of the
/// header's own machine segment (WS7.14). Untrusted inference; see the
/// section comment.
///
/// Returns `None` when some shared variable has no candidate at all in this
/// arrival — the caller then tries the next machine arrival.
#[allow(clippy::too_many_arguments)]
fn locate_cut_registers(
    cut: &SpecCutPoint,
    spec_arrival: &SpecArrival,
    machine_gpr: &[Formula],
    latch: Option<&SpecArrival>,
    code: &[u8],
    base: u64,
    out_width: u32,
    addr: u64,
    cut_addrs: &HashSet<u64>,
) -> Option<Vec<u8>> {
    // (1) Candidates: every register whose value at the arrival is, after
    // normalization, exactly the spec's value for the variable.
    let mut cands: Vec<Vec<u8>> = Vec::with_capacity(cut.shared.len());
    for (sv, spec_val) in cut.shared.iter().zip(&spec_arrival.values) {
        let want = norm(spec_val);
        let c: Vec<u8> = CUT_CANDIDATE_REGS
            .filter(|&r| read_reg(&machine_gpr[r as usize], sv.width) == want)
            .collect();
        if c.is_empty() {
            return None;
        }
        cands.push(c);
    }
    let first: Vec<u8> = cands.iter().map(|c| c[0]).collect();
    if cands.iter().all(|c| c.len() == 1) {
        return Some(first);
    }

    // (2) Several registers hold some variable's value at the arrival (a
    // copy the loop may or may not keep). Probe: run the header segment with
    // every candidate register holding a DISTINCT fresh variable, and keep
    // the assignment under which the machine's latch arrival agrees with the
    // spec's latch arrival structurally. No solver is involved and nothing is
    // trusted: the chosen assignment is still checked by the real obligation.
    let tag = format!("PROBE_bb{}", cut.block);
    let all: Vec<u8> = {
        let mut v: Vec<u8> = cands.iter().flatten().copied().collect();
        v.sort_unstable();
        v.dedup();
        v
    };
    let seeds: Vec<(u8, Formula)> =
        all.iter().map(|&r| (r, Formula::Var(format!("{tag}_X{r}"), Sort::BitVec(64)))).collect();
    let probe =
        symbolic_machine_segment(code, base, out_width, addr, cut_state(&tag, &seeds), cut_addrs)
            .ok();
    let probe_latch = probe.as_ref().and_then(|p| p.arrivals.iter().find(|a| a.addr == addr));
    let (Some(probe_latch), Some(latch)) = (probe_latch, latch) else {
        return Some(first);
    };
    // The assignment under which the MOST variables agree at the latch wins
    // (all of them for correct code; fewer when the bytes are wrong, in which
    // case the registers that still agree are the ones the obligation should
    // be spelled over so the disagreement is a real one and not havoc).
    let mut assignment = first.clone();
    let mut best_score: usize = 0;
    let mut tried = 0usize;
    let mut idx = vec![0usize; cands.len()];
    loop {
        tried += 1;
        if tried > MAX_LOCATION_ASSIGNMENTS {
            break;
        }
        let pick: Vec<u8> = idx.iter().zip(&cands).map(|(&i, c)| c[i]).collect();
        let distinct = {
            let mut p = pick.clone();
            p.sort_unstable();
            p.dedup();
            p.len() == pick.len()
        };
        if distinct {
            let map: HashMap<String, Formula> = cut
                .shared
                .iter()
                .zip(&pick)
                .map(|(sv, &r)| {
                    (
                        sv.name.clone(),
                        read_reg(&Formula::Var(format!("{tag}_X{r}"), Sort::BitVec(64)), sv.width),
                    )
                })
                .collect();
            let score = cut
                .shared
                .iter()
                .zip(&pick)
                .zip(&latch.values)
                .filter(|((sv, r), sv_latch)| {
                    read_reg(&probe_latch.gpr[**r as usize], sv.width)
                        == norm(&substitute_vars(sv_latch, &map))
                })
                .count();
            if score > best_score || (best_score == 0 && assignment == first && tried == 1) {
                best_score = score;
                assignment = pick.clone();
            }
            if score == cut.shared.len() {
                break;
            }
        }
        // Next assignment in lexicographic order.
        let mut k = idx.len();
        loop {
            if k == 0 {
                return Some(assignment);
            }
            k -= 1;
            idx[k] += 1;
            if idx[k] < cands[k].len() {
                break;
            }
            idx[k] = 0;
        }
    }
    Some(assignment)
}

/// A CLAIMED cut point (WS7.14): a header's machine address and the register
/// of each of its shared variables, as an emitter export or a test would
/// state them. Untrusted input; see the section comment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClaimedCutPoint {
    /// The spec header block.
    pub block: u32,
    /// Its claimed machine address.
    pub addr: u64,
    /// One register per `SpecCutPoint::shared` entry.
    pub regs: Vec<u8>,
}

/// The SHAPE check of one claimed cut point (WS7.14 review): every register
/// is one of the modeled value registers, and the address is a 4-byte-aligned
/// instruction of the emitted text. A malformed claim is a named `Unknown`
/// reason — never a panic (an out-of-file register used to index
/// `MachineState::gpr` out of bounds) and never whichever fail-closed reason
/// the bytes happen to produce first.
fn check_claimed_cut_shape(claim: &ClaimedCutPoint, code: &[u8], base: u64) -> Result<(), String> {
    if let Some(bad) = claim.regs.iter().find(|r| !CUT_CANDIDATE_REGS.contains(*r)) {
        return Err(format!(
            "claimed cut point for bb{} locates a shared variable in X{bad}, which is not one \
             of the X{}..=X{} value registers this gate models (X29/X30 are the frame and link \
             registers, and the file holds 31) (fail-closed)",
            claim.block,
            CUT_CANDIDATE_REGS.start(),
            CUT_CANDIDATE_REGS.end()
        ));
    }
    let len = code.len() as u64;
    let offset = claim.addr.checked_sub(base);
    if !offset.is_some_and(|o| o < len && o.is_multiple_of(4)) {
        return Err(format!(
            "claimed cut point for bb{} names the address {:#x}, which is not a 4-byte-aligned \
             instruction of the emitted text [{base:#x}, {:#x}) (fail-closed)",
            claim.block,
            claim.addr,
            base.saturating_add(len)
        ));
    }
    Ok(())
}

/// Build the per-segment obligations of a function WITH loops (WS7.14): run
/// the entry segment, locate each header on its first spec arrival (from the
/// `claimed` map when one is given, else inferred from backward-branch
/// targets), run each header's segment from its seeded cut state, and pair
/// every spec arrival with the machine arrival at the located address.
fn build_segment_obligations(
    spec: &SpecSemantics,
    code: &[u8],
    base: u64,
    claimed: Option<&[ClaimedCutPoint]>,
    x18_reserved: bool,
) -> Result<Vec<SegmentObligation>, String> {
    let out_width = spec.out_width;
    // A CLAIMED map is UNTRUSTED input: every claim's SHAPE is checked before
    // the first machine walk, not only when its header is first reached. The
    // entry walk stops only at claimed addresses, so a claim naming an address
    // outside the emitted text used to let the walk run on to whatever
    // fail-closed reason the bytes produce first (measured 2026-09-27 on the
    // re-pinned trust-cg `count_to` lowering: "backedge at unconditional
    // branch"). That is still `Unknown`, but a malformed map must be refused
    // BY NAME, independent of the emitted code's shape.
    if let Some(claimed) = claimed {
        for claim in claimed {
            check_claimed_cut_shape(claim, code, base)?;
        }
    }
    let cut_candidates: Vec<u64> = match claimed {
        Some(claimed) => claimed.iter().map(|c| c.addr).collect(),
        None => backward_branch_targets(code, base),
    };
    if cut_candidates.is_empty() {
        return Err(format!(
            "the IR has {} loop header(s) but the emitted bytes carry no backward branch to \
             cut at; cut-point map: none (fail-closed)",
            spec.cut_points.len()
        ));
    }
    let cut_addrs: HashSet<u64> = cut_candidates.iter().copied().collect();

    let mut located: Vec<LocatedCut> = Vec::new();
    let mut machine_outcomes: Vec<Option<PathOutcome>> = vec![None; spec.segments.len()];
    machine_outcomes[0] = Some(symbolic_machine_segment(
        code,
        base,
        out_width,
        base,
        MachineState::symbolic(),
        &cut_addrs,
    )?);
    let mut result: Vec<SegmentObligation> = Vec::with_capacity(spec.segments.len());
    // Each segment's machine arrivals, kept for the ABI invariant's inductive
    // step, which needs every header located first.
    let mut machine_arrivals: Vec<Vec<crate::verify_output::MachineArrival>> =
        Vec::with_capacity(spec.segments.len());

    for (k, seg) in spec.segments.iter().enumerate() {
        let m = machine_outcomes[k].take().ok_or_else(|| {
            format!(
                "loop header bb{} has a spec segment but was never located in the bytes \
                 (fail-closed)",
                seg.start.unwrap_or(u32::MAX)
            )
        })?;
        let mut arrivals: Vec<ArrivalObligation> = Vec::with_capacity(seg.arrivals.len());
        for a in &seg.arrivals {
            let cut = spec
                .cut_points
                .iter()
                .find(|c| c.block == a.block)
                .ok_or_else(|| format!("arrival at bb{} without a cut point", a.block))?;
            if !located.iter().any(|l| l.block == a.block) {
                // FIRST ARRIVAL at this header: locate it. Try each machine
                // arrival not yet claimed by another header, in address order.
                let seg_index = spec
                    .segments
                    .iter()
                    .position(|s| s.start == Some(a.block))
                    .ok_or_else(|| format!("bb{} has no spec segment", a.block))?;
                let latch = spec.segments[seg_index].arrivals.iter().find(|x| x.block == a.block);
                let mut found: Option<LocatedCut> = None;
                if let Some(claim) = claimed.and_then(|c| c.iter().find(|c| c.block == a.block)) {
                    // A CLAIMED map is taken as stated and checked by the
                    // obligation, never adjusted. It is UNTRUSTED input, so its
                    // SHAPE is checked before anything indexes with it: a
                    // register number outside the file, or an address that is
                    // not an instruction of the emitted text, is a malformed
                    // map and must be a named `Unknown` — never a panic, which
                    // is a crash of the gate rather than a refusal by it
                    // (WS7.14 review).
                    if claim.regs.len() != cut.shared.len() {
                        return Err(format!(
                            "claimed cut point for bb{} names {} register(s) for {} shared \
                             variable(s) (fail-closed)",
                            a.block,
                            claim.regs.len(),
                            cut.shared.len()
                        ));
                    }
                    // Already checked for every claim before the entry walk;
                    // re-checked here, at the one site that indexes with it.
                    check_claimed_cut_shape(claim, code, base)?;
                    found = Some(LocatedCut {
                        block: a.block,
                        addr: claim.addr,
                        regs: claim.regs.clone(),
                    });
                } else {
                    let mut candidates: Vec<&crate::verify_output::MachineArrival> = m
                        .arrivals
                        .iter()
                        .filter(|ma| !located.iter().any(|l| l.addr == ma.addr))
                        .collect();
                    candidates.sort_by_key(|ma| ma.addr);
                    for ma in candidates {
                        if let Some(regs) = locate_cut_registers(
                            cut, a, &ma.gpr, latch, code, base, out_width, ma.addr, &cut_addrs,
                        ) {
                            found = Some(LocatedCut { block: a.block, addr: ma.addr, regs });
                            break;
                        }
                    }
                }
                let Some(loc) = found else {
                    return Err(format!(
                        "could not locate loop header bb{} in the emitted bytes: no backward-branch \
                         target's register file holds every one of its {} shared variable(s) at \
                         the arrival; cut-point map: none for this header (fail-closed)",
                        a.block,
                        cut.shared.len()
                    ));
                };
                {
                    let mut regs = loc.regs.clone();
                    regs.sort_unstable();
                    regs.dedup();
                    if regs.len() != loc.regs.len() {
                        return Err(format!(
                            "loop header bb{}: two shared variables located in the same register \
                             (fail-closed)",
                            a.block
                        ));
                    }
                }
                // Run the header's own machine segment from its seeded state.
                let tag = format!("CUT_bb{}", a.block);
                let seeds: Vec<(u8, Formula)> = cut
                    .shared
                    .iter()
                    .zip(&loc.regs)
                    .map(|(sv, &r)| (r, seed_for(&tag, r, sv)))
                    .collect();
                // O0 x WS7.14: the ABI invariant's seed — every O0 location
                // not holding a located live-in is its entry value here.
                let mut seeded = cut_state(&tag, &seeds);
                seed_abi_entry_invariant(&mut seeded, &tag, &loc.regs);
                machine_outcomes[seg_index] = Some(symbolic_machine_segment(
                    code,
                    base,
                    out_width,
                    loc.addr,
                    seeded,
                    &cut_addrs,
                )?);
                located.push(loc);
            }
            let loc = located.iter().find(|l| l.block == a.block).ok_or_else(|| {
                format!(
                    "loop header bb{} arrival before its location was fixed (fail-closed)",
                    a.block
                )
            })?;
            let ma = m.arrivals.iter().find(|ma| ma.addr == loc.addr);
            arrivals.push(ArrivalObligation {
                block: a.block,
                machine_addr: loc.addr,
                spec_reach: a.reach.clone(),
                machine_reach: ma.map(|ma| norm(&ma.reach)).unwrap_or(Formula::Bool(false)),
                values: cut
                    .shared
                    .iter()
                    .zip(&loc.regs)
                    .zip(&a.values)
                    .map(|((sv, &r), sv_spec)| {
                        let machine = match ma {
                            Some(ma) => read_reg(&ma.gpr[r as usize], sv.width),
                            None => Formula::BitVec { value: 0, width: sv.width },
                        };
                        (sv_spec.clone(), machine)
                    })
                    .collect(),
            });
        }
        let (machine_addr, locations) = match seg.start {
            None => (None, Vec::new()),
            Some(h) => {
                let l = located.iter().find(|l| l.block == h).ok_or_else(|| {
                    format!("loop header bb{h} segment before its location was fixed (fail-closed)")
                })?;
                (Some(l.addr), l.regs.clone())
            }
        };
        // O0 of this segment's own `RET`s and X18 writes (the entry
        // segment's is moved to `GateObligation::abi_residue` by the caller).
        let abi_residue = abi_guarantee_residue(&m, x18_reserved);
        machine_arrivals.push(m.arrivals.clone());
        result.push(SegmentObligation {
            start: seg.start,
            machine_addr,
            locations,
            spec_value: seg.value.clone(),
            spec_reach: seg.reach.clone(),
            // Normalized (an identity rewrite), so that a formula which
            // merely WRAPS a havoc upper half around a shared variable does
            // not read as depending on it (`mentions_havoc` is syntactic).
            machine_value: norm(&m.value),
            machine_reach: norm(&m.reach),
            arrivals,
            stray_arrivals: m.arrivals.iter().map(|ma| ma.addr).collect(),
            abi_residue,
            abi_invariant: Vec::new(),
        });
    }
    // Strays are known only once every header is located: keep the machine
    // arrival addresses no located header claims.
    for seg in &mut result {
        seg.stray_arrivals.retain(|addr| !located.iter().any(|l| l.addr == *addr));
        seg.stray_arrivals.sort_unstable();
        seg.stray_arrivals.dedup();
    }
    // O0 x WS7.14: the inductive step of the ABI invariant at EVERY machine
    // arrival at a located header — not only the ones a spec arrival is
    // paired with, because the header segment assumes the invariant whoever
    // arrives. A stray arrival continues nowhere, so it owes nothing.
    for (seg, arrivals) in result.iter_mut().zip(&machine_arrivals) {
        for ma in arrivals {
            if let Some(loc) = located.iter().find(|l| l.addr == ma.addr) {
                seg.abi_invariant.extend(abi_arrival_invariant(ma, &loc.regs));
            }
        }
    }
    Ok(result)
}

/// A `Refuted` verdict reached in a segment whose machine run stopped at a
/// STRAY cut candidate is demoted to `Unknown` (WS7.14): the disagreement may
/// be the inferred map's (a candidate that is no loop header), not the
/// bytes'. Every other verdict passes through unchanged.
fn demote_if_stray(symbol: &str, strays: &[u64], verdict: OutputVerdict) -> OutputVerdict {
    match verdict {
        OutputVerdict::Refuted { detail } if !strays.is_empty() => OutputVerdict::Unknown {
            reason: format!(
                "`{symbol}`: the machine stops at cut candidate(s) {strays:x?} that no loop \
                 header of the IR claims, so a failed obligation indicts the cut-point map, not \
                 the bytes (would have been: {detail}; fail-closed)"
            ),
        },
        other => other,
    }
}

/// Discharge an already-built [`GateObligation`] into a verdict.
///
/// O0 (the ABI guarantee) is discharged FIRST: a refutation there is a
/// miscompile whatever the value obligation says. An undecided O0 makes the
/// function undecided unless the value obligation refutes it, and an O0 that
/// needed the solver caps the grade at [VALIDATED] — the kernel certificate
/// covers the value equation only.
fn discharge_trust_ir_obligation(symbol: &str, obligation: &GateObligation) -> OutputVerdict {
    let abi = discharge_abi_guarantee(symbol, &obligation.abi_residue, &obligation.ambient_pre);
    if let AbiDischarge::Verdict(refuted @ OutputVerdict::Refuted { .. }) = abi {
        return refuted;
    }
    let kernel_eligible = matches!(abi, AbiDischarge::Structural);
    let loop_abi = discharge_loop_abi(symbol, &obligation.segments);
    let value = discharge_trust_ir_value_obligation(
        symbol,
        obligation,
        kernel_eligible,
        loop_abi.as_ref().err().map(String::as_str),
    );
    match (abi, value) {
        (_, refuted @ OutputVerdict::Refuted { .. }) => refuted,
        (AbiDischarge::Verdict(undecided), _) => undecided,
        (_, verdict) => verdict,
    }
}

/// O0 across the loop cuts (WS7.14): the ABI invariant's inductive step at
/// every arrival of every segment, then each HEADER segment's own O0 residue
/// (which rests on that invariant). `Err` carries the `Unknown` reason; there
/// is no `Refuted` here (see `verify_output::discharge_abi_loop_conjuncts`).
/// A loop verdict is solver authority already, so no grade is tracked.
fn discharge_loop_abi(symbol: &str, segments: &[SegmentObligation]) -> Result<(), String> {
    let where_ = |seg: &SegmentObligation| match seg.start {
        None => "the entry segment".to_string(),
        Some(h) => format!(
            "the segment from loop header bb{h} (claimed at {:#x})",
            seg.machine_addr.unwrap_or(0)
        ),
    };
    for seg in segments {
        discharge_abi_loop_conjuncts(symbol, &where_(seg), &seg.abi_invariant)?;
    }
    for seg in segments.iter().filter(|seg| seg.start.is_some()) {
        discharge_abi_loop_conjuncts(symbol, &where_(seg), &seg.abi_residue)?;
    }
    Ok(())
}

/// The value, reach and modeling obligations of [`discharge_trust_ir_obligation`].
/// `kernel_eligible` is false when some OTHER conjunct of the function (O0) was
/// discharged by the solver alone, which caps the grade at [VALIDATED].
/// `loop_abi_unproven` (WS7.14) is the reason the ABI invariant across the
/// loop cuts did not discharge: every HEADER segment assumes it, so none of
/// their verdicts may be reported — the function is `Unknown` unless the
/// ENTRY segment (which assumes nothing) already refutes it.
fn discharge_trust_ir_value_obligation(
    symbol: &str,
    obligation: &GateObligation,
    kernel_eligible: bool,
    loop_abi_unproven: Option<&str>,
) -> OutputVerdict {
    let GateObligation {
        spec_value,
        spec_reach,
        machine_value,
        machine_reach,
        spec_side_conditions,
        ambient_pre,
        segments,
        ..
    } = obligation;

    // (3) VACUITY FIREWALL. If `spec_reach` is unsatisfiable, every obligation
    // below is vacuously true. That is NOT a proof; it is a hole. Reject.
    //
    // The AMBIENT assumptions are part of the antecedent of both obligations
    // (WS7.13), so they are firewalled JOINTLY with `spec_reach`: an ambient
    // list that contradicted itself, or contradicted the IR's guards, would
    // make the conditional equality hold for any bytes exactly as an
    // unsatisfiable `spec_reach` does.
    //
    // With LOOPS (WS7.14) the entry segment may legitimately never return
    // directly (every `ret` is after the loop), so the firewalled predicate
    // is "the entry segment returns OR arrives at some cut point"; each
    // header segment is firewalled the same way below.
    let entry_strays: &[u64] = segments.first().map_or(&[], |s| s.stray_arrivals.as_slice());
    let mut antecedent: Vec<Formula> = ambient_pre.clone();
    let entry_total: Formula = match segments.first() {
        Some(entry) if !entry.arrivals.is_empty() => {
            let mut ways = vec![spec_reach.clone()];
            ways.extend(entry.arrivals.iter().map(|a| a.spec_reach.clone()));
            Formula::Or(ways)
        }
        _ => spec_reach.clone(),
    };
    if !matches!(entry_total, Formula::Bool(true)) {
        antecedent.push(entry_total.clone());
    }
    if !antecedent.is_empty() {
        // NOT(a AND b AND ..) == OR(NOT a, NOT b, ..), inside the connective
        // set `formula_to_term` lowers.
        let negated = Formula::Or(antecedent.into_iter().map(|c| Formula::Not(b(c))).collect());
        match discharge_valid(&negated) {
            Discharge::Proven => {
                return OutputVerdict::Unknown {
                    reason: format!(
                        "VACUOUS obligation for `{symbol}`: the IR's own assert guards and the \
                         ambient assumptions are jointly unsatisfiable, so no input reaches a \
                         return and the equality would hold for any bytes; refusing to report \
                         that as proven"
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
    // These are solver-validated from `spec_reach`, not assumed. This runs
    // AFTER the vacuity firewall above, because an unsatisfiable `spec_reach`
    // makes every implication out of it trivially valid, and a side condition
    // "discharged" that way would establish nothing.
    //
    // A failure here is `Unknown`, NEVER `Refuted`: it means the gate could not
    // justify its own model of the IR, which is not evidence against the bytes.
    //
    // With LOOPS a side condition may belong to a header segment, whose
    // antecedent is that segment's reach, not the entry's; that binding is
    // not carried yet, so the combination is refused (WS7.14).
    if !segments.is_empty() && !spec_side_conditions.is_empty() {
        return OutputVerdict::Unknown {
            reason: format!(
                "`{symbol}` has loops and {} spec-side modeling precondition(s) (narrow \
                 shifts); per-segment side conditions are not modeled (fail-closed)",
                spec_side_conditions.len()
            ),
        };
    }
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
        let mut disjuncts = vec![Formula::Not(b(spec_reach.clone())), machine_reach.clone()];
        // Ambient machine-environment assumptions weaken the claim to "for
        // every well-formed stack" — spelled as extra NOT-disjuncts, staying
        // inside the Or/Not connective set `formula_to_term` lowers.
        for amb in ambient_pre {
            disjuncts.insert(0, Formula::Not(b(amb.clone())));
        }
        let implication = Formula::Or(disjuncts);
        match discharge_valid(&implication) {
            Discharge::Proven => {}
            Discharge::CounterExample => {
                return demote_if_stray(
                    symbol,
                    entry_strays,
                    OutputVerdict::Refuted {
                        detail: format!(
                            "emitted bytes for fn `{symbol}` TRAP on an input the IR returns \
                             normally on (ay found a counterexample — the machine does not \
                             reach a RET where the IR does)"
                        ),
                    },
                );
            }
            Discharge::Unknown(reason) => {
                return OutputVerdict::Unknown {
                    reason: format!("reachability obligation did not conclude: {reason}"),
                };
            }
        }
    }

    // (5) OBLIGATION B — the values agree on every input the IR returns on,
    // under the ambient machine-environment assumptions (if any). The
    // conjunction is spelled NOT(OR(NOT ...)) to stay inside the lowered
    // connective set.
    let mut pre_conjuncts: Vec<Formula> = Vec::new();
    if !matches!(spec_reach, Formula::Bool(true)) {
        pre_conjuncts.push(spec_reach.clone());
    }
    pre_conjuncts.extend(ambient_pre.iter().cloned());
    let pre_owned: Option<Formula> = match pre_conjuncts.len() {
        0 => None,
        1 => Some(pre_conjuncts.pop().expect("len checked")),
        _ => Some(Formula::Not(b(Formula::Or(
            pre_conjuncts.into_iter().map(|c| Formula::Not(b(c))).collect(),
        )))),
    };
    let pre = pre_owned.as_ref();
    let entry_value = match discharge_equal_pre(machine_value, spec_value, pre) {
        Discharge::Proven => OutputVerdict::Proven {
            // The value certificate does not certify the solver-only modeling
            // conditions or reachability judgment above. Nor does the existing
            // conditional value reconstruction bind this exact precondition.
            // Until those obligations carry their own composed kernel evidence,
            // the whole function has at most solver authority. Keep all solver
            // checks, including their Unknown/Refuted outcomes, and let the
            // existing strict emission policy refuse this lower evidence grade.
            //
            // Trust (2026-10-03): a spec-side modeling condition (the narrow
            // shift's `amount < width`) may now carry its OWN kernel evidence.
            // With `pre` absent, `spec_reach` is `true`, so each condition is an
            // unconditional claim over the inputs and is kernel-proved as the
            // value equality `ite(condition, 1, 0) == 1`; the function is
            // [PROVED] only when the value AND every condition are.
            //
            // A LOOP verdict (non-empty `segments`) is solver authority only:
            // the kernel certificate covers one value equality, and the
            // segment induction is spelled entirely in solver checks.
            evidence: if kernel_eligible
                && matches!(machine_reach, Formula::Bool(true))
                && pre.is_none()
                && segments.is_empty()
            {
                kernel_value_and_side_conditions(machine_value, spec_value, spec_side_conditions)
                    .unwrap_or(ProvenEvidence::AyValidated)
            } else {
                ProvenEvidence::AyValidated
            },
        },
        Discharge::CounterExample => {
            return demote_if_stray(
                symbol,
                entry_strays,
                OutputVerdict::Refuted {
                    detail: format!(
                        "emitted bytes do not equal the trust-ir semantics for fn `{symbol}` \
                         (ay found a counterexample input — miscompile)"
                    ),
                },
            );
        }
        Discharge::Unknown(reason) => return OutputVerdict::Unknown { reason },
    };
    if segments.is_empty() {
        return entry_value;
    }

    // (6) CUT-POINT SEGMENTS (WS7.14). For every segment: the vacuity
    // firewall over "returns or arrives somewhere"; for a header segment its
    // return half (the entry's was steps 4 and 5); and every arrival:
    // `spec arrives at H'  =>  machine stops at H's claimed address AND every
    // located shared variable holds the spec's value`. A counterexample that
    // depends on a havoc variable indicts the cut-point map, not the bytes,
    // and is `Unknown`; one over shared variables alone is `Refuted`.
    for seg in segments {
        if let (Some(_), Some(reason)) = (seg.start, loop_abi_unproven) {
            return OutputVerdict::Unknown { reason: reason.to_string() };
        }
        match discharge_segment(symbol, seg, ambient_pre) {
            None => {}
            Some(verdict) => return demote_if_stray(symbol, &seg.stray_arrivals, verdict),
        }
    }
    if let Some(reason) = loop_abi_unproven {
        return OutputVerdict::Unknown { reason: reason.to_string() };
    }
    OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }
}

/// Discharge one segment's obligations (WS7.14); `None` when every one of
/// them is proven, otherwise the verdict to return.
fn discharge_segment(
    symbol: &str,
    seg: &SegmentObligation,
    ambient_pre: &[Formula],
) -> Option<OutputVerdict> {
    let where_ = match seg.start {
        None => "the entry segment".to_string(),
        Some(h) => format!(
            "the segment from loop header bb{h} (claimed at {:#x})",
            seg.machine_addr.unwrap_or(0)
        ),
    };
    let not_ambient: Vec<Formula> =
        ambient_pre.iter().map(|a| Formula::Not(b(a.clone()))).collect();

    // Vacuity: some way out of the segment must be satisfiable.
    if seg.start.is_some() {
        let mut ways = vec![seg.spec_reach.clone()];
        ways.extend(seg.arrivals.iter().map(|a| a.spec_reach.clone()));
        let total = Formula::Or(ways);
        if !matches!(total, Formula::Bool(true)) {
            let mut conj: Vec<Formula> = ambient_pre.to_vec();
            conj.push(total);
            let negated = Formula::Or(conj.into_iter().map(|c| Formula::Not(b(c))).collect());
            match discharge_valid(&negated) {
                Discharge::Proven => {
                    return Some(OutputVerdict::Unknown {
                        reason: format!(
                            "VACUOUS obligation for `{symbol}` in {where_}: no input of the \
                             segment returns or reaches a cut point; refusing to report that \
                             as proven"
                        ),
                    });
                }
                Discharge::CounterExample => {}
                Discharge::Unknown(reason) => {
                    return Some(OutputVerdict::Unknown {
                        reason: format!("vacuity check for {where_} did not conclude: {reason}"),
                    });
                }
            }
        }

        // Return half of a header segment: reach, then value.
        if !matches!(seg.machine_reach, Formula::Bool(true)) {
            let mut disjuncts = not_ambient.clone();
            disjuncts.push(Formula::Not(b(seg.spec_reach.clone())));
            disjuncts.push(seg.machine_reach.clone());
            match discharge_valid(&Formula::Or(disjuncts)) {
                Discharge::Proven => {}
                Discharge::CounterExample => {
                    return Some(if mentions_havoc(&seg.machine_reach) {
                        OutputVerdict::Unknown {
                            reason: format!(
                                "in {where_} of `{symbol}` whether the machine reaches a RET \
                                 depends on state the cut-point map does not relate to the IR \
                                 (fail-closed)"
                            ),
                        }
                    } else {
                        OutputVerdict::Refuted {
                            detail: format!(
                                "emitted bytes for fn `{symbol}` TRAP on an input the IR \
                                 returns normally on, in {where_} (ay found a counterexample)"
                            ),
                        }
                    });
                }
                Discharge::Unknown(reason) => {
                    return Some(OutputVerdict::Unknown {
                        reason: format!(
                            "reachability obligation for {where_} did not conclude: {reason}"
                        ),
                    });
                }
            }
        }
        let mut pre_conj: Vec<Formula> = ambient_pre.to_vec();
        if !matches!(seg.spec_reach, Formula::Bool(true)) {
            pre_conj.push(seg.spec_reach.clone());
        }
        let pre = match pre_conj.len() {
            0 => None,
            1 => Some(pre_conj.remove(0)),
            _ => Some(Formula::Not(b(Formula::Or(
                pre_conj.into_iter().map(|c| Formula::Not(b(c))).collect(),
            )))),
        };
        if !matches!(seg.spec_reach, Formula::Bool(false)) {
            match discharge_equal_pre(&seg.machine_value, &seg.spec_value, pre.as_ref()) {
                Discharge::Proven => {}
                Discharge::CounterExample => {
                    return Some(if mentions_havoc(&seg.machine_value) {
                        OutputVerdict::Unknown {
                            reason: format!(
                                "in {where_} of `{symbol}` the machine's return value depends \
                                 on state the cut-point map does not relate to the IR \
                                 (a live-in the map could not locate; fail-closed)"
                            ),
                        }
                    } else {
                        OutputVerdict::Refuted {
                            detail: format!(
                                "emitted bytes do not equal the trust-ir semantics for fn \
                                 `{symbol}` in {where_} (ay found a counterexample input — \
                                 miscompile)"
                            ),
                        }
                    });
                }
                Discharge::Unknown(reason) => return Some(OutputVerdict::Unknown { reason }),
            }
        }
    }

    // Arrivals.
    for a in &seg.arrivals {
        if matches!(a.spec_reach, Formula::Bool(false)) {
            continue;
        }
        let mut conj: Vec<Formula> = Vec::with_capacity(a.values.len() + 1);
        if !matches!(a.machine_reach, Formula::Bool(true)) {
            conj.push(a.machine_reach.clone());
        }
        for (spec_v, machine_v) in &a.values {
            conj.push(Formula::Eq(b(machine_v.clone()), b(spec_v.clone())));
        }
        let consequent = match conj.len() {
            0 => Formula::Bool(true),
            1 => conj.remove(0),
            _ => Formula::And(conj),
        };
        let mut disjuncts = not_ambient.clone();
        disjuncts.push(Formula::Not(b(a.spec_reach.clone())));
        disjuncts.push(consequent);
        match discharge_valid(&Formula::Or(disjuncts)) {
            Discharge::Proven => {}
            Discharge::CounterExample => {
                let havoc = mentions_havoc(&a.machine_reach)
                    || a.values.iter().any(|(_, m)| mentions_havoc(m));
                return Some(if havoc {
                    OutputVerdict::Unknown {
                        reason: format!(
                            "at the arrival of {where_} of `{symbol}` at loop header bb{} \
                             ({:#x}) a located live-in depends on state the cut-point map does \
                             not relate to the IR (fail-closed)",
                            a.block, a.machine_addr
                        ),
                    }
                } else {
                    OutputVerdict::Refuted {
                        detail: format!(
                            "emitted bytes for fn `{symbol}` do not carry the IR's loop state \
                             into loop header bb{} ({:#x}) from {where_}: ay found an input on \
                             which the machine does not reach the header with the IR's live-in \
                             values (miscompile)",
                            a.block, a.machine_addr
                        ),
                    }
                });
            }
            Discharge::Unknown(reason) => {
                return Some(OutputVerdict::Unknown {
                    reason: format!(
                        "arrival obligation of {where_} at loop header bb{} did not conclude: \
                         {reason}",
                        a.block
                    ),
                });
            }
        }
    }
    None
}

/// Trust (2026-09-30, plan §5 fail-open item 1): [`verify_trust_ir_output_preserved`]
/// with the converter's TRAP ORACLE in place of the shipping lowering. Every
/// shipping entry point now refuses an `Assert`-bearing body
/// (`ModuleLirError::ImplicitPanicUnfaithful`), so the gate's `Assert`-reach
/// model is exercised over the pre-refusal `Brif`/`Trap` bytes through this
/// helper — and only in unit tests. The spec side is untouched:
/// [`verify_trust_ir_bytes`] derives it from `source.module` as always.
#[cfg(test)]
pub(crate) fn verify_with_trap_oracle(
    source: &TrustIrGateSource,
    backend: &TrustCgCodegenBackend,
) -> (OutputVerdict, Option<Vec<u8>>) {
    let function = source.module.function_by_id(source.func_id).expect("subject function");
    let lir = crate::module_to_lir::lower_trust_ir_function_to_lir_trap_assert_oracle(
        &source.module,
        function,
        false,
    )
    .expect("the trap oracle lowers the subject");
    let obj = backend
        .emit_object_with_trust_ir_globals(&[lir], &source.module)
        .expect("the oracle's LIR emits");
    let verdict = verify_trust_ir_bytes(source, &obj, backend.target_arch());
    (verdict, Some(obj))
}

/// The shipping gate path refuses an `Assert`-bearing subject at the converter,
/// by name, before any byte is emitted.
#[cfg(test)]
pub(crate) fn assert_shipping_gate_refuses_implicit_panic(
    source: &TrustIrGateSource,
    backend: &TrustCgCodegenBackend,
) {
    match verify_trust_ir_output_preserved(source, backend) {
        (OutputVerdict::Unknown { reason }, None) => assert!(
            reason.contains("[implicit-panic-unfaithful]"),
            "the shipping converter must refuse the Assert by name: {reason}"
        ),
        other => panic!("the shipping gate must refuse an implicit panic, got {other:?}"),
    }
}

#[cfg(test)]
mod tests_gate_grade {
    use super::*;

    fn constant_obligation() -> GateObligation {
        let value = Formula::BitVec { value: 7, width: 32 };
        GateObligation {
            spec_value: value.clone(),
            spec_reach: Formula::Bool(true),
            machine_value: value,
            machine_reach: Formula::Bool(true),
            out_width: 32,
            spec_side_conditions: Vec::new(),
            ambient_pre: Vec::new(),
            abi_residue: Vec::new(),
            segments: Vec::new(),
        }
    }

    fn predicate() -> Formula {
        Formula::Var("grade_condition".into(), Sort::Bool)
    }

    fn tautology() -> Formula {
        Formula::Or(vec![predicate(), Formula::Not(b(predicate()))])
    }

    fn assert_solver_validated(obligation: &GateObligation) {
        let verdict = discharge_trust_ir_obligation("grade_test", obligation);
        assert!(
            matches!(verdict, OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }),
            "solver-only obligations must cap the whole-function grade: {verdict:?}"
        );
        assert!(verdict.kernel_proofs().is_empty());
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn unconditional_value_keeps_kernel_evidence() {
        let verdict = discharge_trust_ir_obligation("grade_test", &constant_obligation());
        assert!(verdict.is_kernel_proved(), "positive control: {verdict:?}");
    }

    #[test]
    fn solver_only_modeling_condition_caps_kernel_grade() {
        // The equality is independently kernel-provable. Only the additional
        // modeling obligation distinguishes this from the positive control.
        let mut obligation = constant_obligation();
        obligation.spec_side_conditions.push(tautology());
        assert_solver_validated(&obligation);
    }

    #[test]
    fn solver_only_machine_reach_caps_kernel_grade() {
        let mut obligation = constant_obligation();
        obligation.machine_reach = tautology();
        assert_solver_validated(&obligation);
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn source_and_ambient_preconditions_cap_conditional_value_evidence() {
        // Identical subtraction formulas take the existing conditional
        // structured-reflexivity route. Prove that route is live so the two
        // negative controls cannot pass merely because value reconstruction
        // happened to decline this fixture.
        let value = Formula::BvSub(b(wn(0)), b(Formula::BitVec { value: 1, width: 32 }), 32);
        assert!(matches!(
            try_kernel_recheckable_proof(&value, &value, Some(&predicate())),
            Some(ProvenEvidence::KernelInstantiated { .. })
        ));
        let mut obligation = constant_obligation();
        obligation.spec_value = value.clone();
        obligation.machine_value = value;
        obligation.spec_reach = predicate();
        assert_solver_validated(&obligation);

        obligation.spec_reach = Formula::Bool(true);
        obligation.ambient_pre.push(predicate());
        assert_solver_validated(&obligation);
    }

    #[test]
    fn invalid_modeling_condition_remains_unknown() {
        let mut obligation = constant_obligation();
        obligation.spec_side_conditions.push(predicate());
        let verdict = discharge_trust_ir_obligation("grade_test", &obligation);
        assert!(matches!(
            verdict,
            OutputVerdict::Unknown { reason } if reason.contains("modeling precondition")
        ));
    }

    #[test]
    fn spurious_machine_trap_remains_refuted() {
        let mut obligation = constant_obligation();
        obligation.machine_reach = predicate();
        let verdict = discharge_trust_ir_obligation("grade_test", &obligation);
        assert!(matches!(
            verdict,
            OutputVerdict::Refuted { detail } if detail.contains("TRAP")
        ));
    }

    #[test]
    fn wrong_value_with_solver_only_condition_remains_refuted() {
        let mut obligation = constant_obligation();
        obligation.spec_side_conditions.push(tautology());
        obligation.machine_value = Formula::BitVec { value: 8, width: 32 };
        let verdict = discharge_trust_ir_obligation("grade_test", &obligation);
        assert!(matches!(verdict, OutputVerdict::Refuted { .. }));
    }

    fn abi_conjunct(claim: Formula) -> AbiConjunct {
        AbiConjunct { slot: "X19".into(), claim }
    }

    /// O0 discharged by the solver alone caps the whole function exactly as
    /// the other solver-only conjuncts do: the kernel certificate covers the
    /// value equation, not the ABI conjunct.
    #[test]
    fn solver_only_abi_residue_caps_kernel_grade() {
        let mut obligation = constant_obligation();
        obligation.abi_residue.push(abi_conjunct(tautology()));
        assert_solver_validated(&obligation);
    }

    /// An O0 violation is a miscompile even when the value is right, and it
    /// dominates an undecided value side (here: a vacuous spec).
    #[test]
    fn abi_violation_is_refuted_and_dominates() {
        let violated = abi_conjunct(Formula::Not(b(Formula::Bool(true))));
        let mut obligation = constant_obligation();
        obligation.abi_residue.push(violated.clone());
        let verdict = discharge_trust_ir_obligation("grade_test", &obligation);
        assert!(
            matches!(&verdict, OutputVerdict::Refuted { detail } if detail.contains("O0")),
            "{verdict:?}"
        );
        obligation.spec_reach = Formula::Bool(false);
        assert!(matches!(
            discharge_trust_ir_obligation("grade_test", &obligation),
            OutputVerdict::Refuted { .. }
        ));
    }

    /// An undecided O0 conjunct (one that reads memory and has a counterexample
    /// only through it) makes a value-Proven function Unknown, never Proven.
    #[test]
    fn memory_dependent_abi_counterexample_is_unknown() {
        let mem = crate::verify_output::mem_array_var();
        let slot = Formula::Select(b(mem), b(xn(1)));
        let byte = Formula::BvExtract { inner: b(xn(19)), high: 7, low: 0 };
        let mut obligation = constant_obligation();
        obligation.abi_residue.push(abi_conjunct(Formula::Eq(b(slot), b(byte))));
        assert!(matches!(
            discharge_trust_ir_obligation("grade_test", &obligation),
            OutputVerdict::Unknown { reason } if reason.contains("O0")
        ));
    }

    #[test]
    fn unsatisfiable_source_reach_remains_unknown() {
        let mut obligation = constant_obligation();
        obligation.spec_reach = Formula::Bool(false);
        let verdict = discharge_trust_ir_obligation("grade_test", &obligation);
        assert!(matches!(
            verdict,
            OutputVerdict::Unknown { reason } if reason.contains("VACUOUS")
        ));
    }
}

/// O0 ACROSS A LOOP CUT (WS7.14 x increment-5 step 5.0): the ABI invariant a
/// header segment is seeded with, its inductive step at an arrival, and the
/// rule that a failure of either is `Unknown`, never `Refuted` — except where
/// the ENTRY segment, which assumes nothing, refutes on its own.
#[cfg(test)]
mod tests_loop_abi {
    use super::*;
    use crate::verify_output::{AbiExit, MachineArrival};

    fn bv(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(64))
    }

    fn arrival(state: &MachineState, reach: Formula) -> MachineArrival {
        MachineArrival {
            addr: 0x40,
            reach,
            gpr: state.gpr.to_vec(),
            abi: AbiExit::at(state, state.read_gpr(30, 64)),
        }
    }

    /// A header-segment state exactly as `build_segment_obligations` seeds it:
    /// everything havoc, then the ABI invariant, then `live_in` re-seeded.
    fn seeded(live_in: &[u8]) -> MachineState {
        let seeds: Vec<(u8, Formula)> =
            live_in.iter().map(|&r| (r, bv(&format!("SHARED_X{r}")))).collect();
        let mut st = cut_state("CUT_bb1", &seeds);
        seed_abi_entry_invariant(&mut st, "CUT_bb1", live_in);
        st
    }

    #[test]
    fn an_untouched_seeded_header_carries_the_invariant_structurally() {
        // The seed round-trips through `AbiExit::at`: nothing to discharge —
        // including D8-D15, whose UPPER halves stay havoc.
        let st = seeded(&[]);
        assert!(abi_arrival_invariant(&arrival(&st, Formula::Bool(true)), &[]).is_empty());
        assert!(mentions_havoc(&st.fpr[8]), "the upper half of V8 must stay havoc");
        assert!(!mentions_havoc(&st.gpr[19]) && !mentions_havoc(&st.sp));
        // The located live-in keeps its own seed; the ABI seed does not
        // overwrite it.
        let st = seeded(&[19]);
        assert_eq!(st.gpr[19], bv("SHARED_X19"));
    }

    #[test]
    fn a_clobbered_callee_saved_register_breaks_the_invariant_by_name() {
        let mut st = seeded(&[]);
        st.gpr[19] = bv("X0");
        let inv = abi_arrival_invariant(&arrival(&st, Formula::Bool(true)), &[]);
        assert_eq!(inv.len(), 1, "{inv:?}");
        assert!(inv[0].slot.starts_with("X19 "), "{inv:?}");
        let err = discharge_abi_loop_conjuncts("f", "the segment", &inv).expect_err("not valid");
        assert!(err.contains("X19") && err.contains("fail-closed"), "{err}");
    }

    #[test]
    fn sp_lr_and_d_lane_moves_are_each_named() {
        let mut st = seeded(&[]);
        st.sp = Formula::BvSub(b(bv("SP")), b(Formula::BitVec { value: 16, width: 64 }), 64);
        st.gpr[30] = bv("X0");
        st.fpr[9] = Formula::Var("V0".into(), Sort::BitVec(128));
        let slots: Vec<String> = abi_arrival_invariant(&arrival(&st, Formula::Bool(true)), &[])
            .into_iter()
            .map(|c| c.slot)
            .collect();
        assert!(slots.iter().any(|s| s.starts_with("SP ")), "{slots:?}");
        assert!(slots.iter().any(|s| s.starts_with("D9 ")), "{slots:?}");
        assert!(slots.iter().any(|s| s.starts_with("return target")), "{slots:?}");
        assert_eq!(slots.len(), 3, "{slots:?}");
    }

    #[test]
    fn a_live_in_register_and_an_unreached_arrival_owe_nothing() {
        let mut st = seeded(&[19]);
        st.gpr[19] = bv("X0");
        assert!(abi_arrival_invariant(&arrival(&st, Formula::Bool(true)), &[19]).is_empty());
        // ... but X19 IS owed when the TARGET header does not locate a live-in
        // there, whatever this segment's own seed was.
        assert_eq!(abi_arrival_invariant(&arrival(&st, Formula::Bool(true)), &[]).len(), 1);
        st.sp = bv("X1");
        assert!(abi_arrival_invariant(&arrival(&st, Formula::Bool(false)), &[]).is_empty());
    }

    #[test]
    fn the_inductive_step_is_conditioned_on_reaching_the_arrival() {
        // X19 is the entry value exactly on the paths that arrive: valid.
        let p = Formula::Var("p".into(), Sort::Bool);
        let mut st = seeded(&[]);
        st.gpr[19] = Formula::Ite(b(p.clone()), b(bv("X19")), b(bv("X0")));
        let inv = abi_arrival_invariant(&arrival(&st, p.clone()), &[]);
        assert_eq!(inv.len(), 1, "not structural, so the solver is asked: {inv:?}");
        assert_eq!(discharge_abi_loop_conjuncts("f", "seg", &inv), Ok(true));
        // The same register on the OTHER paths: refuted claim, so `Unknown`.
        let inv = abi_arrival_invariant(&arrival(&st, Formula::Not(b(p))), &[]);
        assert!(discharge_abi_loop_conjuncts("f", "seg", &inv).is_err());
        assert_eq!(discharge_abi_loop_conjuncts("f", "seg", &[]), Ok(false));
    }

    fn falsifiable(slot: &str) -> AbiConjunct {
        AbiConjunct { slot: slot.into(), claim: Formula::Eq(b(bv("X19")), b(bv("X20"))) }
    }

    fn c32(v: i128) -> Formula {
        Formula::BitVec { value: v, width: 32 }
    }

    /// A loop obligation whose entry segment is proven and whose ONE header
    /// segment returns `header_machine` where the IR returns 7.
    fn loop_obligation(header_machine: i128) -> GateObligation {
        let segment = |start: Option<u32>, machine: i128| SegmentObligation {
            start,
            machine_addr: start.map(|_| 0x40),
            locations: Vec::new(),
            spec_value: c32(7),
            spec_reach: Formula::Bool(true),
            machine_value: c32(machine),
            machine_reach: Formula::Bool(true),
            arrivals: Vec::new(),
            stray_arrivals: Vec::new(),
            abi_residue: Vec::new(),
            abi_invariant: Vec::new(),
        };
        GateObligation {
            spec_value: c32(7),
            spec_reach: Formula::Bool(true),
            machine_value: c32(7),
            machine_reach: Formula::Bool(true),
            out_width: 32,
            spec_side_conditions: Vec::new(),
            ambient_pre: Vec::new(),
            abi_residue: Vec::new(),
            segments: vec![segment(None, 7), segment(Some(1), header_machine)],
        }
    }

    #[test]
    fn controls_a_correct_loop_proves_and_a_wrong_header_value_refutes() {
        assert!(matches!(
            discharge_trust_ir_obligation("f", &loop_obligation(7)),
            OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }
        ));
        assert!(matches!(
            discharge_trust_ir_obligation("f", &loop_obligation(5)),
            OutputVerdict::Refuted { .. }
        ));
    }

    #[test]
    fn an_unproven_invariant_withholds_every_header_verdict() {
        // Wherever the inductive step sits — the entry segment's arrival or the
        // header's own — the function is `Unknown`: neither the header's
        // `Proven` nor its `Refuted` may be reported over an assumed seed.
        for (seg, header_machine) in [(0usize, 7i128), (1, 7), (0, 5), (1, 5)] {
            let mut ob = loop_obligation(header_machine);
            ob.segments[seg].abi_invariant.push(falsifiable("X19 at the arrival at 0x40"));
            match discharge_trust_ir_obligation("f", &ob) {
                OutputVerdict::Unknown { reason } => {
                    assert!(reason.contains("O0") && reason.contains("X19"), "{reason}")
                }
                other => panic!("segment {seg}, header value {header_machine}: {other:?}"),
            }
        }
    }

    #[test]
    fn the_entry_segment_still_refutes_without_the_invariant() {
        let mut ob = loop_obligation(7);
        ob.machine_value = c32(5);
        ob.segments[0].machine_value = c32(5);
        ob.segments[1].abi_invariant.push(falsifiable("X19 at the arrival at 0x40"));
        assert!(matches!(discharge_trust_ir_obligation("f", &ob), OutputVerdict::Refuted { .. }));
    }

    #[test]
    fn a_header_segment_o0_residue_is_unknown_where_the_entry_one_refutes() {
        let mut ob = loop_obligation(7);
        ob.segments[1].abi_residue.push(falsifiable("X19"));
        assert!(
            matches!(discharge_trust_ir_obligation("f", &ob), OutputVerdict::Unknown { .. }),
            "a header segment's O0 rests on the invariant: never Refuted"
        );
        // Control: the SAME conjunct as the entry segment's O0 is a miscompile.
        let mut ob = loop_obligation(7);
        ob.abi_residue.push(falsifiable("X19"));
        assert!(matches!(discharge_trust_ir_obligation("f", &ob), OutputVerdict::Refuted { .. }));
        // ... and a VALID header residue only caps nothing further (loops are
        // solver authority already).
        let mut ob = loop_obligation(7);
        ob.segments[1].abi_residue.push(AbiConjunct {
            slot: "X19".into(),
            claim: Formula::Eq(b(bv("X19")), b(bv("X19"))),
        });
        assert!(matches!(
            discharge_trust_ir_obligation("f", &ob),
            OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }
        ));
    }
}

// ===========================================================================
// PART 3 — THE WHOLE-MODULE BUILD GATE
// ===========================================================================

/// Require every per-function clone to agree on the exact source global table
/// and on every module table that can affect canonical initializer bytes.
///
/// The frontend renames one function in each clone, so comparing whole Modules
/// would reject valid work. These are precisely the non-function inputs read by
/// the canonical global encoder today. The encoded `ObjectGlobal` vectors are
/// compared as a second, downstream tripwire.
fn canonical_gate_global_module<'a>(
    sources: &'a [TrustIrGateSource],
) -> Result<&'a Module, VerifyError> {
    let first = sources.first().ok_or(VerifyError::EmptyModule)?;
    let first_globals = assembled_internal_object_globals(&first.module).map_err(|error| {
        VerifyError::ModuleEmitFailed {
            reason: format!("source global table is not emit-ready: {error}"),
        }
    })?;

    for (index, source) in sources.iter().enumerate().skip(1) {
        // One shared module needs no table-by-table comparison (it was
        // O(module) per function).
        let same_source_context = std::sync::Arc::ptr_eq(&source.module, &first.module)
            || source.module.globals == first.module.globals
            && source.module.types == first.module.types
            && source.module.structs == first.module.structs
            && source.module.enums == first.module.enums
            && source.module.records == first.module.records
            && source.module.closure_types == first.module.closure_types
            && source.module.target_info == first.module.target_info;
        if !same_source_context {
            return Err(VerifyError::ModuleEmitFailed {
                reason: format!(
                    "gate source #{index} (`{}`) carries a different global table or global \
                     encoding context than source #0 (`{}`); refusing to choose one clone's \
                     storage image for the merged object",
                    source.symbol, first.symbol
                ),
            });
        }
        let globals = assembled_internal_object_globals(&source.module).map_err(|error| {
            VerifyError::ModuleEmitFailed {
                reason: format!(
                    "gate source #{index} (`{}`) has a non-emittable global table: {error}",
                    source.symbol
                ),
            }
        })?;
        if globals != first_globals {
            return Err(VerifyError::ModuleEmitFailed {
                reason: format!(
                    "gate source #{index} (`{}`) canonicalizes to different object-global \
                     bytes/attributes than source #0 (`{}`)",
                    source.symbol, first.symbol
                ),
            });
        }
    }
    Ok(&first.module)
}

/// Emit an explicitly ungated Trust-IR codegen unit without dropping the
/// assembled module's global definitions.
///
/// This is not proof authority: it exists solely for the user's explicit
/// `-Ztrust-cg-output-gate=off` acknowledgement. It still enforces identity,
/// table agreement, canonical encoding, and collision checks.
pub fn emit_trust_ir_module_object_unverified(
    sources: &[TrustIrGateSource],
    module: &CompiledModule,
    backend: &TrustCgCodegenBackend,
) -> Result<EmittedModuleObject, VerifyError> {
    if sources.is_empty() || module.lir_functions.is_empty() {
        return Err(VerifyError::EmptyModule);
    }
    if sources.len() != module.lir_functions.len() {
        return Err(VerifyError::ModuleEmitFailed {
            reason: format!(
                "{} gate source(s) for {} lowered function(s)",
                sources.len(),
                module.lir_functions.len()
            ),
        });
    }
    for (index, (source, function)) in sources.iter().zip(&module.lir_functions).enumerate() {
        if source.symbol != function.name {
            return Err(VerifyError::ModuleEmitFailed {
                reason: format!(
                    "position {index} carries gate symbol `{}` but lowered function `{}`",
                    source.symbol, function.name
                ),
            });
        }
    }
    let source_module = canonical_gate_global_module(sources)?;
    let emitted = backend.emit_module_object_with_trust_ir_globals(module, source_module).map_err(
        |error| VerifyError::ModuleEmitFailed {
            reason: format!("globals-aware emit_module_object failed: {error:?}"),
        },
    )?;
    backend
        .require_object_target(&emitted.bytes)
        .map_err(|reason| VerifyError::ModuleEmitFailed { reason })?;
    Ok(emitted)
}

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
    statics: &[trust_cg_codegen::pipeline::ObjectGlobal],
    policy: EmitPolicy,
    backend: &TrustCgCodegenBackend,
) -> Result<(VerifiedModuleObject, CertificationReport), VerifyError> {
    emit_trust_ir_module_object_impl(sources, linkage, statics, policy, backend, false)
        .map(|(object, report, _)| (object, report))
}

/// The same gate and verdict policy, with opt-in non-authorizing evidence
/// retention. A capture error is separate from the original emission verdict.
pub fn emit_trust_ir_module_object_with_replay(
    sources: &[TrustIrGateSource],
    linkage: &[FunctionLinkage],
    statics: &[trust_cg_codegen::pipeline::ObjectGlobal],
    policy: EmitPolicy,
    backend: &TrustCgCodegenBackend,
) -> Result<
    (
        VerifiedModuleObject,
        CertificationReport,
        Result<crate::object_replay::ObjectReplayArtifact, String>,
    ),
    VerifyError,
> {
    emit_trust_ir_module_object_impl(sources, linkage, statics, policy, backend, true)
}

fn emit_trust_ir_module_object_impl(
    sources: &[TrustIrGateSource],
    linkage: &[FunctionLinkage],
    statics: &[trust_cg_codegen::pipeline::ObjectGlobal],
    policy: EmitPolicy,
    backend: &TrustCgCodegenBackend,
    capture: bool,
) -> Result<
    (
        VerifiedModuleObject,
        CertificationReport,
        Result<crate::object_replay::ObjectReplayArtifact, String>,
    ),
    VerifyError,
> {
    if sources.is_empty() {
        return Err(VerifyError::EmptyModule);
    }
    let source_module = canonical_gate_global_module(sources)?;
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
    let mut observations = if capture && sources.len() <= 32 {
        Ok(Vec::with_capacity(sources.len()))
    } else {
        Err("object replay not requested or function population exceeds 32".to_string())
    };
    for source in sources {
        let (verdict, bytes) = verify_trust_ir_output_preserved(source, backend);
        if observations.is_ok() {
            match bytes
                .as_deref()
                .ok_or_else(|| "gate produced no function object".to_string())
                .and_then(|object| {
                    crate::object_replay::observe(source, object, &verdict, backend.target_arch())
                }) {
                Ok(row) => observations.as_mut().expect("checked").push(row),
                Err(error) => observations = Err(error),
            }
        }
        let mut unknown_reason: Option<String> = None;
        match verdict {
            OutputVerdict::Proven { evidence } => match evidence {
                // [PROVED] — the clean kernel is the authority. The pair form is
                // the SAME grade with TWO kernel-accepted certificates (a 128-bit
                // AAPCS64 register pair, which cannot carry one); it is counted
                // as one PROVED FUNCTION, not as two.
                ProvenEvidence::KernelRecheckable(_)
                | ProvenEvidence::KernelRecheckablePair { .. }
                | ProvenEvidence::KernelInstantiated { .. }
                | ProvenEvidence::KernelRecheckableWithSideConditions { .. } => {
                    report.proved += 1
                }
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
                // An AllowUnknown verdict with NO bytes below is an early
                // lower/emit failure whose reason lives HERE — carry it so the
                // refusal names the real defect instead of a generic
                // no-bytes line (measured: a narrow checked-add ISel refusal
                // surfaced as "produced no shippable object bytes" and cost a
                // re-derivation to attribute).
                unknown_reason = Some(reason);
                report.unknown += 1;
            }
        }
        match bytes {
            Some(bytes) => verified.push((source.symbol.clone(), bytes)),
            None => {
                let detail = match unknown_reason.take() {
                    Some(reason) => format!(
                        "verification emission produced no shippable object bytes \
                         (verdict was Unknown: {reason})"
                    ),
                    None => "verification emission produced no shippable object bytes".to_string(),
                };
                return Err(VerifyError::EmitFailed {
                    function: source.symbol.clone(),
                    reason: detail,
                });
            }
        }
    }

    // PHASE 2 — DETERMINISM. Re-lower and re-emit each function and require the
    // bytes to be identical to the ones the gate verified. A backend that emits
    // different bytes when it is not being watched is caught here.
    for (index, (name, bytes)) in verified.iter().enumerate() {
        let source = &sources[index];
        let lir = crate::lower_module_to_lir_maybe_cross_checked(
            &source.module,
            source.func_id,
            source.abi_cross_check.as_ref(),
        )
        .map_err(|e| VerifyError::EmitFailed {
            function: name.clone(),
            reason: format!("re-lower for the determinism check failed: {e}"),
        })?;
        let reemit =
            backend.emit_object_with_trust_ir_globals(&[lir], &source.module).map_err(|e| {
                VerifyError::EmitFailed {
                    function: name.clone(),
                    reason: format!("re-emit globals-aware emit_object failed: {e:?}"),
                }
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
        let lir = crate::lower_module_to_lir_maybe_cross_checked(
            &source.module,
            source.func_id,
            source.abi_cross_check.as_ref(),
        )
        .map_err(|e| VerifyError::EmitFailed {
            function: source.symbol.clone(),
            reason: format!("lowering failed during whole-module emission: {e}"),
        })?;
        lir_functions.push(lir);
    }
    let function_count = lir_functions.len();
    let module = CompiledModule {
        name: "trust_cg.verified_trust_ir_module".to_string(),
        lir_functions,
        object_path: None,
        function_count,
        source_functions: None,
        linkage: linkage.to_vec(),
        statics: statics.to_vec(),
    };
    let emitted = backend
        .emit_module_object_with_trust_ir_globals(&module, source_module)
        .map_err(|e| VerifyError::ModuleEmitFailed {
            reason: format!("globals-aware emit_module_object failed: {e:?}"),
        })?;
    backend
        .require_object_target(&emitted.bytes)
        .map_err(|reason| VerifyError::ModuleEmitFailed { reason })?;
    let expected = sources
        .iter()
        .enumerate()
        .map(|(index, source)| {
            (source.symbol.as_str(), linkage.get(index).copied().unwrap_or_default())
        })
        .collect::<Vec<_>>();
    crate::verify_output::require_exact_elf_function_bindings(&emitted.bytes, &expected)
        .map_err(|reason| VerifyError::ModuleEmitFailed { reason })?;

    // PHASE 3b — DISCHARGE THE BYTE-PRESERVATION OBLIGATION, using the SAME
    // read-back-from-the-shipped-object check the MIR gate uses.
    let preserved: Vec<PreservedFunction> =
        assert_merged_object_preserves_verified_text(&emitted, &verified)?;

    let replay = observations.and_then(|rows| {
        crate::object_replay::finish(backend, linkage, statics, &emitted.bytes, &preserved, rows)
    });
    Ok((VerifiedModuleObject { bytes: emitted.bytes, preserved }, report, replay))
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
            abi: None,
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
        let source = TrustIrGateSource {
            abi_cross_check: None,
            symbol: name.to_string(),
            module: module.into(),
            func_id: FuncId::new(0),
        };
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
        let source = TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".to_string(),
            module: module.into(),
            func_id: FuncId::new(0),
        };
        let (object, report) = emit_trust_ir_module_object_verified(
            std::slice::from_ref(&source),
            &[],
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

    #[test]
    fn wrong_object_cpu_cannot_inherit_aarch64_proof() {
        let source = TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".into(),
            module: std::sync::Arc::new(build("k", &[], Ty::I32, Body::Const(7))),
            func_id: FuncId::new(0),
        };
        for (triple, cpu_offset, wrong_cpu) in
            [("aarch64-apple-darwin", 4, 0x0100_0007u32), ("aarch64-unknown-linux-gnu", 18, 62u32)]
        {
            let backend = TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, triple);
            let (baseline, object) = verify_trust_ir_output_preserved(&source, &backend);
            assert!(matches!(baseline, OutputVerdict::Proven { .. }), "{triple}: {baseline:?}");
            let mut object = object.expect("emitted object");
            let width = if cpu_offset == 18 { 2 } else { 4 };
            object[cpu_offset..cpu_offset + width]
                .copy_from_slice(&wrong_cpu.to_le_bytes()[..width]);
            let verdict = verify_trust_ir_bytes(&source, &object, TrustCgTargetArch::AArch64);
            assert!(matches!(verdict, OutputVerdict::Unknown { .. }), "{triple}: {verdict:?}");
        }
    }

    #[test]
    fn aarch64_elf_abi_header_mutations_cannot_inherit_trust_ir_proof() {
        let source = TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".into(),
            module: std::sync::Arc::new(build("k", &[], Ty::I32, Body::Const(7))),
            func_id: FuncId::new(0),
        };
        let backend = TrustCgCodegenBackend::new_for_triple(
            TrustCgTargetArch::AArch64,
            "aarch64-unknown-linux-gnu",
        );
        let (baseline, object) = verify_trust_ir_output_preserved(&source, &backend);
        assert!(baseline.is_proven(), "baseline must be favorable: {baseline:?}");
        let object = object.expect("AArch64 ELF object");
        for (offset, field) in [
            (8, "EI_ABIVERSION"),
            (48, "e_flags[0]"),
            (49, "e_flags[1]"),
            (50, "e_flags[2]"),
            (51, "e_flags[3]"),
        ] {
            assert_eq!(object[offset], 0, "emitter default for {field}");
            let mut mutated = object.clone();
            mutated[offset] = 1;
            assert_eq!(
                extract_text_from_object(&object).unwrap().0,
                extract_text_from_object(&mutated).unwrap().0,
                "{field} mutation must leave machine text unchanged"
            );
            let verdict = verify_trust_ir_bytes(&source, &mutated, backend.target_arch());
            assert!(
                matches!(verdict, OutputVerdict::Unknown { ref reason } if reason.contains("header")),
                "{field}: {verdict:?}"
            );
        }
    }

    #[test]
    fn malformed_aarch64_elf_symbol_binding_cannot_inherit_trust_ir_proof() {
        let source = TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".into(),
            module: std::sync::Arc::new(build("k", &[], Ty::I32, Body::Const(7))),
            func_id: FuncId::new(0),
        };
        let backend = TrustCgCodegenBackend::new_for_triple(
            TrustCgTargetArch::AArch64,
            "aarch64-unknown-linux-gnu",
        );
        let (baseline, object) = verify_trust_ir_output_preserved(&source, &backend);
        assert!(baseline.is_proven(), "baseline must be favorable: {baseline:?}");
        let object = object.expect("AArch64 ELF object");
        let records = trust_cg_codegen::elf::reparse::read_object_records(&object).unwrap();
        let symbol_index = records.symbols.iter().position(|symbol| symbol.name == "k").unwrap();
        assert_eq!(records.symbols[symbol_index].binding, 1, "emitted function is global");
        let mut mutated = object.clone();
        let section_table = u64::from_le_bytes(object[40..48].try_into().unwrap()) as usize;
        let section_count = u16::from_le_bytes(object[60..62].try_into().unwrap()) as usize;
        let symtab_section = (0..section_count)
            .map(|index| section_table + index * 64)
            .find(|&at| {
                u32::from_le_bytes(object[at + 4..at + 8].try_into().unwrap())
                    == trust_cg_codegen::elf::constants::SHT_SYMTAB
            })
            .expect("emitted symbol table");
        let first_global = u32::from_le_bytes(
            object[symtab_section + 44..symtab_section + 48].try_into().unwrap(),
        ) as usize;
        assert!(symbol_index >= first_global, "function starts in global partition");
        let symtab_offset = u64::from_le_bytes(
            object[symtab_section + 24..symtab_section + 32].try_into().unwrap(),
        ) as usize;
        let info_at = symtab_offset + symbol_index * 24 + 4;
        mutated[info_at] &= 0x0f;
        assert_eq!(
            extract_text_from_object(&object).unwrap().0,
            extract_text_from_object(&mutated).unwrap().0,
            "symbol binding mutation must leave machine text unchanged"
        );
        let verdict = verify_trust_ir_bytes(&source, &mutated, backend.target_arch());
        assert!(
            matches!(verdict, OutputVerdict::Unknown { ref reason } if reason.contains("symbol binding")),
            "{verdict:?}"
        );
    }

    #[test]
    fn valid_elf_rebinding_cannot_inherit_trust_ir_proof() {
        let source = TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".into(),
            module: std::sync::Arc::new(build("k", &[], Ty::I32, Body::Const(7))),
            func_id: FuncId::new(0),
        };
        let backend = TrustCgCodegenBackend::new_for_triple(
            TrustCgTargetArch::AArch64,
            "aarch64-unknown-linux-gnu",
        );
        let (baseline, object) = verify_trust_ir_output_preserved(&source, &backend);
        assert!(baseline.is_proven(), "baseline must be favorable: {baseline:?}");
        let object = object.expect("AArch64 ELF object");
        let records = trust_cg_codegen::elf::reparse::read_object_records(&object).unwrap();
        let symbol_index = records.symbols.iter().position(|symbol| symbol.name == "k").unwrap();
        assert_eq!(records.symbols[symbol_index].binding, 1);
        let section_table = u64::from_le_bytes(object[40..48].try_into().unwrap()) as usize;
        let section_count = u16::from_le_bytes(object[60..62].try_into().unwrap()) as usize;
        let symtab_section = (0..section_count)
            .map(|index| section_table + index * 64)
            .find(|&at| {
                u32::from_le_bytes(object[at + 4..at + 8].try_into().unwrap())
                    == trust_cg_codegen::elf::constants::SHT_SYMTAB
            })
            .expect("emitted symbol table");
        let first_global = u32::from_le_bytes(
            object[symtab_section + 44..symtab_section + 48].try_into().unwrap(),
        ) as usize;
        assert_eq!(symbol_index, first_global, "function is first nonlocal symbol");
        let symtab_offset = u64::from_le_bytes(
            object[symtab_section + 24..symtab_section + 32].try_into().unwrap(),
        ) as usize;
        let info_at = symtab_offset + symbol_index * 24 + 4;
        for (name, binding, local) in [("weak", 2u8, false), ("local", 0u8, true)] {
            let mut mutated = object.clone();
            mutated[info_at] = (binding << 4) | (object[info_at] & 0x0f);
            if local {
                mutated[symtab_section + 44..symtab_section + 48]
                    .copy_from_slice(&u32::try_from(first_global + 1).unwrap().to_le_bytes());
            }
            assert!(
                backend.require_object_target(&mutated).is_ok(),
                "{name} is structurally valid"
            );
            assert_eq!(
                extract_text_from_object(&object).unwrap().0,
                extract_text_from_object(&mutated).unwrap().0,
                "{name} rebinding must not change machine text"
            );
            let verdict = verify_trust_ir_bytes(&source, &mutated, backend.target_arch());
            assert!(
                matches!(verdict, OutputVerdict::Unknown { ref reason } if reason.contains("binding")),
                "{name} must refuse: {verdict:?}"
            );
        }
    }

    /// THE GRADE, through the REAL BYTES. `Proven` alone was never the question
    /// for this fragment — it has been Proven all along. The question is whether
    /// it is Proven with a CLEAN-KERNEL certificate, because
    /// `EmitPolicy::StrictProvenOnly` (the compiler's default gate) ships only
    /// the kernel grade. Before the 128-bit register-pair split this was
    /// `AyValidated` and strict REFUSED it. Since 4ca6047f3b the gate's own
    /// verdict is ONE certificate of the original-term concatenation theorem
    /// (`KernelInstantiated`); the register-pair split, read here directly on
    /// the same obligation, must still carry TWO kernel-accepted certificates,
    /// one per register of the pair.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn i128_constant_return_is_kernel_proved_as_a_pair() {
        let (v, pair) = i128_grades(build("k", &[], Ty::I128, Body::Const(1234)), "k");
        assert!(
            v.is_kernel_proved(),
            "a 128-bit constant return must be kernel-[PROVED], not merely Proven; got {v:?}"
        );
        assert!(routed_through_original_terms(&v), "expected the original-term grade; got {v:?}");
        let pair = OutputVerdict::Proven {
            evidence: pair.expect("the register-pair split must reach the kernel grade"),
        };
        assert!(
            matches!(
                pair,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelRecheckablePair { .. } }
            ),
            "expected the two-certificate register-pair grade; got {pair:?}"
        );
        assert_eq!(
            pair.kernel_proofs().len(),
            2,
            "a 128-bit return rests on TWO certificates (X1 high, X0 low)"
        );
    }

    /// Since 4ca6047f3b the router checks every concatenation through its
    /// original terms first; the register-pair split is the route it falls back
    /// to (`verify_output::tests_pair_128_split::
    /// the_router_falls_back_to_the_pair_split_when_the_original_terms_decline`).
    /// This returns the gate's verdict and the split's own grade on the
    /// obligation read from the same verified bytes.
    #[cfg(feature = "kernel-recheck")]
    fn i128_grades(module: Module, name: &str) -> (OutputVerdict, Option<ProvenEvidence>) {
        let source = TrustIrGateSource {
            abi_cross_check: None,
            symbol: name.to_string(),
            module: module.into(),
            func_id: FuncId::new(0),
        };
        let (v, obj) = verify_trust_ir_output_preserved(&source, &backend());
        let obj = obj.expect("verified bytes");
        let obligation = trust_ir_gate_obligation(&source, &obj, TrustCgTargetArch::AArch64)
            .expect("obligation from the verified bytes");
        let pair = crate::verify_output::try_kernel_recheckable_pair_128(
            &obligation.machine_value,
            &obligation.spec_value,
        );
        (v, pair)
    }

    #[cfg(feature = "kernel-recheck")]
    const ORIGINAL_CONCAT_THEOREM: &str = "Clean.BVC.bvf_concat_cong+selectAddrCong/read-over-write (original memory terms)";

    #[cfg(feature = "kernel-recheck")]
    fn routed_through_original_terms(v: &OutputVerdict) -> bool {
        matches!(
            v,
            OutputVerdict::Proven {
                evidence: ProvenEvidence::KernelInstantiated { theorem, original: None }
            } if theorem == ORIGINAL_CONCAT_THEOREM
        )
    }

    /// The 128-bit IDENTITY, through the real bytes, at the kernel grade. This is
    /// the shape whose halves are SYMBOLIC (`X1`/`X0` register reads) rather than
    /// constant, so it exercises leaf sharing across the split.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn i128_identity_is_kernel_proved_as_a_pair() {
        let (v, pair) = i128_grades(build("i", &[Ty::I128], Ty::I128, Body::Param(0)), "i");
        assert!(
            routed_through_original_terms(&v),
            "the 128-bit identity must be kernel-[PROVED] through its original terms; got {v:?}"
        );
        assert!(
            matches!(pair, Some(ProvenEvidence::KernelRecheckablePair { .. })),
            "the 128-bit identity must be kernel-[PROVED] as a pair; got {pair:?}"
        );
    }

    /// THE LOAD-BEARING TEST. Corrupting the HIGH half alone must flip the
    /// verdict. Without the `X0`/`X1` pair model this mutation is invisible and
    /// the function still reports `Proven` — an X0-only check calling itself a
    /// 128-bit proof.
    #[test]
    fn i128_return_obligation_constrains_the_high_half() {
        let module = build("k", &[], Ty::I128, Body::Const(1234));
        let source = TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".to_string(),
            module: module.into(),
            func_id: FuncId::new(0),
        };
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
    /// corrupted bytes and hands it straight to `try_kernel_recheckable_proof`
    /// (the router, which checks the original terms first) and to the
    /// register-pair split, bypassing the discharge. Neither may return evidence.
    ///
    /// The control at the end is what makes the result attributable: the
    /// UNcorrupted object's obligation, through the identical calls, DOES reach
    /// the kernel grade on both: the router's original-term certificate and the
    /// split's two-certificate pair grade. Same bytes but for one instruction
    /// word, same entry points, opposite answers.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn corrupting_the_high_half_refuses_the_kernel_recheck_path() {
        use crate::verify_output::try_kernel_recheckable_proof;

        let module = build("k", &[], Ty::I128, Body::Const(1234));
        let source = TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".to_string(),
            module: module.into(),
            func_id: FuncId::new(0),
        };
        let (_, obj) = verify_trust_ir_output_preserved(&source, &backend());
        let obj = obj.expect("verified bytes");
        let (off, size) = text_span(&obj).expect("__text");
        let words = size / 4;
        assert!(words >= 2, "need at least one instruction plus the ret");

        // CONTROL FIRST: the pristine object's obligation IS kernel-[PROVED].
        let clean = trust_ir_gate_obligation(&source, &obj, TrustCgTargetArch::AArch64)
            .expect("obligation from pristine bytes");
        assert!(
            routed_through_original_terms(&OutputVerdict::Proven {
                evidence: try_kernel_recheckable_proof(
                    &clean.machine_value,
                    &clean.spec_value,
                    None
                )
                .expect("control: the pristine 128-bit obligation must reach the kernel grade"),
            }),
            "control: the pristine obligation is checked through its original terms"
        );
        assert!(
            matches!(
                crate::verify_output::try_kernel_recheckable_pair_128(
                    &clean.machine_value,
                    &clean.spec_value
                ),
                Some(ProvenEvidence::KernelRecheckablePair { .. })
            ),
            "control: the pristine 128-bit obligation must reach the pair grade"
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
            crate::verify_output::try_kernel_recheckable_pair_128(
                &dirty.machine_value,
                &dirty.spec_value
            )
            .is_none(),
            "a corrupted HIGH half must be REFUSED by the register-pair split"
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
    /// `add w0, w1, #imm` for the projection bed below: the SECOND argument with
    /// bit 0 perturbed, with bits 8 and above perturbed, and unperturbed (the
    /// control). Verified against the system assembler (`as -arch arm64`,
    /// `otool -t`): `11000420`, `11040020`, `11000020`.
    const ADD_W0_W1_1: u32 = 0x1100_0420;
    const ADD_W0_W1_256: u32 = 0x1104_0020;
    const ADD_W0_W1_0: u32 = 0x1100_0020;
    /// `ret` (`d65f03c0`).
    const RET: u32 = 0xd65f_03c0;

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
            abi: None,
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
        TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".to_string(),
            module: module.into(),
            func_id: FuncId::new(0),
        }
    }

    /// The identity `fn(x: T) -> T { x }`: the spec is exactly the argument
    /// register read at the declared width and nothing else. Its O0 body is a
    /// lone `ret` since trust-cg `0d204a30`, so it has no word to mutate; it stays
    /// as the baseline twin of the projection below.
    fn identity(ty: Ty) -> TrustIrGateSource {
        let params = vec![ty.clone()];
        build(&params, ty, Vec::new(), ValueId::new(0))
    }

    /// The projection `fn(x: T, y: T) -> T { y }` — the narrow mutation bed. Its
    /// spec is exactly the SECOND argument register read at the declared width
    /// and nothing else, and no lowering can emit it in fewer than two words:
    /// the value has to move from `w1` to `w0` before the `ret`.
    fn second_of_two(ty: Ty) -> TrustIrGateSource {
        let params = vec![ty.clone(), ty.clone()];
        build(&params, ty, Vec::new(), ValueId::new(1))
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

    /// Re-discharge the UNCHANGED spec against bytes whose function now begins
    /// `insn; ret`. The mutated function is then known in full whatever shape the
    /// lowering chose, because every word after the planted `ret` is unreachable
    /// — the bed does not depend on which word of the shipping code computes
    /// the result.
    fn verdict_after_rewrite(source: &TrustIrGateSource, obj: &[u8], insn: u32) -> OutputVerdict {
        let (off, size) = text_span(obj).expect("__text");
        assert!(size / 4 >= 2, "the bed must have room for `insn; ret`, got {size} byte(s)");
        let mut corrupted = obj.to_vec();
        corrupted[off..off + 4].copy_from_slice(&insn.to_le_bytes());
        corrupted[off + 4..off + 8].copy_from_slice(&RET.to_le_bytes());
        verify_trust_ir_bytes(source, &corrupted, TrustCgTargetArch::AArch64)
    }

    /// THE LOAD-BEARING TEST. One mutation, three widths, three required answers.
    ///
    /// The bed is the projection `fn(x: T, y: T) -> T { y }`, rewritten to
    /// `add w0, w1, #imm; ret`. `#0x100` touches bits 8 and above and nothing
    /// below. At a DECLARED width of 8 those bits are not part of the value — the
    /// Rust ABI gives a narrow slot `arg_ext: None`, so the caller may not read
    /// them — and the verdict must stay `Proven`. At 16 and at 32 bit 8 IS part
    /// of the value and the verdict must flip to `Refuted`. `#0` is the control:
    /// the rewritten function IS the projection, so it must stay `Proven` at
    /// every width, and every verdict that moves below is the perturbation's.
    ///
    /// No hard-coded obligation width can pass this test: a fixed 8 fails the u16
    /// and u32 lines, a fixed 32 fails the u8 line. The width has to come from the
    /// type.
    ///
    /// (Until trust-cg `0d204a30` the bed was the identity, mutated in the word
    /// before its `ret`; that lowering now emits the identity as a lone `ret`.
    /// NARROW-WIDTH-BED-1 in `docs/DECISION_QUEUE.md` records the mutants this
    /// bed was measured against.)
    #[test]
    fn narrow_obligation_sits_at_the_declared_width() {
        for (name, ty, high_bits_are_part_of_the_value) in [
            ("u8", Ty::U8, false),
            ("i8", Ty::I8, false),
            ("u16", Ty::U16, true),
            ("i16", Ty::I16, true),
            ("u32", Ty::U32, true),
        ] {
            let (id, _) = verdict(&identity(ty.clone()));
            assert!(matches!(id, OutputVerdict::Proven { .. }), "{name} identity: {id:?}");

            let source = second_of_two(ty);
            let (base, obj) = verdict(&source);
            assert!(matches!(base, OutputVerdict::Proven { .. }), "{name} baseline: {base:?}");
            let obj = obj.expect("verified bytes");

            let same = verdict_after_rewrite(&source, &obj, ADD_W0_W1_0);
            assert!(
                matches!(same, OutputVerdict::Proven { .. }),
                "{name}: `add w0, w1, #0; ret` is the projection itself, so the rewrite \
                 must stay Proven; got {same:?}"
            );

            let hi = verdict_after_rewrite(&source, &obj, ADD_W0_W1_256);
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
            let lo = verdict_after_rewrite(&source, &obj, ADD_W0_W1_1);
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

    /// A `bool` PARAMETER WITHOUT an attested cross-check stays refused (WS7.13's
    /// negative twin, in the unit lane). The prior finding stands: modeling it
    /// as an unconstrained 32-bit value fabricated six Refuted verdicts, and the
    /// `Zext` promise that justifies the `W{k}[31:1] == 0` precondition is
    /// consumed ONLY from `AbiParamExtensions` on the cross-check — see
    /// `tests/trust_ir_gate_bool_param.rs` for the attested positive fixture.
    #[test]
    fn bool_parameter_without_cross_check_is_unknown() {
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
                assert!(
                    reason.contains("no ABI pass-mode cross-check is attached"),
                    "the refusal must name the missing fact: {reason}"
                );
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
            abi: None,
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
        TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".to_string(),
            module: module.into(),
            func_id: FuncId::new(0),
        }
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
            nodes.push(InstrNode::new(Inst::Assert {
                cond: ValueId::new(3),
                kind: trust_ir::AssertKind::Unspecified,
                site: None,
            }));
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

    /// Trust (trust-ir v52/v54): the kind of the IR's range assert names the panic, not whether
    /// the check fails, so a KINDED siteless assert derives the same spec as the pre-v52 one; a
    /// SITED assert calls its entry on failure, which this model does not have, so the spec is
    /// refused instead of rendered.
    #[test]
    fn a_sited_assert_is_outside_the_modeled_fragment() {
        let set = |source: &mut TrustIrGateSource, kind, site| {
            let module = std::sync::Arc::make_mut(&mut source.module);
            for node in &mut module.functions[0].blocks[0].body {
                if let Inst::Assert { kind: k, site: s, .. } = &mut node.inst {
                    *k = kind;
                    *s = site;
                }
            }
        };
        let mut kinded = narrow_shift(true);
        set(&mut kinded, trust_ir::AssertKind::Overflow(trust_ir::AssertOverflowOp::Shl), None);
        let plain = trust_ir_function_semantics(&narrow_shift(true).module, FuncId::new(0));
        let named = trust_ir_function_semantics(&kinded.module, kinded.func_id);
        assert_eq!(format!("{plain:?}"), format!("{named:?}"), "the kind changes no spec");
        let mut sited = narrow_shift(true);
        set(
            &mut sited,
            trust_ir::AssertKind::Overflow(trust_ir::AssertOverflowOp::Shl),
            Some(trust_ir::PanicSite {
                entry: FuncId::new(0),
                location: trust_ir::PanicLocation::Value(ValueId::new(0)),
            }),
        );
        let err = trust_ir_function_semantics(&sited.module, sited.func_id)
            .expect_err("a sited assert must not derive a spec");
        assert!(err.contains("`Assert` is outside the modeled fragment"), "unexpected: {err}");
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
        assert_shipping_gate_refuses_implicit_panic(&narrow_shift(true), &backend());
        let guarded = verify_with_trap_oracle(&narrow_shift(true), &backend()).0;
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

    /// Trust (2026-09-30): the guarded narrow shift no longer reaches module
    /// emission — the shipping converter refuses its `Assert` under EVERY
    /// policy, `AllowUnknown` included (an implicit panic is not an unproven
    /// function, it is an unfaithful one). The solver-only grade the strict
    /// policy used to refuse is still measured, per function, over the
    /// trap oracle's bytes: `[VALIDATED]` (ay-only), never `[PROVED]`.
    #[test]
    fn solver_only_shift_obligations_refuse_strict_module_emission() {
        let source = narrow_shift(true);
        for policy in [EmitPolicy::StrictProvenOnly, EmitPolicy::AllowUnknown] {
            let error = emit_trust_ir_module_object_verified(
                std::slice::from_ref(&source),
                &[],
                &[],
                policy,
                &backend(),
            )
            .expect_err("no policy may emit an Assert-bearing body");
            assert!(
                format!("{error:?}").contains("[implicit-panic-unfaithful]"),
                "{policy:?}: the refusal must name the implicit panic: {error:?}"
            );
        }

        match verify_with_trap_oracle(&source, &backend()).0 {
            OutputVerdict::Proven { evidence } => assert!(
                matches!(evidence, crate::verify_output::ProvenEvidence::AyValidated),
                "a solver-only shift/reachability obligation grades [VALIDATED] (ay-only), \
                 never [PROVED]: {evidence:?}"
            ),
            other => panic!("the oracle's guarded shift must still be value-proven: {other:?}"),
        }
    }

    /// An ASSERT-FREE 8-bit shift whose amount is in range by construction
    /// (`amount & 7`). The gate still emits the `amount < 8` modeling side
    /// condition. Trust (2026-10-03): with the kernel lane that condition is
    /// kernel-proved too, so the function grades [PROVED]
    /// (`KernelRecheckableWithSideConditions`); without it, `[VALIDATED]`.
    fn masked_narrow_shift() -> TrustIrGateSource {
        narrow_shift_by(TirBinOp::And, 7)
    }

    /// The same shift with the amount reduced by `amount % 8`: in range on every
    /// input, which ay proves, but the condition's `urem` is outside the
    /// kernel-exportable fragment (`formula_to_bvexpr_refuses_dividers`), so it
    /// stays `[VALIDATED]` (ay-only) under every feature set. No `Assert`, so the
    /// shipping converter accepts it and it reaches the emission-policy arm the
    /// `Assert`-bearing subject above no longer reaches.
    fn remainder_narrow_shift() -> TrustIrGateSource {
        narrow_shift_by(TirBinOp::URem, 8)
    }

    fn narrow_shift_by(reduce: TirBinOp, constant: i128) -> TrustIrGateSource {
        build(
            &[Ty::U8, Ty::U8],
            Ty::U8,
            vec![
                InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(constant) })
                    .with_result(ValueId::new(2)),
                InstrNode::new(Inst::BinOp {
                    op: reduce,
                    ty: Ty::U8,
                    lhs: ValueId::new(1),
                    rhs: ValueId::new(2),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::BinOp {
                    op: TirBinOp::Shl,
                    ty: Ty::U8,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(3),
                })
                .with_result(ValueId::new(4)),
            ],
            ValueId::new(4),
        )
    }

    /// THE NEGATIVE TWIN: the same masked shift at 32 bits owes no range side
    /// condition (mod-32 masking IS the hardware reduction), so with the kernel
    /// lane it grades [PROVED] and SHIPS under the default strict policy. The
    /// refusal above is therefore about the ay-only grade, not about shifts,
    /// masks or the strict policy refusing everything.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn the_same_masked_shift_at_32_bits_ships_under_the_default_strict_gate() {
        let source = build(
            &[Ty::U32, Ty::U32],
            Ty::U32,
            vec![
                InstrNode::new(Inst::Const { ty: Ty::U32, value: Constant::Int(31) })
                    .with_result(ValueId::new(2)),
                InstrNode::new(Inst::BinOp {
                    op: TirBinOp::And,
                    ty: Ty::U32,
                    lhs: ValueId::new(1),
                    rhs: ValueId::new(2),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::BinOp {
                    op: TirBinOp::Shl,
                    ty: Ty::U32,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(3),
                })
                .with_result(ValueId::new(4)),
            ],
            ValueId::new(4),
        );
        let (object, report) = emit_trust_ir_module_object_verified(
            std::slice::from_ref(&source),
            &[],
            &[],
            EmitPolicy::default(),
            &backend(),
        )
        .expect("a side-condition-free masked 32-bit shift must ship under the strict default");
        assert_eq!(report.proved, 1, "{report}");
        assert_eq!(report.validated, 0, "{report}");
        assert_eq!(report.unknown, 0, "{report}");
        assert!(!object.bytes.is_empty());
    }

    /// THE MASKED NARROW SHIFT SHIPS. Its `amount < 8` condition is kernel-proved
    /// alongside the value, so the function is [PROVED] with one certificate per
    /// part and the strict default emits it (the F1 run-make row
    /// `variable_shift_narrow` at -O2 is this shape).
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn the_masked_narrow_shift_is_kernel_proved_with_its_side_condition() {
        let source = masked_narrow_shift();
        let verdict = verify_trust_ir_output_preserved(&source, &backend()).0;
        match &verdict {
            OutputVerdict::Proven {
                evidence:
                    crate::verify_output::ProvenEvidence::KernelRecheckableWithSideConditions {
                        side_conditions,
                        ..
                    },
            } => assert_eq!(side_conditions.len(), 1, "one range condition: {verdict:?}"),
            other => panic!("the masked shift's condition must be kernel-proved: {other:?}"),
        }
        assert!(verdict.is_kernel_proved());
        let (object, report) = emit_trust_ir_module_object_verified(
            std::slice::from_ref(&source),
            &[],
            &[],
            EmitPolicy::StrictProvenOnly,
            &backend(),
        )
        .expect("a kernel-proved masked narrow shift ships under the strict default");
        assert!(!object.bytes.is_empty());
        assert_eq!(report.proved, 1, "{report}");
        assert_eq!(report.validated, 0, "{report}");
    }

    /// A side condition outside the exportable fragment keeps the function at
    /// solver authority even though its value equality is kernel-provable.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn a_side_condition_without_kernel_evidence_caps_the_grade() {
        let value = Formula::BitVec { value: 7, width: 32 };
        let a = Formula::Var("side_a".into(), Sort::BitVec(8));
        let reduced = Formula::BvURem(b(a), b(Formula::BitVec { value: 8, width: 8 }), 8);
        let condition = Formula::BvULt(b(reduced), b(Formula::BitVec { value: 8, width: 8 }), 8);
        assert!(kernel_value_and_side_conditions(&value, &value, &[]).is_some());
        assert!(kernel_value_and_side_conditions(&value, &value, &[condition]).is_none());
    }

    /// THE STRICT EMISSION POLICY over a `[VALIDATED]` function, re-pinned on an
    /// `Assert`-free subject (the guarded shift above is now refused earlier, by
    /// the converter, under every policy). `StrictProvenOnly` — the default —
    /// must refuse an ay-only function by naming `[VALIDATED]` and emit no
    /// bytes; the explicit `AllowUnknown` policy ships it, counted as validated.
    /// This is the test that kills disabling the
    /// `StructuralCitation | AyValidated` strict arm of module emission.
    #[test]
    fn solver_only_shift_obligations_refuse_strict_module_emission_assert_free() {
        let source = remainder_narrow_shift();
        assert!(
            !crate::module_to_lir::function_has_unfaithful_assert(
                source.module.function_by_id(source.func_id).expect("subject")
            ),
            "the subject must be Assert-free, or this re-tests the converter refusal"
        );
        match verify_trust_ir_output_preserved(&source, &backend()).0 {
            OutputVerdict::Proven { evidence } => assert!(
                matches!(evidence, crate::verify_output::ProvenEvidence::AyValidated),
                "the masked shift's range side condition is solver-only: [VALIDATED], \
                 never [PROVED]: {evidence:?}"
            ),
            other => panic!("the masked shift must be value-proven on the shipping path: {other:?}"),
        }

        assert_eq!(EmitPolicy::default(), EmitPolicy::StrictProvenOnly, "the default IS strict");
        let error = emit_trust_ir_module_object_verified(
            std::slice::from_ref(&source),
            &[],
            &[],
            EmitPolicy::StrictProvenOnly,
            &backend(),
        )
        .expect_err("a value proof cannot authorize solver-only shift obligations under strict");
        assert!(
            matches!(&error, VerifyError::Unknown { reason, .. } if reason.contains("[VALIDATED]")),
            "strict must refuse BY GRADE, naming [VALIDATED]: {error:?}"
        );

        let (object, report) = emit_trust_ir_module_object_verified(
            std::slice::from_ref(&source),
            &[],
            &[],
            EmitPolicy::AllowUnknown,
            &backend(),
        )
        .expect("the explicit permissive policy retains solver-validated progress");
        assert!(!object.bytes.is_empty());
        assert_eq!(report.proved, 0, "{report}");
        assert_eq!(report.validated, 1, "{report}");
        assert_eq!(report.unknown, 0, "{report}");
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
                InstrNode::new(Inst::Assert {
                    cond: ValueId::new(3),
                    kind: trust_ir::AssertKind::Unspecified,
                    site: None,
                }),
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
        match verify_with_trap_oracle(&source, &backend()).0 {
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

    /// Exhaust every operand pair at widths small enough to enumerate. The
    /// expected answer is computed in Rust integers, independently of the
    /// Formula construction; ay then evaluates each complete truth table as a
    /// single validity obligation.
    #[test]
    fn multiply_overflow_flag_is_exhaustive_at_small_widths() {
        for width in 1..=4 {
            let modulus = 1u128 << width;
            let mask = modulus - 1;
            let sign_bit = 1u128 << (width - 1);
            let signed_value = |bits: u128| {
                if bits & sign_bit == 0 { bits as i128 } else { bits as i128 - modulus as i128 }
            };

            for signed in [false, true] {
                let mut all_cases = Vec::new();
                for lhs_bits in 0..modulus {
                    for rhs_bits in 0..modulus {
                        let lhs = Formula::BitVec { value: lhs_bits as i128, width };
                        let rhs = Formula::BitVec { value: rhs_bits as i128, width };
                        let wrapped_bits = lhs_bits.wrapping_mul(rhs_bits) & mask;
                        let wrapped = Formula::BitVec { value: wrapped_bits as i128, width };
                        let flag = overflow_flag_formula(
                            OverflowOp::MulOverflow,
                            width,
                            signed,
                            &lhs,
                            &rhs,
                            &wrapped,
                        )
                        .expect("small scalar multiply must be modeled");

                        let expected = if signed {
                            let exact = signed_value(lhs_bits) * signed_value(rhs_bits);
                            let min = -(1i128 << (width - 1));
                            let max = (1i128 << (width - 1)) - 1;
                            exact < min || exact > max
                        } else {
                            lhs_bits * rhs_bits > mask
                        };
                        all_cases.push(if expected { flag } else { Formula::Not(b(flag)) });
                    }
                }

                match discharge_valid(&Formula::And(all_cases)) {
                    Discharge::Proven => {}
                    other => panic!(
                        "{width}-bit {} multiply overflow truth table is not exact: {other:?}",
                        if signed { "signed" } else { "unsigned" }
                    ),
                }
            }
        }
    }

    /// At the largest admitted width (32), the flag is DISCHARGED, not merely
    /// compared structurally: each spot check pins concrete operands whose true
    /// answer is known independently and asks ay to prove the flag's value.
    #[test]
    fn multiply_overflow_flag_is_exact_at_32_bits() {
        let cases: [(bool, u32, u32, bool); 8] = [
            // (signed, lhs bits, rhs bits, overflows)
            (false, u32::MAX, 2, true),
            (false, 65_536, 65_536, true),
            // 65535 * 65537 == u32::MAX exactly: the largest non-overflowing product.
            (false, 65_535, 65_537, false),
            (false, u32::MAX, 1, false),
            (true, i32::MIN as u32, (-1i32) as u32, true),
            (true, i32::MAX as u32, 2, true),
            (true, i32::MIN as u32, 1, false),
            (true, (-46_341i32) as u32, 46_340, false),
        ];
        for (signed, lhs_bits, rhs_bits, expected) in cases {
            let lhs = Formula::BitVec { value: i128::from(lhs_bits), width: 32 };
            let rhs = Formula::BitVec { value: i128::from(rhs_bits), width: 32 };
            let wrapped =
                Formula::BitVec { value: i128::from(lhs_bits.wrapping_mul(rhs_bits)), width: 32 };
            let flag =
                overflow_flag_formula(OverflowOp::MulOverflow, 32, signed, &lhs, &rhs, &wrapped)
                    .expect("32-bit checked multiply must be modeled");
            let claim = if expected { flag } else { Formula::Not(b(flag)) };
            match discharge_valid(&claim) {
                Discharge::Proven => {}
                other => panic!(
                    "32-bit {} multiply {lhs_bits:#x} * {rhs_bits:#x}: expected overflow={expected}, \
                     got {other:?}",
                    if signed { "signed" } else { "unsigned" }
                ),
            }
        }
    }

    /// Width zero is not a bit-vector scalar, a checked u64 multiply would need
    /// a 128-bit exact product the exporter does not carry, and a checked u128
    /// multiply a 256-bit one. All of them, and arbitrary wider widths, remain
    /// fail-closed before any malformed or unsupported Formula is constructed.
    #[test]
    fn checked_multiply_rejects_unsupported_widths() {
        for width in [0, 33, 64, 65, 128] {
            let lhs = bv("a", width);
            let rhs = bv("b", width);
            let wrapped = Formula::BvMul(b(lhs.clone()), b(rhs.clone()), width);
            let err =
                overflow_flag_formula(OverflowOp::MulOverflow, width, false, &lhs, &rhs, &wrapped)
                    .expect_err("unsupported checked-multiply width must fail closed");
            assert!(
                err.contains("only nonzero scalar widths through 32"),
                "unexpected reason for width {width}: {err}"
            );
        }
    }

    /// `fn(a: u64, b: u64) -> u64 { a + b }` as rustc's frontend emits it:
    /// `add.overflow`, `assert(!did_overflow)`, return the wrapping value.
    fn checked_add_u64() -> TrustIrGateSource {
        checked_binop(OverflowOp::AddOverflow, Ty::U64)
    }

    /// The same checked-arithmetic shape for any overflow op and scalar type.
    fn checked_binop(op: OverflowOp, ty: Ty) -> TrustIrGateSource {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![ty.clone()],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), ty.clone()));
        block.params.push((ValueId::new(1), ty.clone()));
        block.body = vec![
            InstrNode::new(Inst::Overflow { op, ty, lhs: ValueId::new(0), rhs: ValueId::new(1) })
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
            InstrNode::new(Inst::Assert {
                cond: ValueId::new(6),
                kind: trust_ir::AssertKind::Unspecified,
                site: None,
            }),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        f.blocks.push(block);
        module.functions.push(f);
        TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".to_string(),
            module: module.into(),
            func_id: FuncId::new(0),
        }
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
        assert_shipping_gate_refuses_implicit_panic(&source, &backend());
        let verdict = verify_with_trap_oracle(&source, &backend()).0;
        assert!(
            matches!(verdict, OutputVerdict::Proven { .. }),
            "checked add must be Proven; got {verdict:?}"
        );
    }

    /// A checked 32-bit MULTIPLY now reaches the whole output gate: the spec side
    /// models its flag exactly, and the machine side decodes whatever
    /// `module_to_lir` emitted for it. Before the flag was modeled this shape
    /// was refused (`Unknown`); it must now be `Proven`, and above all an exact
    /// source flag must never turn correct emission into a `Refuted`.
    #[test]
    fn checked_multiply_32_bit_is_proven_end_to_end() {
        for ty in [Ty::U32, Ty::I32] {
            let source = checked_binop(OverflowOp::MulOverflow, ty.clone());
            let spec = trust_ir_function_semantics(&source.module, source.func_id)
                .expect("checked 32-bit multiply must derive a spec");
            assert!(
                !matches!(spec.reach, Formula::Bool(true)),
                "{ty:?}: the assert must make `spec_reach` a real predicate"
            );
            let verdict = verify_with_trap_oracle(&source, &backend()).0;
            assert!(
                matches!(verdict, OutputVerdict::Proven { .. }),
                "{ty:?}: checked multiply must be Proven (never Refuted); got {verdict:?}"
            );
        }
    }

    /// And the VALUE half still bites: corrupt the returned register and the same
    /// obligation flips, so `Proven` above is not riding on a vacuous reach.
    #[test]
    fn checked_add_proof_is_not_vacuous() {
        /// `movz x0, #0x5a5a` — the whole return value replaced by a constant.
        const MOVZ_X0_5A5A: u32 = 0xd280_0000 | (0x5a5a << 5);
        let source = checked_add_u64();
        let (base, obj) = verify_with_trap_oracle(&source, &backend());
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
            abi: None,
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
        TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".to_string(),
            module: module.into(),
            func_id: FuncId::new(0),
        }
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
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), ety));
        block.body = vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] })];
        f.blocks.push(block);
        module.functions.push(f);
        TrustIrGateSource {
            abi_cross_check: None,
            symbol: "k".to_string(),
            module: module.into(),
            func_id: FuncId::new(0),
        }
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

            let lir = crate::lower_module_to_lir_maybe_cross_checked(
                &source.module,
                source.func_id,
                source.abi_cross_check.as_ref(),
            )
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

#[cfg(test)]
mod tests_local_slots {
    use super::*;

    /// An `Alloca` stepped again on the same [`LocalSlots`] starts a fresh, unwritten cell: a
    /// load after it is refused even though the cell was written before. (Each evaluator also
    /// builds a new `LocalSlots` per block evaluation; this pins the reset on its own.)
    #[test]
    fn an_alloca_stepped_again_resets_its_cell() {
        let text = "module \"rung\"\ntarget \"arm64-apple-macosx\" 8 little\n\
                    functy.0 = (u64) -> (u64)\nfn @rung(functy.0) {\nbb0(%0: u64):\n    \
                    %1 = alloca u64\n    store u64 %0, ptr %1\n    %2 = load u64, ptr %1\n    \
                    ret %2\n}\n";
        let module = trust_ir::parser::parse_module(text).expect("parses");
        let func = FuncId::new(0);
        let function = module.function_by_id(func).expect("rung");
        let blocks: HashMap<u32, &trust_ir::Block> =
            function.blocks.iter().map(|b| (b.id.index(), b)).collect();
        let body = &function.blocks[0].body;
        let (alloca, store, load) = (&body[0], &body[1], &body[2]);
        let mut env: HashMap<ValueId, IrValue> = HashMap::new();
        env.insert(ValueId::new(0), IrValue { f: xn(0), width: 64 });
        let mut slots = LocalSlots::default();
        let mut step = |node: &trust_ir::node::InstrNode| {
            slots.step(&module, func, &blocks, 0, &mut env, node).expect("a slot step")
        };
        step(alloca).expect("admitted");
        step(store).expect("stored");
        step(alloca).expect("admitted again");
        let e = step(load).expect_err("the cell was reset");
        assert!(e.contains("before any store"), "{e}");
    }

    /// An inlined callee's slots go through the same step: `interpret_inlined_call` gives s17's
    /// `leaf` the value `x + 5`, and refuses a callee that reads its slot before writing it.
    #[test]
    fn an_inlined_callee_models_its_slots() {
        let module_of = |leaf: &str| {
            let text = format!(
                "module \"rung\"\ntarget \"arm64-apple-macosx\" 8 little\n\
                 functy.0 = (u64) -> (u64)\nfn @leaf(functy.0) {{\nbb0(%0: u64):\n{leaf}\n}}\n"
            );
            trust_ir::parser::parse_module(&text).expect("parses")
        };
        let x = IrValue { f: xn(0), width: 64 };
        let s17 = "    %1 = alloca u64\n    store u64 %0, ptr %1\n    %2 = const u64 5\n    \
                   %3 = load u64, ptr %1\n    %4 = add u64 %3, %2\n    store u64 %4, ptr %1\n    \
                   %5 = load u64, ptr %1\n    ret %5";
        let (v, ..) = interpret_inlined_call(&module_of(s17), None, FuncId::new(0), &[x.clone()])
            .expect("the callee's slot is modeled");
        let shown = format!("{:?}", v.f);
        assert!(shown.contains("BvAdd") && shown.contains("value: 5"), "{shown}");
        let unwritten = "    %1 = alloca u64\n    %2 = load u64, ptr %1\n    ret %2";
        let Err(e) = interpret_inlined_call(&module_of(unwritten), None, FuncId::new(0), &[x])
        else {
            panic!("an unwritten slot is refused");
        };
        assert!(e.contains("before any store"), "{e}");
    }
}
