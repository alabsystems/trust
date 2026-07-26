//! trust_ir::Module -> trust-cg LIR (the "trust-ir first" codegen seam).
//!
//! This is the consumer-side converter that feeds the EXISTING verified
//! LIR -> object emitter (`TrustCgCodegenBackend::emit_object`). The honest
//! seam in this fork is the object-emitting trust-cg-bridge path: trust_ir ->
//! LLVM is sealed (rustc's LLVM builder is `pub(crate)` inside
//! `rustc_codegen_llvm`), so we route `trust_ir::Module -> LIR -> object`
//! instead of going to LLVM.
//!
//! SCOPE (scalar + control-flow core, FAIL-CLOSED on everything else): a
//! function body of `Const` + `BinOp(Add/Sub/Mul/And/Or/Xor, integer
//! Div/Rem, and integer Shl/LShr/AShr)` + `UnOp(Not/Neg)` (integer bitwise
//! complement -> `Bnot`, wrapping negation -> `Ineg`) + `ICmp` over integer scalars, terminated
//! by `Return`, `Br`, `CondBr`, or `Switch` — across MULTIPLE basic blocks with
//! block-param merges. Integer `Div`/`Rem` (i8/i16/i32/i64, signed + unsigned)
//! map to the LIR `Sdiv/Udiv/Srem/Urem` opcodes; integer SHIFTS map
//! `Shl -> Ishl`, logical `LShr -> Ushr`, arithmetic `AShr -> Sshr` (the
//! logical-vs-arithmetic choice is carried by the trust-ir op, set by the
//! producer from the shifted-value signedness). The producer's EXPLICIT
//! div-by-zero / signed-overflow / shift-amount-in-range guards (`ICmp` +
//! `Assert` + `Br`) lower through the existing Assert/Brif/Trap machinery, so the
//! trap behavior is preserved exactly. For shifts the resulting `amount < width`
//! precondition makes the AArch64-masked register shift equal the guarded shift
//! (the hardware masks the amount mod width; masking is a no-op below width).
//!
//! MEMORY: scalar stack slots (`Alloca`/`Load`/`Store`/single-index `GEP`) over
//! fixed-width integers, AND — unblocked by the trust-ir pin c58fa68 (`Ty::Tuple`
//! `byte_size`/`byte_align` + the aggregate Store/Load round-trip) — a WHOLE
//! 2-field scalar `Ty::Tuple` round-tripped through ONE aggregate stack slot
//! (the shape the bridge promotes a multi-block-written tuple local to). The
//! aggregate is DECOMPOSED into its per-field scalars and lowered to per-field
//! Str/Ldr at the C-style field offsets (`aggregate_mem_layout`, byte-for-byte
//! the interpreter's `aggregate_layout`), so the emitted bytes and the reference
//! interpreter agree on the in-memory layout. Every unmapped `Inst` (calls,
//! non-2-field/nested aggregates, floats, casts, i128 div/rem, i128 shifts, ...)
//! returns an explicit [`ModuleLirError`] — it NEVER fabricates wrong LIR.
//!
//! CONTROL FLOW: trust_ir is already SSA with explicit per-edge args and block
//! params at merge points. We map `Br -> Jump`, `CondBr -> Brif`,
//! `Switch -> Switch`, declaring the LIR block params natively and threading the
//! per-edge args into the target's param Values via `Copy` instructions emitted
//! in the predecessor (the established LIR block-argument convention — see
//! `IselSelector::define_block_params`). Conditional edges into a param-carrying
//! target are split through a fresh intermediate edge-block (critical-edge
//! split) so the `Copy`s land on the correct edge.
//!
//! The companion VF -> trust_ir::Module adapter lives in
//! `trust-ir-bridge/src/lower.rs` (`lower_to_trust_ir_functions`); this module
//! is the reverse direction on the codegen side. The two existing bridge
//! lowerings (`lower::lower_to_lir` = VF -> LIR, and the binary_conversion
//! TrustIr -> LIR contract) do NOT consume a `trust_ir::Module`; this is the
//! first converter that does.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::borrow::Cow;
use std::collections::HashMap;

use trust_cg_lower::function::{
    BasicBlock as LirBlock, Function as LirFunction, Signature, StackSlotInfo,
};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
use trust_ir::inst::{BinOp, CastOp, ICmpOp, Inst, OverflowOp, UnOp};
use trust_ir::node::InstrNode;
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Constant, Function as IrFunction, Module};

/// Errors converting a `trust_ir::Module` function into LIR.
///
/// Every variant is a FAIL-CLOSED boundary: the converter refuses to emit LIR
/// rather than produce a plausible-but-wrong lowering for a shape it does not
/// yet model.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum ModuleLirError {
    /// The requested function id is not present in the module.
    #[error("function id {0} not found in module")]
    MissingFunction(u32),

    /// The function has no `ty` entry in `Module::func_types`.
    #[error("function `{name}` has no func_type entry (id {ty})")]
    MissingFuncType { name: String, ty: u32 },

    /// The function body has no basic blocks at all (malformed).
    #[error("function `{name}` has no basic blocks")]
    NoBlocks { name: String },

    /// A branch / switch / case targets a block id not present in the function.
    #[error("function `{name}` branches to block {target} which does not exist")]
    MissingBlock { name: String, target: u32 },

    /// A control-flow edge passed a number of arguments that does not match the
    /// target block's parameter arity. trust_ir is SSA: every edge into a block
    /// must supply exactly one arg per block param.
    #[error(
        "function `{name}` edge into block {target} passes {got} args but block has {expected} params"
    )]
    EdgeArgArity { name: String, target: u32, got: usize, expected: usize },

    /// A `Switch` carried a non-integer case selector constant. Only integer
    /// case values are mapped (LIR `Switch` cases are `i64`).
    #[error("function `{name}` switch has a non-integer case value")]
    UnsupportedSwitchCase { name: String },

    /// The function's control-flow graph is irreducible / unorderable, or a
    /// terminator appears in a non-terminal body position, so a deterministic
    /// reachable block order could not be established.
    #[error("function `{name}` has malformed / unorderable control flow: {detail}")]
    MalformedControlFlow { name: String, detail: String },

    /// The entry block's parameter arity does not match the function signature.
    /// The canonical well-formed Module (matching the trust-ir reference
    /// interpreter) carries the formal arguments as entry-block params; their
    /// count must equal the signature's parameter count.
    #[error("function `{name}` entry block has {got} params but signature has {expected} params")]
    BlockParamArity { name: String, got: usize, expected: usize },

    /// A type appeared that the scalar slice does not map (non-integer scalar,
    /// pointer, aggregate, vector, float, ...).
    #[error("unsupported type in `{context}`: {ty:?}")]
    UnsupportedType { context: String, ty: Ty },

    /// An `Inst` variant outside the scalar core (memory, call, aggregate,
    /// cast, float, control-flow, ...). The discriminant name is reported so the
    /// caller can see exactly which shape forced the fail-closed exit.
    #[error("unsupported instruction `{inst}` in `{name}` (only Const/BinOp/ICmp/Return mapped)")]
    UnsupportedInst { name: String, inst: &'static str },

    /// A `BinOp`/`ICmp` sub-op outside the integer scalar core: an i128 shift
    /// (multi-register, outside the proven single-instruction shift envelope), an
    /// i128 div/rem (libcall-routed, outside the proven-bytes envelope), or any
    /// float op. The i8..i64 shifts (`Shl`/`LShr`/`AShr`) ARE mapped — see
    /// [`map_int_binop`].
    #[error(
        "unsupported binary op `{op}` in `{name}` (scalar slice maps Add/Sub/Mul/And/Or/Xor/Shl/LShr/AShr + i8..i64 Div/Rem)"
    )]
    UnsupportedBinOp { name: String, op: &'static str },

    /// A `UnOp` sub-op outside the integer-scalar unary core: a float unary
    /// (`FNeg`/`FAbs`/`FSqrt`/`FFloor`/`FCeil`/`FTrunc` — no verified float
    /// lowering), an i128 `Neg`/`Not` (register-pair sequence, outside the proven
    /// single-instruction envelope), or `CtPop` (a popcount idiom this bridge does
    /// not yet prove). The i8..i64 `Not` (bitwise complement -> `Bnot`) and `Neg`
    /// (wrapping two's-complement negation -> `Ineg`) ARE mapped — see
    /// [`map_int_unop`]. FAIL-CLOSED so an unmodeled unary is never fabricated.
    #[error("unsupported unary op `{op}` in `{name}` (scalar slice maps i8..i64 Not/Neg)")]
    UnsupportedUnOp { name: String, op: &'static str },

    /// An `Inst::Cast` outside the proven integer-to-integer slice: a float cast
    /// (`FPTrunc`/`FPExt`/`FPToUI`/`FPToSI`/`UIToFP`/`SIToFP` — no verified float
    /// lowering), a pointer cast (`PtrToInt`/`IntToPtr`/`PtrToPtr` — width-less
    /// operands, outside the scalar-int envelope), a `Transmute`/`ReifyFnPointer`
    /// (needs a validity proof this bridge does not carry), or any i128-involving
    /// int-to-int cast (register-pair widths, outside the proven single-instruction
    /// envelope). The i8..i64 int-to-int forms — `Trunc` (narrow -> `Trunc`),
    /// `SExt` (signed widen -> `Sextend`), `ZExt` (unsigned widen -> `Uextend`),
    /// and the same-width `Bitcast` reinterpret (-> `Copy` identity) — ARE mapped
    /// (see [`map_int_cast`]). FAIL-CLOSED so an unmodeled cast is never fabricated.
    #[error("unsupported cast `{op}` in `{name}`: {detail}")]
    UnsupportedCast { name: String, op: &'static str, detail: String },

    /// A `Const` whose payload is not an integer.
    #[error("unsupported constant in `{name}`: only integer constants are mapped")]
    UnsupportedConstant { name: String },

    /// A value was referenced before it was defined (forward ref / undefined
    /// SSA value). The scalar slice requires straight-line definition order.
    #[error("value {value} used before definition in `{name}`")]
    UndefinedValue { name: String, value: u32 },

    /// The block did not end in a `Return`, or `Return` returned the wrong arity.
    #[error("function `{name}` body must end in `Return` with exactly one value")]
    MalformedReturn { name: String },

    /// The function signature is not the supported single-result integer shape.
    #[error("function `{name}` signature unsupported: {detail}")]
    UnsupportedSignature { name: String, detail: String },

    /// A memory instruction (`Load`/`Store`/`GEP`) referenced a pointer/base
    /// value that was not produced by an `Alloca` (or an `Alloca`-rooted `GEP`)
    /// in this function body. The scalar-memory slice only models stack slots it
    /// allocated itself; it cannot reason about an opaque incoming pointer.
    #[error("function `{name}` memory op uses pointer value {value} not rooted at a local Alloca")]
    NonLocalPointer { name: String, value: u32 },

    /// A memory shape outside the scalar-slot AND aggregate-slot slices: a
    /// pointer / float pointee, a counted (array/VLA) `Alloca`, a `GEP` that is
    /// not a single-index scalar-element address, or a partial / re-derived
    /// access into an aggregate slot. The scalar slice models fixed-width integer
    /// slots; the aggregate-memory slice (PASS 1.7, unblocked by the trust-ir pin
    /// c58fa68's `Ty::Tuple` `byte_size` + aggregate Store/Load round-trip) models
    /// a WHOLE 2-field scalar `Ty::Tuple` round-tripped through one slot via
    /// per-field Str/Ldr at the C-style field offsets; anything else fails closed.
    #[error("unsupported memory shape in `{name}`: {detail}")]
    UnsupportedMemory { name: String, detail: String },

    /// A `Call` could not be inlined and so could not be lowered. The detail
    /// names the admission clause that failed (non-local callee, callee itself
    /// calls / is non-leaf, recursive, multi-block, multi-return, impure, or
    /// arity mismatch). The Call is left in place and the scalar converter then
    /// fail-closes on it — the inliner NEVER produces a wrong splice.
    #[error("call in `{name}` is not an inlinable local pure leaf: {detail}")]
    UninlinableCall { name: String, detail: String },

    /// An `Inst::Undef` (poison seed) that the converter could NOT prove is a
    /// dead memory-merge seed — i.e. it could not establish, locally, that the
    /// poison value is overwritten on every path before any observable use. The
    /// only `Undef` shape the converter admits is the producer's cross-block
    /// memory-merge seed: a scalar `Undef` consumed by EXACTLY ONE `Store` into a
    /// local Alloca slot whose every `Load` is dominated by a later non-`Undef`
    /// `Store` (a must-overwrite). Any other `Undef` — read into a strict op /
    /// branch / return, stored into a slot a `Load` can reach while still poison,
    /// or a non-scalar payload — FAILS CLOSED here, so a poison value is NEVER
    /// materialized into a defined LIR Value at a site that could observe it.
    #[error(
        "function `{name}` has an `Undef` that is not a provably-dead memory-merge seed: {detail}"
    )]
    UnsupportedUndef { name: String, detail: String },

    /// A checked-overflow (`Inst::Overflow`) shape outside the supported slice:
    /// a non-integer / non-fixed-width operand type, a 128-bit width (no native
    /// flag-setting / high-half idiom in the verified ISel slice), or a `Mul` at
    /// a width other than i32/u32 (handled by exact i64 widening) or i64/u64
    /// (handled by the first-class `CheckedSmul`/`CheckedUmul`). A `Mul` at
    /// i8/i16/u8/u16 or i128/u128 still fails closed (no verified lowering yet).
    /// FAIL-CLOSED so a mis-widened overflow is never fabricated.
    #[error("unsupported checked-overflow shape in `{name}`: {detail}")]
    UnsupportedOverflow { name: String, detail: String },

    /// An aggregate (`Inst::ExtractField` / `Inst::InsertField`) shape outside
    /// the decomposable checked-arithmetic tuple slice. The ONLY aggregate the
    /// converter models is the BRIDGE's checked-arith result tuple
    /// `Tuple([Int, Bool])` — a 2-field `(value, overflow_flag)` pair built by a
    /// `Tuple`-typed `Undef` seed + two `InsertField`s (field 0 = value, field 1
    /// = flag), read back only by `ExtractField`. It is DECOMPOSED into the two
    /// scalar SSA Values without ever materializing a tuple in memory (the pinned
    /// interpreter lacks `Ty::Tuple` `byte_size`). Any other aggregate — a
    /// non-2-field tuple, a struct/array/record, a tuple stored to memory, a
    /// partially-built tuple read before a field is defined, an `InsertField`
    /// overwriting an already-defined field, or a tuple consumed by anything but
    /// `InsertField`/`ExtractField` — FAILS CLOSED here, so a tuple-in-memory the
    /// converter cannot decompose is never fabricated.
    #[error("unsupported aggregate shape in `{name}`: {detail}")]
    UnsupportedAggregate { name: String, detail: String },
}

/// Map a scalar integer `trust_ir::Ty` to a LIR `Type`.
///
/// FAIL-CLOSED: only the fixed-width integer types (and `Bool`, lowered to the
/// byte-wide `I8` LIR carrier ISel uses for comparison results) are accepted.
fn map_scalar_int_ty(ty: &Ty, context: &str) -> Result<LirType, ModuleLirError> {
    let lir = match ty {
        Ty::I8 | Ty::U8 => LirType::I8,
        Ty::I16 | Ty::U16 => LirType::I16,
        Ty::I32 | Ty::U32 => LirType::I32,
        Ty::I64 | Ty::U64 => LirType::I64,
        // Trust (v25 B1): isize/usize execute at 64 bits on the pinned 64-bit
        // target (same convention as trust-ir interpret's int_shape), so they
        // occupy the same X-register I64 LIR carrier as I64/U64.
        Ty::Isize | Ty::Usize => LirType::I64,
        // Trust (v25 B1): char is a 32-bit unsigned carrier (NOT an integer
        // type — no arithmetic is emitted on it; its constants are Int leaves),
        // so at the machine level it is the same 4-byte W-register value as U32.
        Ty::Char => LirType::I32,
        Ty::I128 | Ty::U128 => LirType::I128,
        // A boolean (comparison result) materializes in a byte-wide GPR slot.
        Ty::Bool => LirType::I8,
        // A thin pointer IS a 64-bit value in a GPR. Admitting `Ty::Ptr` here lets
        // a FUNCTION POINTER arrive as a formal argument (`fn f(fp: fn()->i32)`),
        // which is the OPEN-target CallIndirect source: the fn-ptr traces to an
        // incoming register, NOT a `GlobalAddr`'d symbol, so the indirect call is
        // dispatched HAVOC-only (see the OPEN CallIndirect arm). A pointer value in
        // a register is just its bit pattern; no arithmetic on it is admitted by
        // this fragment (only pass-through into a `CallIndirect` fn-ptr operand),
        // so treating it as an opaque I64 is exact at the machine level.
        //
        // `Ty::Func(_)` — a BARE function pointer (no captures) — is represented in
        // trust-ir as the raw function type directly (see trust_ir::ty doc), yet at
        // the machine level it is the SAME thin 64-bit code address as `Ty::Ptr`.
        // Admitting it here (identical opaque-I64, pass-through-only treatment) lets
        // a whole multi-function program with an fn-ptr formal + indirect dispatch
        // (`fn caller(f: fn(u64)->u64, x)`) lower to LIR instead of failing closed
        // at `UnsupportedType { Func }`. Same soundness argument as `Ty::Ptr`: no
        // arithmetic is admitted, only pass-through into the HAVOC-only CallIndirect.
        Ty::Ptr | Ty::Func(_) => LirType::I64,
        // Trust (v25 B1): `Ty::Error` (and every other non-scalar) deliberately
        // falls through to this arm — the bridge FAILS CLOSED on a leaked Error
        // type rather than fabricating a width for it.
        other => {
            return Err(ModuleLirError::UnsupportedType {
                context: context.to_string(),
                ty: other.clone(),
            });
        }
    };
    Ok(lir)
}

/// Map an integer `trust_ir::BinOp` to its LIR opcode.
///
/// Maps the wrapping integer arithmetic + bitwise ops AND integer
/// division/remainder. The trust_ir op already encodes SIGNEDNESS (`SDiv` vs
/// `UDiv`, `SRem` vs `URem`) — chosen by the producer from the source operand
/// type — so the mapping is a faithful 1:1 to the LIR `Sdiv/Udiv/Srem/Urem`
/// opcodes; the byte-level signed-vs-unsigned divide instruction follows from
/// the opcode, never from a guess. The div-by-zero / signed-overflow GUARDS are
/// NOT this op's concern: the producer emits them as EXPLICIT `ICmp` + `Assert`
/// + `Br` nodes that surround the bare `BinOp { SDiv/.. }`, and the existing
/// Const/ICmp/Assert(->Brif/Trap)/Br machinery lowers them unchanged. This op
/// only emits the bare divide; dropping a guard is therefore impossible here —
/// the guard is a separate node the converter already lowers (a wrong guard
/// would be caught by the proven-output gate, which trips iff the emitted bytes
/// trap differently than the source).
///
/// SHIFTS. `Shl`/`LShr`/`AShr` map to the LIR `Ishl`/`Ushr`/`Sshr` opcodes.
/// The trust-ir op already encodes the LOGICAL-vs-ARITHMETIC distinction (`LShr`
/// = logical, `AShr` = arithmetic), chosen by the producer from the shifted-value
/// operand's signedness (`trust-ir-bridge::lower::map_binop`: `Shr if signed =>
/// AShr` else `LShr`), so `Ushr`/`Sshr` follow the op — never a guess here. The
/// shift-amount-in-range obligation is NOT this op's concern: the producer emits
/// it as an EXPLICIT `Assert { Overflow(Shl|Shr) }` (annotated `ShiftInRange`)
/// that lowers via the SAME Const/ICmp/Assert(->Brif/Trap)/Br machinery the
/// div/rem guards use. This op emits only the bare shift.
///
/// SOUNDNESS — the amount<width precondition. The AArch64 register-form variable
/// shift (LSLV/LSRV/ASRV) MASKS the amount modulo the register width (mod 32 for
/// the W-register I32/narrow forms, mod 64 for the X-register I64 form); the
/// trust-ir shift semantics (interpreter `shift_amount`) instead TRAP when
/// `amount >= width` (Rust `<<`/`>>` UB). The producer's `ShiftInRange` guard
/// establishes exactly the `amount < width` precondition on the no-trap path, and
/// UNDER that precondition masking is a NO-OP (`amount mod width == amount`), so
/// the AArch64-masked shift equals the guarded (mathematical) shift. This is the
/// same guard-lowers-then-precondition-holds argument the div/rem slice uses; the
/// proven-output gate discharges it over the REAL emitted bytes.
///
/// FAIL-CLOSED (the verified div/rem + shift ISel slice this bridge proves over is
/// i32/i64/narrow only):
///   * 128-bit div/rem — the AArch64 ISel routes i128 div/rem to the
///     `__{div,mod}ti3` libcalls (a `Call`); that is outside this bridge's
///     proven-bytes envelope, so it fails closed rather than emit an
///     un-proven-here libcall sequence.
///   * 128-bit shifts — the AArch64 ISel routes i128 shifts through a
///     multi-register sequence (`select_i128_{shl,lshr,ashr}`), outside this
///     bridge's proven single-instruction shift envelope, so they fail closed.
///   * ALL float ops — this Module->LIR path has NO float type/register-class
///     plumbing (`map_scalar_int_ty` fail-closes on every float param/return
///     BEFORE a float `BinOp` is ever reached), so the float arms below stay
///     fail-closed. The PROVEN f64-add path is the gate's own emit lowering
///     (`lower.rs` -> `map_float_binop` -> `Opcode::Fadd`, discharged bit-exactly
///     against `FpToIeeeBv(FpAdd(RNE, FpFromBits, FpFromBits))` in
///     `verify_output`), NOT this converter.
fn map_int_binop(op: BinOp, ty: &Ty, name: &str) -> Result<Opcode, ModuleLirError> {
    let opcode = match op {
        BinOp::Add => Opcode::Iadd,
        BinOp::Sub => Opcode::Isub,
        BinOp::Mul => Opcode::Imul,
        BinOp::And => Opcode::Band,
        BinOp::Or => Opcode::Bor,
        BinOp::Xor => Opcode::Bxor,
        // Integer division / remainder. Signedness is carried by the op itself.
        // The div-by-zero + (signed) overflow guards are EXPLICIT surrounding
        // nodes already lowered by the Assert/Br machinery — see fn-doc. We map
        // the BARE divide here, fail-closing on 128-bit (libcall-routed, outside
        // the proven envelope).
        BinOp::UDiv | BinOp::SDiv | BinOp::URem | BinOp::SRem => {
            if matches!(map_scalar_int_ty(ty, "div/rem operand")?, LirType::I128) {
                return Err(ModuleLirError::UnsupportedBinOp {
                    name: name.to_string(),
                    op: binop_name(op),
                });
            }
            match op {
                BinOp::UDiv => Opcode::Udiv,
                BinOp::SDiv => Opcode::Sdiv,
                BinOp::URem => Opcode::Urem,
                BinOp::SRem => Opcode::Srem,
                _ => unreachable!("outer match restricts to div/rem"),
            }
        }
        // Shifts. Signedness of the SHIFTED VALUE is carried by the op
        // (`LShr` = logical, `AShr` = arithmetic; set by the producer from the
        // operand type — never guessed here), so the LIR opcode follows the op.
        // The shift-amount-in-range guard is a separate EXPLICIT
        // `Assert { Overflow(Shl|Shr) }` node lowered by the Assert/Br machinery;
        // under the resulting `amount < width` precondition the AArch64-masked
        // register shift equals the guarded shift (see fn-doc SOUNDNESS). We map
        // the BARE shift here, fail-closing on 128-bit (multi-register, outside
        // the proven single-instruction envelope).
        BinOp::Shl | BinOp::LShr | BinOp::AShr => {
            if matches!(map_scalar_int_ty(ty, "shift operand")?, LirType::I128) {
                return Err(ModuleLirError::UnsupportedBinOp {
                    name: name.to_string(),
                    op: binop_name(op),
                });
            }
            match op {
                BinOp::Shl => Opcode::Ishl,
                BinOp::LShr => Opcode::Ushr,
                BinOp::AShr => Opcode::Sshr,
                _ => unreachable!("outer match restricts to shifts"),
            }
        }
        // All floating-point binary ops.
        BinOp::FAdd
        | BinOp::FSub
        | BinOp::FMul
        | BinOp::FDiv
        | BinOp::FRem
        | BinOp::FMin
        | BinOp::FMax => {
            return Err(ModuleLirError::UnsupportedBinOp {
                name: name.to_string(),
                op: binop_name(op),
            });
        }
    };
    Ok(opcode)
}

fn binop_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::UDiv => "udiv",
        BinOp::SDiv => "sdiv",
        BinOp::URem => "urem",
        BinOp::SRem => "srem",
        BinOp::FAdd => "fadd",
        BinOp::FSub => "fsub",
        BinOp::FMul => "fmul",
        BinOp::FDiv => "fdiv",
        BinOp::FRem => "frem",
        BinOp::FMin => "fmin",
        BinOp::FMax => "fmax",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Xor => "xor",
        BinOp::Shl => "shl",
        BinOp::LShr => "lshr",
        BinOp::AShr => "ashr",
    }
}

/// Map an integer `trust_ir::UnOp` to its LIR opcode.
///
/// The producer (`trust-ir-bridge::lower`) lowers Rust's integer `!a`
/// (bitwise complement) to `UnOp::Not` and integer `-a` to `UnOp::Neg`, each a
/// BARE single-result unary node (`Rvalue::UnaryOp` -> `Inst::UnOp`). The mapping
/// is a faithful 1:1 to the LIR integer-unary opcodes:
///
///   * `Not -> Bnot` — bitwise NOT (`~x`). The trust-ir semantics
///     (`interpret::eval_int_unop`) are `!value.raw`; the AArch64 ISel lowers
///     `Bnot` to `MVN`/`ORN Xd, XZR, Xn` (`~x`), so the byte-level complement
///     follows the opcode exactly. `!a` here is the INTEGER bitwise complement;
///     the producer routes `!bool` through `Select`, so an integer-only `UnOp`
///     is complete.
///   * `Neg -> Ineg` — two's-complement negation (`0 - x`). The trust-ir
///     semantics are `0u128.wrapping_sub(value.raw)` — WRAPPING, so at the value
///     level `Neg` never traps (`i32::MIN` negates to `i32::MIN`). The AArch64
///     ISel lowers `Ineg` to `NEG`/`SUB Xd, XZR, Xn` (`0 - x`), which is the same
///     wrapping two's-complement, so the emitted bytes equal the wrapping value.
///
/// NEGATION-OVERFLOW GUARD. When Rust overflow checks are on, `-a` is preceded by
/// an EXPLICIT `i32::MIN` guard — the producer emits `_c = (a == MIN);
/// Assert { OverflowNeg } on _c` (`expected: false`, trapping iff `a == MIN`),
/// which lowers to the SAME `Const`/`ICmp`/`Assert(->Brif/Trap)`/`Br` machinery
/// the div/rem and shift guards use (verified above). The guard is a SEPARATE set
/// of nodes surrounding the bare `UnOp { op: Neg }`; this op only emits the bare
/// negate. Dropping a guard is therefore impossible here — the guard is nodes the
/// converter already lowers, and a wrong guard would trip the proven-output gate.
///
/// FAIL-CLOSED (the verified integer-unary ISel slice this bridge proves over is
/// i8..i64 only):
///   * 128-bit `Not`/`Neg` — the AArch64 ISel routes i128 unary through a
///     register-pair sequence (`select_int_unaryop`'s I128 arm), outside this
///     bridge's proven single-instruction envelope, so they fail closed.
///   * `CtPop` (population count) — the LIR has a `CtPop` opcode, but this bridge
///     carries no proof of the popcount lowering, so it fails closed rather than
///     emit an un-proven-here idiom.
///   * ALL float unary ops (`FNeg`/`FAbs`/`FSqrt`/`FFloor`/`FCeil`/`FTrunc`) —
///     no verified float lowering.
fn map_int_unop(op: UnOp, ty: &Ty, name: &str) -> Result<Opcode, ModuleLirError> {
    let opcode = match op {
        UnOp::Not | UnOp::Neg => {
            // The single-instruction integer-unary envelope is i8..i64; i128
            // negate/complement are register-pair (outside the proven envelope).
            if matches!(map_scalar_int_ty(ty, "unary operand")?, LirType::I128) {
                return Err(ModuleLirError::UnsupportedUnOp {
                    name: name.to_string(),
                    op: unop_name(op),
                });
            }
            match op {
                UnOp::Not => Opcode::Bnot,
                UnOp::Neg => Opcode::Ineg,
                _ => unreachable!("outer match restricts to Not/Neg"),
            }
        }
        // Population count: the LIR has a `CtPop` opcode but this bridge carries
        // no verified popcount lowering, so fail closed.
        UnOp::CtPop => {
            return Err(ModuleLirError::UnsupportedUnOp {
                name: name.to_string(),
                op: unop_name(op),
            });
        }
        // All floating-point unary ops.
        UnOp::FNeg | UnOp::FAbs | UnOp::FSqrt | UnOp::FFloor | UnOp::FCeil | UnOp::FTrunc => {
            return Err(ModuleLirError::UnsupportedUnOp {
                name: name.to_string(),
                op: unop_name(op),
            });
        }
    };
    Ok(opcode)
}

fn unop_name(op: UnOp) -> &'static str {
    match op {
        UnOp::Neg => "neg",
        UnOp::Not => "not",
        UnOp::CtPop => "ctpop",
        UnOp::FNeg => "fneg",
        UnOp::FAbs => "fabs",
        UnOp::FSqrt => "fsqrt",
        UnOp::FFloor => "ffloor",
        UnOp::FCeil => "fceil",
        UnOp::FTrunc => "ftrunc",
    }
}

fn cast_op_name(op: CastOp) -> &'static str {
    match op {
        CastOp::Trunc => "trunc",
        CastOp::ZExt => "zext",
        CastOp::SExt => "sext",
        CastOp::FPTrunc => "fptrunc",
        CastOp::FPExt => "fpext",
        CastOp::FPToUI => "fptoui",
        CastOp::FPToSI => "fptosi",
        CastOp::UIToFP => "uitofp",
        CastOp::SIToFP => "sitofp",
        CastOp::PtrToInt => "ptrtoint",
        CastOp::IntToPtr => "inttoptr",
        CastOp::PtrToPtr => "ptrtoptr",
        CastOp::Bitcast => "bitcast",
        CastOp::Transmute => "transmute",
        CastOp::ReifyFnPointer => "reifyfnpointer",
        CastOp::FPToSISat => "fptosi.sat",
        CastOp::FPToUISat => "fptoui.sat",
    }
}

/// Map an integer-to-integer `trust_ir::Inst::Cast` (`op` + `src_ty`/`dst_ty`) to
/// its LIR opcode.
///
/// `Inst::Cast { op, src_ty, dst_ty, operand }` is the producer's single-result
/// cast node (`Rvalue::Cast` -> `Inst::Cast`; see `trust-ir-bridge::lower`). For
/// an integer `a as T` cast the producer picks the `CastOp` from the WIDTHS and
/// the SOURCE signedness (`lower.rs`):
///   * `src_width  > dst_width`  -> `Trunc`  (narrowing; drop high bits),
///   * `src_width  < dst_width`  -> `SExt`   (widen, signed source) /
///                                  `ZExt`   (widen, unsigned source),
///   * `src_width == dst_width`  -> `Bitcast` (same-width reinterpret, e.g.
///                                  `i32 as u32` — a pure signedness relabel).
/// We map each to the pinned LIR cast opcodes the mul-widening slice already
/// proves over:
///   * `Trunc -> Opcode::Trunc { to_ty }`  (AArch64 ISel -> low-bits mask/mov),
///   * `SExt  -> Opcode::Sextend { from_ty, to_ty }` (ISel -> SXT{B,H,W}),
///   * `ZExt  -> Opcode::Uextend { from_ty, to_ty }` (ISel -> UXT{B,H} / mov w),
///   * `Bitcast` (same-width int) -> `Opcode::Copy` — the LIR integer types are
///     WIDTH-ONLY (`I8`/`I16`/`I32`/`I64` carry no signedness), so a same-width
///     int-to-int reinterpret is the identity on the bit pattern; a `Copy` pseudo
///     is the exact (and provably-sound) lowering.
///
/// SOUNDNESS. Rust `as` int-to-int casts are TOTAL (never trap) and their value
/// semantics are exactly: truncate = keep the low `dst_width` bits; signed widen
/// = sign-extend; unsigned widen = zero-extend; same-width = the identical bits.
/// These are precisely the trust-ir `Cast` interpreter semantics AND the pinned
/// LIR opcode semantics, so the mapping is 1:1 at every width — discharged over
/// the REAL emitted bytes by the proven-output gate (a swapped SExt/ZExt or a
/// wrong direction would miscompile and trip that gate).
///
/// FAIL-CLOSED. Returns `UnsupportedCast` for:
///   * any i128-involving int-to-int width (register-pair, outside the proven
///     single-instruction envelope),
///   * all float casts (`FP*`/`*ToFP`/`FPTo*`) — no verified float lowering,
///   * pointer casts (`PtrToInt`/`IntToPtr`/`PtrToPtr`) — width-less operands,
///   * `Transmute`/`ReifyFnPointer` — need a validity/reify proof this bridge
///     does not carry,
///   * a `Trunc`/`SExt`/`ZExt` whose declared width relation contradicts the op
///     (a malformed node — never widen under `Trunc`, etc.),
///   * a `Bitcast` between DIFFERENT integer widths (not a same-width relabel).
///
/// Returns `Ok(Some(opcode))` for the two-type extends and the truncate (the
/// caller emits it with `from_ty`/`to_ty` baked into the opcode), or `Ok(None)`
/// for the same-width `Bitcast` no-op (the caller emits a bare `Copy`).
fn map_int_cast(
    op: CastOp,
    src_ty: &Ty,
    dst_ty: &Ty,
    name: &str,
) -> Result<Option<Opcode>, ModuleLirError> {
    let fail = |detail: String| ModuleLirError::UnsupportedCast {
        name: name.to_string(),
        op: cast_op_name(op),
        detail,
    };

    match op {
        CastOp::Trunc | CastOp::SExt | CastOp::ZExt | CastOp::Bitcast => {
            // Both operands must be scalar integers in the i8..i64 envelope. i128
            // (register-pair) and non-integer (Bool routes through Select at the
            // producer, never a Cast; pointers are handled by the fail-closed
            // pointer arms) fail closed.
            let from = map_scalar_int_ty(src_ty, "cast source")
                .map_err(|_| fail(format!("source type {src_ty:?} is not a scalar integer")))?;
            let to = map_scalar_int_ty(dst_ty, "cast dest")
                .map_err(|_| fail(format!("dest type {dst_ty:?} is not a scalar integer")))?;
            if matches!(from, LirType::I128) || matches!(to, LirType::I128) {
                return Err(fail(
                    "128-bit int-to-int cast is register-pair, outside the proven \
                     single-instruction envelope"
                        .to_string(),
                ));
            }
            let from_bytes = from.bytes();
            let to_bytes = to.bytes();
            match op {
                CastOp::Trunc => {
                    // A truncate MUST narrow (or the producer would have emitted a
                    // different op); a non-narrowing Trunc is a malformed node.
                    if from_bytes <= to_bytes {
                        return Err(fail(format!(
                            "Trunc requires source wider than dest, got {from:?} -> {to:?}"
                        )));
                    }
                    Ok(Some(Opcode::Trunc { to_ty: to }))
                }
                CastOp::SExt | CastOp::ZExt => {
                    // An extend MUST widen; a non-widening extend is malformed.
                    if from_bytes >= to_bytes {
                        return Err(fail(format!(
                            "{} requires source narrower than dest, got {from:?} -> {to:?}",
                            cast_op_name(op)
                        )));
                    }
                    if matches!(op, CastOp::SExt) {
                        Ok(Some(Opcode::Sextend { from_ty: from, to_ty: to }))
                    } else {
                        Ok(Some(Opcode::Uextend { from_ty: from, to_ty: to }))
                    }
                }
                CastOp::Bitcast => {
                    // Same-width int reinterpret only (e.g. `i32 as u32`). A
                    // Bitcast between different widths is not a signedness relabel
                    // and this bridge does not model it; fail closed.
                    if from_bytes != to_bytes {
                        return Err(fail(format!(
                            "int Bitcast requires equal widths, got {from:?} -> {to:?}"
                        )));
                    }
                    // Identity on the bit pattern -> Copy (see doc comment).
                    Ok(None)
                }
                _ => unreachable!("outer match restricts to Trunc/SExt/ZExt/Bitcast"),
            }
        }
        // All float casts — no verified float lowering.
        CastOp::FPTrunc
        | CastOp::FPExt
        | CastOp::FPToUI
        | CastOp::FPToSI
        | CastOp::FPToUISat
        | CastOp::FPToSISat
        | CastOp::UIToFP
        | CastOp::SIToFP => Err(fail("float casts have no verified lowering".to_string())),
        // Pointer casts — width-less operands, outside the scalar-int envelope.
        CastOp::PtrToInt | CastOp::IntToPtr | CastOp::PtrToPtr => {
            Err(fail("pointer casts are outside the scalar-int envelope".to_string()))
        }
        // Transmute / fn-pointer reify — need a validity/reify proof not carried here.
        CastOp::Transmute | CastOp::ReifyFnPointer => {
            Err(fail("needs a validity/reify proof this bridge does not carry".to_string()))
        }
    }
}

/// Map a checked-arithmetic `trust_ir::Inst::Overflow` (`op` + operand `ty`) to
/// the LIR first-class checked opcode that produces `[value, overflow_b1]`.
///
/// `Inst::Overflow` is the MIR-faithful `a + b` shape (`AddWithOverflow`, etc.)
/// the producer emits when overflow checks are on: it carries TWO results — the
/// wrapping value and a 1-bit overflow flag — and is followed by a no-overflow
/// `Assert`. The trust-cg LIR has matching `Checked{S,U}{add,sub,mul}` opcodes
/// (issue #474) whose ISel lowers Add/Sub via flag-setting ADDS/SUBS+CSET at
/// I32/I64, and Mul via the SMULH/UMULH high-half idiom at I64 only.
///
/// FAIL-CLOSED on the shapes the verified ISel slice does not lower:
///   * 128-bit operands (no native flag/high-half idiom),
///   * `Mul` narrower than 64-bit (`CheckedSmul`/`CheckedUmul` are I64-only),
///   * any non-fixed-width-integer operand type.
///
/// NOTE: i32/u32 checked `Mul` is NOT routed here — the caller intercepts it and
/// lowers it via exact i64 widening (`{s,z}ext` + `Imul` + range-check Icmps),
/// so this function only sees `Mul` at i8/i16/u8/u16 (fail closed), i64/u64
/// (first-class `Checked{S,U}mul`), or i128 (fail closed).
fn map_overflow_op(op: OverflowOp, ty: &Ty, name: &str) -> Result<Opcode, ModuleLirError> {
    let signed = ty.is_signed();
    // The compared operands must be a fixed-width integer the ISel handles.
    let lir_ty = map_scalar_int_ty(ty, "Overflow operand")?;
    if matches!(lir_ty, LirType::I128) {
        return Err(ModuleLirError::UnsupportedOverflow {
            name: name.to_string(),
            detail: format!("128-bit checked {op:?} has no verified flag/high-half ISel idiom"),
        });
    }
    let opcode = match (op, signed) {
        (OverflowOp::AddOverflow, true) => Opcode::CheckedSadd,
        (OverflowOp::AddOverflow, false) => Opcode::CheckedUadd,
        (OverflowOp::SubOverflow, true) => Opcode::CheckedSsub,
        (OverflowOp::SubOverflow, false) => Opcode::CheckedUsub,
        (OverflowOp::MulOverflow, signed) => {
            // CheckedSmul/CheckedUmul lower only at I64 (SMULH/UMULH are
            // 64-bit only). A narrower mul would need the fallback widening
            // sequence the verified ISel slice does not yet carry.
            if !matches!(lir_ty, LirType::I64) {
                return Err(ModuleLirError::UnsupportedOverflow {
                    name: name.to_string(),
                    detail: format!(
                        "checked Mul on {lir_ty:?} (CheckedSmul/CheckedUmul lower only at 64-bit)"
                    ),
                });
            }
            if signed { Opcode::CheckedSmul } else { Opcode::CheckedUmul }
        }
    };
    Ok(opcode)
}

/// Map a `trust_ir::ICmpOp` to a LIR `IntCC`.
fn map_icmp(op: ICmpOp) -> IntCC {
    match op {
        ICmpOp::Eq => IntCC::Equal,
        ICmpOp::Ne => IntCC::NotEqual,
        ICmpOp::Ult => IntCC::UnsignedLessThan,
        ICmpOp::Ule => IntCC::UnsignedLessThanOrEqual,
        ICmpOp::Ugt => IntCC::UnsignedGreaterThan,
        ICmpOp::Uge => IntCC::UnsignedGreaterThanOrEqual,
        ICmpOp::Slt => IntCC::SignedLessThan,
        ICmpOp::Sle => IntCC::SignedLessThanOrEqual,
        ICmpOp::Sgt => IntCC::SignedGreaterThan,
        ICmpOp::Sge => IntCC::SignedGreaterThanOrEqual,
    }
}

/// Static discriminant name for an `Inst`, for fail-closed diagnostics.
fn inst_name(inst: &Inst) -> &'static str {
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
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GEP { .. } => "GEP",
        Inst::PtrData { .. } => "PtrData",
        Inst::PtrMetadata { .. } => "PtrMetadata",
        Inst::PtrFromParts { .. } => "PtrFromParts",
        Inst::AtomicLoad { .. } => "AtomicLoad",
        Inst::AtomicStore { .. } => "AtomicStore",
        Inst::AtomicRMW { .. } => "AtomicRMW",
        Inst::CmpXchg { .. } => "CmpXchg",
        Inst::Fence { .. } => "Fence",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::Return { .. } => "Return",
        Inst::ExtractField { .. } => "ExtractField",
        Inst::InsertField { .. } => "InsertField",
        Inst::ExtractElement { .. } => "ExtractElement",
        Inst::InsertElement { .. } => "InsertElement",
        Inst::Const { .. } => "Const",
        Inst::NullPtr => "NullPtr",
        Inst::GlobalAddr { .. } => "GlobalAddr",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Unreachable => "Unreachable",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        Inst::Borrow { .. } => "Borrow",
        Inst::BorrowMut { .. } => "BorrowMut",
        Inst::EndBorrow { .. } => "EndBorrow",
        Inst::Retain { .. } => "Retain",
        Inst::Release { .. } => "Release",
        Inst::IsUnique { .. } => "IsUnique",
        Inst::Dealloc { .. } => "Dealloc",
        Inst::OpenFrame { .. } => "OpenFrame",
        Inst::BindSlot { .. } => "BindSlot",
        Inst::LoadSlot { .. } => "LoadSlot",
        Inst::CloseFrame { .. } => "CloseFrame",
        Inst::SeqMapAddK { .. } => "SeqMapAddK",
        Inst::SeqMapNot { .. } => "SeqMapNot",
        Inst::SeqMap { .. } => "SeqMap",
        Inst::CoroSuspend { .. } => "CoroSuspend",
        Inst::Invoke { .. } => "Invoke",
        Inst::LandingPad { .. } => "LandingPad",
        Inst::Resume { .. } => "Resume",
        Inst::DialectOp(_) => "DialectOp",
    }
}

/// Per-function value-numbering context.
///
/// trust_ir uses a global SSA `ValueId` space; LIR ISel expects formal
/// arguments to occupy `Value(0)..Value(arg_count-1)` and every other value to
/// be a fresh dense `Value`. We map each `trust_ir::ValueId` (encountered as a
/// block param or an instruction result) to a fresh LIR `Value`, fail-closing on
/// any use of a value we have not yet defined.
struct ValueMap {
    map: HashMap<ValueId, Value>,
    next: u32,
}

impl ValueMap {
    fn new() -> Self {
        Self { map: HashMap::new(), next: 0 }
    }

    /// Reserve a dense LIR value for an SSA def (param or result). Idempotent:
    /// re-defining an already-seen `ValueId` returns its existing `Value` (SSA
    /// guarantees a single def, so this only fires for the deliberate entry-param
    /// pre-binding).
    fn define(&mut self, id: ValueId) -> Value {
        if let Some(v) = self.map.get(&id) {
            return *v;
        }
        let v = Value(self.next);
        self.next += 1;
        self.map.insert(id, v);
        v
    }

    /// The next dense LIR value index. Edge-split / cycle-break temporaries
    /// allocate from here so they never alias an SSA-bound value.
    fn next_value(&self) -> u32 {
        self.next
    }

    /// Resolve an already-defined SSA value, fail-closed otherwise.
    fn resolve(&self, id: ValueId, name: &str) -> Result<Value, ModuleLirError> {
        self.map
            .get(&id)
            .copied()
            .ok_or(ModuleLirError::UndefinedValue { name: name.to_string(), value: id.index() })
    }
}

/// Function-scoped stack-slot allocator + alloca-pointer provenance.
///
/// Mirrors the VF->LIR memory model (`lower.rs`: `alloc_stack_slot` +
/// `local_stack_slots`). Each `trust_ir::Inst::Alloca` pushes one
/// `StackSlotInfo` and records that the Alloca's result LIR `Value` is the
/// address of that slot. A later `Load`/`Store`/`GEP` may only use a pointer
/// `Value` that appears in `slot_of` — an opaque incoming pointer fails closed
/// (`NonLocalPointer`), because the scalar-memory slice only reasons about the
/// stack slots it allocated itself.
struct MemoryCtx {
    /// Parallel to LIR `Function::stack_slots`; index == `StackAddr { slot }`.
    stack_slots: Vec<StackSlotInfo>,
    /// LIR pointer `Value` -> the stack-slot index it addresses.
    slot_of: HashMap<Value, u32>,
    /// The scalar pointee LIR type each alloca-rooted pointer addresses, used
    /// to validate that a `Load`/`Store` width matches the slot's element type.
    pointee_ty: HashMap<Value, LirType>,
}

impl MemoryCtx {
    fn new() -> Self {
        Self { stack_slots: Vec::new(), slot_of: HashMap::new(), pointee_ty: HashMap::new() }
    }

    /// Allocate a fresh fixed-size stack slot for `lir_ty`, returning its index.
    fn alloc_slot(&mut self, lir_ty: &LirType) -> u32 {
        let slot = self.stack_slots.len() as u32;
        self.stack_slots.push(StackSlotInfo::new(lir_ty.bytes(), lir_ty.align()));
        slot
    }

    /// Allocate a fresh fixed-size stack slot of an explicit `size`/`align`,
    /// returning its index. Used for AGGREGATE slots whose size/align come from
    /// the C-style [`aggregate_mem_layout`] (matching trust-ir's
    /// `aggregate_layout`), so the slot the field Str/Ldr address into is exactly
    /// the in-memory aggregate the reference interpreter round-trips.
    fn alloc_sized_slot(&mut self, size: u32, align: u32) -> u32 {
        let slot = self.stack_slots.len() as u32;
        self.stack_slots.push(StackSlotInfo::new(size, align));
        slot
    }
}

/// The C-style in-memory layout of a 2-field scalar aggregate (`Ty::Tuple` of
/// two scalar-int/Bool fields), computed IDENTICALLY to the pinned trust-ir
/// reference interpreter's `aggregate_layout` (`first-party/trust-ir/.../
/// interpret.rs`): each field is placed at the next offset aligned up to its
/// natural alignment, and the total size is rounded up to the aggregate
/// alignment (max field alignment, min 1).
///
/// SOUNDNESS — this is the layout-match contract. The value-diff interpreter
/// stores/loads the aggregate through `aggregate_layout`'s `field_offsets`; the
/// converter MUST place its per-field Str/Ldr at the SAME byte offsets or the
/// emitted machine bytes would disagree with the interpreted result. The
/// per-field scalar (`byte_size`/`byte_align`) values used here are exactly the
/// interpreter's (`I8/U8/Bool`=1, `I16/U16`=2, `I32/U32`=4, `I64/U64`=8); a
/// `LirType`'s `bytes()`/`align()` agree with those for the scalar ints this
/// slice admits (re-validated below). Any field type whose layout the converter
/// cannot reproduce 1:1 fails closed (the caller restricts to 2-field scalar
/// tuples before calling this).
#[derive(Clone, Debug, PartialEq, Eq)]
struct AggMemLayout {
    /// Total byte size (rounded up to `align`).
    size: u32,
    /// Aggregate alignment (max field alignment, min 1).
    align: u32,
    /// Per-field `(byte_offset, lir_field_type)` in declaration order.
    field_offsets: Vec<(u32, LirType)>,
}

/// Natural byte size / alignment of a scalar-int/Bool field, matching the
/// trust-ir interpreter's `byte_size`/`byte_align` for these types EXACTLY.
/// FAIL-CLOSED on any non-scalar field (the C layout would need a recursive
/// aggregate layout this slice does not reproduce).
fn scalar_field_size_align(ty: &Ty, name: &str) -> Result<(u32, u32, LirType), ModuleLirError> {
    // trust-ir interpret.rs byte_size/byte_align: Bool/I8/U8 = (1,1),
    // I16/U16 = (2,2), I32/U32 = (4,4), I64/U64 = (8,8). i128 is admitted as a
    // scalar carrier but its 16-byte layout is NOT part of this 2-field slice
    // (the proven mem slice is i8..i64); fail closed so a wrong width is never
    // laid out.
    let (size, align): (u32, u32) = match ty {
        Ty::Bool | Ty::I8 | Ty::U8 => (1, 1),
        Ty::I16 | Ty::U16 => (2, 2),
        Ty::I32 | Ty::U32 => (4, 4),
        Ty::I64 | Ty::U64 => (8, 8),
        // Trust (v25 B1): isize/usize are pointer-width — 8 bytes on the pinned
        // 64-bit target (trust-ir interpret int_shape convention), laid out
        // exactly like I64/U64.
        Ty::Isize | Ty::Usize => (8, 8),
        // Trust (v25 B1): char is a 32-bit unsigned carrier — 4-byte size/align,
        // exactly the U32 layout.
        Ty::Char => (4, 4),
        other => {
            return Err(ModuleLirError::UnsupportedAggregate {
                name: name.to_string(),
                detail: format!(
                    "aggregate field type {other:?} has no reproducible scalar C-layout in the \
                     i8..i64/Bool aggregate-memory slice"
                ),
            });
        }
    };
    let lir = map_scalar_int_ty(ty, "aggregate field")?;
    Ok((size, align, lir))
}

/// Round `value` up to the next multiple of `align` (a power of two). Mirrors
/// the interpreter's `align_up`.
fn align_up_u32(value: u32, align: u32) -> u32 {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

/// Resolve the in-declaration-order scalar field types of an aggregate type,
/// threading the `module` so a `Ty::Struct(sid)` resolves its fields from the
/// Module's `StructDef` EXACTLY as the interpreter's `struct_layout` does
/// (`def.fields.iter().map(|f| &f.ty)`). A `Ty::Tuple` is self-describing.
///
/// FAIL-CLOSED on any non-aggregate type, and — for a struct — on a missing
/// `StructDef` or a `repr` other than the layout-default `Rust`: the converter
/// reproduces ONLY the natural C-style layout the interpreter computes (which
/// ignores `repr`/`size`/`align`/`offset`), so a `#[repr(C/packed/transparent)]`
/// struct — whose real ABI layout could differ — is rejected rather than laid
/// out under a layout the emitted bytes are not proven against. The bridge emits
/// `StructRepr::Rust` for every ADT/closure-env it lowers, so this covers the
/// real emitted shape; a non-default repr is out of the proven slice.
fn aggregate_field_types(ty: &Ty, module: &Module, name: &str) -> Result<Vec<Ty>, ModuleLirError> {
    match ty {
        Ty::Tuple(elems) => Ok(elems.clone()),
        Ty::Struct(sid) => {
            let def =
                module.struct_def(*sid).ok_or_else(|| ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "aggregate Ty::Struct({}) has no StructDef in the module table",
                        sid.as_usize()
                    ),
                })?;
            // Reproduce ONLY the interpreter's natural C layout, which ignores
            // `repr`. A non-`Rust` repr's real ABI layout could diverge from the
            // natural layout the emitted bytes are proven against; fail closed.
            if def.repr != trust_ir::ty::StructRepr::Rust {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "aggregate Ty::Struct({}) has non-default repr {:?}; only the natural \
                         (repr(Rust)) C layout is reproduced in the aggregate-memory slice",
                        sid.as_usize(),
                        def.repr
                    ),
                });
            }
            Ok(def.fields.iter().map(|f| f.ty.clone()).collect())
        }
        other => Err(ModuleLirError::UnsupportedAggregate {
            name: name.to_string(),
            detail: format!(
                "aggregate-memory layout is only computed for Ty::Tuple / Ty::Struct; got {other:?}"
            ),
        }),
    }
}

/// Compute the C-style [`AggMemLayout`] of a `Ty::Tuple`/`Ty::Struct` made of
/// scalar fields, matching the trust-ir interpreter's `aggregate_layout`
/// BYTE-FOR-BYTE. Handles N scalar fields (generalized from the initial 2-field
/// tuple slice). FAIL-CLOSED on a non-aggregate type, a non-scalar field, or a
/// zero-field aggregate (there is nothing to round-trip and the bridge never
/// emits one for a promoted local).
fn aggregate_mem_layout(
    ty: &Ty,
    module: &Module,
    name: &str,
) -> Result<AggMemLayout, ModuleLirError> {
    let fields = aggregate_field_types(ty, module, name)?;
    // The bridge only promotes a NON-EMPTY aggregate local to a slot. A
    // zero-field aggregate has no field to Str/Ldr; reject rather than emit a
    // vacuous slot.
    if fields.is_empty() {
        return Err(ModuleLirError::UnsupportedAggregate {
            name: name.to_string(),
            detail: format!("aggregate-memory slice rejects a zero-field aggregate {ty:?}"),
        });
    }
    let mut offset: u32 = 0;
    let mut max_align: u32 = 1;
    let mut field_offsets = Vec::with_capacity(fields.len());
    for field_ty in &fields {
        // scalar_field_size_align FAILS CLOSED on any non-scalar field (nested
        // struct/tuple, float, i128, pointer), so a struct-of-struct / float /
        // i128-field aggregate never lays out under this slice.
        let (f_size, f_align, f_lir) = scalar_field_size_align(field_ty, name)?;
        offset = align_up_u32(offset, f_align);
        field_offsets.push((offset, f_lir));
        offset += f_size;
        max_align = max_align.max(f_align);
    }
    let size = align_up_u32(offset, max_align);
    Ok(AggMemLayout { size, align: max_align, field_offsets })
}

/// Convert the function with id `func_id` in `module` into a LIR `Function`.
///
/// Fail-closed on every shape outside the scalar slice — see
/// [`ModuleLirError`]. The produced LIR is exactly the shape
/// `TrustCgCodegenBackend::emit_object` consumes; the resulting object's
/// machine output is verified equal to the function's `trust_ir` semantics by
/// the proven-output gate (see `verify_output`).
pub fn lower_module_to_lir(
    module: &Module,
    func_id: trust_ir::value::FuncId,
) -> Result<LirFunction, ModuleLirError> {
    let function =
        module.function_by_id(func_id).ok_or(ModuleLirError::MissingFunction(func_id.index()))?;
    lower_trust_ir_function_to_lir(module, function)
}

/// Convert a `trust_ir::Function` into a LIR `Function` using `module` for type
/// resolution (`func_types`).
///
/// Before lowering, a Module-level pre-pass ([`inline_local_pure_leaf_calls`])
/// rewrites every CALL to a local pure leaf function into the callee's body
/// spliced inline (params bound to the call's args, the callee's `Return` value
/// routed to the call's result). The downstream converter therefore only ever
/// sees a call-FREE function and the existing scalar / control-flow / memory
/// machinery handles it with zero changes. Any call that does NOT meet the
/// admission predicate is left untouched and the converter fail-closes on it
/// (`UnsupportedInst { inst: "Call" }`).
pub fn lower_trust_ir_function_to_lir(
    module: &Module,
    function: &IrFunction,
) -> Result<LirFunction, ModuleLirError> {
    lower_trust_ir_function_to_lir_impl(module, function, false)
}

/// Like [`lower_trust_ir_function_to_lir`], but a `Call` to a LOCAL pure callee
/// in the gate's single-register AAPCS64 scalar fragment
/// ([`callee_is_real_call_composable`]) is lowered to a REAL LIR
/// `Opcode::Call { name }` (ISel: `Bl` + an `ARM64_RELOC_BRANCH26` naming the
/// callee) INSTEAD of being inlined. Every OTHER call (impure / non-local /
/// non-fragment / not-yet-composable) is still routed through the inliner and, if
/// that too declines, fails closed — a real Call is NEVER emitted for a callee
/// the proven-output gate could not compose.
///
/// This is the FIRST structural step toward cross-function calls: the emitted
/// __text carries a genuine `Bl` cross-function edge (the OPPOSITE of the inline
/// slice's no-`Bl` guarantee), which the gate / proven-output executor discharges
/// by composing the callee at the reloc target (mirroring
/// `verify_output::model_local_call`). Inlining remains the DEFAULT; this is the
/// new capability that unblocks closures / trait-object dispatch.
pub fn lower_trust_ir_function_to_lir_real_calls(
    module: &Module,
    function: &IrFunction,
) -> Result<LirFunction, ModuleLirError> {
    lower_trust_ir_function_to_lir_impl(module, function, true)
}

fn lower_trust_ir_function_to_lir_impl(
    module: &Module,
    function: &IrFunction,
    real_calls: bool,
) -> Result<LirFunction, ModuleLirError> {
    // PRE-PASS: inline admitted local pure leaf calls. Returns the original
    // function unchanged when it contains no inlinable call. When `real_calls` is
    // set, a call to a gate-composable local pure callee is DEFERRED (left in
    // place) so the body lowering below emits a REAL `Opcode::Call` for it; all
    // other calls still go through the inliner.
    let inlined = inline_local_pure_leaf_calls(module, function, real_calls)?;
    let function: &IrFunction = inlined.as_ref();
    let name = &function.name;

    // --- Signature: resolve the FuncTy and map params + the single result. ---
    let func_ty = module.func_types.get(function.ty.as_usize()).ok_or_else(|| {
        ModuleLirError::MissingFuncType { name: name.clone(), ty: function.ty.index() }
    })?;

    if func_ty.is_vararg {
        return Err(ModuleLirError::UnsupportedSignature {
            name: name.clone(),
            detail: "variadic functions are unsupported".to_string(),
        });
    }
    if func_ty.returns.len() != 1 {
        return Err(ModuleLirError::UnsupportedSignature {
            name: name.clone(),
            detail: format!("expected exactly 1 return value, got {}", func_ty.returns.len()),
        });
    }

    let mut params = Vec::with_capacity(func_ty.params.len());
    for p in &func_ty.params {
        params.push(map_scalar_int_ty(p, "function parameter")?);
    }
    let return_ty = map_scalar_int_ty(&func_ty.returns[0], "function return")?;
    let signature = Signature { params, returns: vec![return_ty] };

    // --- Body: one OR MORE basic blocks with SSA block-param merges. ---
    if function.blocks.is_empty() {
        return Err(ModuleLirError::NoBlocks { name: name.clone() });
    }

    // Index blocks by their BlockId so branch targets resolve, and validate that
    // the entry block is present.
    let blocks_by_id: HashMap<u32, &trust_ir::Block> =
        function.blocks.iter().map(|b| (b.id.index(), b)).collect();
    if !blocks_by_id.contains_key(&function.entry.index()) {
        return Err(ModuleLirError::MissingBlock {
            name: name.clone(),
            target: function.entry.index(),
        });
    }

    // ----------------------------------------------------------------------
    // PASS 1 — pre-allocate a dense LIR `Value` for every SSA def in the whole
    // function so cross-block uses resolve regardless of block visitation order.
    //
    // The ISel convention requires the formal arguments to occupy
    // Value(0)..Value(arg_count-1). The canonical well-formed Module carries the
    // formals as the ENTRY block's params, so we bind those FIRST and in order.
    // Then every non-entry block's params and every instruction result get a
    // fresh dense Value.
    // ----------------------------------------------------------------------
    let entry_block = blocks_by_id[&function.entry.index()];
    let mut vmap = ValueMap::new();
    let mut value_types: HashMap<Value, LirType> = HashMap::new();

    // Entry-block params == formal arguments (positional, Value(0..n)).
    if entry_block.params.len() != func_ty.params.len() {
        return Err(ModuleLirError::BlockParamArity {
            name: name.clone(),
            got: entry_block.params.len(),
            expected: func_ty.params.len(),
        });
    }
    for ((param_id, param_ty), sig_ty) in entry_block.params.iter().zip(&func_ty.params) {
        let lir_ty = map_scalar_int_ty(param_ty, "entry block param")?;
        if param_ty != sig_ty {
            return Err(ModuleLirError::UnsupportedSignature {
                name: name.clone(),
                detail: format!(
                    "entry block param type {param_ty:?} disagrees with signature {sig_ty:?}"
                ),
            });
        }
        let v = vmap.define(*param_id);
        value_types.insert(v, lir_ty);
    }

    // Establish a deterministic reachable block order (entry first), and along
    // the way pre-allocate non-entry block params + every instruction result.
    let order = reachable_block_order(function, &blocks_by_id, name)?;
    for &bid in &order {
        let block = blocks_by_id[&bid];
        if bid != function.entry.index() {
            for (param_id, param_ty) in &block.params {
                let lir_ty = map_scalar_int_ty(param_ty, "block param")?;
                let v = vmap.define(*param_id);
                value_types.insert(v, lir_ty);
            }
        }
        for node in &block.body {
            // A terminator must be last; results on it are an error (handled in
            // pass 2). Pre-allocate the value-producing instruction results.
            for result in &node.results {
                let _ = vmap.define(*result);
            }
        }
    }

    // ----------------------------------------------------------------------
    // PASS 1.5 — DEAD-UNDEF-SEED ANALYSIS (fail-closed). The producer's
    // cross-block control-flow merge (`if c { _0 = a } else { _0 = b }; _0`)
    // does NOT use block params: it promotes the joined local to a stack slot,
    // seeds the slot with a fresh `Inst::Undef`, Stores that seed once, then
    // OVERWRITES the slot on every arm before the join `Load`
    // (`trust-ir-bridge::lower::promote_local_to_memory`). Under the RATIFIED
    // trust-ir poison semantics (`first-party/trust-ir/docs/ub-numerics-policy.md`
    // §4: `Undef` is a poison value; only READING poison into a strict op or
    // BRANCHING on it is UB), that seed poison is never observed — it is a dead
    // store, fully determined (overwritten) before the only `Load`.
    //
    // PASS 1.6 — CHECKED-ARITH TUPLE DECOMPOSITION (fail-closed). The BRIDGE's
    // `a + b` idiom builds the MIR `(value, overflowed)` pair as a 2-field SSA
    // TUPLE (`undef (Int,Bool)` seed + two `InsertField`s), read back by
    // `ExtractField`. This pre-pass PROVES the tuple can be decomposed into the
    // two scalar SSA Values it carries (NO tuple-in-memory; the pinned
    // interpreter lacks `Ty::Tuple` `byte_size`), returning the seed/insert/
    // extract bookkeeping the body lowering consumes. Run BEFORE the scalar
    // Undef analysis so its admitted `Tuple` seeds are excluded from the scalar
    // memory-merge scan. Fail-closes on any non-decomposable aggregate.
    let tuple_decompose = analyze_checked_arith_tuples(&order, &blocks_by_id, name)?;

    // PASS 1.7 — AGGREGATE-IN-MEMORY DECOMPOSITION (fail-closed). The BRIDGE
    // promotes a multi-block-written aggregate local to a WHOLE-aggregate stack
    // slot and round-trips a 2-field scalar `Ty::Tuple` through it as a unit
    // (`Alloca(Tuple)` + `Store(Tuple)` + `Load(Tuple)`, fields built/read by
    // `InsertField`/`ExtractField`). This pre-pass PROVES the aggregate decomposes
    // into per-field scalars laid out at the C-style field offsets
    // (`aggregate_mem_layout`, byte-for-byte the trust-ir interpreter's
    // `aggregate_layout`), returning the slot-layout + seed/insert/store/load/
    // extract bookkeeping the body lowering consumes. Run AFTER the checked-arith
    // tuple analysis so its admitted pure-SSA pairs are excluded, and BEFORE the
    // scalar Undef analysis so the aggregate `Undef`/`Const` seeds are excluded
    // from the scalar memory-merge scan. Fail-closes on any aggregate it cannot
    // lay out 1:1.
    let agg_mem = analyze_aggregate_memory(module, &order, &blocks_by_id, &tuple_decompose, name)?;

    // `admitted_undef_seeds` is the set of `Undef` result ValueIds we have
    // PROVEN to be exactly this dead-seed shape. Only those may be lowered (to a
    // defined `Iconst 0`, whose Store is then dead). Every OTHER `Undef` is left
    // unadmitted and fail-closes in `lower_value_inst` — a poison value is never
    // materialized at a site that could observe it. The check is a local,
    // conservative MUST analysis; anything it cannot prove is rejected. The
    // aggregate-memory `Undef(Tuple)` seeds (admitted above) are excluded so the
    // scalar scan only sees the SCALAR seeds it models.
    let admitted_undef_seeds = analyze_dead_undef_seeds(
        function,
        &order,
        &blocks_by_id,
        &tuple_decompose.admitted_tuple_seeds,
        &agg_mem.agg_undef_seeds,
        name,
    )?;

    // ----------------------------------------------------------------------
    // PASS 2 — lower each block's straight-line body and terminator. Per-edge
    // block-arg passing is realized by emitting `Copy` into the TARGET block's
    // param Values inside the predecessor (the LIR block-argument convention).
    // Conditional edges into a param-carrying target are split through a fresh
    // edge-block so the Copy lands on the correct side of the branch.
    // ----------------------------------------------------------------------
    // Trust: std HashMap is required by the trust-cg-lower `Function` API.
    #[allow(rustc::default_hash_types)]
    let mut blocks: std::collections::HashMap<Block, LirBlock> = std::collections::HashMap::new();
    let mut block_order: Vec<Block> = Vec::with_capacity(order.len());
    // Edge-split blocks accumulate here and are appended after the real blocks.
    let mut edge_blocks: Vec<(Block, LirBlock)> = Vec::new();
    let mut next_edge_block: u32 = order.iter().copied().max().unwrap_or(0) + 1;
    // Fresh-value allocator for cycle-breaking edge-copy temporaries; starts past
    // every SSA-bound value so a temp never aliases a real value.
    let mut next_value: u32 = vmap.next_value();

    // Function-scoped memory state: stack slots accumulate across all blocks and
    // alloca-pointer provenance flows along the straight-line bodies.
    let mut mem = MemoryCtx::new();

    // KNOWN-TARGET INDIRECT-CALL provenance: LIR pointer `Value` -> the symbol
    // name a `GlobalAddr` materialized into it (via `Opcode::GlobalRef`). A
    // `CallIndirect` whose function-pointer operand resolves to a Value in this
    // map is a KNOWN target — it is admitted (and composed by the executor)
    // exactly like a direct `Call` to that symbol. An operand NOT in this map is
    // an OPEN target (a fn-pointer not traceable to a concrete local pure fn) and
    // fails closed (a future havoc-only slice).
    let mut global_addr_syms: HashMap<Value, String> = HashMap::new();

    // Function-scoped per-aggregate field-value bookkeeping for the aggregate-
    // memory slice: each tracked aggregate SSA value -> its per-field LIR Values
    // (the scalar each field decomposes to). Built incrementally as the body is
    // lowered: a `Const::Aggregate`/`InsertField` records field Values without
    // emitting whole-aggregate LIR; an aggregate `Load` records the per-field Ldr
    // results; an aggregate `Store` reads them; an `ExtractField` copies the
    // field. Empty (and untouched) when the function has no aggregate slot.
    let mut agg_field_values: HashMap<ValueId, Vec<Value>> = HashMap::new();

    // A shared trap block for `Assert` no-overflow checks. Allocated lazily the
    // first time an `Assert` is lowered: every failed overflow assert branches
    // here, and the block is a single `Trap` (a synchronous abort, mirroring the
    // VF -> LIR panic-block convention — the trap-iff-overflow semantics of MIR's
    // overflow assert without fabricating a normal return path).
    let mut trap_block: Option<Block> = None;
    // Assert-split continuation blocks (params-free) accumulate here, like the
    // edge-split trampolines, and are appended after the real blocks.
    let mut split_blocks: Vec<(Block, LirBlock)> = Vec::new();

    for &bid in &order {
        let block = blocks_by_id[&bid];
        let lir_id = Block(bid);
        block_order.push(lir_id);

        let (body, terminator) = split_terminator(block, name)?;

        // Lower the straight-line body, splitting the LIR block at each `Assert`:
        // an `Assert { cond }` becomes `Brif(cond, cont, trap)`, ending the
        // current LIR segment and starting a fresh params-free continuation that
        // carries the rest of the body. `seg` is the in-progress segment; the
        // FIRST segment keeps the trust_ir block's params, every continuation is
        // params-free.
        let mut seg: Vec<Instruction> = Vec::new();
        let mut cur_block = lir_id;
        let mut is_first_segment = true;

        for node in body {
            if let Inst::Assert { cond } = &node.inst {
                // The assert condition is `ok` (== !overflowed): branch to the
                // continuation when true, to the shared trap block when false.
                let cond_v = vmap.resolve(*cond, name)?;
                let trap = *trap_block.get_or_insert_with(|| {
                    let b = Block(next_edge_block);
                    next_edge_block += 1;
                    split_blocks.push((
                        b,
                        LirBlock {
                            params: vec![],
                            instructions: vec![Instruction {
                                opcode: Opcode::Trap,
                                args: vec![],
                                results: vec![],
                            }],
                            source_locs: vec![],
                        },
                    ));
                    b
                });
                let cont = Block(next_edge_block);
                next_edge_block += 1;

                seg.push(Instruction {
                    opcode: Opcode::Brif { cond: cond_v, then_dest: cont, else_dest: trap },
                    args: vec![cond_v],
                    results: vec![],
                });

                // Finalize the current segment.
                let seg_params: Vec<(Value, LirType)> = if is_first_segment {
                    block
                        .params
                        .iter()
                        .map(|(pid, pty)| {
                            let v = vmap.resolve(*pid, name)?;
                            let lty = map_scalar_int_ty(pty, "block param")?;
                            Ok((v, lty))
                        })
                        .collect::<Result<_, ModuleLirError>>()?
                } else {
                    vec![]
                };
                let finished = std::mem::take(&mut seg);
                if cur_block == lir_id {
                    blocks.insert(
                        lir_id,
                        LirBlock {
                            params: seg_params,
                            instructions: finished,
                            source_locs: vec![],
                        },
                    );
                } else {
                    split_blocks.push((
                        cur_block,
                        LirBlock {
                            params: seg_params,
                            instructions: finished,
                            source_locs: vec![],
                        },
                    ));
                }
                cur_block = cont;
                is_first_segment = false;
                continue;
            }
            lower_value_inst(
                module,
                node,
                &vmap,
                &mut value_types,
                &mut mem,
                &mut global_addr_syms,
                &mut seg,
                &mut next_value,
                &admitted_undef_seeds,
                &tuple_decompose,
                &agg_mem,
                &mut agg_field_values,
                real_calls,
                name,
            )?;
        }

        // Terminator goes into the final segment.
        lower_terminator(
            terminator,
            &vmap,
            &blocks_by_id,
            &mut seg,
            &mut edge_blocks,
            &mut next_edge_block,
            &mut next_value,
            name,
        )?;

        // Finalize the final segment (which is `lir_id` itself when no Assert
        // split occurred — the common, prior-slice-preserving path).
        let final_params: Vec<(Value, LirType)> = if is_first_segment {
            block
                .params
                .iter()
                .map(|(pid, pty)| {
                    let v = vmap.resolve(*pid, name)?;
                    let lty = map_scalar_int_ty(pty, "block param")?;
                    Ok((v, lty))
                })
                .collect::<Result<_, ModuleLirError>>()?
        } else {
            vec![]
        };
        if cur_block == lir_id {
            blocks.insert(
                lir_id,
                LirBlock { params: final_params, instructions: seg, source_locs: vec![] },
            );
        } else {
            split_blocks.push((
                cur_block,
                LirBlock { params: final_params, instructions: seg, source_locs: vec![] },
            ));
        }
    }

    // Append the edge-split blocks (params-free Copy+Jump trampolines) and the
    // Assert-split continuation / trap blocks.
    for (id, blk) in edge_blocks.into_iter().chain(split_blocks) {
        block_order.push(id);
        blocks.insert(id, blk);
    }

    let entry = Block(function.entry.index());

    #[allow(rustc::default_hash_types)]
    let value_types_std: std::collections::HashMap<Value, LirType> =
        value_types.into_iter().collect();

    Ok(LirFunction {
        name: name.clone(),
        signature,
        blocks,
        block_order,
        #[allow(rustc::default_hash_types)]
        trust_ir_origins: std::collections::HashMap::new(),
        entry_block: entry,
        stack_slots: mem.stack_slots,
        value_types: value_types_std,
        #[allow(rustc::default_hash_types)]
        pure_callees: std::collections::HashSet::new(),
        // trust-cg's LirFunction carries the libm callees ISel may treat as
        // pure; the bridge asserts no libm purity, and empty is that claim.
        libm_pure_callees: Default::default(),
        debug_meta: Default::default(),
        debug_value_bindings: vec![],
        stack_protector: Default::default(),
        param_pointee_types: Vec::new(),
        eh_info: Default::default(),
    })
}

// ===========================================================================
// INLINING PRE-PASS — `trust_ir::Module` level, before LIR lowering.
//
// A `Call` to a LOCAL PURE LEAF function is replaced by the callee's body
// spliced inline: the callee's params are bound to the call's args, every
// callee value/result gets a FRESH `ValueId` (so it cannot collide with a
// caller value or another inlined copy), and the callee's single `Return`
// operand is routed to the call's result `ValueId` via a `Copy`. The result is
// a call-FREE caller body the existing converter lowers unchanged.
//
// ADMISSION PREDICATE (all must hold; any failure leaves the Call in place so
// the converter fail-closes — the inliner never produces a wrong splice):
//
//   * LOCAL    — the callee `FuncId` resolves to a `Function` in this Module.
//   * ACYCLIC  — the callee is not the caller itself (no self-recursion). A
//                leaf callee cannot mutually recurse because it makes no calls.
//   * SINGLE-BLOCK — the callee has exactly one basic block (this first slice
//                scopes to the straight-line splice; multi-block is a sound but
//                unimplemented follow-on, reported below).
//   * SINGLE-RETURN — that block ends in `Return` with exactly one value, and
//                no other terminator appears in it.
//   * LEAF + PURE — every non-terminator instruction in the callee body is a
//                value-producing op with NO observable effect and NO nested
//                call: it is drawn from the remappable pure-scalar set
//                {Const, BinOp, ICmp, Cast, Copy, Select}. Anything else
//                (Call/CallIndirect, any Store/Load/Alloca/atomic/borrow/ARC,
//                a terminator mid-body, ...) makes the callee inadmissible. We
//                deliberately exclude memory ops here even though some are
//                "local": an inlined `Alloca` would need slot-provenance
//                threading across the splice, out of this first slice.
// ===========================================================================

/// Inline every admitted local pure leaf `Call` in `function`, returning the
/// rewritten function. Returns `Cow::Borrowed` (zero-copy) when the function
/// contains no `Call` at all, so the non-call paths (scalar / CFG / memory) are
/// completely unaffected.
///
/// A `Call` that is present but NOT admissible is left in the body verbatim;
/// the downstream converter then fail-closes on it. This function only ever
/// returns `Err` when a *would-be* inline cannot be performed soundly — it
/// never silently mis-inlines.
fn inline_local_pure_leaf_calls<'a>(
    module: &Module,
    function: &'a IrFunction,
    real_calls: bool,
) -> Result<Cow<'a, IrFunction>, ModuleLirError> {
    // Fast path: no calls anywhere -> borrow unchanged.
    let has_call = function
        .blocks
        .iter()
        .flat_map(|b| b.body.iter())
        .any(|n| matches!(n.inst, Inst::Call { .. }));
    if !has_call {
        return Ok(Cow::Borrowed(function));
    }

    // Fresh-ValueId / fresh-BlockId allocators: start past every id mentioned
    // anywhere in the caller so a spliced callee id can never alias a caller id
    // (or a previously-spliced callee id, since the counters only grow).
    let mut next_value = max_value_id(function) + 1;
    let mut next_block = max_block_id(function) + 1;

    let name = function.name.clone();
    let mut new_function = function.clone();

    // We rebuild the function's block list. Each original (caller) block is
    // processed: if it contains an admitted SINGLE-BLOCK call, the callee body
    // is spliced inline (as today, no new blocks); if it contains an admitted
    // MULTI-BLOCK call, the block is SPLIT at the call site, the callee's blocks
    // are cloned (fresh ids) and appended, and a fresh continuation block (whose
    // single param is the call result) carries the post-call instructions. A
    // block carrying neither is copied through unchanged.
    //
    // A single inlining pass handles AT MOST ONE call per original caller block
    // (the first admitted one). The cab/add shape — and every bridge-produced
    // call shape — places the call in its own block (the MIR call terminator
    // becomes `Inst::Call` + a `Br`), so one-call-per-block is the real case.
    // A second call in the same block is left for the converter to fail-close on
    // (it is NOT mis-inlined); the multi-call-per-block generalization is a
    // sound follow-on, not a correctness gap.
    let original_blocks = std::mem::take(&mut new_function.blocks);
    let mut out_blocks: Vec<trust_ir::Block> = Vec::with_capacity(original_blocks.len());

    for mut block in original_blocks {
        // Find the FIRST inlinable call in this block, and whether it is a
        // single-block or multi-block splice.
        let call_pos = block.body.iter().position(|n| matches!(n.inst, Inst::Call { .. }));
        let Some(pos) = call_pos else {
            // No call here — copy through unchanged.
            out_blocks.push(block);
            continue;
        };

        let call_node = block.body[pos].clone();
        let Inst::Call { callee, args } = &call_node.inst else {
            unreachable!("position only matches Inst::Call");
        };

        // REAL-CALL DEFERRAL. When `real_calls` is set and this call targets a
        // LOCAL callee in the gate's single-register scalar-pure fragment, we do
        // NOT inline it — we leave the `Inst::Call` in place so the body lowering
        // emits a REAL `Opcode::Call` (a `Bl` cross-function edge) the gate then
        // composes at the reloc target. Every OTHER call (impure / non-local /
        // non-fragment) still falls through to the inliner below.
        if real_calls {
            if let Some(callee_fn) = module.function_by_id(*callee) {
                if callee_fn.id != function.id && callee_is_real_call_composable(module, callee_fn)
                {
                    // Leave the Call verbatim; the converter emits a real Call.
                    out_blocks.push(block);
                    continue;
                }
            }
        }

        // SINGLE-BLOCK fast path (the established, prior-slice-preserving splice):
        // splice the callee body inline, replacing just the call node.
        match try_inline_call(module, function, *callee, args, &call_node, &mut next_value) {
            Ok(spliced) => {
                let mut new_body: Vec<InstrNode> =
                    Vec::with_capacity(block.body.len() + spliced.len());
                for (i, node) in std::mem::take(&mut block.body).into_iter().enumerate() {
                    if i == pos {
                        new_body.extend(spliced.iter().cloned());
                    } else {
                        new_body.push(node);
                    }
                }
                block.body = new_body;
                out_blocks.push(block);
                continue;
            }
            Err(_single_detail) => {
                // Not a single-block inline; try the MULTI-BLOCK splice.
            }
        }

        // MULTI-BLOCK splice. On success this appends the split caller block,
        // the cloned callee blocks, and the continuation block to `out_blocks`.
        match try_inline_call_multiblock(
            module,
            function,
            *callee,
            args,
            &call_node,
            &block,
            pos,
            &mut next_value,
            &mut next_block,
        ) {
            Ok(mut spliced_blocks) => {
                out_blocks.append(&mut spliced_blocks);
            }
            Err(_multi_detail) => {
                // Neither single- nor multi-block inline is admissible: leave the
                // Call in place verbatim so the converter fail-closes on it. We
                // never produce a wrong splice.
                out_blocks.push(block);
            }
        }
    }

    new_function.blocks = out_blocks;

    // Defensive: the splice should have removed every admitted call. Any Call
    // that REMAINS is an inadmissible one we intentionally left for the
    // converter to reject — that is the designed fail-closed boundary, NOT an
    // inliner error, so we simply return the rewritten function and let the
    // downstream converter produce its `UnsupportedInst { inst: "Call" }`.
    let _ = &name;
    Ok(Cow::Owned(new_function))
}

/// The largest `BlockId` index appearing anywhere in `function` (every block's
/// own id plus every branch/switch target), or 0 if none. Used to allocate
/// fresh BlockIds for cloned callee blocks that cannot alias a caller block.
fn max_block_id(function: &IrFunction) -> u32 {
    let mut max = 0u32;
    let mut bump = |b: BlockId| {
        if b.index() > max {
            max = b.index();
        }
    };
    for block in &function.blocks {
        bump(block.id);
        for node in &block.body {
            for t in inst_block_targets(&node.inst) {
                bump(t);
            }
        }
    }
    max
}

/// The `BlockId` targets a terminator references. Used only for the max-block
/// scan, so a conservative match over the control-flow variants suffices.
fn inst_block_targets(inst: &Inst) -> Vec<BlockId> {
    match inst {
        Inst::Br { target, .. } => vec![*target],
        Inst::CondBr { then_target, else_target, .. } => vec![*then_target, *else_target],
        Inst::Switch { default, cases, .. } => {
            let mut v: Vec<BlockId> = cases.iter().map(|c| c.target).collect();
            v.push(*default);
            v
        }
        Inst::Invoke { normal_dest, unwind_dest, .. } => vec![*normal_dest, *unwind_dest],
        _ => vec![],
    }
}

/// The largest `ValueId` index appearing anywhere in `function` (block params,
/// instruction operands, and instruction results), or 0 if none.
fn max_value_id(function: &IrFunction) -> u32 {
    let mut max = 0u32;
    let mut bump = |v: ValueId| {
        if v.index() > max {
            max = v.index();
        }
    };
    for block in &function.blocks {
        for (pid, _) in &block.params {
            bump(*pid);
        }
        for node in &block.body {
            for r in &node.results {
                bump(*r);
            }
            for v in inst_value_operands(&node.inst) {
                bump(v);
            }
        }
    }
    max
}

/// Attempt to inline ONE `Call`. On success returns the spliced instruction
/// nodes (callee body with fresh values + a final `Copy` of the callee's
/// `Return` operand into the call's result). On failure returns the admission
/// clause that was violated (the caller leaves the Call in place).
fn try_inline_call(
    module: &Module,
    caller: &IrFunction,
    callee_id: FuncId,
    args: &[ValueId],
    call_node: &InstrNode,
    next_value: &mut u32,
) -> Result<Vec<InstrNode>, String> {
    // ---- LOCAL ----
    let callee = module.function_by_id(callee_id).ok_or_else(|| {
        format!("callee FuncId {} is not local to this module", callee_id.index())
    })?;

    // ---- ACYCLIC (no self-recursion) ----
    if callee.id == caller.id {
        return Err("self-recursive call".to_string());
    }

    // ---- SINGLE-BLOCK ----
    let [callee_block] = callee.blocks.as_slice() else {
        return Err(format!(
            "callee `{}` has {} blocks; only single-block leaf callees are inlined",
            callee.name,
            callee.blocks.len()
        ));
    };

    // ---- the call must produce exactly one result (matched to one return) ----
    let [call_result] = call_node.results.as_slice() else {
        return Err(format!(
            "call has {} results; only single-result calls are inlined",
            call_node.results.len()
        ));
    };

    // ---- arity: one arg per callee param ----
    if args.len() != callee_block.params.len() {
        return Err(format!(
            "call passes {} args but callee `{}` has {} params",
            args.len(),
            callee.name,
            callee_block.params.len()
        ));
    }

    // ---- SINGLE-RETURN + LEAF + PURE: validate the whole body, and find the
    // single trailing `Return` operand. ----
    let Some((last, body)) = callee_block.body.split_last() else {
        return Err(format!("callee `{}` block is empty", callee.name));
    };
    // No terminator may appear before the last node.
    for n in body {
        if is_terminator(&n.inst) {
            return Err(format!("callee `{}` has a non-final terminator", callee.name));
        }
    }
    // The trailing node must be a single-value `Return`.
    let Inst::Return { values } = &last.inst else {
        return Err(format!(
            "callee `{}` does not end in `Return` (ends in `{}`)",
            callee.name,
            inst_name(&last.inst)
        ));
    };
    let [ret_val] = values.as_slice() else {
        return Err(format!(
            "callee `{}` returns {} values; only single-return is inlined",
            callee.name,
            values.len()
        ));
    };
    // Every straight-line node must be a remappable PURE LEAF op.
    for n in body {
        if !is_pure_leaf_inlinable(&n.inst) {
            return Err(format!(
                "callee `{}` body contains non-pure-leaf inst `{}`",
                callee.name,
                inst_name(&n.inst)
            ));
        }
        // A pure-leaf op is value-producing with exactly one result; guard it.
        if n.results.len() != 1 {
            return Err(format!(
                "callee `{}` pure-leaf inst `{}` does not have exactly one result",
                callee.name,
                inst_name(&n.inst)
            ));
        }
    }

    // ---- REMAP: build a ValueId substitution. Callee params -> the call's
    // args; every callee-defined value (instruction result) -> a FRESH id. ----
    let mut remap: HashMap<ValueId, ValueId> = HashMap::new();
    for ((param_id, _), arg) in callee_block.params.iter().zip(args) {
        remap.insert(*param_id, *arg);
    }
    for n in body {
        // Single result (validated above).
        let old = n.results[0];
        let fresh = ValueId::new(*next_value);
        *next_value += 1;
        remap.insert(old, fresh);
    }

    let resolve = |v: ValueId| -> Result<ValueId, String> {
        remap.get(&v).copied().ok_or_else(|| {
            format!(
                "callee `{}` references value {} not bound by a param or prior def \
                 (forward ref / out-of-block use)",
                callee.name,
                v.index()
            )
        })
    };

    // ---- SPLICE: emit each remapped pure-leaf node, then a `Copy` routing the
    // remapped return operand into the call's destination value. ----
    let mut out: Vec<InstrNode> = Vec::with_capacity(body.len() + 1);
    for n in body {
        let inst = remap_pure_leaf_inst(&n.inst, &resolve)?;
        let dst = resolve(n.results[0])?;
        out.push(InstrNode::new(inst).with_result(dst));
    }
    // Route the callee's return value into the call's result value. The return
    // operand is either a callee param (mapped to a caller arg) or a callee def
    // (mapped to a fresh value) — both are in `remap`.
    let ret_src = resolve(*ret_val)?;
    // The result type carrier on `Copy` is the callee's declared return ty.
    let ret_ty = callee_return_ty(module, callee).ok_or_else(|| {
        format!("callee `{}` has no resolvable return type for the splice Copy", callee.name)
    })?;
    out.push(InstrNode::new(Inst::Copy { ty: ret_ty, operand: ret_src }).with_result(*call_result));

    Ok(out)
}

// ===========================================================================
// MULTI-BLOCK INLINING — splice a LOCAL, NON-RECURSIVE, PURE, LEAF callee whose
// body spans MORE THAN ONE basic block (the real post-mono shape: `add` is a
// checked-arith body `bb0: overflow + tuple + assert -> Br bb1`, `bb1: extract
// + return`). The caller's block is SPLIT at the call; the callee's blocks are
// cloned with FRESH BlockIds + ValueIds; each callee `Return(v)` becomes a
// `Br -> cont, args=[v]` into a fresh CONTINUATION block whose single param IS
// the call's result. The post-call instructions move into `cont`.
//
// ADMISSION (all must hold; any failure returns Err and the caller leaves the
// Call in place — the inliner NEVER produces a wrong splice):
//
//   * LOCAL          — callee FuncId resolves to a Function in this Module.
//   * ACYCLIC        — callee != caller. A LEAF callee (no nested Call) cannot
//                      transitively recurse, so the leaf check below closes the
//                      whole recursion question.
//   * SINGLE-RESULT  — the call binds exactly one result value.
//   * ARITY          — one call arg per callee ENTRY-block param.
//   * PURE + LEAF    — EVERY instruction in EVERY callee block is in the
//                      converter-supported, side-effect-free set:
//                        value ops {Const, BinOp, Overflow, ICmp, Cast, Copy,
//                                   Select, Undef, InsertField, ExtractField},
//                        proof obligations {Assert, Assume} (a failed assert is
//                          a DIVERGENCE/trap, not an observable side effect),
//                        terminators {Br, CondBr, Switch, Return, Unreachable}.
//                      Anything else — a nested Call/CallIndirect/Invoke, ANY
//                      memory op (Load/Store/Alloca/GEP — would need slot
//                      provenance threaded across the splice), atomics, borrow/
//                      ARC, dealloc, frames, coroutine, EH, or dialect — makes
//                      the callee inadmissible and FAILS CLOSED.
//   * ROUTABLE RETURN — every `Return` in the callee returns exactly ONE value.
//                      Multiple `Return`s are fine: they all `Br` to the SAME
//                      single continuation block, which is the join carrying the
//                      result. A multi-value return cannot be routed -> Err.
//
// The clone preserves the callee's own control flow exactly (intra-callee edge
// targets are rewritten to the cloned BlockIds, edge ARGS are remapped through
// the value substitution), so the spliced subgraph computes precisely the
// callee's semantics on the call's args, and the continuation observes only the
// callee's returned value. The downstream converter (checked-tuple decompose,
// Assert-split, edge-arg threading, two-pass SSA pre-alloc) handles the result
// with ZERO changes — it is the same shape it lowers when the callee is the
// whole function.
// ===========================================================================

/// True for an instruction admissible ANYWHERE in a multi-block callee body:
/// the converter-supported, observably-pure value ops + the proof obligations.
/// Terminators are validated separately (`is_terminator`). This is a tight
/// ALLOW-LIST, so a new `Inst` variant is inadmissible until added here.
fn is_multiblock_inlinable_value(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Const { .. }
            | Inst::BinOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::Cast { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::Undef { .. }
            | Inst::InsertField { .. }
            | Inst::ExtractField { .. }
            // Proof obligations: a failed Assert is a divergence (trap), not an
            // observable side effect; Assume is a pure constraint. Both are in
            // the converter's supported set.
            | Inst::Assume { .. }
            | Inst::Assert { .. }
    )
}

/// Clone an arbitrary multi-block-inlinable instruction, running every `ValueId`
/// operand through `resolve` (callee value -> caller-arg / fresh value). Covers
/// EXACTLY the variant set `is_multiblock_inlinable_value` admits plus the
/// terminators (`Br`/`CondBr`/`Switch`/`Return`/`Unreachable`); any other
/// variant is an admission bug and returns `Err` (fail-closed).
fn remap_multiblock_inst(
    inst: &Inst,
    resolve: &impl Fn(ValueId) -> Result<ValueId, String>,
    remap_block: &impl Fn(BlockId) -> Result<BlockId, String>,
) -> Result<Inst, String> {
    let mapped = match inst {
        Inst::Const { ty, value } => Inst::Const { ty: ty.clone(), value: value.clone() },
        Inst::BinOp { op, ty, lhs, rhs } => {
            Inst::BinOp { op: *op, ty: ty.clone(), lhs: resolve(*lhs)?, rhs: resolve(*rhs)? }
        }
        Inst::Overflow { op, ty, lhs, rhs } => {
            Inst::Overflow { op: *op, ty: ty.clone(), lhs: resolve(*lhs)?, rhs: resolve(*rhs)? }
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            Inst::ICmp { op: *op, ty: ty.clone(), lhs: resolve(*lhs)?, rhs: resolve(*rhs)? }
        }
        Inst::Cast { op, src_ty, dst_ty, operand } => Inst::Cast {
            op: *op,
            src_ty: src_ty.clone(),
            dst_ty: dst_ty.clone(),
            operand: resolve(*operand)?,
        },
        Inst::Copy { ty, operand } => Inst::Copy { ty: ty.clone(), operand: resolve(*operand)? },
        Inst::Select { ty, cond, then_val, else_val } => Inst::Select {
            ty: ty.clone(),
            cond: resolve(*cond)?,
            then_val: resolve(*then_val)?,
            else_val: resolve(*else_val)?,
        },
        Inst::Undef { ty } => Inst::Undef { ty: ty.clone() },
        Inst::InsertField { ty, aggregate, field, value } => Inst::InsertField {
            ty: ty.clone(),
            aggregate: resolve(*aggregate)?,
            field: *field,
            value: resolve(*value)?,
        },
        Inst::ExtractField { ty, aggregate, field } => {
            Inst::ExtractField { ty: ty.clone(), aggregate: resolve(*aggregate)?, field: *field }
        }
        Inst::Assume { cond } => Inst::Assume { cond: resolve(*cond)? },
        Inst::Assert { cond } => Inst::Assert { cond: resolve(*cond)? },
        // --- Terminators (intra-callee targets rewritten; edge args remapped). ---
        Inst::Br { target, args } => Inst::Br {
            target: remap_block(*target)?,
            args: args.iter().map(|a| resolve(*a)).collect::<Result<_, _>>()?,
        },
        Inst::CondBr { cond, then_target, then_args, else_target, else_args } => Inst::CondBr {
            cond: resolve(*cond)?,
            then_target: remap_block(*then_target)?,
            then_args: then_args.iter().map(|a| resolve(*a)).collect::<Result<_, _>>()?,
            else_target: remap_block(*else_target)?,
            else_args: else_args.iter().map(|a| resolve(*a)).collect::<Result<_, _>>()?,
        },
        Inst::Switch { value, default, default_args, cases, exhaustive_enum_unreachable } => {
            let mut new_cases = Vec::with_capacity(cases.len());
            for c in cases {
                new_cases.push(trust_ir::inst::SwitchCase {
                    value: c.value.clone(),
                    target: remap_block(c.target)?,
                    args: c.args.iter().map(|a| resolve(*a)).collect::<Result<_, _>>()?,
                });
            }
            Inst::Switch {
                value: resolve(*value)?,
                default: remap_block(*default)?,
                default_args: default_args.iter().map(|a| resolve(*a)).collect::<Result<_, _>>()?,
                cases: new_cases,
                exhaustive_enum_unreachable: *exhaustive_enum_unreachable,
            }
        }
        Inst::Return { values } => {
            Inst::Return { values: values.iter().map(|v| resolve(*v)).collect::<Result<_, _>>()? }
        }
        Inst::Unreachable => Inst::Unreachable,
        other => {
            return Err(format!(
                "remap_multiblock_inst reached non-inlinable inst `{}` (admission bug)",
                inst_name(other)
            ));
        }
    };
    Ok(mapped)
}

/// Attempt the MULTI-BLOCK splice of ONE `Call` at position `call_pos` in
/// `caller_block`. On success returns the replacement blocks for this caller
/// block: the split caller block (pre-call instructions + a `Br` into the cloned
/// callee entry), the cloned callee blocks, and the continuation block. On
/// failure returns the admission clause that was violated (the outer loop then
/// leaves the Call in place, so the converter fail-closes — never a wrong splice).
#[allow(clippy::too_many_arguments)]
fn try_inline_call_multiblock(
    module: &Module,
    caller: &IrFunction,
    callee_id: FuncId,
    args: &[ValueId],
    call_node: &InstrNode,
    caller_block: &trust_ir::Block,
    call_pos: usize,
    next_value: &mut u32,
    next_block: &mut u32,
) -> Result<Vec<trust_ir::Block>, String> {
    // ---- LOCAL ----
    let callee = module.function_by_id(callee_id).ok_or_else(|| {
        format!("callee FuncId {} is not local to this module", callee_id.index())
    })?;

    // ---- ACYCLIC (no self-recursion); leaf check below closes transitivity ----
    if callee.id == caller.id {
        return Err("self-recursive call".to_string());
    }

    if callee.blocks.is_empty() {
        return Err(format!("callee `{}` has no blocks (body-less declaration)", callee.name));
    }

    // ---- the call must produce exactly one result (matched to the return) ----
    let [call_result] = call_node.results.as_slice() else {
        return Err(format!(
            "call has {} results; only single-result calls are inlined",
            call_node.results.len()
        ));
    };

    // ---- the callee entry block holds the formal params; arity must match ----
    let entry_block = callee.blocks.iter().find(|b| b.id == callee.entry).ok_or_else(|| {
        format!("callee `{}` entry block {} is absent", callee.name, callee.entry.index())
    })?;
    if args.len() != entry_block.params.len() {
        return Err(format!(
            "call passes {} args but callee `{}` entry has {} params",
            args.len(),
            callee.name,
            entry_block.params.len()
        ));
    }

    // ---- PURE + LEAF + ROUTABLE-RETURN: validate EVERY inst in EVERY block. ----
    // A single trailing terminator per block; no terminator mid-body; every
    // straight-line inst is multiblock-inlinable; every Return is single-value.
    for block in &callee.blocks {
        let Some((last, body)) = block.body.split_last() else {
            return Err(format!("callee `{}` block {} is empty", callee.name, block.id.index()));
        };
        if !is_terminator(&last.inst) {
            return Err(format!(
                "callee `{}` block {} does not end in a terminator",
                callee.name,
                block.id.index()
            ));
        }
        if let Inst::Return { values } = &last.inst {
            if values.len() != 1 {
                return Err(format!(
                    "callee `{}` has a {}-value Return; only single-value returns are routable",
                    callee.name,
                    values.len()
                ));
            }
        }
        for n in body {
            if is_terminator(&n.inst) {
                return Err(format!(
                    "callee `{}` block {} has a non-final terminator",
                    callee.name,
                    block.id.index()
                ));
            }
            if !is_multiblock_inlinable_value(&n.inst) {
                return Err(format!(
                    "callee `{}` body contains non-inlinable inst `{}`",
                    callee.name,
                    inst_name(&n.inst)
                ));
            }
        }
    }

    // ---- Allocate the fresh continuation block id up front. ----
    let cont_id = BlockId::new(*next_block);
    *next_block += 1;

    // ---- BlockId remap: every callee block -> a fresh BlockId. ----
    let mut block_remap: HashMap<BlockId, BlockId> = HashMap::new();
    for block in &callee.blocks {
        let fresh = BlockId::new(*next_block);
        *next_block += 1;
        block_remap.insert(block.id, fresh);
    }
    let entry_clone_id = block_remap[&callee.entry];

    // ---- ValueId remap: entry params -> call args; every other callee value
    // (non-entry block params + every instruction result) -> a FRESH id. ----
    let mut remap: HashMap<ValueId, ValueId> = HashMap::new();
    for ((param_id, _), arg) in entry_block.params.iter().zip(args) {
        remap.insert(*param_id, *arg);
    }
    for block in &callee.blocks {
        if block.id != callee.entry {
            for (param_id, _) in &block.params {
                let fresh = ValueId::new(*next_value);
                *next_value += 1;
                remap.insert(*param_id, fresh);
            }
        }
        for node in &block.body {
            for r in &node.results {
                let fresh = ValueId::new(*next_value);
                *next_value += 1;
                remap.insert(*r, fresh);
            }
        }
    }

    let resolve = |v: ValueId| -> Result<ValueId, String> {
        remap.get(&v).copied().ok_or_else(|| {
            format!(
                "callee `{}` references value {} not bound by a param or prior def",
                callee.name,
                v.index()
            )
        })
    };
    let remap_block = |b: BlockId| -> Result<BlockId, String> {
        block_remap.get(&b).copied().ok_or_else(|| {
            format!("callee `{}` branches to unknown block {}", callee.name, b.index())
        })
    };

    // ---- The continuation block's single param: the call result. Typed by the
    // callee's declared return type. ----
    let ret_ty = callee_return_ty(module, callee).ok_or_else(|| {
        format!(
            "callee `{}` has no single resolvable return type for the continuation",
            callee.name
        )
    })?;

    // ---- Clone every callee block with fresh ids; route each Return -> the
    // continuation block, passing the (remapped) return value as the cont arg. --
    let mut cloned_blocks: Vec<trust_ir::Block> = Vec::with_capacity(callee.blocks.len());
    for block in &callee.blocks {
        let mut nb = trust_ir::Block::new(remap_block(block.id)?);
        // Non-entry params keep their (fresh) ids as real block params; the
        // entry's params were substituted directly with the call args.
        if block.id != callee.entry {
            for (param_id, param_ty) in &block.params {
                nb.params.push((resolve(*param_id)?, param_ty.clone()));
            }
        }
        let Some((last, body)) = block.body.split_last() else {
            return Err(format!(
                "callee `{}` block {} is empty (revalidate)",
                callee.name,
                block.id.index()
            ));
        };
        for n in body {
            let inst = remap_multiblock_inst(&n.inst, &resolve, &remap_block)?;
            let results: Vec<ValueId> =
                n.results.iter().map(|r| resolve(*r)).collect::<Result<_, _>>()?;
            nb.body.push(InstrNode::new(inst).with_results(results));
        }
        // The terminator: a `Return(v)` becomes `Br -> cont, args=[v]`; any other
        // terminator is cloned with its targets/args remapped.
        if let Inst::Return { values } = &last.inst {
            let [v] = values.as_slice() else {
                return Err(format!(
                    "callee `{}` Return arity changed under validation (expected 1)",
                    callee.name
                ));
            };
            let ret_src = resolve(*v)?;
            nb.body.push(InstrNode::new(Inst::Br { target: cont_id, args: vec![ret_src] }));
        } else {
            let term = remap_multiblock_inst(&last.inst, &resolve, &remap_block)?;
            nb.body.push(InstrNode::new(term));
        }
        cloned_blocks.push(nb);
    }

    // ---- Split the caller block: pre-call instructions + `Br -> entry_clone`. --
    let mut split_caller = trust_ir::Block::new(caller_block.id);
    split_caller.params = caller_block.params.clone();
    for node in &caller_block.body[..call_pos] {
        split_caller.body.push(node.clone());
    }
    split_caller.body.push(InstrNode::new(Inst::Br { target: entry_clone_id, args: vec![] }));

    // ---- The continuation: its single param IS the call result; it carries the
    // POST-call instructions and the caller block's original terminator. ----
    let mut cont = trust_ir::Block::new(cont_id);
    cont.params.push((*call_result, ret_ty));
    for node in &caller_block.body[call_pos + 1..] {
        cont.body.push(node.clone());
    }

    // Assemble: split caller, cloned callee blocks, continuation.
    let mut out = Vec::with_capacity(cloned_blocks.len() + 2);
    out.push(split_caller);
    out.append(&mut cloned_blocks);
    out.push(cont);
    Ok(out)
}

/// The callee's single declared return `Ty`, looked up via the Module's
/// `func_types`. Used to type the splice's terminal `Copy`.
fn callee_return_ty(module: &Module, callee: &IrFunction) -> Option<Ty> {
    let func_ty = module.func_types.get(callee.ty.as_usize())?;
    match func_ty.returns.as_slice() {
        [ty] => Some(ty.clone()),
        _ => None,
    }
}

/// True for the value-producing, observably-pure, NON-call instruction shapes
/// that the splice can remap operand-for-operand. This is intentionally a tight
/// allow-list (NOT a deny-list): a new `Inst` variant is inadmissible until it
/// is explicitly added here, so the inliner stays fail-closed by construction.
fn is_pure_leaf_inlinable(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Const { .. }
            | Inst::BinOp { .. }
            | Inst::ICmp { .. }
            | Inst::Cast { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. }
    )
}

/// Clone a pure-leaf instruction with its `ValueId` operands run through
/// `resolve` (callee value -> caller/fresh value). Mirrors exactly the variant
/// set `is_pure_leaf_inlinable` admits; any other variant is a logic error
/// (the caller validated admissibility first) and returns `Err`.
fn remap_pure_leaf_inst(
    inst: &Inst,
    resolve: &impl Fn(ValueId) -> Result<ValueId, String>,
) -> Result<Inst, String> {
    let mapped = match inst {
        Inst::Const { ty, value } => Inst::Const { ty: ty.clone(), value: value.clone() },
        Inst::BinOp { op, ty, lhs, rhs } => {
            Inst::BinOp { op: *op, ty: ty.clone(), lhs: resolve(*lhs)?, rhs: resolve(*rhs)? }
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            Inst::ICmp { op: *op, ty: ty.clone(), lhs: resolve(*lhs)?, rhs: resolve(*rhs)? }
        }
        Inst::Cast { op, src_ty, dst_ty, operand } => Inst::Cast {
            op: *op,
            src_ty: src_ty.clone(),
            dst_ty: dst_ty.clone(),
            operand: resolve(*operand)?,
        },
        Inst::Copy { ty, operand } => Inst::Copy { ty: ty.clone(), operand: resolve(*operand)? },
        Inst::Select { ty, cond, then_val, else_val } => Inst::Select {
            ty: ty.clone(),
            cond: resolve(*cond)?,
            then_val: resolve(*then_val)?,
            else_val: resolve(*else_val)?,
        },
        other => {
            return Err(format!(
                "remap_pure_leaf_inst reached non-pure-leaf inst `{}` (admission bug)",
                inst_name(other)
            ));
        }
    };
    Ok(mapped)
}

/// The `ValueId` operands an instruction READS, for the max-value scan. Need
/// not be exhaustive in meaning, only an upper bound on referenced ids, so a
/// conservative match over every variant's value fields is used.
fn inst_value_operands(inst: &Inst) -> Vec<ValueId> {
    match inst {
        Inst::BinOp { lhs, rhs, .. }
        | Inst::Overflow { lhs, rhs, .. }
        | Inst::ICmp { lhs, rhs, .. }
        | Inst::FCmp { lhs, rhs, .. } => vec![*lhs, *rhs],
        Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } | Inst::Copy { operand, .. } => {
            vec![*operand]
        }
        Inst::Load { ptr, .. } => vec![*ptr],
        Inst::Store { ptr, value, .. } => vec![*ptr, *value],
        Inst::Alloca { count, .. } | Inst::HeapAlloc { count, .. } => {
            count.iter().copied().collect()
        }
        Inst::GEP { base, indices, .. } => {
            let mut v = vec![*base];
            v.extend(indices.iter().copied());
            v
        }
        Inst::PtrData { ptr, .. } | Inst::PtrMetadata { ptr, .. } => vec![*ptr],
        Inst::PtrFromParts { data, metadata, .. } => vec![*data, *metadata],
        Inst::AtomicLoad { ptr, .. } => vec![*ptr],
        Inst::AtomicStore { ptr, value, .. } | Inst::AtomicRMW { ptr, value, .. } => {
            vec![*ptr, *value]
        }
        Inst::CmpXchg { ptr, expected, desired, .. } => vec![*ptr, *expected, *desired],
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
            for c in cases {
                v.extend(c.args.iter().copied());
            }
            v
        }
        Inst::Call { args, .. } => args.clone(),
        Inst::CallIndirect { callee, args, .. } => {
            let mut v = vec![*callee];
            v.extend(args.iter().copied());
            v
        }
        Inst::Return { values } => values.clone(),
        Inst::ExtractField { aggregate, .. } => vec![*aggregate],
        Inst::InsertField { aggregate, value, .. } => vec![*aggregate, *value],
        Inst::ExtractElement { array, index, .. } => vec![*array, *index],
        Inst::InsertElement { array, index, value, .. } => vec![*array, *index, *value],
        Inst::Assume { cond } | Inst::Assert { cond } => vec![*cond],
        Inst::Select { cond, then_val, else_val, .. } => vec![*cond, *then_val, *else_val],
        Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => vec![*ptr],
        Inst::EndBorrow { borrow_ptr } => vec![*borrow_ptr],
        Inst::Retain { ptr } | Inst::Release { ptr } | Inst::IsUnique { ptr } => vec![*ptr],
        Inst::Dealloc { ptr, .. } => vec![*ptr],
        // Variants with no `ValueId` operands (or whose operands are not in the
        // remappable scalar core) contribute nothing to the max scan.
        _ => vec![],
    }
}

/// Split a block's body into its straight-line value instructions and its single
/// trailing terminator node. Fail-closed if there is no terminator, or if a
/// terminator appears anywhere but the final position.
fn split_terminator<'a>(
    block: &'a trust_ir::Block,
    name: &str,
) -> Result<(&'a [trust_ir::node::InstrNode], &'a Inst), ModuleLirError> {
    let Some((last, body)) = block.body.split_last() else {
        return Err(ModuleLirError::MalformedControlFlow {
            name: name.to_string(),
            detail: format!("block {} is empty", block.id.index()),
        });
    };
    if !is_terminator(&last.inst) {
        return Err(ModuleLirError::MalformedControlFlow {
            name: name.to_string(),
            detail: format!("block {} does not end in a terminator", block.id.index()),
        });
    }
    for node in body {
        if is_terminator(&node.inst) {
            return Err(ModuleLirError::MalformedControlFlow {
                name: name.to_string(),
                detail: format!("terminator in non-final position in block {}", block.id.index()),
            });
        }
    }
    Ok((body, &last.inst))
}

fn is_terminator(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::Unreachable
    )
}

// ===========================================================================
// REAL (NON-INLINED) CALL — the FIRST structural step toward cross-function
// calls in the Module -> LIR converter.
//
// The default converter path INLINES an admitted local pure leaf callee (so the
// emitted __text carries NO `Bl`). This is the OPPOSITE capability: emit a REAL
// LIR `Opcode::Call { name }` (which ISel lowers to `Bl` + an
// `ARM64_RELOC_BRANCH26` naming the callee symbol), so the call survives as a
// genuine cross-function edge. The proven-output gate / test executor then
// COMPOSES the callee at the reloc target — exactly mirroring the bundle gate's
// `verify_output::model_local_call` (parse BRANCH26 -> callee symbol -> substitute
// the callee's derived pure output into X0 + havoc caller-saved regs).
//
// A real call is ADMITTED ONLY when the callee clears the SAME single-register
// AAPCS64 scalar-pure fragment the gate composes (`derive_callee_pure`): a LOCAL
// pure function whose params + return are all single-X/W-register integer/bool
// scalars (<= 8 args), whose body is memory-pure (no store, no nested call).
// This is the exact class the gate's machine side can soundly stand-in for the
// resolved `bl`. Anything else FAILS CLOSED (the call is left for the converter
// to reject) so a real Call is never emitted where the gate could not compose it.
// ===========================================================================

/// True iff a real (non-inlined) `Opcode::Call` to `callee` can be soundly
/// emitted AND later composed by the proven-output gate — i.e. `callee` is in the
/// gate's single-register AAPCS64 scalar-pure fragment (`derive_callee_pure`):
///
///   * every parameter is a single-X/W-register integer/bool scalar (<= 8 args);
///   * the return type is a single-register integer/bool scalar;
///   * the body is MEMORY-PURE (no `Store`, no `Load`, no nested `Call`) — the
///     gate declines any callee that touches memory or calls, because its result
///     could then depend on state the composition cannot stand in for.
///
/// FAIL-CLOSED: returns `false` for anything outside this fragment, so a real
/// Call is only ever emitted for a callee the gate can compose. This is the
/// trust-ir mirror of `verify_output::derive_callee_pure`.
fn callee_is_real_call_composable(module: &Module, callee: &IrFunction) -> bool {
    let Some(func_ty) = module.func_types.get(callee.ty.as_usize()) else {
        return false;
    };
    if func_ty.is_vararg {
        return false;
    }
    // <= 8 integer/pointer args in X0..X7, all single-register scalars.
    if func_ty.params.len() > 8 {
        return false;
    }
    for p in &func_ty.params {
        if !is_single_register_scalar(p) {
            return false;
        }
    }
    // A single-register scalar return (no unit/aggregate/float/i128 register-pair).
    match func_ty.returns.as_slice() {
        [ret] if is_single_register_scalar(ret) => {}
        _ => return false,
    }
    // MEMORY-PURITY + LEAF: every instruction in every block must be a
    // value-producing pure op, a Const, or a pure-scalar terminator — NO memory
    // op (Store/Load/Alloca/GEP), NO nested Call/CallIndirect. The gate composes
    // only callees whose result is a pure function of the argument registers.
    for block in &callee.blocks {
        for node in &block.body {
            if !is_real_call_pure_body_inst(&node.inst) {
                return false;
            }
        }
    }
    true
}

/// True for the fixed-width scalar integer / bool types that occupy a SINGLE
/// X/W register in the AAPCS64 integer fragment. `i128`/`u128` are register
/// PAIRS (outside the fragment); floats/aggregates are excluded. Matches the
/// gate's `derive_callee_pure` per-argument acceptance.
fn is_single_register_scalar(ty: &Ty) -> bool {
    // Trust (v25 B1): Isize/Usize are 64-bit (X-register) and Char is a 32-bit
    // unsigned (W-register) carrier on the pinned 64-bit target — each occupies
    // a SINGLE integer register, same as I64/U64 and U32 respectively.
    matches!(
        ty,
        Ty::I8
            | Ty::U8
            | Ty::I16
            | Ty::U16
            | Ty::I32
            | Ty::U32
            | Ty::I64
            | Ty::U64
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::Bool
    )
}

/// True for the pure, memory-free, call-free instruction shapes a real-call
/// composable callee body may contain: the pure-leaf value ops, plus the
/// pure-scalar control-flow terminators (`Br`/`CondBr`/`Switch`/`Return`) the
/// gate's DAG-CFG interpreter models. Explicitly EXCLUDES every memory op
/// (`Store`/`Load`/`Alloca`/`GEP`), `Call`/`CallIndirect`, and aggregate/undef
/// shapes — a deny-by-default allow-list so a new `Inst` is inadmissible until
/// added here.
fn is_real_call_pure_body_inst(inst: &Inst) -> bool {
    is_pure_leaf_inlinable(inst)
        || matches!(
            inst,
            Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. } | Inst::Return { .. }
        )
}

/// Emit the LIR address of a field at `offset` within the aggregate stack
/// `slot`: `StackAddr { slot }` (the slot base) for offset 0, else
/// `StackAddr { slot }` then `ArrayGep { elem_ty: I8 }` with a byte-offset index
/// constant, which computes `base + offset * sizeof(I8) = base + offset`. Both
/// `StackAddr` and `ArrayGep` are in the verified ISel slice (the existing scalar
/// memory arm already proves them), so the field address is an already-proven
/// addressing primitive — never a fabricated offset. Returns the address Value.
fn emit_field_addr(
    slot: u32,
    offset: u32,
    value_types: &mut HashMap<Value, LirType>,
    instructions: &mut Vec<Instruction>,
    next_value: &mut u32,
) -> Value {
    let base = Value(*next_value);
    *next_value += 1;
    value_types.insert(base, LirType::I64);
    instructions.push(Instruction {
        opcode: Opcode::StackAddr { slot },
        args: vec![],
        results: vec![base],
    });
    if offset == 0 {
        return base;
    }
    // idx = offset (as I64); addr = base + idx * sizeof(I8) = base + offset.
    let idx = Value(*next_value);
    *next_value += 1;
    value_types.insert(idx, LirType::I64);
    instructions.push(Instruction {
        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(offset) },
        args: vec![],
        results: vec![idx],
    });
    let addr = Value(*next_value);
    *next_value += 1;
    value_types.insert(addr, LirType::I64);
    instructions.push(Instruction {
        opcode: Opcode::ArrayGep { elem_ty: LirType::I8 },
        args: vec![base, idx],
        results: vec![addr],
    });
    addr
}

/// Lower an aggregate-in-memory node (PASS 1.7). Returns `Ok(true)` when the node
/// was part of the aggregate slice and fully handled here, `Ok(false)` when it is
/// NOT an aggregate node (the caller falls through to the scalar/CFG machinery).
///
/// Decomposes the whole-aggregate round trip into per-field scalar LIR at the
/// C-style field offsets (`AggMemDecompose.agg_alloca_layout`, matching the
/// trust-ir interpreter's `aggregate_layout`):
///   * `Alloca(Tuple)`   -> one sized stack slot; record its layout/field offsets.
///   * `Const::Aggregate`-> materialize each field constant as an `Iconst`; record
///                          the per-field LIR Values (NO whole-aggregate LIR).
///   * `Undef(Tuple)`    -> register an empty field map (fields filled by Insert).
///   * `InsertField`     -> set field k's LIR Value (clone source map); NO LIR.
///   * `Store(Tuple)`    -> per-field Str at each field offset.
///   * `Load(Tuple)`     -> per-field Ldr at each field offset; record the loaded
///                          field Values as the result aggregate's fields.
///   * `ExtractField`    -> `Copy` of the resolved field's LIR Value.
#[allow(clippy::too_many_arguments)]
fn lower_aggregate_inst(
    module: &Module,
    node: &trust_ir::node::InstrNode,
    vmap: &ValueMap,
    value_types: &mut HashMap<Value, LirType>,
    mem: &mut MemoryCtx,
    instructions: &mut Vec<Instruction>,
    next_value: &mut u32,
    agg_mem: &AggMemDecompose,
    agg_field_values: &mut HashMap<ValueId, Vec<Value>>,
    name: &str,
) -> Result<bool, ModuleLirError> {
    let result0 = node.results.first().copied();

    match &node.inst {
        // ---- Aggregate Alloca (Tuple or Struct) -> one sized stack slot. ----
        Inst::Alloca { ty: Ty::Tuple(_) | Ty::Struct(_), .. } => {
            let Some(result) = result0 else { return Ok(false) };
            let Some(layout) = agg_mem.agg_alloca_layout.get(&result) else {
                // An aggregate Alloca the analysis did NOT admit — fall through so
                // the scalar memory arm fails closed on it (never fabricate).
                return Ok(false);
            };
            let slot = mem.alloc_sized_slot(layout.size, layout.align);
            // The Alloca's SSA result IS the slot's base address. Record it as an
            // aggregate slot so a Store/Load resolves the slot + field offsets.
            let ptr = vmap.resolve(result, name)?;
            value_types.insert(ptr, LirType::I64);
            mem.slot_of.insert(ptr, slot);
            instructions.push(Instruction {
                opcode: Opcode::StackAddr { slot },
                args: vec![],
                results: vec![ptr],
            });
            Ok(true)
        }
        // ---- Const aggregate seed (Tuple or Struct) -> field constants (NO LIR). --
        Inst::Const { ty: ty @ (Ty::Tuple(_) | Ty::Struct(_)), value: Constant::Aggregate(_) } => {
            let Some(result) = result0 else { return Ok(false) };
            let Some(consts) = agg_mem.agg_const_seeds.get(&result) else {
                return Ok(false);
            };
            // Field LIR types come from THIS node's own aggregate type (struct
            // fields resolved via the module), so a function with two
            // differently-shaped aggregate slots materializes each const's fields
            // at its own widths.
            let field_tys = aggregate_field_types(ty, module, name)?;
            if consts.len() != field_tys.len() {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: "Const aggregate value/type field-count mismatch".to_string(),
                });
            }
            let mut field_vals = Vec::with_capacity(consts.len());
            for (c, fty) in consts.iter().zip(&field_tys) {
                let lir_ty = map_scalar_int_ty(fty, "Const aggregate field")?;
                let imm = match c {
                    Constant::Int(v) => i128_to_i64(*v, name)?,
                    Constant::Bool(b) => i64::from(*b),
                    _ => {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: "Const aggregate field is not an integer/bool constant"
                                .to_string(),
                        });
                    }
                };
                let v = Value(*next_value);
                *next_value += 1;
                value_types.insert(v, lir_ty.clone());
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: lir_ty.clone(), imm },
                    args: vec![],
                    results: vec![v],
                });
                field_vals.push(v);
            }
            agg_field_values.insert(result, field_vals);
            Ok(true)
        }
        // ---- Undef(Tuple|Struct) seed -> empty field map (filled by Insert). ----
        Inst::Undef { ty: ty @ (Ty::Tuple(_) | Ty::Struct(_)) }
            if result0.is_some_and(|r| agg_mem.agg_undef_seeds.contains(&r)) =>
        {
            let result = result0.expect("guarded");
            // The field map starts "unset" (sentinel `Value(u32::MAX)`); every
            // entry MUST be overwritten by an `InsertField` before any
            // Store/Load/Extract reads it (PASS 1.7 proved this — it rejects a
            // read of an unset field, and the Store arm re-checks every field is
            // defined). The sentinel is never materialized into LIR, so the
            // aggregate Undef seed itself is dead, exactly like the scalar seed.
            // Arity comes from THIS node's own aggregate type (struct fields
            // resolved via the module).
            let n = aggregate_field_types(ty, module, name)?.len();
            agg_field_values.insert(result, vec![Value(u32::MAX); n]);
            Ok(true)
        }
        // ---- InsertField builds a tracked aggregate -> set one field (NO LIR). --
        Inst::InsertField { aggregate, field, value, .. }
            if result0.is_some_and(|r| agg_mem.agg_insert_results.contains(&r)) =>
        {
            let result = result0.expect("guarded");
            let src = agg_field_values.get(aggregate).cloned().ok_or_else(|| {
                ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "InsertField builds on value {} with no tracked field map",
                        aggregate.index()
                    ),
                }
            })?;
            let idx = *field as usize;
            if idx >= src.len() {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!("InsertField field {idx} out of range"),
                });
            }
            let val_v = vmap.resolve(*value, name)?;
            let mut new_fields = src;
            new_fields[idx] = val_v;
            agg_field_values.insert(result, new_fields);
            Ok(true)
        }
        // ---- Whole-aggregate Store -> per-field Str at field offsets. ----
        Inst::Store { ty: Ty::Tuple(_) | Ty::Struct(_), ptr, value, .. }
            if agg_mem.agg_store_values.contains(value) =>
        {
            let layout = agg_mem.agg_alloca_layout.get(ptr).ok_or_else(|| {
                ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: format!("aggregate Store pointer {} has no slot layout", ptr.index()),
                }
            })?;
            let ptr_v = vmap.resolve(*ptr, name)?;
            let slot =
                *mem.slot_of.get(&ptr_v).ok_or_else(|| ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: format!("aggregate Store slot for ptr {} not allocated", ptr.index()),
                })?;
            let field_vals = agg_field_values.get(value).cloned().ok_or_else(|| {
                ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "aggregate Store value {} has no tracked fields",
                        value.index()
                    ),
                }
            })?;
            // Defensive: every field must be a real (defined) Value.
            for (i, v) in field_vals.iter().enumerate() {
                if *v == Value(u32::MAX) {
                    return Err(ModuleLirError::UnsupportedAggregate {
                        name: name.to_string(),
                        detail: format!("aggregate Store value field {i} is undefined"),
                    });
                }
            }
            let offsets = layout.field_offsets.clone();
            // Arity must match the slot layout (the analysis proved this; a
            // `zip` mismatch would silently drop a field's Str). Fail closed.
            if field_vals.len() != offsets.len() {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "aggregate Store has {} field values but slot layout has {} offsets",
                        field_vals.len(),
                        offsets.len()
                    ),
                });
            }
            for (val_v, (offset, lir_ty)) in field_vals.iter().zip(&offsets) {
                let addr = emit_field_addr(slot, *offset, value_types, instructions, next_value);
                instructions.push(Instruction {
                    opcode: Opcode::Store { ty: lir_ty.clone(), align: None },
                    args: vec![*val_v, addr],
                    results: vec![],
                });
            }
            Ok(true)
        }
        // ---- Whole-aggregate Load -> per-field Ldr at field offsets. ----
        Inst::Load { ty: Ty::Tuple(_) | Ty::Struct(_), ptr, .. }
            if result0.is_some_and(|r| agg_mem.agg_load_results.contains(&r)) =>
        {
            let result = result0.expect("guarded");
            let layout = agg_mem.agg_alloca_layout.get(ptr).ok_or_else(|| {
                ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: format!("aggregate Load pointer {} has no slot layout", ptr.index()),
                }
            })?;
            let ptr_v = vmap.resolve(*ptr, name)?;
            let slot =
                *mem.slot_of.get(&ptr_v).ok_or_else(|| ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: format!("aggregate Load slot for ptr {} not allocated", ptr.index()),
                })?;
            let offsets = layout.field_offsets.clone();
            let mut loaded = Vec::with_capacity(offsets.len());
            for (offset, lir_ty) in &offsets {
                let addr = emit_field_addr(slot, *offset, value_types, instructions, next_value);
                let dst = Value(*next_value);
                *next_value += 1;
                value_types.insert(dst, lir_ty.clone());
                instructions.push(Instruction {
                    opcode: Opcode::Load { ty: lir_ty.clone(), align: None },
                    args: vec![addr],
                    results: vec![dst],
                });
                loaded.push(dst);
            }
            agg_field_values.insert(result, loaded);
            Ok(true)
        }
        // ---- ExtractField on a tracked aggregate -> Copy of the field Value. ----
        Inst::ExtractField { aggregate, field, .. }
            if result0.is_some_and(|r| agg_mem.agg_extract_field.contains_key(&r)) =>
        {
            let result = result0.expect("guarded");
            let src_fields = agg_field_values.get(aggregate).ok_or_else(|| {
                ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "ExtractField reads value {} with no tracked field map",
                        aggregate.index()
                    ),
                }
            })?;
            let idx = *field as usize;
            let src = *src_fields.get(idx).ok_or_else(|| ModuleLirError::UnsupportedAggregate {
                name: name.to_string(),
                detail: format!("ExtractField field {idx} out of range"),
            })?;
            if src == Value(u32::MAX) {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!("ExtractField reads undefined field {idx}"),
                });
            }
            let lir_ty = value_types.get(&src).cloned().ok_or_else(|| {
                ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!("ExtractField field {idx} source has no LIR type"),
                }
            })?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, lir_ty);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![src],
                results: vec![dst],
            });
            Ok(true)
        }
        // Not an aggregate-slice node — fall through to the scalar machinery.
        _ => Ok(false),
    }
}

/// Lower one straight-line (non-terminator) value instruction into LIR.
#[allow(clippy::too_many_arguments)]
fn lower_value_inst(
    module: &Module,
    node: &trust_ir::node::InstrNode,
    vmap: &ValueMap,
    value_types: &mut HashMap<Value, LirType>,
    mem: &mut MemoryCtx,
    global_addr_syms: &mut HashMap<Value, String>,
    instructions: &mut Vec<Instruction>,
    next_value: &mut u32,
    admitted_undef_seeds: &std::collections::HashSet<ValueId>,
    tuple_decompose: &TupleDecompose,
    agg_mem: &AggMemDecompose,
    agg_field_values: &mut HashMap<ValueId, Vec<Value>>,
    real_calls: bool,
    name: &str,
) -> Result<(), ModuleLirError> {
    // ---- Aggregate-in-memory decomposition (PASS 1.7). When the function has an
    // aggregate slot, handle the aggregate build/store/load/extract nodes here
    // FIRST (they decompose into per-field scalar LIR; see
    // `lower_aggregate_inst`). A node not part of the aggregate slice falls
    // through to the scalar/CFG/checked-tuple machinery unchanged.
    if !agg_mem.is_empty() {
        if lower_aggregate_inst(
            module,
            node,
            vmap,
            value_types,
            mem,
            instructions,
            next_value,
            agg_mem,
            agg_field_values,
            name,
        )? {
            return Ok(());
        }
    }

    // ---- Decomposed checked-arith tuple build (NO LIR; folded into SSA). ----
    //
    // PASS 1.6 (`analyze_checked_arith_tuples`) PROVED these tuple-build nodes
    // are part of a decomposable `(value, overflow)` pair carried entirely in
    // scalar SSA Values. They materialize NO tuple in memory and emit NO LIR:
    //   * the `Tuple`-typed `Undef` SEED — a dead placeholder, fully overwritten
    //     by its `InsertField`s before any `ExtractField` reads a field;
    //   * each `InsertField` — its effect (field k := value k) is recorded in the
    //     analysis's field map, not lowered.
    // Reached ONLY for the proven-decomposable shapes; any other tuple use
    // fail-closed in PASS 1.6 already.
    if let [result] = node.results.as_slice() {
        if tuple_decompose.admitted_tuple_seeds.contains(result)
            || tuple_decompose.insert_results.contains(result)
        {
            return Ok(());
        }
    }

    match &node.inst {
        // ---- ExtractField on a decomposed checked-arith tuple -> Copy. ----
        //
        // PASS 1.6 resolved this read to the scalar field `ValueId` the tuple
        // carries at that index (the `Inst::Overflow` value/flag result). We emit
        // a `Copy` of that field's LIR Value so the ExtractField result is a
        // defined scalar SSA value — exactly as if the tuple had been decomposed.
        // The Value's LIR type is the field's type (the resolved source's type),
        // which already lives in `value_types` from the `Inst::Overflow` lowering.
        Inst::ExtractField { .. }
            if node
                .results
                .first()
                .is_some_and(|r| tuple_decompose.extract_field_src.contains_key(r)) =>
        {
            let result = expect_single_result(node, name)?;
            let src_id = tuple_decompose.extract_field_src[&result];
            let src = vmap.resolve(src_id, name)?;
            let dst = vmap.resolve(result, name)?;
            // The field carrier's LIR type is the source Value's type. The
            // `Inst::Overflow` lowering recorded it (value -> int width, flag ->
            // B1); a field whose source type is unknown is a bug in the analysis
            // (it only resolves to an `Inst::Overflow` result), so fail closed.
            let lir_ty = value_types.get(&src).cloned().ok_or_else(|| {
                ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "ExtractField source value {} has no resolved LIR type",
                        src_id.index()
                    ),
                }
            })?;
            value_types.insert(dst, lir_ty);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![src],
                results: vec![dst],
            });
        }
        // ---- Dead cross-block memory-merge seed (`Inst::Undef` -> slot). ----
        //
        // Reached ONLY for an `Undef` the PASS-1.5 analysis PROVED to be a dead
        // memory-merge seed (`analyze_dead_undef_seeds`): a scalar `Undef`
        // consumed by exactly one `Store` into a local Alloca whose every `Load`
        // is must-overwritten by a later non-`Undef` `Store`. Such a seed's
        // poison is never observed, so materializing a DEFINED, deterministic
        // `Iconst 0` is a sound refinement of the ratified poison semantics
        // (poison refines to any concrete value) AND the resulting Store is dead
        // (overwritten before any Load). We NEVER reach here for an `Undef` that
        // could be read while poison — that fails closed below.
        Inst::Undef { ty } => {
            let result = expect_single_result(node, name)?;
            if !admitted_undef_seeds.contains(&result) {
                // Not a proven-dead seed: refuse rather than fabricate a value.
                return Err(ModuleLirError::UnsupportedUndef {
                    name: name.to_string(),
                    detail: format!(
                        "value {} was not proven to be a dead memory-merge seed",
                        result.index()
                    ),
                });
            }
            // A scalar integer carrier only (the analysis already required this,
            // but re-validate so the materialized constant has a real LIR width).
            let lir_ty = map_scalar_int_ty(ty, "Undef seed")?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, lir_ty.clone());
            // Materialize the proven-dead seed as a defined 0. Its only consumer
            // is the seed `Store`, which is overwritten on every path before the
            // join `Load`, so this constant can never be observed.
            instructions.push(Instruction {
                opcode: Opcode::Iconst { ty: lir_ty, imm: 0 },
                args: vec![],
                results: vec![dst],
            });
        }
        Inst::Const { ty, value } => {
            let result = expect_single_result(node, name)?;
            let lir_ty = map_scalar_int_ty(ty, "Const")?;
            let imm = match value {
                Constant::Int(v) => i128_to_i64(*v, name)?,
                Constant::Bool(b) => i64::from(*b),
                _ => return Err(ModuleLirError::UnsupportedConstant { name: name.to_string() }),
            };
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, lir_ty.clone());
            instructions.push(Instruction {
                opcode: Opcode::Iconst { ty: lir_ty, imm },
                args: vec![],
                results: vec![dst],
            });
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            let result = expect_single_result(node, name)?;
            let lir_ty = map_scalar_int_ty(ty, "BinOp")?;
            let opcode = map_int_binop(*op, ty, name)?;
            let a = vmap.resolve(*lhs, name)?;
            let b = vmap.resolve(*rhs, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, lir_ty);
            instructions.push(Instruction { opcode, args: vec![a, b], results: vec![dst] });
        }
        // ---- Integer unary ops (`!a` bitwise complement, `-a` negation). ----
        //
        // `Inst::UnOp { op, ty, operand }` is the producer's bare single-result
        // unary node (`Rvalue::UnaryOp` -> `Inst::UnOp`; see
        // `trust-ir-bridge::lower`). We map the scalar integer forms:
        //   * `Not -> Bnot` (bitwise complement `~x`; ISel -> MVN),
        //   * `Neg -> Ineg` (wrapping two's-complement `0 - x`; ISel -> NEG).
        // `map_int_unop` fail-closes on i128 (register-pair), `CtPop` (unproven
        // here), and all float unary ops. The Rust `-a` negation-overflow guard,
        // when present, is a SEPARATE `Const`/`ICmp`/`Assert`/`Br` node group that
        // the existing machinery lowers unchanged; this arm emits only the bare
        // negate/complement.
        Inst::UnOp { op, ty, operand } => {
            let result = expect_single_result(node, name)?;
            let lir_ty = map_scalar_int_ty(ty, "UnOp")?;
            let opcode = map_int_unop(*op, ty, name)?;
            let a = vmap.resolve(*operand, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, lir_ty);
            instructions.push(Instruction { opcode, args: vec![a], results: vec![dst] });
        }
        // ---- Integer-to-integer cast (`a as T`). ----
        //
        // `Inst::Cast { op, src_ty, dst_ty, operand }` is the producer's bare
        // single-result cast node (`Rvalue::Cast` -> `Inst::Cast`; see
        // `trust-ir-bridge::lower`). For an integer `a as T`, the producer picks
        // the `CastOp` from the widths + source signedness:
        //   * narrowing        -> `Trunc`   (keep low bits),
        //   * signed widen      -> `SExt`    (sign-extend),
        //   * unsigned widen    -> `ZExt`    (zero-extend),
        //   * same-width relabel-> `Bitcast` (e.g. `i32 as u32` — identical bits).
        // `map_int_cast` maps these to the pinned LIR cast opcodes the mul-widening
        // slice already proves over (`Trunc`/`Sextend`/`Uextend`), and to a `Copy`
        // for the same-width `Bitcast` (LIR int types are width-only, so a
        // same-width int reinterpret is the identity on the bit pattern). It
        // fail-closes on i128 widths, ALL float casts, pointer casts, and
        // Transmute/ReifyFnPointer. The Rust `as` int-to-int casts are TOTAL (never
        // trap), so this arm emits ONLY the single cast op — no guard. The
        // narrowing cast's `NoOverflow` proof annotation (see the dumped Module) is
        // an informational value-range marker the LIR mapping does not consume; the
        // truncate's WRAP semantics (`value & mask`) are what the source `as`
        // computes, so no obligation is dropped here.
        Inst::Cast { op, src_ty, dst_ty, operand } => {
            let result = expect_single_result(node, name)?;
            let lir_dst = map_scalar_int_ty(dst_ty, "Cast dest")?;
            let opcode = map_int_cast(*op, src_ty, dst_ty, name)?;
            let a = vmap.resolve(*operand, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, lir_dst);
            let opcode = opcode.unwrap_or(Opcode::Copy);
            instructions.push(Instruction { opcode, args: vec![a], results: vec![dst] });
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            // The COMPARED operands are `ty`-typed integers; the result is a
            // boolean carried in a byte slot.
            let result = expect_single_result(node, name)?;
            let _ = map_scalar_int_ty(ty, "ICmp operand")?;
            let cond = map_icmp(*op);
            let a = vmap.resolve(*lhs, name)?;
            let b = vmap.resolve(*rhs, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, LirType::I8);
            instructions.push(Instruction {
                opcode: Opcode::Icmp { cond },
                args: vec![a, b],
                results: vec![dst],
            });
        }
        // ---- Checked-overflow arithmetic (`a + b` with overflow checks). ----
        //
        // `Inst::Overflow { op, ty, lhs, rhs }` is the MIR-faithful checked-add
        // shape: it binds TWO SSA results — `[value, overflowed]` — and is
        // followed by a no-overflow `Assert` (the producer emits exactly this
        // for `a + b` when overflow checks are on; see trust-thir-lower). It is
        // NOT a materialized tuple in memory: the two results are plain SSA
        // values, so there is no `ExtractField` to lower — we bind the two LIR
        // result Values directly. The LIR `Checked{S,U}{add,sub,mul}` opcodes
        // produce the SAME `[value, overflow_b1]` pair (issue #474), so the
        // mapping is 1:1.
        Inst::Overflow { op, ty, lhs, rhs } => {
            let [value_res, overflow_res] = node.results.as_slice() else {
                return Err(ModuleLirError::UnsupportedOverflow {
                    name: name.to_string(),
                    detail: format!(
                        "Overflow must bind exactly [value, overflowed]; got {} result(s)",
                        node.results.len()
                    ),
                });
            };
            let value_lir_ty = map_scalar_int_ty(ty, "Overflow value")?;
            let a = vmap.resolve(*lhs, name)?;
            let b = vmap.resolve(*rhs, name)?;
            let value_dst = vmap.resolve(*value_res, name)?;
            let overflow_dst = vmap.resolve(*overflow_res, name)?;

            // ---- i32/u32 CHECKED MULTIPLY via exact i64 widening. ----
            //
            // `CheckedSmul`/`CheckedUmul` lower only at I64 in the pinned ISel
            // (SMULH/UMULH are 64-bit). Rather than change the pinned ISel, we
            // widen the narrow mul into a plain i64 `Imul` whose result is EXACT
            // (a 32-bit product never exceeds 2^63), then detect overflow as an
            // i32/u32-RANGE check on that exact 64-bit product:
            //
            //   signed   (i32): a64 = sext a; b64 = sext b; p = a64 * b64
            //                   value    = trunc_i32(p)
            //                   overflow = (p < i32::MIN) OR (p > i32::MAX)
            //   unsigned (u32): a64 = zext a; b64 = zext b; p = a64 * b64
            //                   value    = trunc_i32(p)            (low 32 bits)
            //                   overflow = (p > u32::MAX)          (unsigned cmp)
            //
            // SOUNDNESS: for signed i32, |a*b| <= (2^31)^2 = 2^62 < 2^63, so the
            // 64-bit two's-complement product is the exact mathematical product;
            // i32 overflow ⟺ that product falls outside [i32::MIN, i32::MAX], and
            // the low 32 bits are the wrapping value. For u32, a*b <= (2^32-1)^2 <
            // 2^64 and both operands are non-negative after zero-extension, so the
            // 64-bit product is exact and non-negative; u32 overflow ⟺ product >
            // u32::MAX, value = low 32 bits. A wrong bound/compare-direction here
            // would miscompile, so this is gated by the proven-output test.
            if matches!(op, OverflowOp::MulOverflow) && matches!(value_lir_ty, LirType::I32) {
                let signed = ty.is_signed();
                // Fresh I64 temps for the widened operands and the exact product.
                let a64 = Value(*next_value);
                *next_value += 1;
                let b64 = Value(*next_value);
                *next_value += 1;
                let prod = Value(*next_value);
                *next_value += 1;
                value_types.insert(a64, LirType::I64);
                value_types.insert(b64, LirType::I64);
                value_types.insert(prod, LirType::I64);

                let ext_opcode = |from: LirType, to: LirType| {
                    if signed {
                        Opcode::Sextend { from_ty: from, to_ty: to }
                    } else {
                        Opcode::Uextend { from_ty: from, to_ty: to }
                    }
                };
                // a64 = {s,z}ext_i32->i64 a ; b64 = {s,z}ext_i32->i64 b
                instructions.push(Instruction {
                    opcode: ext_opcode(LirType::I32, LirType::I64),
                    args: vec![a],
                    results: vec![a64],
                });
                instructions.push(Instruction {
                    opcode: ext_opcode(LirType::I32, LirType::I64),
                    args: vec![b],
                    results: vec![b64],
                });
                // prod = a64 * b64   (exact 64-bit product)
                instructions.push(Instruction {
                    opcode: Opcode::Imul,
                    args: vec![a64, b64],
                    results: vec![prod],
                });
                // value = trunc_i64->i32(prod)   (the wrapping low 32 bits)
                value_types.insert(value_dst, value_lir_ty);
                instructions.push(Instruction {
                    opcode: Opcode::Trunc { to_ty: LirType::I32 },
                    args: vec![prod],
                    results: vec![value_dst],
                });

                // overflow flag (B1).
                if signed {
                    // overflow = (prod < i32::MIN) OR (prod > i32::MAX)
                    let lo_bound = Value(*next_value);
                    *next_value += 1;
                    let hi_bound = Value(*next_value);
                    *next_value += 1;
                    let lt_lo = Value(*next_value);
                    *next_value += 1;
                    let gt_hi = Value(*next_value);
                    *next_value += 1;
                    value_types.insert(lo_bound, LirType::I64);
                    value_types.insert(hi_bound, LirType::I64);
                    value_types.insert(lt_lo, LirType::B1);
                    value_types.insert(gt_hi, LirType::B1);
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i32::MIN as i64 },
                        args: vec![],
                        results: vec![lo_bound],
                    });
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i32::MAX as i64 },
                        args: vec![],
                        results: vec![hi_bound],
                    });
                    instructions.push(Instruction {
                        opcode: Opcode::Icmp { cond: IntCC::SignedLessThan },
                        args: vec![prod, lo_bound],
                        results: vec![lt_lo],
                    });
                    instructions.push(Instruction {
                        opcode: Opcode::Icmp { cond: IntCC::SignedGreaterThan },
                        args: vec![prod, hi_bound],
                        results: vec![gt_hi],
                    });
                    value_types.insert(overflow_dst, LirType::B1);
                    instructions.push(Instruction {
                        opcode: Opcode::Bor,
                        args: vec![lt_lo, gt_hi],
                        results: vec![overflow_dst],
                    });
                } else {
                    // overflow = (prod > u32::MAX)   (unsigned compare; prod >= 0)
                    let hi_bound = Value(*next_value);
                    *next_value += 1;
                    value_types.insert(hi_bound, LirType::I64);
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: u32::MAX as i64 },
                        args: vec![],
                        results: vec![hi_bound],
                    });
                    value_types.insert(overflow_dst, LirType::B1);
                    instructions.push(Instruction {
                        opcode: Opcode::Icmp { cond: IntCC::UnsignedGreaterThan },
                        args: vec![prod, hi_bound],
                        results: vec![overflow_dst],
                    });
                }
                return Ok(());
            }

            // ---- Add/Sub (any supported width) + 64-bit Mul: first-class op. ----
            let opcode = map_overflow_op(*op, ty, name)?;
            // The value result is the wrapping arithmetic result (operand width);
            // the overflow result is a 1-bit boolean (B1 carrier).
            value_types.insert(value_dst, value_lir_ty);
            value_types.insert(overflow_dst, LirType::B1);
            instructions.push(Instruction {
                opcode,
                args: vec![a, b],
                results: vec![value_dst, overflow_dst],
            });
        }
        // ---- Conditional select (`cond ? then : else`). ----
        //
        // The overflow-assert idiom negates the overflow bit through a `Select`
        // (`overflowed ? false : true` == `!overflowed`) because the trust-ir
        // interpreter accepts a `bool` operand only via `as_bool` (Select /
        // Assert), not through `ICmp`/`UnOp::Not`. The LIR `Select { cond }`
        // takes args `[cc_val, true_val, false_val]` and lowers to
        // `CMP cc_val,#0; CSEL true_val, false_val, <cond>`: with `NotEqual`
        // that is `cc_val != 0 ? true_val : false_val`, matching the trust-ir
        // `Select` semantics (cond true -> then_val) exactly.
        Inst::Select { ty, cond, then_val, else_val } => {
            let result = expect_single_result(node, name)?;
            let lir_ty = map_scalar_int_ty(ty, "Select")?;
            let cond_v = vmap.resolve(*cond, name)?;
            let then_v = vmap.resolve(*then_val, name)?;
            let else_v = vmap.resolve(*else_val, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, lir_ty);
            instructions.push(Instruction {
                opcode: Opcode::Select { cond: IntCC::NotEqual },
                args: vec![cond_v, then_v, else_v],
                results: vec![dst],
            });
        }
        // A scalar value copy: `dst = src`. Maps 1:1 to the LIR `Copy` opcode.
        // The inlining pre-pass emits one of these to route an inlined callee's
        // `Return` value into the call's destination value; it is also the
        // honest lowering of a stand-alone `trust_ir::Copy` over a scalar.
        Inst::Copy { ty, operand } => {
            let result = expect_single_result(node, name)?;
            let lir_ty = map_scalar_int_ty(ty, "Copy")?;
            let src = vmap.resolve(*operand, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, lir_ty);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![src],
                results: vec![dst],
            });
        }
        // ---- Memory: stack-slot Alloca / Load / Store / single-index GEP. ----
        //
        // The pinned trust-ir interpreter models only SCALAR memory (no
        // aggregate `byte_size`), so every pointee here is a fixed-width
        // integer and every slot holds exactly one element. A pointer value is
        // ALWAYS an alloca-rooted LIR `Value` (or an `ArrayGep` off one); an
        // opaque incoming pointer fails closed (`NonLocalPointer`).
        Inst::Alloca { ty, count, align: _ } => {
            // Counted (array / VLA) allocas are out of the scalar-slot slice:
            // the interpreter would need an aggregate byte_size the pinned
            // commit lacks.
            if count.is_some() {
                return Err(ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail:
                        "counted (array/VLA) Alloca; only single-element scalar slots are mapped"
                            .to_string(),
                });
            }
            let result = expect_single_result(node, name)?;
            let lir_ty = map_scalar_mem_ty(ty, name, "Alloca pointee")?;
            let slot = mem.alloc_slot(&lir_ty);
            // The Alloca's SSA result IS the slot address; materialize it as a
            // StackAddr whose result Value is the alloca's pre-allocated Value.
            let ptr = vmap.resolve(result, name)?;
            // A pointer is carried in an I64 GPR at the LIR level (the LIR Type
            // enum has no Ptr variant — pointers are I64).
            value_types.insert(ptr, LirType::I64);
            mem.slot_of.insert(ptr, slot);
            mem.pointee_ty.insert(ptr, lir_ty);
            instructions.push(Instruction {
                opcode: Opcode::StackAddr { slot },
                args: vec![],
                results: vec![ptr],
            });
        }
        Inst::Load { ty, ptr, volatile, align: _ } => {
            if *volatile {
                return Err(ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: "volatile Load is out of the scalar-memory slice".to_string(),
                });
            }
            let result = expect_single_result(node, name)?;
            let lir_ty = map_scalar_mem_ty(ty, name, "Load")?;
            let ptr_v = resolve_local_pointer(*ptr, vmap, mem, name)?;
            // The load width must match the slot's element type.
            if let Some(slot_ty) = mem.pointee_ty.get(&ptr_v) {
                if *slot_ty != lir_ty {
                    return Err(ModuleLirError::UnsupportedMemory {
                        name: name.to_string(),
                        detail: format!(
                            "Load width {lir_ty:?} does not match slot element {slot_ty:?}"
                        ),
                    });
                }
            }
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, lir_ty.clone());
            instructions.push(Instruction {
                opcode: Opcode::Load { ty: lir_ty, align: None },
                args: vec![ptr_v],
                results: vec![dst],
            });
        }
        Inst::Store { ty, ptr, value, volatile, align: _ } => {
            if *volatile {
                return Err(ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: "volatile Store is out of the scalar-memory slice".to_string(),
                });
            }
            // A Store produces no value; reject any stray result.
            if !node.results.is_empty() {
                return Err(ModuleLirError::UnsupportedInst {
                    name: name.to_string(),
                    inst: inst_name(&node.inst),
                });
            }
            let lir_ty = map_scalar_mem_ty(ty, name, "Store")?;
            let ptr_v = resolve_local_pointer(*ptr, vmap, mem, name)?;
            if let Some(slot_ty) = mem.pointee_ty.get(&ptr_v) {
                if *slot_ty != lir_ty {
                    return Err(ModuleLirError::UnsupportedMemory {
                        name: name.to_string(),
                        detail: format!(
                            "Store width {lir_ty:?} does not match slot element {slot_ty:?}"
                        ),
                    });
                }
            }
            let val_v = vmap.resolve(*value, name)?;
            instructions.push(Instruction {
                opcode: Opcode::Store { ty: lir_ty, align: None },
                args: vec![val_v, ptr_v],
                results: vec![],
            });
        }
        Inst::GEP { pointee_ty, base, indices, inbounds: _ } => {
            // trust-ir GEP is flat single-scale array indexing:
            //   base + (Σ indices) * size_of(pointee_ty).
            // LIR ArrayGep is base + index * size_of(elem_ty) (a single index).
            // We map the clean single-index scalar-pointee case; multi-index,
            // zero-index, or non-scalar-pointee GEP fails closed.
            let result = expect_single_result(node, name)?;
            let elem_ty = map_scalar_mem_ty(pointee_ty, name, "GEP pointee")?;
            let [index] = indices.as_slice() else {
                return Err(ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: format!(
                        "GEP with {} indices; only single-index scalar-element addressing is mapped",
                        indices.len()
                    ),
                });
            };
            let base_v = resolve_local_pointer(*base, vmap, mem, name)?;
            let index_v = vmap.resolve(*index, name)?;
            let dst = vmap.resolve(result, name)?;
            // The GEP result is still an alloca-rooted pointer into the SAME
            // slot, addressing an element of `elem_ty`.
            value_types.insert(dst, LirType::I64);
            if let Some(&slot) = mem.slot_of.get(&base_v) {
                mem.slot_of.insert(dst, slot);
            }
            mem.pointee_ty.insert(dst, elem_ty.clone());
            instructions.push(Instruction {
                opcode: Opcode::ArrayGep { elem_ty },
                args: vec![base_v, index_v],
                results: vec![dst],
            });
        }
        // ---- GlobalAddr (a function's address as a fn-pointer) -> Opcode::GlobalRef. ----
        //
        // A `GlobalAddr { global }` materializes the address of a module global
        // into a register. ISel lowers `Opcode::GlobalRef { name }` to
        // `ADRP Xd, name@PAGE` (`ARM64_RELOC_PAGE21`) + `ADD Xd, Xd, name@PAGEOFF`
        // (`ARM64_RELOC_PAGEOFF12`) — the LINKER-resolved address of the named
        // LOCAL symbol. This is the foundation for a KNOWN-target indirect call: a
        // subsequent `CallIndirect` through this register BLRs to the callee.
        //
        // We record the materialized symbol name in `global_addr_syms` keyed by the
        // result Value, so the `CallIndirect` arm can trace its function-pointer
        // operand back to a concrete symbol (a KNOWN target) — and so the executor
        // composes the BLR from the SAME real PAGE21/PAGEOFF12 relocations the
        // linker resolves, not the IR's claim.
        //
        // The result is an I64 pointer. Taking a global's address is always pure,
        // so `GlobalAddr` is admitted regardless of `real_calls` (a plain address
        // computation) — but it is USEFUL only under `real_calls`, where a
        // `CallIndirect` through it is emitted rather than rejected.
        Inst::GlobalAddr { global } => {
            let g = module.globals.get(global.as_usize()).ok_or_else(|| {
                ModuleLirError::UnsupportedInst {
                    name: name.to_string(),
                    inst: inst_name(&node.inst),
                }
            })?;
            let result = expect_single_result(node, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, LirType::I64);
            // Record the symbol the address points at (for CallIndirect tracing).
            global_addr_syms.insert(dst, g.name.clone());
            instructions.push(Instruction {
                opcode: Opcode::GlobalRef { name: g.name.clone() },
                args: vec![],
                results: vec![dst],
            });
        }
        // ---- CallIndirect (BLR through a fn-ptr): KNOWN-target compose OR
        //      OPEN-target HAVOC-only. ----
        //
        // Reached ONLY when `real_calls` is set. `callee` is the function-pointer
        // operand; `args` are the call arguments. Two dispositions, split on
        // whether the fn-pointer traces (via `global_addr_syms`) to a concrete
        // GlobalAddr'd symbol:
        //
        //  * KNOWN target (a `global_addr_syms` HIT that names a LOCAL pure fn in
        //    the SAME gate-composable fragment as the direct-call path,
        //    `callee_is_real_call_composable`): emit `Opcode::CallIndirect` (args[0]
        //    = fn ptr, args[1..] = the call args) -> `BLR <fn-ptr-reg>` (a genuine
        //    INDIRECT branch, not a direct `Bl`). The executor COMPOSES it exactly
        //    like the direct case: trace the BLR's target register to its GlobalRef
        //    symbol via the emitted PAGE21/PAGEOFF12 relocations, substitute that
        //    callee's derived pure output into X0, havoc caller-saved registers.
        //    A `global_addr_syms` HIT that resolves to a data global or an
        //    impure/nonlocal fn is a TRACEABLE-but-not-composable target and FAILS
        //    CLOSED (it is not OPEN — its identity is known, but a BLR into data or
        //    an effectful callee cannot be soundly modeled as a pure formula).
        //
        //  * OPEN target (a `global_addr_syms` MISS: an incoming fn-pointer arg, a
        //    vtable-slot load, or a closure-env field — the shape trait-object /
        //    closure dynamic dispatch produces): its target is NOT statically known,
        //    so we CANNOT compose a specific callee. We admit a HAVOC-ONLY BLR: the
        //    executor makes the RESULT and all CALLER-SAVED state fresh (X0, X0..X18,
        //    flags) AND havocs MEMORY (a fresh symbolic MEM array). Callee-saved regs
        //    (X19..X28, SP, FP) are preserved by the AAPCS64 contract. This is the
        //    most conservative over-approximation of an arbitrary callee, so no
        //    property that depends on the call's result or on post-call memory can
        //    be wrongly proved; only the caller's OWN non-result behavior survives.
        Inst::CallIndirect { callee, args, sig, .. } if real_calls => {
            let ptr_v = vmap.resolve(*callee, name)?;
            // Does the fn-pointer trace to a GlobalAddr'd symbol (a KNOWN target)?
            match global_addr_syms.get(&ptr_v) {
                // ---- KNOWN target: trace to a symbol. ----
                Some(sym) => {
                    // The symbol must name a LOCAL pure function in the composable
                    // fragment (same gate as the direct-call path). A symbol that
                    // resolves to a data global or an impure/nonlocal function is a
                    // TRACEABLE target we cannot soundly model as a pure formula, so
                    // it FAILS CLOSED here (a BLR into data would run garbage; an
                    // impure callee's effects would be dropped). This is NOT the
                    // OPEN case — the pointer is a concrete, resolvable symbol whose
                    // *identity* is known but whose behavior is not composable.
                    let callee_fn = match module.function_by_name(sym) {
                        Some(c) if callee_is_real_call_composable(module, c) => c,
                        _ => {
                            return Err(ModuleLirError::UnsupportedInst {
                                name: name.to_string(),
                                inst: inst_name(&node.inst),
                            });
                        }
                    };
                    let func_ty =
                        module.func_types.get(callee_fn.ty.as_usize()).ok_or_else(|| {
                            ModuleLirError::UnsupportedInst {
                                name: name.to_string(),
                                inst: inst_name(&node.inst),
                            }
                        })?;
                    // A composable callee returns exactly one single-register scalar.
                    let [ret_ty] = func_ty.returns.as_slice() else {
                        return Err(ModuleLirError::UnsupportedInst {
                            name: name.to_string(),
                            inst: inst_name(&node.inst),
                        });
                    };
                    // Arity must match: one call arg per callee parameter.
                    if args.len() != func_ty.params.len() {
                        return Err(ModuleLirError::UnsupportedInst {
                            name: name.to_string(),
                            inst: inst_name(&node.inst),
                        });
                    }
                    let result = expect_single_result(node, name)?;
                    let lir_ret = map_scalar_int_ty(ret_ty, "indirect-call return")?;
                    // args[0] = the function pointer (I64); args[1..] = the call args.
                    let mut call_args: Vec<Value> = Vec::with_capacity(args.len() + 1);
                    call_args.push(ptr_v);
                    for a in args {
                        call_args.push(vmap.resolve(*a, name)?);
                    }
                    let dst = vmap.resolve(result, name)?;
                    value_types.insert(dst, lir_ret);
                    instructions.push(Instruction {
                        opcode: Opcode::CallIndirect,
                        args: call_args,
                        results: vec![dst],
                    });
                }
                // ---- OPEN target: NOT traceable to a concrete symbol. ----
                //
                // The fn-pointer is an incoming argument, a vtable-slot load, or a
                // closure-env field — the shape trait-object / closure dynamic
                // dispatch produces. Its target is NOT statically known, so we
                // CANNOT compose a specific callee. Instead we admit the call as a
                // HAVOC-ONLY BLR: the executor models the open callee by making the
                // RESULT and all CALLER-SAVED state fresh (result X0, X0..X18,
                // flags), and — critically — HAVOCING MEMORY (a fresh symbolic MEM
                // array), so any post-call load reads a fresh value. CALLEE-SAVED
                // registers (X19..X28, SP, FP) are preserved by the AAPCS64 contract,
                // which is what lets the caller's own frame survive.
                //
                // SOUNDNESS: an open callee can do anything an arbitrary function
                // can — clobber caller-saved regs, write anywhere in memory, return
                // any value. Modeling all of that as FRESH is the most conservative
                // possible over-approximation: nothing the callee could do is
                // excluded, so no property that depends on the call's result or on
                // post-call memory can be wrongly proved. Only the caller's OWN
                // non-result, callee-saved-frame behavior (e.g. a return value that
                // is a constant independent of the call) remains provable.
                //
                // We still validate the SIGNATURE arity so a malformed indirect call
                // is rejected, but we do NOT resolve any callee — there is none.
                None => {
                    let call_sig = module.func_types.get(sig.as_usize()).ok_or_else(|| {
                        ModuleLirError::UnsupportedInst {
                            name: name.to_string(),
                            inst: inst_name(&node.inst),
                        }
                    })?;
                    if call_sig.is_vararg {
                        return Err(ModuleLirError::UnsupportedInst {
                            name: name.to_string(),
                            inst: inst_name(&node.inst),
                        });
                    }
                    // A single-register scalar return, matching the composable shape.
                    let [ret_ty] = call_sig.returns.as_slice() else {
                        return Err(ModuleLirError::UnsupportedInst {
                            name: name.to_string(),
                            inst: inst_name(&node.inst),
                        });
                    };
                    if args.len() != call_sig.params.len() {
                        return Err(ModuleLirError::UnsupportedInst {
                            name: name.to_string(),
                            inst: inst_name(&node.inst),
                        });
                    }
                    let result = expect_single_result(node, name)?;
                    let lir_ret = map_scalar_int_ty(ret_ty, "open-indirect-call return")?;
                    // args[0] = the (untraceable) fn-pointer; args[1..] = call args.
                    let mut call_args: Vec<Value> = Vec::with_capacity(args.len() + 1);
                    call_args.push(ptr_v);
                    for a in args {
                        call_args.push(vmap.resolve(*a, name)?);
                    }
                    let dst = vmap.resolve(result, name)?;
                    value_types.insert(dst, lir_ret);
                    instructions.push(Instruction {
                        opcode: Opcode::CallIndirect,
                        args: call_args,
                        results: vec![dst],
                    });
                }
            }
        }
        // ---- REAL (non-inlined) Call to a local pure callee -> Opcode::Call. ----
        //
        // Reached ONLY when `real_calls` is set AND the inlining pre-pass DEFERRED
        // this call (it is a LOCAL callee in the gate's single-register scalar-pure
        // fragment). We emit a genuine LIR `Opcode::Call { name }` — ISel lowers it
        // to `Bl <callee>` + an `ARM64_RELOC_BRANCH26` naming the callee symbol —
        // instead of splicing the body inline. The proven-output gate / executor
        // then COMPOSES the callee at the reloc target (substitute its derived pure
        // output into X0, havoc caller-saved regs), mirroring
        // `verify_output::model_local_call`.
        //
        // FAIL-CLOSED re-check (defense in depth): even under `real_calls` we
        // re-verify LOCAL + gate-composable here, so a Call the inliner did not
        // handle and this arm cannot soundly emit falls through to the catch-all
        // `UnsupportedInst` — a real Call is never emitted for a callee outside the
        // composable fragment.
        Inst::Call { callee, args } if real_calls => {
            // Resolve the callee and re-check LOCAL + gate-composable. Anything
            // outside the composable fragment fails closed (never a real Call).
            let callee_fn = match module.function_by_id(*callee) {
                Some(c) if callee_is_real_call_composable(module, c) => c,
                _ => {
                    return Err(ModuleLirError::UnsupportedInst {
                        name: name.to_string(),
                        inst: inst_name(&node.inst),
                    });
                }
            };
            let func_ty = module.func_types.get(callee_fn.ty.as_usize()).ok_or_else(|| {
                ModuleLirError::UnsupportedInst {
                    name: name.to_string(),
                    inst: inst_name(&node.inst),
                }
            })?;
            // A composable callee returns exactly one single-register scalar (the
            // `callee_is_real_call_composable` gate guarantees this shape).
            let [ret_ty] = func_ty.returns.as_slice() else {
                return Err(ModuleLirError::UnsupportedInst {
                    name: name.to_string(),
                    inst: inst_name(&node.inst),
                });
            };
            // Arity must match: one call arg per callee parameter.
            if args.len() != func_ty.params.len() {
                return Err(ModuleLirError::UnsupportedInst {
                    name: name.to_string(),
                    inst: inst_name(&node.inst),
                });
            }
            let result = expect_single_result(node, name)?;
            let lir_ret = map_scalar_int_ty(ret_ty, "real-call return")?;
            let arg_vals: Vec<Value> =
                args.iter().map(|a| vmap.resolve(*a, name)).collect::<Result<_, _>>()?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, lir_ret);
            instructions.push(Instruction {
                opcode: Opcode::Call { name: callee_fn.name.clone() },
                args: arg_vals,
                results: vec![dst],
            });
        }
        other => {
            return Err(ModuleLirError::UnsupportedInst {
                name: name.to_string(),
                inst: inst_name(other),
            });
        }
    }
    Ok(())
}

/// Map a scalar pointee/element `trust_ir::Ty` for a memory op. The scalar-
/// memory slice only models fixed-width integer (and `Bool`) slots; a float or
/// aggregate pointee fails closed (the pinned trust-ir interpreter lacks
/// aggregate-in-memory `byte_size`).
///
/// `Ty::Ptr` is admitted as an 8-byte `I64` slot (mirroring `map_scalar_int_ty`
/// :270 and the Alloca/GEP I64 pointer carrier). SOUNDNESS: a pointer is a thin
/// 64-bit machine word, so an `Alloca{Ptr}` / `Store{Ptr}` / `Load{Ptr}` is
/// exactly an 8-byte scalar slot at the machine level — the same width the
/// interpreter round-trips for `I64`. Admitting it lets a FUNCTION POINTER be
/// spilled/reloaded through a stack slot: a `Load{ty:Ptr}` off an alloca-rooted
/// slot models a VTABLE-SLOT / CLOSURE-ENV-FIELD read (the shape real
/// trait-object / closure dispatch produces). A fn-ptr read from memory is a
/// `global_addr_syms` MISS (only `GlobalAddr` results are tagged), so a
/// `CallIndirect` through it routes to the ALREADY-PROVEN OPEN-target havoc BLR
/// arm — the most conservative over-approximation of an arbitrary callee. This
/// admits NO arithmetic-on-`Ptr` path: the BinOp/Cast/UnOp/ICmp arms consult
/// `map_scalar_int_ty`, never this function, so their gating is unchanged. The
/// width-match guards on `Load`/`Store` (slot element `== I64`) still reject any
/// mixed-width aliasing, so fail-closed is preserved everywhere else.
fn map_scalar_mem_ty(ty: &Ty, name: &str, context: &str) -> Result<LirType, ModuleLirError> {
    match ty {
        // Trust (v25 B1): Isize/Usize (64-bit on the pinned target) and Char
        // (32-bit unsigned carrier) are fixed-width scalars in memory too —
        // map_scalar_int_ty assigns them the I64/I32 LIR widths.
        Ty::I8 | Ty::U8 | Ty::I16 | Ty::U16 | Ty::I32 | Ty::U32 | Ty::I64 | Ty::U64
        | Ty::Isize | Ty::Usize | Ty::Char
        | Ty::I128 | Ty::U128 | Ty::Bool | Ty::Ptr => map_scalar_int_ty(ty, context),
        other => Err(ModuleLirError::UnsupportedMemory {
            name: name.to_string(),
            detail: format!("non-scalar {context} type {other:?}"),
        }),
    }
}

/// Resolve a memory-op pointer/base operand to its LIR `Value`, requiring that
/// it be an alloca-rooted local pointer (or an `ArrayGep` off one). An opaque
/// incoming pointer fails closed — the scalar-memory slice only reasons about
/// the stack slots it allocated itself.
fn resolve_local_pointer(
    ptr: ValueId,
    vmap: &ValueMap,
    mem: &MemoryCtx,
    name: &str,
) -> Result<Value, ModuleLirError> {
    let v = vmap.resolve(ptr, name)?;
    if mem.slot_of.contains_key(&v) {
        Ok(v)
    } else {
        Err(ModuleLirError::NonLocalPointer { name: name.to_string(), value: ptr.index() })
    }
}

/// Lower a block terminator into LIR control flow, threading per-edge block-args.
#[allow(clippy::too_many_arguments)]
fn lower_terminator(
    term: &Inst,
    vmap: &ValueMap,
    blocks_by_id: &HashMap<u32, &trust_ir::Block>,
    instructions: &mut Vec<Instruction>,
    edge_blocks: &mut Vec<(Block, LirBlock)>,
    next_edge_block: &mut u32,
    next_value: &mut u32,
    name: &str,
) -> Result<(), ModuleLirError> {
    match term {
        Inst::Return { values } => {
            if values.len() != 1 {
                return Err(ModuleLirError::MalformedReturn { name: name.to_string() });
            }
            let v = vmap.resolve(values[0], name)?;
            instructions.push(Instruction {
                opcode: Opcode::Return,
                args: vec![v],
                results: vec![],
            });
        }
        Inst::Unreachable => {
            // A diverging terminator; model as a bare Trap so no fall-through
            // path is fabricated.
            instructions.push(Instruction { opcode: Opcode::Trap, args: vec![], results: vec![] });
        }
        Inst::Br { target, args } => {
            // Unconditional jump: emit the block-arg copies in THIS block, then
            // jump. No edge split is needed for an unconditional edge.
            emit_edge_arg_copies(
                *target,
                args,
                vmap,
                blocks_by_id,
                instructions,
                next_value,
                name,
            )?;
            instructions.push(Instruction {
                opcode: Opcode::Jump { dest: Block(target.index()) },
                args: vec![],
                results: vec![],
            });
        }
        Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
            let cond_v = vmap.resolve(*cond, name)?;
            let then_dest = conditional_edge_dest(
                *then_target,
                then_args,
                vmap,
                blocks_by_id,
                edge_blocks,
                next_edge_block,
                next_value,
                name,
            )?;
            let else_dest = conditional_edge_dest(
                *else_target,
                else_args,
                vmap,
                blocks_by_id,
                edge_blocks,
                next_edge_block,
                next_value,
                name,
            )?;
            instructions.push(Instruction {
                opcode: Opcode::Brif { cond: cond_v, then_dest, else_dest },
                args: vec![cond_v],
                results: vec![],
            });
        }
        Inst::Switch { value, default, default_args, cases, .. } => {
            let sel = vmap.resolve(*value, name)?;
            let mut lir_cases = Vec::with_capacity(cases.len());
            for case in cases {
                let case_val = match &case.value {
                    Constant::Int(v) => i128_to_i64(*v, name)?,
                    Constant::Bool(b) => i64::from(*b),
                    _ => {
                        return Err(ModuleLirError::UnsupportedSwitchCase {
                            name: name.to_string(),
                        });
                    }
                };
                let dest = conditional_edge_dest(
                    case.target,
                    &case.args,
                    vmap,
                    blocks_by_id,
                    edge_blocks,
                    next_edge_block,
                    next_value,
                    name,
                )?;
                lir_cases.push((case_val, dest));
            }
            let default_dest = conditional_edge_dest(
                *default,
                default_args,
                vmap,
                blocks_by_id,
                edge_blocks,
                next_edge_block,
                next_value,
                name,
            )?;
            instructions.push(Instruction {
                opcode: Opcode::Switch { cases: lir_cases, default: default_dest },
                args: vec![sel],
                results: vec![],
            });
        }
        other => {
            return Err(ModuleLirError::UnsupportedInst {
                name: name.to_string(),
                inst: inst_name(other),
            });
        }
    }
    Ok(())
}

/// Resolve a conditional-branch edge destination. If the target block has params
/// AND the edge carries args, the args must be copied on this specific edge — so
/// we synthesize a fresh trampoline (edge-split) block that performs the Copys
/// then Jumps to the real target, and branch to the trampoline instead. If the
/// target has no params, branch directly (no split needed).
#[allow(clippy::too_many_arguments)]
fn conditional_edge_dest(
    target: trust_ir::value::BlockId,
    args: &[ValueId],
    vmap: &ValueMap,
    blocks_by_id: &HashMap<u32, &trust_ir::Block>,
    edge_blocks: &mut Vec<(Block, LirBlock)>,
    next_edge_block: &mut u32,
    next_value: &mut u32,
    name: &str,
) -> Result<Block, ModuleLirError> {
    let target_block = blocks_by_id
        .get(&target.index())
        .ok_or(ModuleLirError::MissingBlock { name: name.to_string(), target: target.index() })?;
    if target_block.params.is_empty() {
        // Validate arity (must also be zero on the edge).
        if !args.is_empty() {
            return Err(ModuleLirError::EdgeArgArity {
                name: name.to_string(),
                target: target.index(),
                got: args.len(),
                expected: 0,
            });
        }
        return Ok(Block(target.index()));
    }

    // The target has params: build a trampoline that copies the edge args into
    // the target's param Values, then jumps to the real target.
    let mut tramp = Vec::new();
    emit_edge_arg_copies(target, args, vmap, blocks_by_id, &mut tramp, next_value, name)?;
    tramp.push(Instruction {
        opcode: Opcode::Jump { dest: Block(target.index()) },
        args: vec![],
        results: vec![],
    });
    let id = Block(*next_edge_block);
    *next_edge_block += 1;
    edge_blocks.push((id, LirBlock { params: vec![], instructions: tramp, source_locs: vec![] }));
    Ok(id)
}

/// Emit the parallel `Copy`s that move a branch edge's args into the target
/// block's param Values. Validates SSA arity (one arg per target param).
///
/// trust_ir edge semantics are a PARALLEL bind (the interpreter evaluates all
/// args in the predecessor's scope, then binds the target params). We sequence
/// the copies through a fresh temporary whenever a later copy would clobber a
/// source a still-pending copy reads — the same swap-safe scheme the VF->LIR path
/// uses — so a `swap`-shaped edge (params (x,y) <- args (y,x)) is correct.
fn emit_edge_arg_copies(
    target: trust_ir::value::BlockId,
    args: &[ValueId],
    vmap: &ValueMap,
    blocks_by_id: &HashMap<u32, &trust_ir::Block>,
    instructions: &mut Vec<Instruction>,
    next_value: &mut u32,
    name: &str,
) -> Result<(), ModuleLirError> {
    let target_block = blocks_by_id
        .get(&target.index())
        .ok_or(ModuleLirError::MissingBlock { name: name.to_string(), target: target.index() })?;
    if args.len() != target_block.params.len() {
        return Err(ModuleLirError::EdgeArgArity {
            name: name.to_string(),
            target: target.index(),
            got: args.len(),
            expected: target_block.params.len(),
        });
    }

    // (src_value, dst_param_value) pairs, skipping identity copies.
    let mut pending: Vec<(Value, Value)> = Vec::with_capacity(args.len());
    for (arg, (param_id, _)) in args.iter().zip(&target_block.params) {
        let src = vmap.resolve(*arg, name)?;
        let dst = vmap.resolve(*param_id, name)?;
        if src != dst {
            pending.push((src, dst));
        }
    }

    // Swap-safe sequencing: emit a copy whose destination no other pending copy
    // still reads; if none exists (a cycle), break it via a fresh temporary.
    while !pending.is_empty() {
        if let Some(idx) = (0..pending.len()).find(|&i| {
            let dest = pending[i].1;
            !pending.iter().enumerate().any(|(j, (s, _))| j != i && *s == dest)
        }) {
            let (src, dst) = pending.swap_remove(idx);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![src],
                results: vec![dst],
            });
            continue;
        }
        // Cycle: route the first copy's source through a fresh temp.
        let temp = Value(*next_value);
        *next_value += 1;
        let (src, _) = pending[0];
        instructions.push(Instruction {
            opcode: Opcode::Copy,
            args: vec![src],
            results: vec![temp],
        });
        pending[0].0 = temp;
    }

    Ok(())
}

/// Deterministic reachable block order: entry first, then a DFS over successors.
/// Fail-closed if a successor references a missing block.
fn reachable_block_order(
    function: &IrFunction,
    blocks_by_id: &HashMap<u32, &trust_ir::Block>,
    name: &str,
) -> Result<Vec<u32>, ModuleLirError> {
    let mut order = Vec::with_capacity(function.blocks.len());
    let mut seen: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut stack = vec![function.entry.index()];
    // Use an explicit stack but push successors in reverse so the visitation
    // order is the natural (then-before-else, cases-in-order) order.
    while let Some(bid) = stack.pop() {
        if !seen.insert(bid) {
            continue;
        }
        let block = blocks_by_id
            .get(&bid)
            .ok_or(ModuleLirError::MissingBlock { name: name.to_string(), target: bid })?;
        order.push(bid);
        let succs = block_successors(block, name)?;
        for s in succs.into_iter().rev() {
            if !seen.contains(&s) {
                stack.push(s);
            }
        }
    }
    Ok(order)
}

/// Successor block ids of a block's terminator, in deterministic order.
fn block_successors(block: &trust_ir::Block, name: &str) -> Result<Vec<u32>, ModuleLirError> {
    let (_body, term) = split_terminator(block, name)?;
    let succs = match term {
        Inst::Br { target, .. } => vec![target.index()],
        Inst::CondBr { then_target, else_target, .. } => {
            vec![then_target.index(), else_target.index()]
        }
        Inst::Switch { default, cases, .. } => {
            let mut s: Vec<u32> = cases.iter().map(|c| c.target.index()).collect();
            s.push(default.index());
            s
        }
        Inst::Return { .. } | Inst::Unreachable => vec![],
        other => {
            return Err(ModuleLirError::UnsupportedInst {
                name: name.to_string(),
                inst: inst_name(other),
            });
        }
    };
    Ok(succs)
}

fn expect_single_result(
    node: &trust_ir::node::InstrNode,
    name: &str,
) -> Result<ValueId, ModuleLirError> {
    match node.results.as_slice() {
        [r] => Ok(*r),
        _ => Err(ModuleLirError::UnsupportedInst {
            name: name.to_string(),
            inst: inst_name(&node.inst),
        }),
    }
}

// ===========================================================================
// CHECKED-ARITH TUPLE DECOMPOSITION (fail-closed, SSA, no tuple-in-memory).
//
// The BRIDGE's idiom for `a + b` (overflow checks on) builds the MIR
// `(value, overflowed)` pair as a 2-field SSA TUPLE — DIFFERENT from the
// producer's separate-SSA `Inst::Overflow -> [value, overflowed]` the prior
// overflow slice handled. The real emitted shape (verified against
// `trust_ir_bridge::lower_to_trust_ir` on the `CheckedBinaryOp` VF) is:
//
//     %v, %o = add.overflow i32 %a, %b      ; Inst::Overflow  -> [value, flag]
//     %u  = undef (i32, bool)               ; TUPLE-typed Undef SEED
//     %t0 = insertfield (i32,bool) %u, 0, %v   ; field 0 <- value
//     %t  = insertfield (i32,bool) %t0, 1, %o  ; field 1 <- flag  (FULL tuple)
//     ... extractfield bool %t, 1  -> the overflow flag (the assert reads this)
//     ... extractfield i32  %t, 0  -> the value         (the result reads this)
//
// The tuple is a PURE SSA value — never stored to memory — so we DECOMPOSE it
// into the two scalar SSA Values it carries (which already exist: the
// `Inst::Overflow` results) WITHOUT ever materializing a `Ty::Tuple` in memory
// (the pinned interpreter lacks `Ty::Tuple` `byte_size`, so tuple-in-memory is
// out of scope and fails closed). The `Undef` seed and the `InsertField`s emit
// NO LIR; each `ExtractField` becomes a `Copy` of the resolved field Value.
//
// SOUNDNESS (a wrong checked-arith mapping miscompiles): this is a MUST analysis
// that admits a tuple ONLY when it can prove, for every tuple-typed SSA value:
//   * its def-chain roots at a `Tuple([_, _])`-typed `Undef` SEED;
//   * every `InsertField` defines a DISTINCT in-range field exactly once (no
//     double-write, no out-of-range field);
//   * by the time ANY `ExtractField` reads field `k`, field `k` is DEFINED
//     (the producer always builds field 0 then field 1 before either read, and
//     trust_ir is SSA with defs-before-uses, so the straight-line def order
//     witnesses this);
//   * NO tuple-typed value is consumed by anything but `InsertField`/
//     `ExtractField` (no `Store`, `Return`, branch-arg, strict op, `Call`, ...).
// Any deviation FAILS CLOSED (`UnsupportedAggregate` / `UnsupportedUndef`), so a
// tuple the converter cannot soundly decompose is never lowered.
// ===========================================================================

/// The per-tuple-SSA-value field map: index `k` holds the scalar field-`k`
/// `ValueId` once an `InsertField` has defined it, or `None` while undefined.
type TupleFields = Vec<Option<ValueId>>;

/// The result of the checked-arith tuple decomposition pre-pass.
struct TupleDecompose {
    /// `Tuple`-typed `Undef` result ValueIds proven to be dead checked-arith
    /// tuple seeds — these emit NO LIR (the field values carry the data).
    admitted_tuple_seeds: std::collections::HashSet<ValueId>,
    /// `InsertField` result ValueIds that build an admitted tuple — these emit
    /// NO LIR; their effect is folded into the field map.
    insert_results: std::collections::HashSet<ValueId>,
    /// For each `ExtractField` result ValueId, the scalar field `ValueId` it
    /// resolves to (the field that the read aggregate carries at that index).
    /// The `ExtractField` lowers to a `Copy` of this field's LIR Value.
    extract_field_src: std::collections::HashMap<ValueId, ValueId>,
}

/// Prove which checked-arith result tuples can be decomposed into scalar SSA
/// Values, returning the seed/insert/extract bookkeeping. FAILS CLOSED on any
/// aggregate shape the converter cannot decompose soundly (see
/// [`ModuleLirError::UnsupportedAggregate`]).
///
/// `order` is the reachable block order; the analysis walks blocks (and the
/// straight-line body within each) in that order. trust_ir SSA guarantees every
/// value is defined before it is used and the producer emits the tuple build
/// (seed + two `InsertField`s) strictly before any `ExtractField`, so a single
/// forward pass that propagates a per-tuple-value field map is a sound MUST
/// witness: an `ExtractField` only resolves when the read field is already
/// `Some`.
fn analyze_checked_arith_tuples(
    order: &[u32],
    blocks_by_id: &HashMap<u32, &trust_ir::Block>,
    name: &str,
) -> Result<TupleDecompose, ModuleLirError> {
    use std::collections::{HashMap as Map, HashSet as Set};

    // ---- Gather every Tuple-typed Undef seed and validate its tuple type. ----
    // A scalar Undef is left for `analyze_dead_undef_seeds`. Only a
    // `Tuple([scalar_int, Bool])`-typed Undef (the checked-arith pair) is a
    // candidate here; any other Tuple shape fails closed.
    let mut tuple_field_count: Map<ValueId, usize> = Map::new();
    for &bid in order {
        let block = blocks_by_id[&bid];
        for node in &block.body {
            if let Inst::Undef { ty: Ty::Tuple(elems) } = &node.inst {
                let [result] = node.results.as_slice() else {
                    return Err(ModuleLirError::UnsupportedUndef {
                        name: name.to_string(),
                        detail: "Tuple Undef must bind exactly one result".to_string(),
                    });
                };
                // The decomposable shape THIS pass claims is EXACTLY the
                // checked-arith pair: a 2-field tuple `[scalar_int, Bool]` whose
                // field 1 is the overflow flag. A tuple that is NOT this shape —
                // a different arity, or a 2-field tuple whose field 1 is not
                // `Bool` (e.g. the `(i32, i32)` aggregate-in-memory tuple the
                // BRIDGE promotes to a stack slot) — is NOT a checked-arith pair
                // and is left UNCLAIMED here (skip, do not error), so PASS 1.7
                // (`analyze_aggregate_memory`) or, failing that, the fail-closed
                // default in `lower_value_inst` handles it. This keeps the two
                // tuple slices disjoint: checked-arith owns `[Int, Bool]`,
                // aggregate-memory owns the stored scalar tuple.
                let is_checked_arith_pair = elems.len() == 2
                    && matches!(elems[1], Ty::Bool)
                    && map_scalar_int_ty(&elems[0], "checked-arith value field").is_ok();
                if !is_checked_arith_pair {
                    continue;
                }
                tuple_field_count.insert(*result, elems.len());
            }
        }
    }

    // Fast path: no Tuple Undef seed anywhere -> nothing to decompose.
    if tuple_field_count.is_empty() {
        return Ok(TupleDecompose {
            admitted_tuple_seeds: Set::new(),
            insert_results: Set::new(),
            extract_field_src: Map::new(),
        });
    }

    // ---- Forward field-map propagation over the reachable straight-line body.
    // `fields[tuple_value]` is the per-field `Option<scalar ValueId>` carried by
    // that tuple SSA value. A seed starts all-`None`; each `InsertField` clones
    // its source aggregate's map and sets one field. Because trust_ir is SSA and
    // the producer emits the build before any read, walking in `order` with each
    // block's body in program order visits a tuple value's definition before any
    // use. We require defs-before-uses (fail closed on a forward/undefined
    // reference) rather than assume it. ----
    let mut fields: Map<ValueId, TupleFields> = Map::new();
    // `root[v]` = the seed `Undef` ValueId at the base of `v`'s tuple chain.
    let mut root: Map<ValueId, ValueId> = Map::new();
    for (&seed, &n) in &tuple_field_count {
        fields.insert(seed, vec![None; n]);
        root.insert(seed, seed);
    }
    // Seeds that are actually BUILT (consumed by ≥1 InsertField). A tuple `Undef`
    // that is never built into a real `(value, overflow)` pair is NOT the
    // checked-arith decompose idiom; it stays unadmitted and fails closed, so a
    // bare aggregate poison value is never silently dropped.
    let mut built_seeds: Set<ValueId> = Set::new();

    let mut insert_results: Set<ValueId> = Set::new();
    let mut extract_field_src: Map<ValueId, ValueId> = Map::new();

    for &bid in order {
        let block = blocks_by_id[&bid];
        for node in &block.body {
            match &node.inst {
                // The seed itself: already registered in `fields`. Nothing to do.
                Inst::Undef { ty: Ty::Tuple(_) } => {}
                Inst::InsertField { ty, aggregate, field, value } => {
                    // Only InsertFields that build a TRACKED checked-arith tuple
                    // are folded. An InsertField whose aggregate is NOT a tracked
                    // tuple is an aggregate shape we do not model -> fail closed
                    // (it cannot reach the scalar/CFG/memory slices).
                    let Some(src_map) = fields.get(aggregate).cloned() else {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "InsertField builds on value {} which is not a tracked \
                                 checked-arith tuple seed/chain",
                                aggregate.index()
                            ),
                        });
                    };
                    // The InsertField's declared ty must be the SAME tuple shape
                    // (2-field Int/Bool) — a mismatch means a different aggregate.
                    if let Ty::Tuple(elems) = ty {
                        if elems.len() != src_map.len() {
                            return Err(ModuleLirError::UnsupportedAggregate {
                                name: name.to_string(),
                                detail: format!(
                                    "InsertField tuple arity {} disagrees with the tracked \
                                     tuple arity {}",
                                    elems.len(),
                                    src_map.len()
                                ),
                            });
                        }
                    } else {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: "InsertField on a tracked tuple has a non-Tuple ty".to_string(),
                        });
                    }
                    let [result] = node.results.as_slice() else {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: "InsertField must bind exactly one result".to_string(),
                        });
                    };
                    let idx = *field as usize;
                    if idx >= src_map.len() {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "InsertField field {idx} out of range for {}-field tuple",
                                src_map.len()
                            ),
                        });
                    }
                    if src_map[idx].is_some() {
                        // A double-write to the same field would discard the
                        // first value; the decomposition assumes single-write
                        // fields. Fail closed rather than silently drop.
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "InsertField re-writes already-defined tuple field {idx}"
                            ),
                        });
                    }
                    let mut new_map = src_map;
                    new_map[idx] = Some(*value);
                    fields.insert(*result, new_map);
                    insert_results.insert(*result);
                    // Carry the chain root forward and record that this seed is
                    // genuinely built into a tuple. `aggregate` is a tracked tuple
                    // value (its `fields` entry exists), so its root is known.
                    let chain_root = *root.get(aggregate).unwrap_or(aggregate);
                    root.insert(*result, chain_root);
                    built_seeds.insert(chain_root);
                }
                Inst::ExtractField { aggregate, field, .. } => {
                    // An ExtractField on a TRACKED tuple resolves to the scalar
                    // field Value; on any non-tracked aggregate it fails closed.
                    let Some(src_map) = fields.get(aggregate) else {
                        // Not a tracked tuple: leave it for `lower_value_inst`,
                        // which fail-closes (`UnsupportedInst { ExtractField }`).
                        continue;
                    };
                    let idx = *field as usize;
                    let Some(src) = src_map.get(idx).copied().flatten() else {
                        // The field is NOT defined at this read point (partial
                        // tuple, or out of range). FAIL CLOSED: a read of an
                        // undefined field would observe the dead Undef seed.
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "ExtractField reads tuple field {idx} that is not defined on \
                                 every path (would observe the Undef seed)"
                            ),
                        });
                    };
                    let [result] = node.results.as_slice() else {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: "ExtractField must bind exactly one result".to_string(),
                        });
                    };
                    extract_field_src.insert(*result, src);
                }
                // Any OTHER instruction that consumes a tracked tuple value as an
                // operand is a shape we cannot decompose (a Store to memory, a
                // Return of the tuple, a branch arg, ...). FAIL CLOSED so a tuple
                // never escapes the SSA decomposition into memory or a strict op.
                other => {
                    for op in inst_value_operands(other) {
                        if fields.contains_key(&op) {
                            return Err(ModuleLirError::UnsupportedAggregate {
                                name: name.to_string(),
                                detail: format!(
                                    "tracked checked-arith tuple value {} is consumed by `{}` \
                                     (only InsertField/ExtractField decompose a tuple; a tuple \
                                     escaping to memory/return/branch is out of scope)",
                                    op.index(),
                                    inst_name(other)
                                ),
                            });
                        }
                    }
                }
            }
        }
    }

    // Every registered tuple seed must be genuinely BUILT into a `(value,
    // overflow)` pair by ≥1 `InsertField`. A tuple `Undef` that is never built is
    // NOT the checked-arith decompose idiom — fail closed so a bare aggregate
    // poison value is never silently admitted/dropped. (A `built` seed already
    // survived the consume-shape check: any non-Insert/Extract use of any value
    // in its chain would have fail-closed above.)
    for &seed in tuple_field_count.keys() {
        if !built_seeds.contains(&seed) {
            return Err(ModuleLirError::UnsupportedUndef {
                name: name.to_string(),
                detail: format!(
                    "Tuple Undef value {} is not built into a checked-arith (value, overflow) \
                     pair by any InsertField (not the decomposable idiom)",
                    seed.index()
                ),
            });
        }
    }

    // The built seeds are exactly the admitted dead tuple seeds. They emit no LIR
    // (the decomposed scalar field Values carry the data).
    let admitted_tuple_seeds = built_seeds;

    Ok(TupleDecompose { admitted_tuple_seeds, insert_results, extract_field_src })
}

// ===========================================================================
// AGGREGATE-IN-MEMORY DECOMPOSITION (fail-closed).
//
// The BRIDGE promotes a multi-block-written aggregate local to a whole-aggregate
// stack slot (`trust_ir_bridge::lower::promote_local_to_memory` +
// `ensure_local_storage`). The real emitted shape (verified against
// `lower_to_trust_ir`) round-trips a 2-field scalar `Ty::Tuple` through ONE
// stack slot AS A UNIT:
//
//     %base = const (i32,i32) [0,0]      ; or undef (i32,i32) seed
//     %t0   = insertfield (i32,i32) %base, 0, %a
//     %t    = insertfield (i32,i32) %t0,   1, %b      ; full SSA aggregate
//     %slot = alloca (i32,i32)                        ; AGGREGATE stack slot
//     store (i32,i32) %t -> *%slot                    ; whole-aggregate store
//     %ld   = load  (i32,i32) *%slot                  ; whole-aggregate load
//     %f0   = extractfield i32 %ld, 0
//     %f1   = extractfield i32 %ld, 1
//
// We DECOMPOSE the aggregate into its per-field scalar SSA values and lower the
// whole-aggregate Store/Load into PER-FIELD scalar Str/Ldr at the C-style field
// OFFSETS within the slot (`aggregate_mem_layout`, byte-for-byte identical to
// the trust-ir interpreter's `aggregate_layout`). The aggregate value never
// materializes as a single machine register; field 0 lands at offset 0 and
// field 1 at its aligned offset, exactly where the interpreter's
// `encode_value`/`decode_value` place them, so the emitted bytes and the
// reference interpreter agree.
//
// SOUNDNESS (a wrong aggregate lowering miscompiles): this is a MUST analysis
// that admits an aggregate slot ONLY when it can prove, for the whole function:
//   * the slot's `Alloca` pointee is a self-describing 2-field scalar `Ty::Tuple`
//     whose C-layout `aggregate_mem_layout` reproduces 1:1;
//   * EVERY `Store`/`Load` whose pointer is that slot is WHOLE-aggregate (the
//     slot's tuple type) — a partial/scalar access into the aggregate slot, or a
//     `GEP` re-derived address into it, fails closed (the GEP field-index idiom
//     `idx * byte_size(field)` does NOT in general equal the C-style offset, so
//     it is NOT admitted here);
//   * every stored aggregate VALUE decomposes to a per-field scalar map rooted at
//     a `Const::Aggregate`/`Undef` base built by distinct single-write
//     `InsertField`s, OR is itself a tracked aggregate `Load` result;
//   * every tracked aggregate value is consumed ONLY by `InsertField` (build),
//     `Store` (into a slot), or `ExtractField` (read) — a tuple escaping to a
//     return / branch-arg / strict op / `Call` fails closed.
// Any deviation FAILS CLOSED (`UnsupportedAggregate`/`UnsupportedMemory`), so an
// aggregate the converter cannot soundly decompose is never lowered.
// ===========================================================================

/// The bookkeeping the aggregate-memory lowering consumes.
struct AggMemDecompose {
    /// Aggregate `Alloca` result `ValueId` -> its C-style slot layout. The
    /// lowering allocates ONE sized stack slot per entry.
    agg_alloca_layout: std::collections::HashMap<ValueId, AggMemLayout>,
    /// `Const::Aggregate` result `ValueId`s that seed a tracked aggregate — they
    /// emit NO LIR (the per-field scalar Values carry the data); the const's
    /// field constants are materialized lazily by the build/store lowering.
    agg_const_seeds: std::collections::HashMap<ValueId, Vec<Constant>>,
    /// `Undef`(Tuple) result `ValueId`s that seed a tracked aggregate — emit NO
    /// LIR (every field is overwritten by an `InsertField` before any read/store).
    agg_undef_seeds: std::collections::HashSet<ValueId>,
    /// `InsertField` result `ValueId`s that build a tracked aggregate — emit NO
    /// LIR; their effect is folded into the field map.
    agg_insert_results: std::collections::HashSet<ValueId>,
    /// Whole-aggregate `Store` node positions (by stored-value `ValueId`) we have
    /// proven are aggregate-slot stores — lowered to per-field Str.
    agg_store_values: std::collections::HashSet<ValueId>,
    /// Aggregate `Load` result `ValueId`s — lowered to per-field Ldr producing a
    /// fresh tracked aggregate.
    agg_load_results: std::collections::HashSet<ValueId>,
    /// `ExtractField` result `ValueId`s that read a tracked aggregate — the field
    /// index they read (resolved against the live per-field map at lowering).
    agg_extract_field: std::collections::HashMap<ValueId, u32>,
}

impl AggMemDecompose {
    fn empty() -> Self {
        Self {
            agg_alloca_layout: std::collections::HashMap::new(),
            agg_const_seeds: std::collections::HashMap::new(),
            agg_undef_seeds: std::collections::HashSet::new(),
            agg_insert_results: std::collections::HashSet::new(),
            agg_store_values: std::collections::HashSet::new(),
            agg_load_results: std::collections::HashSet::new(),
            agg_extract_field: std::collections::HashMap::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.agg_alloca_layout.is_empty()
    }
}

/// Prove which aggregates round-trip through memory soundly, returning the
/// per-field decomposition + slot-layout bookkeeping the lowering consumes.
/// FAILS CLOSED on any aggregate-memory shape outside the admitted slice.
///
/// `tuple_decompose` is the already-run checked-arith tuple analysis; its
/// admitted tuple seeds / insert / extract results are EXCLUDED here (the
/// checked-arith pair is a pure-SSA decomposition that never touches memory), so
/// the two analyses never double-claim a node.
fn analyze_aggregate_memory(
    module: &Module,
    order: &[u32],
    blocks_by_id: &HashMap<u32, &trust_ir::Block>,
    tuple_decompose: &TupleDecompose,
    name: &str,
) -> Result<AggMemDecompose, ModuleLirError> {
    use std::collections::{HashMap as Map, HashSet as Set};

    // ---- 1. Find aggregate Alloca slots (self-describing Ty::Tuple, or a
    // Ty::Struct whose StructDef the module resolves). A scalar Alloca is left to
    // the scalar memory slice. Only an aggregate pointee enters here; its C-layout
    // (from `aggregate_mem_layout`, resolving struct fields via the module) must
    // reproduce the interpreter's 1:1 (fail closed otherwise). We record the slot's
    // aggregate type so a Store/Load width can be checked against the WHOLE-
    // aggregate type. The resolved field count (N, generalized from the initial
    // 2-field slice) that Store/Load check against comes from the layout's
    // `field_offsets.len()`.
    let mut agg_alloca_layout: Map<ValueId, AggMemLayout> = Map::new();
    for &bid in order {
        let block = blocks_by_id[&bid];
        for node in &block.body {
            if let Inst::Alloca { ty: ty @ (Ty::Tuple(_) | Ty::Struct(_)), count, align: _ } =
                &node.inst
            {
                if count.is_some() {
                    return Err(ModuleLirError::UnsupportedMemory {
                        name: name.to_string(),
                        detail: "counted (array/VLA) aggregate Alloca is out of the aggregate \
                                 memory slice"
                            .to_string(),
                    });
                }
                let [result] = node.results.as_slice() else {
                    return Err(ModuleLirError::UnsupportedAggregate {
                        name: name.to_string(),
                        detail: "aggregate Alloca must bind exactly one result".to_string(),
                    });
                };
                let layout = aggregate_mem_layout(ty, module, name)?;
                agg_alloca_layout.insert(*result, layout);
            }
        }
    }

    // Fast path: no aggregate slot -> nothing to decompose (the scalar/checked
    // slices handle everything).
    if agg_alloca_layout.is_empty() {
        return Ok(AggMemDecompose::empty());
    }

    // ---- 2. Track aggregate SSA values' per-field maps. A tracked aggregate is
    // rooted at a Const::Aggregate, an Undef(Tuple) seed, or an aggregate Load.
    // `fields[v]` is the per-field scalar `Option<ValueId>` carried by aggregate
    // SSA value `v`. Walk in program order (SSA defs-before-uses); a forward use
    // of an undefined field fails closed.
    let mut fields: Map<ValueId, Vec<Option<ValueId>>> = Map::new();
    let mut agg_const_seeds: Map<ValueId, Vec<Constant>> = Map::new();
    let mut agg_undef_seeds: Set<ValueId> = Set::new();
    let mut agg_insert_results: Set<ValueId> = Set::new();
    let mut agg_store_values: Set<ValueId> = Set::new();
    let mut agg_load_results: Set<ValueId> = Set::new();
    let mut agg_extract_field: Map<ValueId, u32> = Map::new();

    // Arity is per-aggregate (N fields, generalized from the initial 2-field
    // slice): each Const/Undef/Insert/Extract node's field count is resolved from
    // its OWN aggregate type (`aggregate_field_types`, threading the module for a
    // Ty::Struct), and each whole-aggregate Store/Load's arity is checked against
    // the target slot's layout.

    for &bid in order {
        let block = blocks_by_id[&bid];
        for node in &block.body {
            match &node.inst {
                // ---- Const aggregate base (Tuple or Struct): all-None field map.
                Inst::Const {
                    ty: ty @ (Ty::Tuple(_) | Ty::Struct(_)),
                    value: Constant::Aggregate(consts),
                } => {
                    let [result] = node.results.as_slice() else {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: "Const aggregate must bind one result".to_string(),
                        });
                    };
                    // Resolve the aggregate's field types (struct fields via the
                    // module). Every field must be a scalar carrier we lay out.
                    let field_tys = aggregate_field_types(ty, module, name)?;
                    let n = field_tys.len();
                    if consts.len() != n {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "Const aggregate has {} const fields but type has {n} fields",
                                consts.len()
                            ),
                        });
                    }
                    for fty in &field_tys {
                        scalar_field_size_align(fty, name)?;
                    }
                    fields.insert(*result, vec![None; n]);
                    agg_const_seeds.insert(*result, consts.clone());
                }
                // ---- Undef(Tuple|Struct) seed: all-None field map. ----
                Inst::Undef { ty: ty @ (Ty::Tuple(_) | Ty::Struct(_)) }
                    if !tuple_decompose
                        .admitted_tuple_seeds
                        .contains(node.results.first().unwrap_or(&ValueId::new(u32::MAX))) =>
                {
                    let [result] = node.results.as_slice() else {
                        return Err(ModuleLirError::UnsupportedUndef {
                            name: name.to_string(),
                            detail: "aggregate Undef must bind one result".to_string(),
                        });
                    };
                    let field_tys = aggregate_field_types(ty, module, name)?;
                    for fty in &field_tys {
                        scalar_field_size_align(fty, name)?;
                    }
                    fields.insert(*result, vec![None; field_tys.len()]);
                    agg_undef_seeds.insert(*result);
                }
                // ---- InsertField builds a tracked aggregate. ----
                Inst::InsertField { ty, aggregate, field, value }
                    if fields.contains_key(aggregate) =>
                {
                    // The InsertField's declared ty must be the SAME aggregate the
                    // source carries (same arity of scalar fields). A struct ty
                    // resolves its fields via the module.
                    let n = fields[aggregate].len();
                    let matches_shape = matches!(ty, Ty::Tuple(_) | Ty::Struct(_))
                        && aggregate_field_types(ty, module, name).map(|f| f.len()) == Ok(n);
                    if !matches_shape {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "InsertField ty {ty:?} disagrees with the tracked aggregate arity {n}"
                            ),
                        });
                    }
                    let [result] = node.results.as_slice() else {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: "InsertField must bind one result".to_string(),
                        });
                    };
                    let mut new_map = fields[aggregate].clone();
                    let idx = *field as usize;
                    if idx >= n {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "InsertField field {idx} out of range ({n}-field aggregate)"
                            ),
                        });
                    }
                    if new_map[idx].is_some() {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!("InsertField re-writes already-defined field {idx}"),
                        });
                    }
                    new_map[idx] = Some(*value);
                    fields.insert(*result, new_map);
                    agg_insert_results.insert(*result);
                }
                // ---- Whole-aggregate Store into a tracked slot. ----
                Inst::Store {
                    ty: Ty::Tuple(_) | Ty::Struct(_),
                    ptr,
                    value,
                    volatile,
                    align: _,
                } => {
                    if *volatile {
                        return Err(ModuleLirError::UnsupportedMemory {
                            name: name.to_string(),
                            detail: "volatile aggregate Store is out of the slice".to_string(),
                        });
                    }
                    // The pointer must be a direct aggregate Alloca slot.
                    if !agg_alloca_layout.contains_key(ptr) {
                        return Err(ModuleLirError::UnsupportedMemory {
                            name: name.to_string(),
                            detail: format!(
                                "aggregate Store pointer {} is not a direct aggregate Alloca slot \
                                 (re-derived/GEP addresses into an aggregate slot are not admitted)",
                                ptr.index()
                            ),
                        });
                    }
                    // The stored value must be a tracked aggregate (so its fields
                    // decompose). A stored aggregate we cannot decompose is fatal.
                    if !fields.contains_key(value) {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "aggregate Store value {} is not a tracked decomposable aggregate",
                                value.index()
                            ),
                        });
                    }
                    // The stored aggregate's arity MUST equal the target slot's
                    // layout arity — otherwise a per-field Str loop would write
                    // the wrong number of fields into the slot.
                    let slot_arity = agg_alloca_layout[ptr].field_offsets.len();
                    if fields[value].len() != slot_arity {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "aggregate Store value {} has {} fields but slot layout has {}",
                                value.index(),
                                fields[value].len(),
                                slot_arity
                            ),
                        });
                    }
                    // Every field of the stored aggregate must be DEFINED (else a
                    // store of an undefined field would write the dead seed).
                    let map = &fields[value];
                    for (i, f) in map.iter().enumerate() {
                        if f.is_none() {
                            return Err(ModuleLirError::UnsupportedAggregate {
                                name: name.to_string(),
                                detail: format!(
                                    "aggregate Store value {} has undefined field {i}",
                                    value.index()
                                ),
                            });
                        }
                    }
                    agg_store_values.insert(*value);
                }
                // ---- Whole-aggregate Load from a tracked slot. ----
                Inst::Load { ty: Ty::Tuple(_) | Ty::Struct(_), ptr, volatile, align: _ } => {
                    if *volatile {
                        return Err(ModuleLirError::UnsupportedMemory {
                            name: name.to_string(),
                            detail: "volatile aggregate Load is out of the slice".to_string(),
                        });
                    }
                    if !agg_alloca_layout.contains_key(ptr) {
                        return Err(ModuleLirError::UnsupportedMemory {
                            name: name.to_string(),
                            detail: format!(
                                "aggregate Load pointer {} is not a direct aggregate Alloca slot",
                                ptr.index()
                            ),
                        });
                    }
                    let [result] = node.results.as_slice() else {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: "aggregate Load must bind one result".to_string(),
                        });
                    };
                    // The Load result is a fresh tracked aggregate; its per-field
                    // ValueIds are the load result itself indexed per field at
                    // lowering. Register an all-None placeholder; ExtractField
                    // resolves against the SLOT's per-field loaded Values which the
                    // lowering materializes. We mark every field "defined" with a
                    // sentinel == the load result so the consume-shape scan treats
                    // it as a fully-built aggregate (no undefined-field reads). The
                    // arity comes from the SLOT's resolved layout (N fields).
                    let n = agg_alloca_layout[ptr].field_offsets.len();
                    fields.insert(*result, vec![Some(*result); n]);
                    agg_load_results.insert(*result);
                }
                // ---- ExtractField on a tracked aggregate. ----
                Inst::ExtractField { aggregate, field, .. } if fields.contains_key(aggregate) => {
                    let idx = *field as usize;
                    let n = fields[aggregate].len();
                    if idx >= n {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "ExtractField field {idx} out of range ({n}-field aggregate)"
                            ),
                        });
                    }
                    if fields[aggregate][idx].is_none() {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "ExtractField reads aggregate field {idx} not defined on every path"
                            ),
                        });
                    }
                    let [result] = node.results.as_slice() else {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: "ExtractField must bind one result".to_string(),
                        });
                    };
                    agg_extract_field.insert(*result, *field);
                }
                // ---- Any OTHER use of a tracked aggregate value escapes. ----
                other => {
                    for op in inst_value_operands(other) {
                        if fields.contains_key(&op) {
                            return Err(ModuleLirError::UnsupportedAggregate {
                                name: name.to_string(),
                                detail: format!(
                                    "tracked aggregate value {} is consumed by `{}` (only \
                                     InsertField/ExtractField/Store/Load decompose an aggregate; a \
                                     tuple escaping to return/branch/strict-op is out of scope)",
                                    op.index(),
                                    inst_name(other)
                                ),
                            });
                        }
                    }
                }
            }
        }
    }

    Ok(AggMemDecompose {
        agg_alloca_layout,
        agg_const_seeds,
        agg_undef_seeds,
        agg_insert_results,
        agg_store_values,
        agg_load_results,
        agg_extract_field,
    })
}

// ===========================================================================
// DEAD-UNDEF-SEED ANALYSIS (fail-closed must-overwrite).
//
// The ONLY `Inst::Undef` shape the converter admits is the producer's
// cross-block memory-merge seed: a SCALAR `Undef` that is (1) consumed by
// exactly one `Store` into a local Alloca slot, and (2) whose slot is, on EVERY
// path, overwritten by a later NON-`Undef` `Store` before any `Load` of it. For
// such a seed the poison value is provably never observed (per the ratified
// trust-ir poison semantics: poison is UB only when READ into a strict op or
// BRANCHED on — `ub-numerics-policy.md` §4), so it is a dead store and can be
// lowered to a defined `Iconst 0` (a sound poison refinement) whose Store is
// overwritten before any Load.
//
// This is a LOCAL, CONSERVATIVE must-analysis. It returns the set of `Undef`
// result ValueIds it PROVED dead; every other `Undef` is left unadmitted and
// fails closed in `lower_value_inst`. The analysis never admits an `Undef` whose
// poison could be read while still poison.
// ===========================================================================

/// The slot (Alloca result `ValueId`) a memory-op pointer operand DIRECTLY
/// addresses, or `None` if the pointer is not a direct Alloca result. The
/// analysis is intentionally limited to direct Alloca pointers (no GEP / no
/// re-derived address): an indirected address is not provably the same slot, so
/// it is conservatively treated as opaque and forces fail-closed.
fn direct_alloca_slot(
    ptr: ValueId,
    alloca_results: &std::collections::HashSet<ValueId>,
) -> Option<ValueId> {
    if alloca_results.contains(&ptr) { Some(ptr) } else { None }
}

/// Prove which `Inst::Undef` results are dead cross-block memory-merge seeds.
///
/// Returns the set of admitted `Undef` result `ValueId`s. FAILS CLOSED
/// (`UnsupportedUndef`) on any `Undef` present in the function that the
/// must-analysis cannot prove dead — so a poison value is never materialized at
/// a site that could observe it.
fn analyze_dead_undef_seeds(
    function: &IrFunction,
    order: &[u32],
    blocks_by_id: &HashMap<u32, &trust_ir::Block>,
    admitted_tuple_seeds: &std::collections::HashSet<ValueId>,
    admitted_agg_undef_seeds: &std::collections::HashSet<ValueId>,
    name: &str,
) -> Result<std::collections::HashSet<ValueId>, ModuleLirError> {
    use std::collections::{HashMap as Map, HashSet as Set};

    // Gather every Undef seed (result + scalar-int requirement) and every
    // Alloca's result ValueId (the local slots).
    let mut undef_seeds: Map<ValueId, ()> = Map::new();
    let mut alloca_results: Set<ValueId> = Set::new();
    for &bid in order {
        let block = blocks_by_id[&bid];
        for node in &block.body {
            match &node.inst {
                Inst::Undef { ty } => {
                    let [result] = node.results.as_slice() else {
                        return Err(ModuleLirError::UnsupportedUndef {
                            name: name.to_string(),
                            detail: "Undef must bind exactly one result".to_string(),
                        });
                    };
                    // A `Tuple`-typed Undef already PROVEN to be a decomposable
                    // checked-arith tuple seed (PASS 1.6,
                    // `analyze_checked_arith_tuples`) is handled there — it emits
                    // no LIR and never materializes a tuple in memory. Skip it
                    // here so the scalar memory-merge analysis only sees the
                    // SCALAR seeds it models.
                    if admitted_tuple_seeds.contains(result) {
                        continue;
                    }
                    // An aggregate `Undef(Tuple)` seed already PROVEN to be a
                    // decomposable aggregate-in-memory seed (PASS 1.7,
                    // `analyze_aggregate_memory`) is handled there — its fields are
                    // overwritten by `InsertField`s before any store/read, so it
                    // emits no LIR. Skip it here so the scalar scan only sees the
                    // SCALAR seeds it models.
                    if admitted_agg_undef_seeds.contains(result) {
                        continue;
                    }
                    // Only a scalar-integer Undef can be materialized as a
                    // defined `Iconst 0`. An aggregate / pointer / float Undef
                    // NOT admitted by the tuple decomposition is OUT of this slice
                    // and fails closed.
                    map_scalar_int_ty(ty, "Undef seed").map_err(|_| {
                        ModuleLirError::UnsupportedUndef {
                            name: name.to_string(),
                            detail: format!("Undef has non-scalar-integer type {ty:?}"),
                        }
                    })?;
                    undef_seeds.insert(*result, ());
                }
                Inst::Alloca { .. } => {
                    if let [result] = node.results.as_slice() {
                        alloca_results.insert(*result);
                    }
                }
                _ => {}
            }
        }
    }

    // Fast path: no Undef anywhere -> nothing to admit, nothing to reject.
    if undef_seeds.is_empty() {
        return Ok(Set::new());
    }

    // For each Undef seed, find ALL of its uses across the whole function. It
    // must have EXACTLY ONE use, a `Store { value: seed, ptr: <direct Alloca> }`.
    // Map each admitted seed to the slot it seeds. Any other use shape (a read
    // into a strict op, a second Store, a branch arg, a Return, a non-Alloca
    // Store pointer, ...) is fatal.
    let mut seed_slot: Map<ValueId, ValueId> = Map::new();
    for (&seed, _) in &undef_seeds {
        let mut store_into: Option<ValueId> = None;
        let mut other_use = false;
        for &bid in order {
            let block = blocks_by_id[&bid];
            // A block param can never be an Undef result (params are not Undef),
            // but an edge could pass the seed as a block-arg — scan terminator
            // operands too via `inst_value_operands`.
            for node in &block.body {
                match &node.inst {
                    Inst::Store { ptr, value, .. } if *value == seed => {
                        // The seed's defining store. Require a direct Alloca slot.
                        match direct_alloca_slot(*ptr, &alloca_results) {
                            Some(slot) if store_into.is_none() => store_into = Some(slot),
                            _ => other_use = true, // second store, or non-Alloca ptr
                        }
                    }
                    _ => {
                        // Any OTHER instruction that READS the seed is fatal.
                        if inst_value_operands(&node.inst).contains(&seed) {
                            other_use = true;
                        }
                    }
                }
            }
        }
        let Some(slot) = store_into else {
            return Err(ModuleLirError::UnsupportedUndef {
                name: name.to_string(),
                detail: format!(
                    "Undef value {} is not consumed by a single Store into a local Alloca",
                    seed.index()
                ),
            });
        };
        if other_use {
            return Err(ModuleLirError::UnsupportedUndef {
                name: name.to_string(),
                detail: format!(
                    "Undef value {} has a use beyond its single seed-Store (could be read while poison)",
                    seed.index()
                ),
            });
        }
        seed_slot.insert(seed, slot);
    }

    // The set of slots that carry a poison seed (one or more). A slot with a
    // poison seed must be must-overwritten before any Load.
    let seeded_slots: Set<ValueId> = seed_slot.values().copied().collect();

    // ------------------------------------------------------------------
    // Forward MUST-OVERWRITE dataflow. For each block we compute the set of
    // SEEDED slots that are "definitely non-poison" (overwritten by a later
    // non-Undef Store on EVERY path to the block entry). Meet = intersection
    // (a slot is non-poison at a join only if non-poison on all preds).
    //
    // Transfer within a block (in program order):
    //   * `Store { value=<undef seed>, ptr=slot }` -> slot becomes POISON
    //     (remove from the non-poison set).
    //   * `Store { value=<non-undef>, ptr=slot }`   -> slot becomes NON-POISON
    //     (add to the set).
    //   * `Load { ptr=slot }` where slot is seeded and NOT in the set -> the
    //     poison seed could be observed: FAIL CLOSED.
    // ------------------------------------------------------------------

    // Predecessor map over the reachable order.
    let mut preds: Map<u32, Vec<u32>> = Map::new();
    for &bid in order {
        preds.entry(bid).or_default();
    }
    for &bid in order {
        let block = blocks_by_id[&bid];
        for succ in block_successors(block, name)? {
            // Only track reachable successors (order is the reachable set).
            if preds.contains_key(&succ) {
                preds.entry(succ).or_default().push(bid);
            }
        }
    }

    // entry_state[bid] = set of seeded slots non-poison at the block's entry.
    let mut entry_state: Map<u32, Set<ValueId>> = Map::new();
    for &bid in order {
        // Entry block starts with NOTHING non-poison (the seed store hasn't run).
        entry_state.insert(bid, Set::new());
    }

    // Iterate to a fixpoint (monotone: the only growth is via the transfer; meet
    // shrinks). Bounded by |order| * |slots| so a fixed iteration cap suffices.
    let entry_id = function.entry.index();
    let max_iters = order.len().saturating_mul(seeded_slots.len().max(1)) + order.len() + 1;
    for _ in 0..max_iters {
        let mut changed = false;
        for &bid in order {
            // Compute the meet (intersection) of predecessor EXIT states. The
            // entry block has no predecessors -> empty set (all poison).
            let new_entry: Set<ValueId> = if bid == entry_id {
                Set::new()
            } else {
                let plist = &preds[&bid];
                if plist.is_empty() {
                    Set::new()
                } else {
                    let mut acc: Option<Set<ValueId>> = None;
                    for &p in plist {
                        let undef_set: Set<ValueId> = undef_seeds.keys().copied().collect();
                        let exit = transfer_block_exit(
                            blocks_by_id[&p],
                            &entry_state[&p],
                            &seeded_slots,
                            &undef_set,
                        );
                        acc = Some(match acc {
                            None => exit,
                            Some(a) => a.intersection(&exit).copied().collect(),
                        });
                    }
                    acc.unwrap_or_default()
                }
            };
            if new_entry != entry_state[&bid] {
                entry_state.insert(bid, new_entry);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Final validation pass: at every Load of a seeded slot, the slot MUST be
    // non-poison at that point. Re-run the transfer within each block and check.
    for &bid in order {
        let block = blocks_by_id[&bid];
        let mut cur = entry_state[&bid].clone();
        for node in &block.body {
            match &node.inst {
                Inst::Store { ptr, value, .. } => {
                    if let Some(slot) = direct_alloca_slot(*ptr, &alloca_results) {
                        if seeded_slots.contains(&slot) {
                            if undef_seeds.contains_key(value) {
                                cur.remove(&slot); // poison seed store
                            } else {
                                cur.insert(slot); // overwrite with a defined value
                            }
                        }
                    }
                }
                Inst::Load { ptr, .. } => {
                    if let Some(slot) = direct_alloca_slot(*ptr, &alloca_results) {
                        if seeded_slots.contains(&slot) && !cur.contains(&slot) {
                            return Err(ModuleLirError::UnsupportedUndef {
                                name: name.to_string(),
                                detail: format!(
                                    "Load of slot {} may observe its Undef seed (not must-overwritten on all paths)",
                                    slot.index()
                                ),
                            });
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // Every Undef seed survived: all are provably-dead memory-merge seeds.
    Ok(seed_slot.keys().copied().collect())
}

/// The EXIT non-poison set of a block, given its ENTRY non-poison set. Applies
/// the in-order transfer (a non-Undef Store defines a seeded slot; an Undef-seed
/// Store re-poisons it). Loads do not change the state (they are checked in the
/// final validation pass, not here). `undef_seeds` is the GLOBAL set of `Undef`
/// result ValueIds so a poison-seed Store is recognized regardless of which
/// block defines the seed.
fn transfer_block_exit(
    block: &trust_ir::Block,
    entry: &std::collections::HashSet<ValueId>,
    seeded_slots: &std::collections::HashSet<ValueId>,
    undef_seeds: &std::collections::HashSet<ValueId>,
) -> std::collections::HashSet<ValueId> {
    let mut cur = entry.clone();
    for node in &block.body {
        if let Inst::Store { ptr, value, .. } = &node.inst {
            // The pointer is a slot only if it is one of the seeded slots (every
            // seeded slot is an Alloca result by construction). A Store to a
            // non-seeded pointer never changes a seeded slot's state.
            if seeded_slots.contains(ptr) {
                if undef_seeds.contains(value) {
                    cur.remove(ptr);
                } else {
                    cur.insert(*ptr);
                }
            }
        }
    }
    cur
}

/// Narrow an i128 immediate to the LIR `i64` immediate carrier, fail-closed on
/// values that do not fit (wide i128 constants need `Iconst128`, out of slice).
fn i128_to_i64(v: i128, name: &str) -> Result<i64, ModuleLirError> {
    i64::try_from(v).map_err(|_| ModuleLirError::UnsupportedConstant { name: name.to_string() })
}

#[cfg(test)]
mod tests {
    use trust_ir::Block;
    use trust_ir::inst::ICmpOp;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::FuncTy;
    use trust_ir::value::{BlockId, FuncId, FuncTyId};

    use super::*;

    /// Build a single-block 2-arg i32 function whose body is `body`. The entry
    /// block carries the two args as params (the canonical well-formed shape).
    fn module_with_body(name: &str, returns: Vec<Ty>, body: Vec<InstrNode>) -> Module {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns,
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::I32));
        block.params.push((ValueId::new(1), Ty::I32));
        block.body = body;
        f.blocks.push(block);
        module.functions.push(f);
        module
    }

    #[test]
    fn maps_const_add_icmp_return() {
        // %2 = const 1; %3 = add %0, %2; %4 = icmp slt %3, %1; (cmp consumes,
        // but we just return %3 to keep a single i32 result)
        let body = vec![
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(1) })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: ValueId::new(3),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }),
        ];
        let module = module_with_body("ok", vec![Ty::I32], body);
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("scalar core maps");
        assert_eq!(lir.name, "ok");
        assert_eq!(lir.signature.params, vec![LirType::I32, LirType::I32]);
        assert_eq!(lir.signature.returns, vec![LirType::I32]);
        let block = lir.blocks.get(&Block(0)).expect("entry block");
        // Iconst, Iadd, Icmp, Return.
        assert_eq!(block.instructions.len(), 4);
        assert!(matches!(block.instructions[0].opcode, Opcode::Iconst { .. }));
        assert!(matches!(block.instructions[1].opcode, Opcode::Iadd));
        assert!(matches!(block.instructions[2].opcode, Opcode::Icmp { .. }));
        assert!(matches!(block.instructions[3].opcode, Opcode::Return));
    }

    #[test]
    fn maps_i32_signed_division() {
        // The bare `Inst::BinOp { SDiv }` now maps 1:1 to the LIR `Sdiv`. The
        // div-by-zero / overflow GUARDS are separate producer-emitted nodes
        // (`ICmp` + `Assert` + `Br`) lowered by the existing Assert/Brif/Trap
        // machinery — see `module_to_lir_divrem_proven_output.rs` for the real
        // guarded bridge shape proven over the emitted bytes.
        let body = vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::SDiv,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        let module = module_with_body("div", vec![Ty::I32], body);
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("i32 sdiv maps");
        let block = lir.blocks.get(&Block(0)).expect("entry block");
        assert!(matches!(block.instructions[0].opcode, Opcode::Sdiv));
        assert!(matches!(block.instructions[1].opcode, Opcode::Return));
    }

    #[test]
    fn maps_u32_unsigned_remainder() {
        let body = vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::URem,
                ty: Ty::U32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        // The bare URem result is U32; the helper's entry params are I32, but the
        // BinOp operand width is taken from its own `ty` (U32 -> I32 LIR carrier),
        // and the return type is the single U32.
        let module = module_with_body("rem", vec![Ty::U32], body);
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("u32 urem maps");
        let block = lir.blocks.get(&Block(0)).expect("entry block");
        assert!(matches!(block.instructions[0].opcode, Opcode::Urem));
    }

    #[test]
    fn fail_closed_on_i128_division() {
        // i128 div/rem is libcall-routed in the AArch64 ISel (outside the
        // proven-bytes envelope), so it stays FAIL-CLOSED.
        let body = vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::SDiv,
                ty: Ty::I128,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        let module = module_with_body("div128", vec![Ty::I128], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedBinOp { op: "sdiv", .. })
        ));
    }

    #[test]
    fn shift_ops_map_to_lir_opcodes() {
        // i32/i64 shifts MAP: Shl -> Ishl, LShr -> Ushr (logical), AShr -> Sshr
        // (arithmetic). The shift-amount-in-range guard is a separate Assert node
        // lowered by the existing Assert/Br machinery; under the resulting
        // amount<width precondition the AArch64-masked register shift equals the
        // guarded shift (see `map_int_binop` SOUNDNESS).
        for (op, want) in
            [(BinOp::Shl, Opcode::Ishl), (BinOp::LShr, Opcode::Ushr), (BinOp::AShr, Opcode::Sshr)]
        {
            let body = vec![
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: Ty::I32,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
            ];
            let module = module_with_body("shift", vec![Ty::I32], body);
            let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("i32 shift maps");
            let block = lir.blocks.get(&Block(0)).expect("entry block");
            assert_eq!(block.instructions[0].opcode, want, "{op:?} must map to {want:?}");
        }
    }

    #[test]
    fn fail_closed_on_i128_shift() {
        // i128 shifts route through a multi-register AArch64 sequence (outside
        // the proven single-instruction shift envelope), so they FAIL CLOSED.
        for op in [BinOp::Shl, BinOp::LShr, BinOp::AShr] {
            let body = vec![
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: Ty::I128,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
            ];
            let module = module_with_body("shift128", vec![Ty::I128], body);
            assert!(
                matches!(
                    lower_module_to_lir(&module, FuncId::new(0)),
                    Err(ModuleLirError::UnsupportedBinOp { .. })
                ),
                "i128 {op:?} must fail closed"
            );
        }
    }

    /// The MIR-faithful checked-add idiom: Overflow -> [res, ovf], a Select
    /// negation, and a no-overflow Assert. Maps to CheckedSadd + Select + a
    /// Brif-to-Trap block split, with all prior arithmetic preserved.
    fn checked_add_idiom_body(op: OverflowOp, ty: Ty) -> Vec<InstrNode> {
        vec![
            // %2,%3 = <op>.overflow %0, %1
            InstrNode::new(Inst::Overflow { op, ty, lhs: ValueId::new(0), rhs: ValueId::new(1) })
                .with_results([ValueId::new(2), ValueId::new(3)]),
            // %4 = const false ; %5 = const true
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(ValueId::new(5)),
            // %6 = select %3 ? %4 : %5  (== !overflowed)
            InstrNode::new(Inst::Select {
                ty: Ty::Bool,
                cond: ValueId::new(3),
                then_val: ValueId::new(4),
                else_val: ValueId::new(5),
            })
            .with_result(ValueId::new(6)),
            // assert %6
            InstrNode::new(Inst::Assert { cond: ValueId::new(6) }),
            // return %2
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ]
    }

    #[test]
    fn maps_checked_add_overflow_idiom_i32() {
        let module = module_with_body(
            "cadd",
            vec![Ty::I32],
            checked_add_idiom_body(OverflowOp::AddOverflow, Ty::I32),
        );
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("checked-add idiom maps");

        // The lowered LIR must carry exactly one CheckedSadd, one Select, one
        // Brif (the assert), and one Trap (the shared trap block).
        let mut checked = 0;
        let mut select = 0;
        let mut brif = 0;
        let mut trap = 0;
        for block in lir.blocks.values() {
            for inst in &block.instructions {
                match inst.opcode {
                    Opcode::CheckedSadd => checked += 1,
                    Opcode::Select { .. } => select += 1,
                    Opcode::Brif { .. } => brif += 1,
                    Opcode::Trap => trap += 1,
                    _ => {}
                }
            }
        }
        assert_eq!(checked, 1, "exactly one CheckedSadd");
        assert_eq!(select, 1, "exactly one Select (!overflowed)");
        assert_eq!(brif, 1, "exactly one Brif (overflow assert)");
        assert_eq!(trap, 1, "exactly one Trap (shared trap block)");

        // The CheckedSadd must bind two results [value, overflow_b1].
        let value_op = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .find(|i| matches!(i.opcode, Opcode::CheckedSadd))
            .expect("CheckedSadd present");
        assert_eq!(value_op.results.len(), 2, "CheckedSadd binds [value, overflow_b1]");
    }

    #[test]
    fn maps_checked_add_unsigned_to_uadd() {
        let module = module_with_body(
            "uadd",
            vec![Ty::U32],
            checked_add_idiom_body(OverflowOp::AddOverflow, Ty::U32),
        );
        // module_with_body declares I32 params/entry; override the entry to U32
        // so the unsigned operand type flows through.
        let module = {
            let mut m = module;
            m.func_types[0].params = vec![Ty::U32, Ty::U32];
            m.functions[0].blocks[0].params =
                vec![(ValueId::new(0), Ty::U32), (ValueId::new(1), Ty::U32)];
            m
        };
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("unsigned checked-add maps");
        assert!(
            lir.blocks
                .values()
                .flat_map(|b| &b.instructions)
                .any(|i| matches!(i.opcode, Opcode::CheckedUadd)),
            "unsigned add.overflow must map to CheckedUadd"
        );
    }

    #[test]
    fn checked_mul_i32_widens_to_exact_i64_product() {
        // `CheckedSmul` lowers only at 64-bit, so a 32-bit signed checked mul is
        // lowered via EXACT i64 widening: two Sextend (i32->i64), an Imul, a
        // Trunc (i64->i32) for the value, and two range-violation Icmps OR'd into
        // the overflow flag — NOT the I64-only CheckedSmul. (See the proven-output
        // gate `module_to_lir_checked_mul_proven_output.rs`.)
        let module = module_with_body(
            "cmul32",
            vec![Ty::I32],
            checked_add_idiom_body(OverflowOp::MulOverflow, Ty::I32),
        );
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("i32 checked-mul widens");
        let (mut smul, mut imul, mut sext, mut trunc, mut bor, mut icmp) = (0, 0, 0, 0, 0, 0);
        for inst in lir.blocks.values().flat_map(|b| &b.instructions) {
            match inst.opcode {
                Opcode::CheckedSmul | Opcode::CheckedUmul => smul += 1,
                Opcode::Imul => imul += 1,
                Opcode::Sextend { .. } => sext += 1,
                Opcode::Trunc { .. } => trunc += 1,
                Opcode::Bor => bor += 1,
                Opcode::Icmp { .. } => icmp += 1,
                _ => {}
            }
        }
        assert_eq!(smul, 0, "i32 mul must NOT use the I64-only CheckedSmul");
        assert_eq!(imul, 1, "one i64 Imul for the widened product");
        assert_eq!(sext, 2, "two Sextend (i32->i64) for the signed operands");
        assert_eq!(trunc, 1, "one Trunc (i64->i32) for the wrapping value");
        assert_eq!(bor, 1, "one Bor combining the two range-violation compares");
        assert_eq!(icmp, 2, "two range-check Icmps (< i32::MIN, > i32::MAX)");
    }

    #[test]
    fn checked_mul_u32_widens_to_exact_i64_product_unsigned() {
        // 32-bit unsigned checked mul widens via Uextend + Imul + Trunc with a
        // SINGLE unsigned range check (> u32::MAX); no CheckedUmul.
        let module = module_with_body(
            "cmul32u",
            vec![Ty::U32],
            checked_add_idiom_body(OverflowOp::MulOverflow, Ty::U32),
        );
        let module = {
            let mut m = module;
            m.func_types[0].params = vec![Ty::U32, Ty::U32];
            m.functions[0].blocks[0].params =
                vec![(ValueId::new(0), Ty::U32), (ValueId::new(1), Ty::U32)];
            m
        };
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("u32 checked-mul widens");
        let (mut umul, mut imul, mut uext, mut trunc, mut bor, mut icmp) = (0, 0, 0, 0, 0, 0);
        for inst in lir.blocks.values().flat_map(|b| &b.instructions) {
            match inst.opcode {
                Opcode::CheckedSmul | Opcode::CheckedUmul => umul += 1,
                Opcode::Imul => imul += 1,
                Opcode::Uextend { .. } => uext += 1,
                Opcode::Trunc { .. } => trunc += 1,
                Opcode::Bor => bor += 1,
                Opcode::Icmp { .. } => icmp += 1,
                _ => {}
            }
        }
        assert_eq!(umul, 0, "u32 mul must NOT use the I64-only CheckedUmul");
        assert_eq!(imul, 1, "one i64 Imul for the widened product");
        assert_eq!(uext, 2, "two Uextend (u32->i64) for the unsigned operands");
        assert_eq!(trunc, 1, "one Trunc (i64->i32) for the wrapping value");
        assert_eq!(bor, 0, "unsigned needs a SINGLE range check, no Bor");
        assert_eq!(icmp, 1, "one unsigned range-check Icmp (> u32::MAX)");
    }

    #[test]
    fn fail_closed_on_checked_mul_i16() {
        // i16/i8 checked mul has no verified widening lowering yet (only i32/u32
        // is widened, i64/u64 uses the first-class op) — it must fail closed.
        let module = module_with_body(
            "cmul16",
            vec![Ty::I16],
            checked_add_idiom_body(OverflowOp::MulOverflow, Ty::I16),
        );
        let module = {
            let mut m = module;
            m.func_types[0].params = vec![Ty::I16, Ty::I16];
            m.func_types[0].returns = vec![Ty::I16];
            m.functions[0].blocks[0].params =
                vec![(ValueId::new(0), Ty::I16), (ValueId::new(1), Ty::I16)];
            m
        };
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedOverflow { .. })
        ));
    }

    #[test]
    fn fail_closed_on_checked_overflow_i128() {
        // 128-bit checked arithmetic has no verified flag/high-half ISel idiom.
        let module = module_with_body(
            "cadd128",
            vec![Ty::I32],
            checked_add_idiom_body(OverflowOp::AddOverflow, Ty::I128),
        );
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedOverflow { .. })
        ));
    }

    #[test]
    fn fail_closed_on_float_op() {
        let body = vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        // float param types alone already fail-close in the signature.
        let mut module = module_with_body("f", vec![Ty::F32], body);
        module.func_types[0].params = vec![Ty::F32, Ty::F32];
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedType { .. })
        ));
    }

    #[test]
    fn maps_integer_unary_not_and_neg() {
        // %2 = not %0 (Bnot) ; %3 = neg %2 (Ineg) ; return %3. The bare unary
        // nodes map 1:1 to the LIR integer-unary opcodes; the negation-overflow
        // guard (when present) is a separate producer-emitted Const/ICmp/Assert/Br
        // node group lowered by the existing machinery — see
        // `module_to_lir_unop_proven_output.rs` for the real guarded bridge shape
        // proven over the emitted bytes.
        let body = vec![
            InstrNode::new(Inst::UnOp { op: UnOp::Not, ty: Ty::I32, operand: ValueId::new(0) })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::UnOp { op: UnOp::Neg, ty: Ty::I32, operand: ValueId::new(2) })
                .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }),
        ];
        let module = module_with_body("un", vec![Ty::I32], body);
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("integer unary maps");
        let block = lir.blocks.get(&Block(0)).expect("entry block");
        // Bnot, Ineg, Return.
        assert_eq!(block.instructions.len(), 3);
        assert!(matches!(block.instructions[0].opcode, Opcode::Bnot));
        assert!(matches!(block.instructions[1].opcode, Opcode::Ineg));
        assert!(matches!(block.instructions[2].opcode, Opcode::Return));
        assert!(lir.stack_slots.is_empty(), "integer unary must materialize no memory");
    }

    #[test]
    fn fail_closed_on_float_unary_neg() {
        // A float `UnOp` (FNeg here) has no verified lowering — fail closed.
        let body = vec![
            InstrNode::new(Inst::UnOp { op: UnOp::FNeg, ty: Ty::F32, operand: ValueId::new(0) })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        // Float param/return types alone already fail-close in the signature, so
        // give the function an integer signature and only the BODY carries the
        // float unary, forcing the `map_int_unop` fail-closed path specifically.
        let module = module_with_body("fneg", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedType { .. })
                | Err(ModuleLirError::UnsupportedUnOp { .. })
        ));
    }

    #[test]
    fn fail_closed_on_i128_neg() {
        // i128 negate is a register-pair sequence outside the proven
        // single-instruction envelope — fail closed. Build a fully-i128 function
        // (params, return, and operand all i128) so the fail-close is on the
        // `map_int_unop` i128 arm, not a signature type mismatch.
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::I128],
            returns: vec![Ty::I128],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "neg128", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::I128));
        block.body = vec![
            InstrNode::new(Inst::UnOp { op: UnOp::Neg, ty: Ty::I128, operand: ValueId::new(0) })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        f.blocks.push(block);
        module.functions.push(f);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedUnOp { op: "neg", .. })
        ));
    }

    #[test]
    fn fail_closed_on_ctpop() {
        // CtPop has an LIR opcode but no proof carried here — fail closed.
        let body = vec![
            InstrNode::new(Inst::UnOp { op: UnOp::CtPop, ty: Ty::I32, operand: ValueId::new(0) })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        let module = module_with_body("ctpop", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedUnOp { op: "ctpop", .. })
        ));
    }

    #[test]
    fn fail_closed_on_nonlocal_pointer_load() {
        // A Load whose pointer is an INCOMING argument (%0), not an alloca-rooted
        // local pointer, must fail closed — the scalar-memory slice only reasons
        // about stack slots it allocated itself.
        let body = vec![
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        let module = module_with_body("ld", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::NonLocalPointer { value: 0, .. })
        ));
    }

    #[test]
    fn maps_alloca_store_load() {
        // %p = alloca i32 ; store %0 -> *%p ; %r = load *%p ; return %r
        // (an identity-through-memory round trip).
        let p = ValueId::new(2);
        let r = ValueId::new(3);
        let body = vec![
            InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: None }).with_result(p),
            InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: p,
                value: ValueId::new(0),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Load { ty: Ty::I32, ptr: p, volatile: false, align: None })
                .with_result(r),
            InstrNode::new(Inst::Return { values: vec![r] }),
        ];
        let module = module_with_body("mem_id", vec![Ty::I32], body);
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("scalar memory maps");
        // Exactly one stack slot (the i32 alloca), 4 bytes / 4-align.
        assert_eq!(lir.stack_slots.len(), 1);
        assert_eq!(lir.stack_slots[0].size, 4);
        let block = lir.blocks.get(&Block(0)).expect("entry block");
        // StackAddr, Store, Load, Return.
        assert_eq!(block.instructions.len(), 4);
        assert!(matches!(block.instructions[0].opcode, Opcode::StackAddr { slot: 0 }));
        assert!(matches!(block.instructions[1].opcode, Opcode::Store { .. }));
        assert!(matches!(block.instructions[2].opcode, Opcode::Load { .. }));
        assert!(matches!(block.instructions[3].opcode, Opcode::Return));
        // Store args are [value, ptr]; the ptr is the StackAddr's result.
        let stack_ptr = block.instructions[0].results[0];
        assert_eq!(block.instructions[1].args[1], stack_ptr);
        assert_eq!(block.instructions[2].args[0], stack_ptr);
    }

    #[test]
    fn fail_closed_on_counted_alloca() {
        let p = ValueId::new(2);
        let body = vec![
            InstrNode::new(Inst::Alloca { ty: Ty::I32, count: Some(ValueId::new(0)), align: None })
                .with_result(p),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
        ];
        let module = module_with_body("vla", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedMemory { .. })
        ));
    }

    #[test]
    fn admits_2field_scalar_aggregate_round_trip() {
        // UNBLOCKED (trust-ir pin c58fa68 added Ty::Tuple byte_size + aggregate
        // Store/Load round-trip): a 2-field scalar Tuple round-tripped through a
        // stack slot is now ADMITTED (per-field Str/Ldr at the C-style offsets).
        // sf(a,b) = { let t=(a,b); t.0+t.1 }, Const-aggregate base.
        let tup = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let body = vec![
            InstrNode::new(Inst::Const {
                ty: tup.clone(),
                value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::InsertField {
                ty: tup.clone(),
                aggregate: ValueId::new(2),
                field: 0,
                value: ValueId::new(0),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::InsertField {
                ty: tup.clone(),
                aggregate: ValueId::new(3),
                field: 1,
                value: ValueId::new(1),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Alloca { ty: tup.clone(), count: None, align: None })
                .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Store {
                ty: tup.clone(),
                ptr: ValueId::new(5),
                value: ValueId::new(4),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Load {
                ty: tup.clone(),
                ptr: ValueId::new(5),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: ValueId::new(6),
                field: 0,
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: ValueId::new(6),
                field: 1,
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(7),
                rhs: ValueId::new(8),
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(9)] }),
        ];
        let module = module_with_body("agg_ok", vec![Ty::I32], body);
        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("2-field scalar aggregate round trip must lower");
        // One aggregate slot, C-style sized (i32,i32) -> 8/4; two per-field
        // Stores and two per-field Loads.
        assert_eq!(lir.stack_slots.len(), 1);
        assert_eq!(lir.stack_slots[0].size, 8);
        assert_eq!(lir.stack_slots[0].align, 4);
        let stores = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
            .count();
        let loads = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Load { .. }))
            .count();
        assert_eq!(stores, 2, "two per-field stores");
        assert_eq!(loads, 2, "two per-field loads");
    }

    #[test]
    fn admits_3field_aggregate_alloca_layout() {
        // GENERALIZED (N-field slice): a 3-field scalar aggregate is now IN the
        // aggregate-memory slice. Its C-layout is reproduced 1:1 (three i32 fields
        // -> size 12, align 4), byte-for-byte the interpreter's `aggregate_layout`.
        // A bare Alloca (no round-trip) lowers to one sized slot; the full 3-field
        // round-trip + proven-output lives in
        // `module_to_lir_struct_mem_proven_output.rs`.
        let tup = Ty::Tuple(vec![Ty::I32, Ty::I32, Ty::I32]);
        let body = vec![
            InstrNode::new(Inst::Alloca { ty: tup, count: None, align: None })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
        ];
        let module = module_with_body("agg3", vec![Ty::I32], body);
        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("3-field scalar aggregate Alloca is now admitted (N-field slice)");
        assert_eq!(lir.stack_slots.len(), 1, "one aggregate slot");
        assert_eq!(lir.stack_slots[0].size, 12, "3-field i32 tuple C-layout size is 12");
        assert_eq!(lir.stack_slots[0].align, 4, "3-field i32 tuple C-layout align is 4");
    }

    #[test]
    fn fail_closed_on_nested_aggregate_field_alloca() {
        // A 2-field tuple whose field is ITSELF an aggregate has no reproducible
        // scalar C-layout in this slice -> fail closed (never lay out a nested
        // aggregate offset we cannot prove matches the interpreter).
        let tup = Ty::Tuple(vec![Ty::I32, Ty::Tuple(vec![Ty::I32, Ty::I32])]);
        let body = vec![
            InstrNode::new(Inst::Alloca { ty: tup, count: None, align: None })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
        ];
        let module = module_with_body("aggnest", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedAggregate { .. })
        ));
    }

    #[test]
    fn fail_closed_on_call() {
        // A Call to a NON-LOCAL callee (FuncId 1 absent from the module) is left
        // in place by the inliner; the converter then fail-closes on it.
        let body = vec![
            InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        let module = module_with_body("c", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedInst { inst: "Call", .. })
        ));
    }

    /// Build a 2-arg-i32 caller that calls a local pure leaf `add(x,y)=x+y` and
    /// then does `call_result + 1`. The caller is FuncId 0, the callee FuncId 1.
    fn caller_calls_add_module() -> Module {
        let mut module = Module::new("inl");
        // ty 0: caller (i32,i32)->i32 ; ty 1: callee add (i32,i32)->i32
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        // callee add(x,y) = x + y   (FuncId 1, single pure leaf block).
        let mut add = IrFunction::new(FuncId::new(1), "add", FuncTyId::new(1), BlockId::new(0));
        let x = ValueId::new(10);
        let y = ValueId::new(11);
        let s = ValueId::new(12);
        let mut ab = Block::new(BlockId::new(0));
        ab.params.push((x, Ty::I32));
        ab.params.push((y, Ty::I32));
        ab.body.push(
            InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: x, rhs: y })
                .with_result(s),
        );
        ab.body.push(InstrNode::new(Inst::Return { values: vec![s] }));
        add.blocks.push(ab);

        // caller(a,b) = add(a,b) + 1   (FuncId 0).
        let mut caller =
            IrFunction::new(FuncId::new(0), "caller", FuncTyId::new(0), BlockId::new(0));
        let a = ValueId::new(0);
        let b = ValueId::new(1);
        let called = ValueId::new(2);
        let one = ValueId::new(3);
        let out = ValueId::new(4);
        let mut cb = Block::new(BlockId::new(0));
        cb.params.push((a, Ty::I32));
        cb.params.push((b, Ty::I32));
        cb.body.push(
            InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![a, b] })
                .with_result(called),
        );
        cb.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(1) }).with_result(one),
        );
        cb.body.push(
            InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: called, rhs: one })
                .with_result(out),
        );
        cb.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
        caller.blocks.push(cb);

        module.functions.push(caller);
        module.functions.push(add);
        module
    }

    #[test]
    fn inlines_local_pure_leaf_add() {
        let module = caller_calls_add_module();
        // The caller has a Call; the converter must succeed because the inliner
        // splices the pure leaf add inline and the result is call-free.
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("inlined call lowers");
        assert_eq!(lir.name, "caller");
        let block = lir.blocks.get(&Block(0)).expect("entry block");
        // No LIR call opcode survives (the call was inlined).
        for inst in &block.instructions {
            assert!(
                !matches!(inst.opcode, Opcode::Call { .. } | Opcode::CallIndirect),
                "a call opcode survived inlining: {:?}",
                inst.opcode
            );
        }
        // The body must contain the inlined add (Iadd from add) AND the caller's
        // own Iadd (+1): at least two Iadds.
        let iadds = block.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Iadd)).count();
        assert!(iadds >= 2, "expected >= 2 Iadd (inlined add + caller +1), got {iadds}");
    }

    #[test]
    fn inliner_pre_pass_removes_the_call_node() {
        // White-box: the pre-pass output has zero Call insts in the caller body.
        let module = caller_calls_add_module();
        let caller = module.function_by_id(FuncId::new(0)).unwrap();
        let inlined = inline_local_pure_leaf_calls(&module, caller, false).expect("pre-pass ok");
        let calls =
            inlined.blocks[0].body.iter().filter(|n| matches!(n.inst, Inst::Call { .. })).count();
        assert_eq!(calls, 0, "inliner left a Call node in the caller body");
    }

    #[test]
    fn fail_closed_on_recursive_call() {
        // A self-recursive call (callee == caller) is NOT admissible -> left in
        // place -> converter fail-closes.
        let mut module = Module::new("rec");
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "rec", FuncTyId::new(0), BlockId::new(0));
        let mut bb = Block::new(BlockId::new(0));
        bb.params.push((ValueId::new(0), Ty::I32));
        bb.params.push((ValueId::new(1), Ty::I32));
        bb.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
        );
        bb.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }));
        f.blocks.push(bb);
        module.functions.push(f);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedInst { inst: "Call", .. })
        ));
    }

    #[test]
    fn fail_closed_on_non_leaf_callee() {
        // The callee itself CALLS a third function -> non-leaf -> not inlined ->
        // converter fail-closes on the surviving Call in the caller.
        let mut module = Module::new("nonleaf");
        for _ in 0..3 {
            module.func_types.push(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                is_vararg: false,
            });
        }
        // FuncId 2: a leaf the middle callee calls.
        let mut leaf = IrFunction::new(FuncId::new(2), "leaf", FuncTyId::new(2), BlockId::new(0));
        let mut lb = Block::new(BlockId::new(0));
        lb.params.push((ValueId::new(20), Ty::I32));
        lb.params.push((ValueId::new(21), Ty::I32));
        lb.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(20)] }));
        leaf.blocks.push(lb);

        // FuncId 1: the (non-leaf) callee that itself calls FuncId 2.
        let mut mid = IrFunction::new(FuncId::new(1), "mid", FuncTyId::new(1), BlockId::new(0));
        let mut mb = Block::new(BlockId::new(0));
        mb.params.push((ValueId::new(10), Ty::I32));
        mb.params.push((ValueId::new(11), Ty::I32));
        mb.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(2),
                args: vec![ValueId::new(10), ValueId::new(11)],
            })
            .with_result(ValueId::new(12)),
        );
        mb.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(12)] }));
        mid.blocks.push(mb);

        // FuncId 0: caller calls the non-leaf mid.
        let mut caller =
            IrFunction::new(FuncId::new(0), "caller", FuncTyId::new(0), BlockId::new(0));
        let mut cb = Block::new(BlockId::new(0));
        cb.params.push((ValueId::new(0), Ty::I32));
        cb.params.push((ValueId::new(1), Ty::I32));
        cb.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
        );
        cb.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }));
        caller.blocks.push(cb);

        module.functions.push(caller);
        module.functions.push(mid);
        module.functions.push(leaf);

        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedInst { inst: "Call", .. })
        ));
    }

    #[test]
    fn multi_block_condbr_lowers() {
        // bb0(a,b): %2 = icmp sgt a,b; condbr %2 -> bb1 else bb2
        // bb1: br bb3(a)
        // bb2: br bb3(b)
        // bb3(m): return m
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "mb_max", FuncTyId::new(0), BlockId::new(0));

        let a = ValueId::new(0);
        let b = ValueId::new(1);
        let cmp = ValueId::new(2);
        let m = ValueId::new(3);

        let mut bb0 = Block::new(BlockId::new(0));
        bb0.params.push((a, Ty::I32));
        bb0.params.push((b, Ty::I32));
        bb0.body.push(
            InstrNode::new(Inst::ICmp { op: ICmpOp::Sgt, ty: Ty::I32, lhs: a, rhs: b })
                .with_result(cmp),
        );
        bb0.body.push(InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        }));

        let mut bb1 = Block::new(BlockId::new(1));
        bb1.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![a] }));

        let mut bb2 = Block::new(BlockId::new(2));
        bb2.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![b] }));

        let mut bb3 = Block::new(BlockId::new(3));
        bb3.params.push((m, Ty::I32));
        bb3.body.push(InstrNode::new(Inst::Return { values: vec![m] }));

        // NOTE: bb1/bb2 pass `a`/`b` directly into bb3's param; the join through
        // the CondBr's then_args/else_args is the merge under test.
        f.blocks.push(bb0);
        f.blocks.push(bb1);
        f.blocks.push(bb2);
        f.blocks.push(bb3);
        module.functions.push(f);

        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("multi-block lowers");
        assert_eq!(lir.name, "mb_max");
        // Entry, bb1, bb2, bb3 are all present (4 real blocks; bb3 has a param
        // so the CondBr edges into it are split, adding trampolines).
        assert!(lir.blocks.len() >= 4, "expected >= 4 blocks, got {}", lir.blocks.len());
        // bb0 must end in a Brif.
        let bb0 = lir.blocks.get(&Block(0)).expect("entry");
        assert!(matches!(bb0.instructions.last().unwrap().opcode, Opcode::Brif { .. }));
        // bb3 must carry exactly one LIR block param (the merged value).
        let bb3 = lir.blocks.get(&Block(3)).expect("join");
        assert_eq!(bb3.params.len(), 1);
        assert!(matches!(bb3.instructions.last().unwrap().opcode, Opcode::Return));
    }

    #[test]
    fn fail_closed_on_missing_branch_target() {
        let mut module = module_with_body(
            "mb",
            vec![Ty::I32],
            // br to a block that doesn't exist
            vec![InstrNode::new(Inst::Br { target: BlockId::new(9), args: vec![] })],
        );
        // The single block now ends in Br -> missing target.
        let _ = &mut module;
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::MissingBlock { target: 9, .. })
        ));
    }

    #[test]
    fn fail_closed_on_undefined_value() {
        // Return a value (99) that was never defined.
        let body = vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(99)] })];
        let module = module_with_body("u", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UndefinedValue { value: 99, .. })
        ));
    }

    #[test]
    fn fail_closed_on_missing_function() {
        let module = module_with_body(
            "x",
            vec![Ty::I32],
            vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] })],
        );
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(7)),
            Err(ModuleLirError::MissingFunction(7))
        ));
    }

    // =======================================================================
    // DEAD-UNDEF-SEED merge (the REAL VF->Module control-flow merge shape).
    // =======================================================================

    /// Build the producer-faithful Undef-seeded memory merge for
    /// `mx(a,b) = if a>b {a} else {b}`:
    ///   bb0: %4=undef i32; %5=alloca i32; store %4->*%5; %6=icmp sgt a,b;
    ///        condbr %6 -> bb1 else bb2
    ///   bb1: %9=copy a;  store %9 ->*%5; br bb3
    ///   bb2: %10=copy b; store %10->*%5; br bb3
    ///   bb3: %11=load *%5; return %11
    fn undef_merge_max_module() -> Module {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "mx", FuncTyId::new(0), BlockId::new(0));
        let (a, b) = (ValueId::new(0), ValueId::new(1));
        let seed = ValueId::new(4);
        let slot = ValueId::new(5);
        let cmp = ValueId::new(6);
        let tv = ValueId::new(9);
        let ev = ValueId::new(10);
        let loaded = ValueId::new(11);

        let mut bb0 = Block::new(BlockId::new(0));
        bb0.params.push((a, Ty::I32));
        bb0.params.push((b, Ty::I32));
        bb0.body.push(InstrNode::new(Inst::Undef { ty: Ty::I32 }).with_result(seed));
        bb0.body.push(
            InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: None })
                .with_result(slot),
        );
        bb0.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: slot,
            value: seed,
            volatile: false,
            align: None,
        }));
        bb0.body.push(
            InstrNode::new(Inst::ICmp { op: ICmpOp::Sgt, ty: Ty::I32, lhs: a, rhs: b })
                .with_result(cmp),
        );
        bb0.body.push(InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        }));

        let mut bb1 = Block::new(BlockId::new(1));
        bb1.body.push(InstrNode::new(Inst::Copy { ty: Ty::I32, operand: a }).with_result(tv));
        bb1.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: slot,
            value: tv,
            volatile: false,
            align: None,
        }));
        bb1.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![] }));

        let mut bb2 = Block::new(BlockId::new(2));
        bb2.body.push(InstrNode::new(Inst::Copy { ty: Ty::I32, operand: b }).with_result(ev));
        bb2.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: slot,
            value: ev,
            volatile: false,
            align: None,
        }));
        bb2.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![] }));

        let mut bb3 = Block::new(BlockId::new(3));
        bb3.body.push(
            InstrNode::new(Inst::Load { ty: Ty::I32, ptr: slot, volatile: false, align: None })
                .with_result(loaded),
        );
        bb3.body.push(InstrNode::new(Inst::Return { values: vec![loaded] }));

        f.blocks.push(bb0);
        f.blocks.push(bb1);
        f.blocks.push(bb2);
        f.blocks.push(bb3);
        module.functions.push(f);
        module
    }

    #[test]
    fn lowers_dead_undef_seed_memory_merge() {
        // The producer's real merge (Undef seed, overwritten on both arms) must
        // lower: the Undef becomes a defined Iconst 0, the merge flows through the
        // stack slot, and a real Brif drives the branch.
        let module = undef_merge_max_module();
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("dead-undef merge lowers");
        // Exactly one stack slot (the i32 merge slot).
        assert_eq!(lir.stack_slots.len(), 1);
        // The Undef seed materialized as an Iconst (its only consumer is the dead
        // seed Store, overwritten before the join Load).
        let iconsts = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Iconst { .. }))
            .count();
        assert!(iconsts >= 1, "the Undef seed must lower to a defined Iconst, got {iconsts}");
        // A real conditional branch survives.
        assert!(
            lir.blocks
                .values()
                .flat_map(|b| &b.instructions)
                .any(|i| matches!(i.opcode, Opcode::Brif { .. })),
            "the diamond must lower to a Brif"
        );
        // No poison: every value the slot can yield is a real Store/Load chain.
        let loads = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Load { .. }))
            .count();
        assert_eq!(loads, 1, "exactly one join Load");
    }

    #[test]
    fn fail_closed_on_undef_read_into_strict_op() {
        // An Undef whose value is READ into a BinOp (not merely a dead seed Store)
        // could be observed while poison -> MUST fail closed.
        //   %2 = undef i32 ; %3 = add a, %2 ; return %3
        let body = vec![
            InstrNode::new(Inst::Undef { ty: Ty::I32 }).with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }),
        ];
        let module = module_with_body("undef_read", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedUndef { .. })
        ));
    }

    #[test]
    fn fail_closed_on_undef_returned_directly() {
        // An Undef returned directly (read into Return) -> fail closed.
        let body = vec![
            InstrNode::new(Inst::Undef { ty: Ty::I32 }).with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        let module = module_with_body("undef_ret", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedUndef { .. })
        ));
    }

    #[test]
    fn fail_closed_on_undef_seed_loaded_without_overwrite() {
        // A slot seeded with Undef and then LOADED without an intervening
        // overwrite: the poison seed is observable -> fail closed.
        //   %2 = undef i32 ; %3 = alloca i32 ; store %2 -> *%3 ;
        //   %4 = load *%3 ; return %4
        let seed = ValueId::new(2);
        let slot = ValueId::new(3);
        let loaded = ValueId::new(4);
        let body = vec![
            InstrNode::new(Inst::Undef { ty: Ty::I32 }).with_result(seed),
            InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: None })
                .with_result(slot),
            InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: slot,
                value: seed,
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Load { ty: Ty::I32, ptr: slot, volatile: false, align: None })
                .with_result(loaded),
            InstrNode::new(Inst::Return { values: vec![loaded] }),
        ];
        let module = module_with_body("undef_loaded", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedUndef { .. })
        ));
    }

    #[test]
    fn fail_closed_on_undef_seed_overwritten_on_only_one_arm() {
        // A diamond where ONLY the then-arm overwrites the slot; the else-arm
        // leaves the Undef seed live to the join Load -> NOT must-overwritten on
        // all paths -> fail closed (the poison could be observed on the else path).
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "one_arm", FuncTyId::new(0), BlockId::new(0));
        let (a, b) = (ValueId::new(0), ValueId::new(1));
        let seed = ValueId::new(4);
        let slot = ValueId::new(5);
        let cmp = ValueId::new(6);
        let tv = ValueId::new(9);
        let loaded = ValueId::new(11);

        let mut bb0 = Block::new(BlockId::new(0));
        bb0.params.push((a, Ty::I32));
        bb0.params.push((b, Ty::I32));
        bb0.body.push(InstrNode::new(Inst::Undef { ty: Ty::I32 }).with_result(seed));
        bb0.body.push(
            InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: None })
                .with_result(slot),
        );
        bb0.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: slot,
            value: seed,
            volatile: false,
            align: None,
        }));
        bb0.body.push(
            InstrNode::new(Inst::ICmp { op: ICmpOp::Sgt, ty: Ty::I32, lhs: a, rhs: b })
                .with_result(cmp),
        );
        bb0.body.push(InstrNode::new(Inst::CondBr {
            cond: cmp,
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(2),
            else_args: vec![],
        }));

        // bb1 overwrites the slot; bb2 does NOT.
        let mut bb1 = Block::new(BlockId::new(1));
        bb1.body.push(InstrNode::new(Inst::Copy { ty: Ty::I32, operand: a }).with_result(tv));
        bb1.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: slot,
            value: tv,
            volatile: false,
            align: None,
        }));
        bb1.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![] }));

        let mut bb2 = Block::new(BlockId::new(2));
        bb2.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![] }));

        let mut bb3 = Block::new(BlockId::new(3));
        bb3.body.push(
            InstrNode::new(Inst::Load { ty: Ty::I32, ptr: slot, volatile: false, align: None })
                .with_result(loaded),
        );
        bb3.body.push(InstrNode::new(Inst::Return { values: vec![loaded] }));

        f.blocks.push(bb0);
        f.blocks.push(bb1);
        f.blocks.push(bb2);
        f.blocks.push(bb3);
        module.functions.push(f);

        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedUndef { .. })
        ));
    }

    #[test]
    fn fail_closed_on_non_scalar_undef() {
        // A tuple-typed Undef that is NOT built into a checked-arith (value,
        // overflow) pair by any InsertField is not the decomposable idiom — it
        // is a bare aggregate poison seed and must fail closed (a tuple is never
        // materialized in memory, and an unbuilt seed carries no scalar fields).
        let body = vec![
            InstrNode::new(Inst::Undef { ty: Ty::Tuple(vec![Ty::I32, Ty::Bool]) })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
        ];
        let module = module_with_body("undef_tuple", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedUndef { .. })
        ));
    }

    /// Build the REAL bridge checked-arith TUPLE idiom (verified against
    /// `trust_ir_bridge::lower_to_trust_ir` on a `CheckedBinaryOp` VF): an
    /// `Inst::Overflow -> [value, flag]`, a `Tuple([Int,Bool])` `Undef` seed,
    /// two `InsertField`s (field 0 = value, field 1 = flag), an `ExtractField`
    /// of the flag, an `ICmp Eq(flag, false)` = `ok`, an `assert ok`, then in a
    /// second block an `ExtractField` of the value and `return`. Two blocks so
    /// the tuple decompose is exercised CROSS-block (the value read is in bb1).
    fn bridge_checked_add_tuple_module(op: OverflowOp, ty: Ty) -> Module {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![ty.clone()],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "add", FuncTyId::new(0), BlockId::new(0));
        let tuple_ty = Ty::Tuple(vec![ty.clone(), Ty::Bool]);
        let a = ValueId::new(0);
        let b = ValueId::new(1);
        let (val, flag) = (ValueId::new(4), ValueId::new(5));
        let (seed, ins0, ins1) = (ValueId::new(6), ValueId::new(7), ValueId::new(8));
        let (ef_flag, c_false, ok) = (ValueId::new(9), ValueId::new(10), ValueId::new(11));
        let (ef_val, copied) = (ValueId::new(12), ValueId::new(13));

        let mut bb0 = Block::new(BlockId::new(0));
        bb0.params.push((a, ty.clone()));
        bb0.params.push((b, ty.clone()));
        bb0.body.push(
            InstrNode::new(Inst::Overflow { op, ty: ty.clone(), lhs: a, rhs: b })
                .with_results([val, flag]),
        );
        bb0.body.push(InstrNode::new(Inst::Undef { ty: tuple_ty.clone() }).with_result(seed));
        bb0.body.push(
            InstrNode::new(Inst::InsertField {
                ty: tuple_ty.clone(),
                aggregate: seed,
                field: 0,
                value: val,
            })
            .with_result(ins0),
        );
        bb0.body.push(
            InstrNode::new(Inst::InsertField {
                ty: tuple_ty.clone(),
                aggregate: ins0,
                field: 1,
                value: flag,
            })
            .with_result(ins1),
        );
        bb0.body.push(
            InstrNode::new(Inst::ExtractField { ty: Ty::Bool, aggregate: ins1, field: 1 })
                .with_result(ef_flag),
        );
        bb0.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                .with_result(c_false),
        );
        bb0.body.push(
            InstrNode::new(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::Bool, lhs: ef_flag, rhs: c_false })
                .with_result(ok),
        );
        bb0.body.push(InstrNode::new(Inst::Assert { cond: ok }));
        bb0.body.push(InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![] }));

        let mut bb1 = Block::new(BlockId::new(1));
        bb1.body.push(
            InstrNode::new(Inst::ExtractField { ty: ty.clone(), aggregate: ins1, field: 0 })
                .with_result(ef_val),
        );
        bb1.body.push(
            InstrNode::new(Inst::Copy { ty: ty.clone(), operand: ef_val }).with_result(copied),
        );
        bb1.body.push(InstrNode::new(Inst::Return { values: vec![copied] }));

        f.blocks.push(bb0);
        f.blocks.push(bb1);
        module.functions.push(f);
        module
    }

    #[test]
    fn decomposes_bridge_checked_add_tuple_i32() {
        let module = bridge_checked_add_tuple_module(OverflowOp::AddOverflow, Ty::I32);
        let lir =
            lower_module_to_lir(&module, FuncId::new(0)).expect("bridge tuple idiom decomposes");

        // NO tuple is materialized in memory: there must be ZERO stack slots.
        assert!(lir.stack_slots.is_empty(), "tuple decompose materializes no memory");

        // Exactly one CheckedSadd, one Brif (the assert), one Trap, one Icmp.
        let mut checked = 0;
        let mut brif = 0;
        let mut trap = 0;
        let mut icmp = 0;
        let mut copy = 0;
        for block in lir.blocks.values() {
            for inst in &block.instructions {
                match inst.opcode {
                    Opcode::CheckedSadd => checked += 1,
                    Opcode::Brif { .. } => brif += 1,
                    Opcode::Trap => trap += 1,
                    Opcode::Icmp { .. } => icmp += 1,
                    Opcode::Copy => copy += 1,
                    _ => {}
                }
            }
        }
        assert_eq!(checked, 1, "one CheckedSadd from the Overflow");
        assert_eq!(brif, 1, "one Brif (overflow assert)");
        assert_eq!(trap, 1, "one Trap (shared trap block)");
        assert_eq!(icmp, 1, "one Icmp (ok = flag == false)");
        // Two ExtractFields -> two Copy decompositions (flag + value); the trust_ir
        // `Inst::Copy` of the value is a third.
        assert!(copy >= 2, "ExtractFields decompose to Copy of the field Values");

        // The CheckedSadd binds [value, overflow_b1].
        let value_op = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .find(|i| matches!(i.opcode, Opcode::CheckedSadd))
            .expect("CheckedSadd present");
        assert_eq!(value_op.results.len(), 2, "CheckedSadd binds [value, overflow_b1]");
    }

    #[test]
    fn decomposes_bridge_checked_add_tuple_unsigned() {
        let module = {
            let mut m = bridge_checked_add_tuple_module(OverflowOp::AddOverflow, Ty::U32);
            // The helper used I32 entry params; align them to U32.
            m.func_types[0].params = vec![Ty::U32, Ty::U32];
            m.functions[0].blocks[0].params =
                vec![(ValueId::new(0), Ty::U32), (ValueId::new(1), Ty::U32)];
            m
        };
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("unsigned tuple decomposes");
        assert!(
            lir.blocks
                .values()
                .flat_map(|b| &b.instructions)
                .any(|i| matches!(i.opcode, Opcode::CheckedUadd)),
            "unsigned bridge tuple add maps to CheckedUadd"
        );
    }

    #[test]
    fn fail_closed_on_extractfield_of_undefined_tuple_field() {
        // A tuple seed built ONLY at field 0, then ExtractField field 1 (never
        // defined) must fail closed — reading field 1 would observe the Undef.
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut f = IrFunction::new(FuncId::new(0), "bad", FuncTyId::new(0), BlockId::new(0));
        let tuple_ty = Ty::Tuple(vec![Ty::I32, Ty::Bool]);
        let mut bb0 = Block::new(BlockId::new(0));
        bb0.params.push((ValueId::new(0), Ty::I32));
        bb0.params.push((ValueId::new(1), Ty::I32));
        bb0.body.push(
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_results([ValueId::new(4), ValueId::new(5)]),
        );
        bb0.body.push(
            InstrNode::new(Inst::Undef { ty: tuple_ty.clone() }).with_result(ValueId::new(6)),
        );
        bb0.body.push(
            InstrNode::new(Inst::InsertField {
                ty: tuple_ty.clone(),
                aggregate: ValueId::new(6),
                field: 0,
                value: ValueId::new(4),
            })
            .with_result(ValueId::new(7)),
        );
        // Read field 1 (never defined).
        bb0.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Bool,
                aggregate: ValueId::new(7),
                field: 1,
            })
            .with_result(ValueId::new(8)),
        );
        bb0.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(4)] }));
        f.blocks.push(bb0);
        module.functions.push(f);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedAggregate { .. })
        ));
    }
}
