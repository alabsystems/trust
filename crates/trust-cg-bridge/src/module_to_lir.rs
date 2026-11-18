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
//! **Superseded 2026-09-30 (plan §5 fail-open item 1):** that trap is not Rust's
//! panic (no message, no hook, SIGTRAP), so every function whose lowered body
//! carries an `Assert` is now refused by name —
//! [`ModuleLirError::ImplicitPanicUnfaithful`], predicate
//! [`function_has_unfaithful_assert`] — and the guarded shapes above lower only
//! once the guard is absent (e.g. `-Coverflow-checks=off` for overflow/shift).
//!
//! MEMORY: scalar stack slots (`Alloca`/`Load`/`Store`/single-index `GEP`) over
//! fixed-width integers, AND — unblocked by the trust-ir pin c58fa68 (`Ty::Tuple`
//! `byte_size`/`byte_align` + the aggregate Store/Load round-trip) — a WHOLE
//! N-field scalar `Ty::Tuple`, or a `Ty::Struct` whose `StructDef` the module
//! resolves, round-tripped through ONE aggregate stack slot (the shape the bridge
//! promotes a multi-block-written tuple or struct local to). The
//! aggregate is DECOMPOSED into its per-field scalars and lowered to per-field
//! Str/Ldr at the field offsets of the interpreter's own layout of the type
//! (`aggregate_mem_layout`, CG-DECLARED-LAYOUT-1): a declared `StructDef`
//! size/align/offset triple or `Module::tuple_layouts` descriptor read and
//! re-validated, and the declaration-order `aggregate_layout` only for a type
//! that declares none. A slot is only ever stored and loaded WHOLE at its own
//! type, or through a FIELD POINTER of a `Ty::Struct` slot: a `gep i8` at a
//! constant that starts exactly one field in that layout, used only as the
//! pointer of a non-volatile Load/Store at that field's type (PASS 1.7 step 1b,
//! F1-FIELD-POINTER-AGREEMENT-1). Every
//! unmapped `Inst` (calls,
//! nested aggregates, floats, casts, i128 div/rem, i128 shifts, ...)
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
    AbiSretParam, BasicBlock as LirBlock, Function as LirFunction, Signature, StackSlotInfo,
};
use trust_cg_lower::instructions::{Block, DirectCallBinding, Instruction, IntCC, Opcode, Value};
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

    /// A transformation cannot reserve another fresh identifier without
    /// overflowing its u32 space. Refuse before any wrapped id can alias one
    /// already present in the source function or a previous splice.
    #[error("function `{name}` exhausts fresh {space} identifiers")]
    FreshIdExhausted { name: String, space: &'static str },

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

    /// A `Switch`'s integer case constants cannot be put in the form the LIR
    /// switch lowering compares against for this selector (a 128-bit selector,
    /// a non-integer selector, a selector with no recorded LIR type, or two
    /// case constants that denote one selector value). See
    /// `mapping::encode_switch_case` for the encoding contract.
    #[error("function `{name}` switch cases cannot be encoded for its selector: {detail}")]
    UnencodableSwitchCase { name: String, detail: String },

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

    /// An `Inst` variant outside the converter's mapped fragment. The
    /// discriminant name is reported so the caller can see exactly which shape
    /// forced the fail-closed exit. (A residual `Call` here means the inliner
    /// declined every splice for it: non-local / body-less / recursive /
    /// non-flattenable callee — see `inline_local_pure_leaf_calls`.)
    #[error(
        "unsupported instruction `{inst}` in `{name}` (outside the converter's mapped fragment)"
    )]
    UnsupportedInst { name: String, inst: &'static str },

    /// A `Producer::Clean` function reached the codegen consumer. Trust: the
    /// binding boundary "no codegen consumes a Clean-origin trust-ir row below
    /// tier `gate`" is enforced HERE, on the `Function` itself — never read off
    /// the Clean-origin disclosure `SpecModule`, whose `tier`/`body_gate`
    /// strings are claim-style prose this backend does not consult. Since plan
    /// step 3.4 a tier-`gate` row carries a Function-level carrier (the
    /// `clean-carrier-gate` stamp beside a session-ledger entry), but this
    /// converter honors none (it gets no new coverage, plan R-5; the carrier is
    /// admitted only on the `Compiler::compile` lane at step 3.6), so EVERY
    /// Clean-producer body is refused fail-closed, whether it is the function
    /// being lowered or a callee the inliner / real-call path would otherwise
    /// splice into a Rust caller's object, with or without a body.
    #[error(
        "Clean-origin trust-ir function `{name}` is not admitted to codegen ({detail}). This converter honors no Clean carrier: a tier-`gate` row's authenticated `clean-carrier-gate` license (plan step 3.4) is admitted only on F1's `Compiler::compile` lane (plan step 3.6), so the trust-ir codegen frontend refuses every `Producer::Clean` body fail-closed. Options: (1) keep the MIR lane, the sole value-producing path for Clean-origin bodies today; (2) for a tier-`gate` row, build on the `Compiler::compile` lane once plan step 3.6 admits it there; (3) if the body was reached through a Rust caller's IR-5 call edge, lower that caller on the MIR lane or keep the call outside the trust-ir-frontend unit"
    )]
    CleanOriginBelowCodegenGate { name: String, detail: String },

    /// A `GlobalAddr` named a module-global table entry that does not exist.
    #[error("function `{name}` references missing global id {global}")]
    MissingGlobal { name: String, global: u32 },

    /// A `BinOp`/`ICmp` sub-op outside the integer scalar core: an i128 shift
    /// (multi-register, outside the proven single-instruction shift envelope), an
    /// i128 div/rem (libcall-routed, outside the proven-bytes envelope), a
    /// Bool-only connective (`BAnd`/`BOr`/`BXor`) presented to this integer
    /// lane, or any float op. The i8..i64 shifts (`Shl`/`LShr`/`AShr`) ARE
    /// mapped — see [`map_int_binop`].
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
    /// value outside the explicitly admitted provenance sets: a local Alloca,
    /// a shared slice input (Load/GEP only), or an immutable assembled scalar
    /// global (direct Load only).
    #[error("function `{name}` memory op uses pointer value {value} with unsupported provenance")]
    NonLocalPointer { name: String, value: u32 },

    /// A memory shape outside the scalar-slot AND aggregate-slot slices: a
    /// pointer / float pointee, a counted (array/VLA) `Alloca`, a `GEP` that is
    /// not a single-index scalar-element address, or a partial / re-derived
    /// access into an aggregate slot. The scalar slice models fixed-width integer
    /// slots; the aggregate-memory slice (PASS 1.7, unblocked by the trust-ir pin
    /// c58fa68's `Ty::Tuple` `byte_size` + aggregate Store/Load round-trip) models
    /// a WHOLE 2-field scalar `Ty::Tuple` round-tripped through one slot via
    /// per-field Str/Ldr at the interpreter's field offsets; anything else fails
    /// closed.
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

    /// An aggregate (`Inst::ExtractField` / `Inst::InsertField` /
    /// `Inst::MakeAggregate`) shape outside the two decomposable aggregate
    /// slices: the BRIDGE's checked-arith result pair `Tuple([Int, Bool])`,
    /// DECOMPOSED into its two scalar SSA Values and never stored (PASS 1.6), and
    /// a scalar-field tuple or struct round-tripped whole through one stack slot
    /// (PASS 1.7). Since BMC-LANE-1 (2026-11-06) the bridge builds a complete
    /// aggregate of either kind with one `MakeAggregate`; the legacy spelling, a
    /// `Tuple`-typed `Undef` seed + one `InsertField` per field, is still
    /// decomposed. Any other aggregate FAILS CLOSED here — for example a checked
    /// pair stored to memory, a tuple-typed field or lane (a nested aggregate), a
    /// constructor whose lane count differs from its type's field count, a pair
    /// read before a field is defined, or an `InsertField` overwriting an
    /// already-defined pair field — so an aggregate the converter cannot
    /// decompose is never fabricated.
    #[error("unsupported aggregate shape in `{name}`: {detail}")]
    UnsupportedAggregate { name: String, detail: String },

    /// The module DECLARES `StructPassingPolicy::Unclassified` — "the producer
    /// performs NO aggregate classification, and says so" — and a by-value
    /// aggregate nonetheless crosses a call edge THIS lowering realizes, with no
    /// [`AbiPassModeCrossCheck`] attached to it.
    ///
    /// trust-ir's contract for that value is explicit, and it is a contract on
    /// the CONSUMER: *"A CONSUMER MUST NOT infer either scheme from it — it is a
    /// declaration of absence, not a third convention. A backend needing a
    /// classification must refuse the module rather than pick one."*
    ///
    /// This converter DOES need one: it classifies by-value aggregates by its own
    /// size/shape rules (`indirect_struct_sig`, `pair_struct_sig`,
    /// `newtype_struct_sig`, `pair_enum_sig`) and reads `ParamAttrs::sret` that an
    /// `Unclassified` producer never emits (`sret_convention` then yields
    /// `abi_sret_param: None` and an EMPTY `sret_arg_callees` — faithful to the
    /// IR it was handed, and not a safety argument on its own). Admitting such a
    /// module would therefore be exactly the inference the contract forbids, and
    /// what it produces is not a refusal but a SILENT WRONG ABI: caller and callee
    /// each self-consistent, disagreeing with every LLVM-compiled neighbour. That
    /// is the class trust-cg measured and fixed in 822fdc69 / 67122610, where a
    /// `{i32,i32}` packed into one register made llvm x tcg exit 188 at `-O0`.
    ///
    /// The refusal is lifted by ATTACHING evidence, never by relaxing the check:
    /// see [`AbiPassModeCrossCheck`] and
    /// [`lower_module_to_lir_with_abi_cross_check`]. Under `Unclassified` that
    /// token is the ONLY admission for a by-value aggregate edge (trust-ir SPEC
    /// §17: a consumer places such a slot only from an authority outside the
    /// module), and it places the lowered function's OWN signature edge only —
    /// an aggregate on a `CallIndirect`'s declared `sig` is refused by this
    /// variant with a token attached too; the two declared policies refuse the
    /// same edges by their own variants, [`Self::NativeCAggregateAbiUnsupported`]
    /// and [`Self::AlwaysMemoryByValueAggregate`].
    #[error(
        "function `{name}`: the module declares `struct_passing = unclassified` (the producer \
         performs no aggregate classification, and says so), but {detail}. Lowering it would \
         require this backend to CHOOSE a classification, which trust-ir's contract for that \
         value forbids in terms — \"a backend needing a classification must refuse the module \
         rather than pick one\". Options: (1) ATTACH A PASS-MODE CROSS-CHECK to this lowering — \
         call `lower_module_to_lir_with_abi_cross_check` (or the \
         `lower_trust_ir_function_to_lir*_with_abi_cross_check` twins) from a consumer that has \
         already validated every aggregate argument and the return against the target's real \
         parameter passing modes, which is what the rustc driver does by running \
         `validate_codegen_instance_abi_trust_ir` (`rustc_codegen_trust_cg`) over rustc's own \
         `FnAbi` immediately before it lowers (a cross-check places the lowered function's OWN \
         signature edge only: an aggregate on an indirect call edge's declared signature stays \
         refused with one attached, and needs option (2) or (3)); (2) have the PRODUCER \
         pre-lower the crossing — pass the aggregate's address as a pointer parameter, and \
         return an aggregate through a leading `sret` pointer parameter with an empty return \
         list (read by `sret_convention`) \
         — because a pointer is not a by-value aggregate slot under any policy (a declared \
         `native_c` or `always_memory` policy does NOT admit a by-value aggregate here: this \
         converter implements no native-C aggregate ruleset, and `always_memory` means no such \
         slot exists); (3) keep aggregates off the call edge (scalarize the signature), which \
         makes the `unclassified` claim range over nothing and admits the module unchanged"
    )]
    UnclassifiedAggregateAbi { name: String, detail: String },

    /// The module DECLARES `StructPassingPolicy::NativeC` and a by-value
    /// aggregate crosses a call edge this lowering reads.
    ///
    /// Under `NativeC` it is the CONSUMER that classifies: each by-value
    /// aggregate slot crosses where the target's C ruleset for the edge's calling
    /// convention places it, and the producer claims the other side of every
    /// edge uses that placement (trust-ir SPEC §17, ratified 2026-09-27; "a
    /// consumer that implements no ruleset for an edge's convention refuses the
    /// slot"). This converter implements NO native-C aggregate ruleset. Its
    /// classifiers (`indirect_struct_sig`, `pair_struct_sig`,
    /// `newtype_struct_sig`, `pair_enum_sig`) are size/shape rules for rustc's
    /// own Rust ABI, and the only ABI authority they are ever held against is a
    /// pass-mode cross-check over rustc's `FnAbi`. The two ABIs disagree on real shapes
    /// (§17 measured an `F3 { f32; 3 }` passed `Indirect` by the Rust ABI and
    /// as an HFA by C on aarch64-apple-darwin, and `int32x4_t` `Indirect` vs
    /// `Direct`), so lowering a `NativeC` aggregate by these rules would place
    /// it where the module says nobody else does.
    ///
    /// An [`AbiPassModeCrossCheck`] does NOT lift this refusal: it attests
    /// rustc's placement for the lowered instance, which is not the C placement
    /// the module claims, so it cannot establish that the two agree. Before
    /// 2026-09-27 this converter admitted every `NativeC` module unchecked, on
    /// the retracted reading that the policy obliged the producer to mark
    /// `byval`/`sret` (no producer ever did).
    #[error(
        "function `{name}`: the module declares `struct_passing = native_c`, under which the \
         CONSUMER must place every by-value aggregate slot by the target's C ruleset for the \
         edge's calling convention (trust-ir SPEC §17), but {detail}. This converter implements \
         no native-C aggregate ruleset: its classifiers (`indirect_struct_sig`, \
         `pair_struct_sig`, `newtype_struct_sig`, `pair_enum_sig`) are shapes of rustc's own \
         Rust ABI, and the only ABI authority they are held against is a pass-mode cross-check \
         over rustc's `FnAbi` — which attests rustc's placement, not the C placement this \
         module claims, so no cross-check lifts this refusal. Options: (1) have the PRODUCER stamp \
         `unclassified` when it performed no C classification (the honest value for a rustc-ABI \
         producer) and lower with the pass-mode cross-check attached; (2) have the PRODUCER \
         pre-lower the crossing — a pointer parameter, and a leading `sret` pointer parameter \
         with an empty return list for a returned aggregate; (3) scalarize the signature; \
         (4) lower the module with a backend that implements the target's C aggregate ruleset"
    )]
    NativeCAggregateAbiUnsupported { name: String, detail: String },

    /// The module DECLARES `StructPassingPolicy::AlwaysMemory` and a by-value
    /// aggregate nonetheless crosses a call edge this lowering reads.
    ///
    /// `AlwaysMemory` states that every aggregate crossing is PRE-LOWERED, so no
    /// `FuncTy` of the module has a by-value aggregate slot at all (trust-ir
    /// SPEC §17, decided by `validate_module` as `AlwaysMemoryByValueAggregate`
    /// at the ratification the pinned trust-ir predates). A module carrying one
    /// contradicts its own policy, and no evidence from outside the module can
    /// reconcile a module with itself — so, unlike `Unclassified`, an
    /// [`AbiPassModeCrossCheck`] does NOT lift this refusal.
    #[error(
        "function `{name}`: the module declares `struct_passing = always_memory` — every \
         aggregate crossing is PRE-LOWERED, so no signature has a by-value aggregate slot \
         (trust-ir SPEC §17, `AlwaysMemoryByValueAggregate`) — but {detail}. The module \
         contradicts its own policy, and no evidence from outside it can reconcile that, so a \
         pass-mode cross-check does not lift this refusal. Options: (1) have the PRODUCER \
         pre-lower the crossing — a pointer parameter, and a leading `sret` pointer parameter \
         with an empty return list for a returned aggregate; (2) have the PRODUCER stamp the \
         policy it actually established (`unclassified` when it classified nothing)"
    )]
    AlwaysMemoryByValueAggregate { name: String, detail: String },

    /// A call edge this lowering reads RECORDS a slot ABI fact this converter
    /// does not read: `ParamAttrs.pass`, a non-`None` `ParamAttrs.ext`, or any
    /// `FuncAttrs.ret` (return-slot) fact.
    ///
    /// Each is a producer's statement of how a slot crosses the edge. This
    /// converter places every slot by its own classification and reads none of
    /// them, so admitting the module would drop the statement silently — and a
    /// recorded fact that disagreed with the emitted placement would be a wrong
    /// ABI at a boundary, not a refusal. trust-ir SPEC §17: a recorded `pass` /
    /// `ret` fact "must AGREE" with the placement the consumer computes, and "a
    /// consumer that cannot establish agreement MUST refuse the module rather
    /// than prefer either statement"; `ext` is unrecorded only as `None`, never
    /// "no extension needed". Refused under EVERY policy, with or without a
    /// pinned target, and a pass-mode cross-check does not lift it: the token is
    /// minted outside the module and says nothing about facts recorded inside it.
    #[error(
        "function `{name}`: {detail}. This converter places every slot by its own \
         classification and reads no recorded `ParamAttrs.pass`, `ParamAttrs.ext` or \
         `FuncAttrs.ret` fact, so it cannot establish that the recorded fact AGREES with the \
         placement it would emit; trust-ir SPEC §17 requires a consumer in that position to \
         refuse rather than prefer either statement, and ignoring the fact would be a silent \
         ABI disagreement. No `struct_passing` policy and no pass-mode cross-check lifts this \
         refusal. Options: (1) have the PRODUCER leave the fact unrecorded (`pass: None`, \
         `ext: None`, an empty `ret` slot) where it has nothing this converter must honour; \
         (2) lower the module with a backend that reads and honours the recorded facts"
    )]
    RecordedAbiSlotFact { name: String, detail: String },

    /// The function can reach a failed `Inst::Assert` — an IMPLICIT Rust panic
    /// (arithmetic overflow, division or remainder by zero, `MIN / -1`, a shift
    /// amount out of range, an index out of bounds) — and this converter has no
    /// faithful lowering for one.
    ///
    /// trust-ir's `Assert` names WHICH panic it is (`kind`, v52) and may name
    /// the entry a failed check calls and its location (`site`, v54), but this
    /// converter lowers neither: the only lowering it ever had for an assert
    /// was `Brif(cond, cont, trap)` into a shared
    /// `Opcode::Trap` block — a bare `brk`. Under that lowering a failing check
    /// prints nothing, never runs the panic handler or a `std::panic::set_hook`
    /// hook, and kills the process with SIGTRAP (exit 133) where the MIR/LLVM
    /// path prints `attempt to add with overflow` (or the bounds / division
    /// message) and aborts through the panic handler (exit 134 under
    /// `panic=abort`). The proven-output gate could not catch it: it proves the
    /// bytes against trust-ir, where a failed assert IS a divergence, so a
    /// `[PROVED]` row would certify the trap (R-8 audit
    /// `docs/audits/2026-09-29-r8-trust-ir-vs-mir.md`, finding 1; plan §5,
    /// fail-open item 1). The MIR lane already refuses the same shape
    /// (`trust-mir-extract`: "Assert omits the exact panic payload and
    /// executable unwind edge"); this is F1's twin of that refusal.
    ///
    /// Refused for EVERY `Assert` in the lowered body — the function's own and
    /// any an inlined callee contributes — whatever the block's reachability:
    /// [`function_has_unfaithful_assert`] is a syntactic predicate, so an assert
    /// the converter cannot see past is refused rather than reasoned away. It
    /// is lifted only by plan §5 item P (an `Assert` that carries its message,
    /// operands and span, lowered to Rust's panic entry points), never by
    /// relaxing this check.
    #[error(
        "function `{name}` [implicit-panic-unfaithful]: {detail}. A failed trust-ir `Assert` is \
         an implicit Rust panic (overflow, division by zero, shift range, bounds), and `Assert` \
         carries no panic message, operands or location, so the only lowering this converter has \
         is a bare trap: no message, no panic hook, SIGTRAP instead of the panic handler's \
         abort. The trust-ir codegen frontend refuses the function rather than emit a program \
         that panics differently from the MIR path. Options: (1) keep the MIR lane for this \
         crate; (2) build with the check provably absent (`-Coverflow-checks=off` removes the \
         overflow and shift asserts; division and bounds checks remain); (3) land plan §5 item \
         P (an `Assert` with message, operands and span, lowered to Rust's panic entry points)"
    )]
    ImplicitPanicUnfaithful { name: String, detail: String },
}

/// Where a function body carries an `Inst::Assert`: the trust-ir block and the
/// node's position in that block's body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnfaithfulAssertSite {
    /// The block that carries the `Assert`.
    pub block: BlockId,
    /// The `Assert` node's index in `block.body`.
    pub index: usize,
}

/// The FIRST `Inst::Assert` in `function`'s body (blocks in stored order,
/// nodes in body order), or `None` when it carries none. An
/// `Inst::AssertInvoke` (trust-ir v54: a sited check whose failure enters an
/// in-frame landing pad) is the same check and counts as one.
///
/// This is the predicate behind [`ModuleLirError::ImplicitPanicUnfaithful`],
/// shared with every other trust-ir codegen consumer the superproject drives
/// (`compiler_consumer`), so the two lanes refuse exactly the same functions.
/// It is SYNTACTIC on purpose: every block is scanned, reachable or not, and a
/// body-less declaration answers `None` (it has no code to emit here).
#[must_use]
pub fn unfaithful_assert_site(function: &IrFunction) -> Option<UnfaithfulAssertSite> {
    function.blocks.iter().find_map(|block| {
        block
            .body
            .iter()
            .position(|node| matches!(node.inst, Inst::Assert { .. } | Inst::AssertInvoke { .. }))
            .map(|index| UnfaithfulAssertSite { block: block.id, index })
    })
}

/// `true` when `function` carries any `Inst::Assert`, i.e. when a trust-ir
/// codegen consumer that cannot lower a panic faithfully must refuse it. See
/// [`unfaithful_assert_site`] and [`ModuleLirError::ImplicitPanicUnfaithful`].
#[must_use]
pub fn function_has_unfaithful_assert(function: &IrFunction) -> bool {
    unfaithful_assert_site(function).is_some()
}

impl ModuleLirError {
    /// The variant's stable name, for refusal censuses that bucket by class
    /// without parsing the rendered message.
    #[must_use]
    pub fn class_name(&self) -> &'static str {
        match self {
            Self::MissingFunction(_) => "MissingFunction",
            Self::MissingFuncType { .. } => "MissingFuncType",
            Self::FreshIdExhausted { .. } => "FreshIdExhausted",
            Self::NoBlocks { .. } => "NoBlocks",
            Self::MissingBlock { .. } => "MissingBlock",
            Self::EdgeArgArity { .. } => "EdgeArgArity",
            Self::UnsupportedSwitchCase { .. } => "UnsupportedSwitchCase",
            Self::UnencodableSwitchCase { .. } => "UnencodableSwitchCase",
            Self::MalformedControlFlow { .. } => "MalformedControlFlow",
            Self::BlockParamArity { .. } => "BlockParamArity",
            Self::UnsupportedType { .. } => "UnsupportedType",
            Self::UnsupportedInst { .. } => "UnsupportedInst",
            Self::CleanOriginBelowCodegenGate { .. } => "CleanOriginBelowCodegenGate",
            Self::MissingGlobal { .. } => "MissingGlobal",
            Self::UnsupportedBinOp { .. } => "UnsupportedBinOp",
            Self::UnsupportedUnOp { .. } => "UnsupportedUnOp",
            Self::UnsupportedCast { .. } => "UnsupportedCast",
            Self::UnsupportedConstant { .. } => "UnsupportedConstant",
            Self::UndefinedValue { .. } => "UndefinedValue",
            Self::MalformedReturn { .. } => "MalformedReturn",
            Self::UnsupportedSignature { .. } => "UnsupportedSignature",
            Self::NonLocalPointer { .. } => "NonLocalPointer",
            Self::UnsupportedMemory { .. } => "UnsupportedMemory",
            Self::UninlinableCall { .. } => "UninlinableCall",
            Self::UnsupportedUndef { .. } => "UnsupportedUndef",
            Self::UnsupportedOverflow { .. } => "UnsupportedOverflow",
            Self::UnsupportedAggregate { .. } => "UnsupportedAggregate",
            Self::UnclassifiedAggregateAbi { .. } => "UnclassifiedAggregateAbi",
            Self::NativeCAggregateAbiUnsupported { .. } => "NativeCAggregateAbiUnsupported",
            Self::AlwaysMemoryByValueAggregate { .. } => "AlwaysMemoryByValueAggregate",
            Self::RecordedAbiSlotFact { .. } => "RecordedAbiSlotFact",
            Self::ImplicitPanicUnfaithful { .. } => "ImplicitPanicUnfaithful",
        }
    }
}

/// THE ONE INTEGER TYPE a FIELDLESS (C-like) enum's value occupies, or `None`
/// when this type is not such an enum or the module does not carry enough to
/// decide (fail-closed).
///
/// # Why this is exact, and not a guess about rustc's layout
///
/// A fieldless enum has no payload, so its VALUE *is* its discriminant tag —
/// there is nothing else in it. What must be pinned is the tag's INTEGER TYPE,
/// and that is not read off trust-ir's own canonical enum layout (which is
/// deliberately not rustc's — see `trust_ir::EnumDef`'s doc). It is read off the
/// producer's `EnumLayoutDescriptor`, which the F1 producer only ever fills from
/// rustc's OWN layout query and only under a check that pins the two together:
/// `trust_thir_lower::producer_enum_layout_descriptor` emits
/// `EnumTagEncoding::Direct` **only** when `def.canonical_tag_repr()` equals
/// `enum_tag_repr_of_scalar(rustc's tag scalar)`, and sets `size` to
/// `l.size.bytes()` from that same rustc layout. So on the F1 path, for a
/// `Direct`-encoded def, `canonical_tag_repr()` IS rustc's tag scalar type.
///
/// Everything else fails closed:
///
/// * a NICHE encoding — the value is not a plain tag there;
/// * a payload-carrying variant — the value is not just the tag;
/// * a def with fewer than 2 variants — 1 variant is a ZST and 0 is
///   uninhabited; rustc gives both `PassMode::Ignore`, so neither is a register
///   value and neither belongs in this fragment;
/// * a missing layout descriptor, an unresolvable/duplicated discriminant set, a
///   `#[repr]` hint too narrow for the values (all `None` from
///   `canonical_tag_repr`), or a total size that is not exactly the tag's — the
///   last one is what would betray a payload or padding this rule does not model.
pub(crate) fn fieldless_enum_carrier(module: &Module, ty: &Ty) -> Option<Ty> {
    let Ty::Enum(id) = ty else { return None };
    let def = module.enums.get(id.as_usize())?;
    if def.variants.len() < 2 || !def.variants.iter().all(|v| v.fields.is_empty()) {
        return None;
    }
    let layout = def.layout.as_ref()?;
    // A fieldless enum's tag sits at offset 0 and IS the whole value.
    if !matches!(layout.encoding, trust_ir::EnumTagEncoding::Direct { tag_offset: 0 }) {
        return None;
    }
    let repr = def.canonical_tag_repr()?;
    let tag_bytes = match repr {
        trust_ir::EnumTagRepr::U8 | trust_ir::EnumTagRepr::I8 => 1,
        trust_ir::EnumTagRepr::U16 | trust_ir::EnumTagRepr::I16 => 2,
        trust_ir::EnumTagRepr::U32 | trust_ir::EnumTagRepr::I32 => 4,
        trust_ir::EnumTagRepr::U64 | trust_ir::EnumTagRepr::I64 => 8,
        // trust-ir v45. This lane admits a fieldless enum as a SCALAR
        // carrier, and nothing downstream of it carries a 128-bit tag: the
        // mask this width feeds is computed as `(1u128 << (bytes * 8)) - 1`,
        // which OVERFLOWS at 16. Refusing is the fail-closed answer and the
        // one this function already spells for every other shape it cannot
        // model — a `None` here just means the enum is not carried as a
        // scalar, never that it is miscompiled.
        trust_ir::EnumTagRepr::U128 | trust_ir::EnumTagRepr::I128 => return None,
    };
    if layout.size != tag_bytes {
        return None;
    }
    Some(repr.ty())
}

/// `true` when `disc` is one of `ty`'s DECLARED discriminants.
///
/// This is the value-validity half of the fieldless-enum admission. rustc's ABI
/// marks such a value `NoUndef` with a validity range, and a returned tag that
/// is not a declared discriminant would be an invalid value of the type — so the
/// converter refuses to materialize one. Together with the fact that the only
/// enum-typed sites this converter maps are `Inst::Const`, block parameters and
/// the signature (every other instruction still fails closed on an enum type),
/// this makes every enum-typed value in an admitted function either a caller's
/// argument or a checked declared discriminant.
pub(crate) fn fieldless_enum_has_discriminant(module: &Module, ty: &Ty, disc: i128) -> bool {
    let Ty::Enum(id) = ty else { return false };
    let Some(def) = module.enums.get(id.as_usize()) else { return false };
    def.effective_discriminants().is_some_and(|d| d.contains(&disc))
}

/// Public re-export of the fieldless-enum carrier rule for offline census
/// tooling. Same function, no second definition.
pub fn fieldless_enum_carrier_pub(module: &Module, ty: &Ty) -> Option<Ty> {
    fieldless_enum_carrier(module, ty)
}

/// [`map_scalar_int_ty`] plus the FIELDLESS-ENUM carrier.
///
/// Used at exactly the four sites an enum-typed value may legally appear in this
/// fragment — the signature's parameters and return, block parameters, and
/// `Inst::Const`. Every other use of an enum type still reaches the module-blind
/// [`map_scalar_int_ty`] and fails closed there, which is what keeps enum values
/// out of arithmetic, casts, comparisons and memory.
fn map_scalar_int_ty_in(
    module: &Module,
    ty: &Ty,
    context: &str,
) -> Result<LirType, ModuleLirError> {
    match fieldless_enum_carrier(module, ty) {
        Some(carrier) => map_scalar_int_ty(&carrier, context),
        None => map_scalar_int_ty(ty, context),
    }
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
        | BinOp::FMax
        | BinOp::FCopySign
        | BinOp::RotL
        | BinOp::RotR
        // Trust: the boolean-carrier LOGICAL connectives are REFUSED here, not
        // mapped onto `Band`/`Bor`/`Bxor`. On a well-formed 0/1 carrier the two
        // agree, but that premise is exactly what this converter cannot check
        // locally — it sees a `BinOp` and a `Ty`, not the provenance that
        // established the operands are 0/1. trust-ir introduced `BAnd`/`BOr`/
        // `BXor` precisely BECAUSE `And`/`Or`/`Xor` overload bitwise and logical
        // readings in a way the Lean semantics does not share (`semIntBinOp .And`
        // is `Int.land` unconditionally), so silently collapsing them back onto
        // the bitwise opcodes would re-create the ambiguity the split exists to
        // remove — inside VERIFIED CODEGEN, where the cost is a wrong binary
        // rather than a failed proof. A narrow enforced fragment refuses what it
        // has not modelled; widening it is a deliberate, provable act.
        | BinOp::BAnd
        | BinOp::BOr
        | BinOp::BXor => {
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
        BinOp::BAnd => "band",
        BinOp::BOr => "bor",
        BinOp::BXor => "bxor",
        BinOp::FMin => "fmin",
        BinOp::FMax => "fmax",
        BinOp::FCopySign => "fcopysign",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Xor => "xor",
        BinOp::Shl => "shl",
        BinOp::LShr => "lshr",
        BinOp::AShr => "ashr",
        BinOp::RotL => "rotl",
        BinOp::RotR => "rotr",
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
///     a scalar-`Bool` `!` is respelled `ICmp Eq(x, false)` by the producer
///     (`trust-ir-bridge`'s `LoweringCtx::emit_unop`) and is refused outright
///     below, so an integer-only `UnOp` is complete — CHECKED here, not assumed.
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
///   * a scalar `Bool` carrier — `Bnot` on the byte-wide bool carrier computes
///     `0xFE` for `!true`, and `Ineg` on a bool has no meaning; the sibling
///     proof-of-output lane already refuses it, so this lane must too.
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
            // FAIL CLOSED on a scalar `Bool` carrier. `map_scalar_int_ty` maps
            // `Ty::Bool` to the byte-wide `I8` LIR carrier, so a bool `!` would have
            // emitted `Bnot`/`MVN` — the BITWISE complement of a 0/1 byte
            // (`!true -> 0xFE`), not `!b` — and a bool `-` `Ineg`/`NEG`, which has no
            // meaning at all. The doc above asserts "the producer routes `!bool`
            // through `Select`, so an integer-only `UnOp` is complete"; that premise
            // was stated but never CHECKED, and the trust-ir producer did emit
            // `UnOp { op: Not, ty: Bool }` until `LoweringCtx::emit_unop` respelled it.
            // Check it here so the two lanes agree: the sibling proof-of-output lane
            // already refuses this exact shape ("UnOp on a bool carrier is not
            // modeled (fail-closed)", `verify_output_trust_ir`), and a code generator
            // that emits what its own verifier declines to model is a hole. Nothing
            // sound is lost: no producer in the tree emits it, and `Bnot` on a bool
            // carrier does not compute `!b` under any reading.
            if matches!(ty, Ty::Bool) {
                return Err(ModuleLirError::UnsupportedUnOp {
                    name: name.to_string(),
                    op: unop_name(op),
                });
            }
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
        UnOp::CtPop | UnOp::CtLz | UnOp::CtTz | UnOp::BSwap | UnOp::BitReverse => {
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
        UnOp::CtLz => "ctlz",
        UnOp::CtTz => "cttz",
        UnOp::BSwap => "bswap",
        UnOp::BitReverse => "bitreverse",
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
            // Both operands must be scalar integers. The i8..i64 envelope maps
            // 1:1; the I128 register-pair forms are ALSO in the ISel's
            // envelope (measured, not hoped: `select_extend` defines BOTH
            // halves of the pair for an extension to I128 — Uxt*/Sxt* low
            // plus zero/ASR-#63 high — and `Trunc(I128 -> I64)` reads the low
            // half; `select_i128_{add,sub,mul,sdiv}` and the I128 `Icmp`
            // lane consume the pairs). What stays refused: Bitcast involving
            // I128 (no measured lane), and non-integers (a `bool` SOURCE is
            // the one exception — `b as uN` is a `ZExt` from the 1-bit `Bool`
            // whose byte carrier maps below; pointers are handled by the
            // fail-closed pointer arms). The trust-ir gate rejects
            // 128-bit arithmetic in its own fragment, so functions taking
            // this lane emit UNCERTIFIED under allow-unknown — completeness
            // now, proofs with the pair-aware gate later.
            let from = map_scalar_int_ty(src_ty, "cast source")
                .map_err(|_| fail(format!("source type {src_ty:?} is not a scalar integer")))?;
            let to = map_scalar_int_ty(dst_ty, "cast dest")
                .map_err(|_| fail(format!("dest type {dst_ty:?} is not a scalar integer")))?;
            if (matches!(from, LirType::I128) || matches!(to, LirType::I128))
                && matches!(op, CastOp::Bitcast)
            {
                return Err(fail("128-bit Bitcast has no measured lane (fail-closed)".to_string()));
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
                    // A `bool` -> 8-bit `ZExt` is what the producer emits for
                    // `b as u8` / `b as i8` (trust-ir's `Bool` is 1 bit wide,
                    // so the cast classifies as an extension), and the bool's
                    // byte-wide LIR carrier ALREADY IS its zero-extended value
                    // (0 or 1 in the byte) — so at the LIR level it is the
                    // identity on the bit pattern, exactly like a same-width
                    // `Bitcast`, and lowers to `Copy` (WS7.13: measured on the
                    // `<bool as AsPrimitive<u8>>::as_` corpus row, which this
                    // arm refused as a non-widening extend; the gate still
                    // discharges the emitted bytes against the IR's own
                    // `zext(bool -> u8)` semantics, so nothing is trusted here).
                    if matches!(op, CastOp::ZExt)
                        && matches!(src_ty, Ty::Bool)
                        && matches!(to, LirType::I8)
                    {
                        return Ok(None);
                    }
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
/// Add/Sub at I128 map first-class too: the ISel lowers them over the
/// register pair via the flag-setting carry chain (ADDS lo; ADCS hi; CSET /
/// SUBS lo; SBCS hi; CSET — overflow read from the FINAL NZCV).
///
/// FAIL-CLOSED on the shapes the verified ISel slice does not lower:
///   * 128-bit `Mul` (SMULH/UMULH give one high half; no checked idiom),
///   * `Mul` narrower than 64-bit (`CheckedSmul`/`CheckedUmul` are I64-only),
///   * any non-fixed-width-integer operand type.
///
/// NOTE: checked `Mul` at i8/i16/i32 (and unsigned) is NOT routed here — the
/// caller intercepts those widths and lowers them via exact i64 widening
/// (`{s,z}ext` + `Imul` + range-check Icmps), so this function only sees `Mul`
/// at i64/u64 (first-class `Checked{S,U}mul`) or i128 (fail closed).
fn map_overflow_op(op: OverflowOp, ty: &Ty, name: &str) -> Result<Opcode, ModuleLirError> {
    let signed = ty.is_signed();
    // The compared operands must be a fixed-width integer the ISel handles.
    let lir_ty = map_scalar_int_ty(ty, "Overflow operand")?;
    if matches!(lir_ty, LirType::I128) && matches!(op, OverflowOp::MulOverflow) {
        // Checked add/sub at I128 lower to the flag-setting carry chain
        // (ADDS lo; ADCS hi; CSET / SUBS lo; SBCS hi; CSET). Checked mul has
        // no 128-bit ISel idiom.
        return Err(ModuleLirError::UnsupportedOverflow {
            name: name.to_string(),
            detail: format!("128-bit checked {op:?} has no verified flag/high-half ISel idiom"),
        });
    }
    let opcode = match (op, signed) {
        // The flag-setting ADDS/SUBS+CSET ISel idiom exists at I32/I64 only
        // (measured: emit_object refuses I16 with "checked add/sub requires
        // I32 or I64 operands"). The caller intercepts I8/I16 and lowers them
        // via exact i64 widening, so narrower widths here are a wiring bug.
        (OverflowOp::AddOverflow | OverflowOp::SubOverflow, _)
            if matches!(lir_ty, LirType::I8 | LirType::I16) =>
        {
            return Err(ModuleLirError::UnsupportedOverflow {
                name: name.to_string(),
                detail: format!(
                    "checked {op:?} on {lir_ty:?} reached the first-class map (the i64-widening \
                     interception should have taken it)"
                ),
            });
        }
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
        Inst::MemCopy { .. } => "MemCopy",
        Inst::MemSet { .. } => "MemSet",
        Inst::Alloca { .. } => "Alloca",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GEP { .. } => "GEP",
        Inst::PtrData { .. } => "PtrData",
        Inst::PtrMetadata { .. } => "PtrMetadata",
        Inst::PtrFromParts { .. } => "PtrFromParts",
        Inst::BoxDeref { .. } => "BoxDeref",
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
        Inst::MakeAggregate { .. } => "MakeAggregate",
        Inst::MakeClosure { .. } => "MakeClosure",
        Inst::ArraySplat { .. } => "ArraySplat",
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
        Inst::Drop { .. } => "Drop",
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
        Inst::AssertInvoke { .. } => "AssertInvoke",
        Inst::CallCannotUnwind { .. } => "CallCannotUnwind",
        Inst::CallIndirectCannotUnwind { .. } => "CallIndirectCannotUnwind",
        Inst::DropInvoke { .. } => "DropInvoke",
        Inst::InvokeIndirect { .. } => "InvokeIndirect",
        Inst::TensorContract { .. } => "TensorContract",
        Inst::TensorMap { .. } => "TensorMap",
        Inst::TensorReduce { .. } => "TensorReduce",
        Inst::TensorView { .. } => "TensorView",
        Inst::TensorGather { .. } => "TensorGather",
        Inst::TensorScatter { .. } => "TensorScatter",
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

    /// Allocate the next dense LIR value WITHOUT binding a trust-ir `ValueId`
    /// to it. Used for the split halves of a fat slice parameter, whose
    /// positional formal slots must stay dense while the fat pointer's own
    /// `ValueId` deliberately resolves to NOTHING (fail-closed on any use the
    /// fat-param lanes do not handle).
    fn define_anonymous(&mut self) -> Value {
        let v = Value(self.next);
        self.next += 1;
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
    /// FAT SLICE PARAMETERS (`&[T]` formals). Keyed by the trust-ir entry
    /// param's `ValueId` (which is deliberately NOT in the `ValueMap`, so any
    /// use of the whole fat pointer other than `PtrData`/`PtrMetadata` fails
    /// closed as an undefined value). The split (data, len) LIR values occupy
    /// two consecutive formal-argument positions — bit-for-bit rustc's
    /// `ScalarPair` passing of a slice reference (data in the first GPR slot,
    /// length in the next).
    fat_params: HashMap<ValueId, FatSliceParam>,
    /// INCOMING READ-ONLY roots: pointer `Value`s derived from a fat slice
    /// param's data pointer (the `PtrData` result and `GEP`s off it), with the
    /// scalar element type they address. `Load` accepts them; `Store` does NOT
    /// (a `&[T]` is shared — writes through it are not admitted), and neither
    /// does anything requiring slot provenance.
    incoming_pointee: HashMap<Value, LirType>,
    /// BY-VALUE STRUCT params passed INDIRECTLY (rustc's hidden pointer for a
    /// large-aggregate argument). Keyed by the trust-ir param `ValueId`; the
    /// LIR value is the hidden pointer (one I64 formal), and the layout is the
    /// RUSTC-RECORDED one ([`recorded_struct_mem_layout`]). `ExtractField` on
    /// the param loads the field through the pointer at its recorded offset;
    /// every other use of the whole-struct value fails closed. The F1 ABI
    /// validator independently confirms the real `PassMode` is `Indirect`.
    indirect_struct_params: HashMap<ValueId, IndirectStructParam>,
    /// BY-VALUE 2-scalar-field struct params passed as a register PAIR.
    /// `ExtractField` on the param is a Copy of the mapped formal; every
    /// other use of the whole-struct value fails closed.
    pair_struct_params: HashMap<ValueId, PairStructParam>,
    /// BY-VALUE NEWTYPE struct params (one plain-scalar field, Direct as the
    /// field scalar). The param's own value IS the field; `ExtractField 0`
    /// is a Copy of it.
    newtype_struct_params: HashMap<ValueId, LirType>,
    /// ASSEMBLED READ-ONLY GLOBAL roots. Only an immutable, initialized,
    /// non-TLS, module-local `u64` definition enters this map. `Load` consumes
    /// it directly; Store, GEP, and copied/escaped aliases remain refused.
    global_pointee: HashMap<Value, LirType>,
}

/// Provenance for a pointer produced directly by `GlobalAddr`.
///
/// Keeping data symbols in this map is essential: a direct address of known
/// data is not an "open" function pointer. If it reaches `CallIndirect`, the
/// call must fail closed instead of taking the conservative open-call lane.
enum GlobalAddrProvenance {
    FunctionSymbol(String),
    DataSymbol,
}

/// One by-value 2-scalar-field struct formal passed as a register PAIR
/// (rustc `PassMode::Pair` — `Range<usize>`-class shapes).
struct PairStructParam {
    /// The two LIR formals, indexed by the struct's DECLARATION field order
    /// (the formals themselves are emitted in LAYOUT/offset order; this
    /// mapping absorbs any repr(Rust) reorder).
    by_decl_index: [Value; 2],
    /// The two field LIR types, by declaration index.
    tys: [LirType; 2],
    /// Declaration indices in LAYOUT (offset) order — the order the two
    /// formals were emitted in the signature.
    layout_order: [usize; 2],
}

/// One by-value struct formal passed via rustc's hidden pointer.
struct IndirectStructParam {
    /// The LIR value carrying the hidden pointer.
    ptr: Value,
    /// The rustc-recorded layout of the pointee struct.
    layout: AggMemLayout,
    /// The struct's field types in declaration order (for nested
    /// fieldless-enum registration at extract time).
    field_tys: Vec<Ty>,
}

/// One split `&[T]` formal: the two LIR values carrying (data, len) and the
/// scalar element type loads through the data pointer must match.
struct FatSliceParam {
    data: Value,
    len: Value,
    elem: LirType,
}

impl MemoryCtx {
    fn new() -> Self {
        Self {
            stack_slots: Vec::new(),
            slot_of: HashMap::new(),
            pointee_ty: HashMap::new(),
            fat_params: HashMap::new(),
            incoming_pointee: HashMap::new(),
            global_pointee: HashMap::new(),
            indirect_struct_params: HashMap::new(),
            pair_struct_params: HashMap::new(),
            newtype_struct_params: HashMap::new(),
        }
    }

    /// Allocate a fresh fixed-size stack slot for `lir_ty`, returning its index.
    fn alloc_slot(&mut self, lir_ty: &LirType) -> u32 {
        let slot = self.stack_slots.len() as u32;
        self.stack_slots.push(StackSlotInfo::new(lir_ty.bytes(), lir_ty.align()));
        slot
    }

    /// Allocate a fresh fixed-size stack slot of an explicit `size`/`align`,
    /// returning its index. Used for AGGREGATE slots whose size/align come from
    /// [`aggregate_mem_layout`], which is the trust-ir interpreter's own layout
    /// of the slot's type (declared, or declaration order when none is declared;
    /// CG-DECLARED-LAYOUT-1).
    fn alloc_sized_slot(&mut self, size: u32, align: u32) -> u32 {
        let slot = self.stack_slots.len() as u32;
        self.stack_slots.push(StackSlotInfo::new(size, align));
        slot
    }
}

/// The in-memory layout of a scalar-field aggregate (`Ty::Tuple` or
/// `Ty::Struct`): its byte size and alignment and each field's byte offset, in
/// declaration order.
///
/// Two producers build one. [`aggregate_mem_layout`] builds the layout of a slot
/// this converter allocates, and it is the pinned trust-ir reference
/// interpreter's own layout of the type, byte for byte (CG-DECLARED-LAYOUT-1): a
/// declared layout read verbatim and re-validated as the interpreter's
/// `declared_struct_layout` / `tuple_layout_in` validate it, or, when the type
/// declares none, the interpreter's declaration-order `aggregate_layout` (each
/// field at the next offset aligned up to its natural alignment, the size
/// rounded up to the maximum field alignment, min 1).
/// [`recorded_struct_mem_layout`] builds the layout of memory a CALLER laid out,
/// and reads only rustc's recorded triple.
///
/// The per-field scalar (`byte_size`/`byte_align`) values used here are exactly
/// the interpreter's (`I8/U8/Bool`=1, `I16/U16`=2, `I32/U32`=4, `I64/U64`=8); a
/// `LirType`'s `bytes()`/`align()` agree with those for the scalar ints this
/// slice admits. Any field type without such a scalar layout fails closed
/// (`scalar_field_size_align`).
#[derive(Clone, Debug, PartialEq, Eq)]
struct AggMemLayout {
    /// Total byte size (a multiple of `align`).
    size: u32,
    /// Aggregate alignment (a power of two).
    align: u32,
    /// Per-field `(byte_offset, lir_field_type)` in declaration order.
    field_offsets: Vec<(u32, LirType)>,
}

/// Natural byte size / alignment of a scalar-int/Bool field, matching the
/// trust-ir interpreter's `byte_size`/`byte_align` for these types EXACTLY.
/// FAIL-CLOSED on any non-scalar field (the C layout would need a recursive
/// aggregate layout this slice does not reproduce), and on a pointer-width
/// field (`isize`/`usize`) of a module whose target does not have 8-byte
/// pointers: the interpreter sizes that field at the target's pointer width
/// (4 bytes on wasm32 or i686) and this table only has the 64-bit width.
fn scalar_field_size_align(
    ty: &Ty,
    module: &Module,
    name: &str,
) -> Result<(u32, u32, LirType), ModuleLirError> {
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
        // Trust (v25 B1): isize/usize are pointer-width — 8 bytes on a
        // target-free module (the interpreter's 64-bit reference width) and on
        // a target with 8-byte pointers, laid out exactly like I64/U64. Any
        // other pointer width is refused, never laid out at 8.
        Ty::Isize | Ty::Usize => match module.target_info.as_ref().map(|t| t.pointer_size) {
            None | Some(8) => (8, 8),
            Some(pointer_size) => {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "aggregate field type {ty:?} is pointer-width and the module's target has \
                         {pointer_size}-byte pointers; this converter's field table sizes it only \
                         at 8 bytes"
                    ),
                });
            }
        },
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
/// Module's `StructDef` (`def.fields.iter().map(|f| &f.ty)`). A `Ty::Tuple` is
/// self-describing.
///
/// FAIL-CLOSED on any non-aggregate type, and — for a struct — on a missing
/// `StructDef` or a `repr` other than the layout-default `Rust`: a
/// `#[repr(C/packed/transparent)]` struct is outside the slice whose emitted
/// bytes are proven (the interpreter re-validates a packed clamp and a
/// transparent carrier this file does not reproduce), so it is rejected rather
/// than laid out. The bridge emits `StructRepr::Rust` for every ADT/closure-env
/// it lowers, so this covers the real emitted shape.
///
/// This answers the field TYPES only. Where each field LIVES is
/// [`aggregate_mem_layout`]'s answer, and since CG-DECLARED-LAYOUT-1
/// (2026-11-10) that is the interpreter's: a declared `StructDef`
/// size/align/`FieldDef::offset` triple or a `Module::tuple_layouts` descriptor
/// is read and re-validated, and only a type that declares none is laid out in
/// declaration order. (Until then this doc carried a KNOWN GAP: the slot was laid
/// out in declaration order for every type, while the interpreter has used a
/// declared layout since trust-ir `c951b2e` — *"a declared struct layout is
/// NORMATIVE"* — and the producer's `register_struct` fills one from rustc's
/// reorder-aware offsets for every concrete struct; wave-SG measured 3,489 of
/// 4,788 field offsets on `clean-kernel` differing. Values agreed only because the
/// slot was round-tripped whole, step 1b refused every partial access, and the
/// declaration-order slot was never smaller than rustc's.)
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
            // Only `repr(Rust)` is in the proven slice: a packed clamp or a
            // transparent carrier changes what the interpreter accepts as a
            // declared layout, and neither is reproduced here; fail closed.
            if def.repr != trust_ir::ty::StructRepr::Rust {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "aggregate Ty::Struct({}) has non-default repr {:?}; only repr(Rust) is in \
                         the aggregate-memory slice",
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

/// A layout the module DECLARES for an aggregate type, as the interpreter reads
/// it: a `StructDef`'s `(size, align, FieldDef::offset)` triple, or a
/// `Module::tuple_layouts` descriptor. Offsets are in declaration order.
struct DeclaredAggLayout {
    size: u64,
    align: u64,
    offsets: Vec<u64>,
}

/// The layout `ty` DECLARES, exactly where the pinned trust-ir interpreter finds
/// one (`interpret::struct_layout_unguarded` / `tuple_layout_in`), or `None` when
/// it declares none and the interpreter lays it out in declaration order.
///
/// FAIL-CLOSED on every declaration the interpreter refuses, so this converter
/// never lowers a slot the reference semantics cannot execute:
/// * a struct: a size without an alignment or the reverse; an offset on a field of
///   a struct with neither; under a declared size and alignment, a field with no
///   offset (the interpreter admits that only for a zero-sized field, and every
///   field this slice admits is a non-zero-sized scalar);
/// * a tuple: a `Module::tuple_layouts` table that does not validate (the
///   interpreter validates the whole table before laying out any tuple), or two
///   descriptors for one tuple;
/// * either, on a module whose target is not the 64-bit little-endian
///   canonical-scalar layout `scalar_field_size_align` describes: the interpreter
///   refuses a declared layout on a big-endian or non-canonical-scalar target
///   (`require_reference_execution_layout`), and on a 32-bit target it sizes
///   `isize`/`usize` at 4 bytes where this converter's field table says 8.
fn declared_aggregate_layout(
    ty: &Ty,
    module: &Module,
    name: &str,
) -> Result<Option<DeclaredAggLayout>, ModuleLirError> {
    let refuse =
        |detail: String| ModuleLirError::UnsupportedAggregate { name: name.to_string(), detail };
    let declared = declared_aggregate_layout_unchecked_target(ty, module, &refuse)?;
    if declared.is_some()
        && let Some(target) = &module.target_info
        && !(target.pointer_size == 8
            && target.endianness == trust_ir::Endianness::Little
            && module.target_has_canonical_scalar_layout())
    {
        return Err(refuse(format!(
            "{ty:?} declares a layout for target {:?} ({}-byte pointers, {:?}), which is not the \
             64-bit little-endian canonical-scalar layout this converter's field table describes",
            target.triple, target.pointer_size, target.endianness
        )));
    }
    Ok(declared)
}

/// [`declared_aggregate_layout`] before its target check.
fn declared_aggregate_layout_unchecked_target(
    ty: &Ty,
    module: &Module,
    refuse: &dyn Fn(String) -> ModuleLirError,
) -> Result<Option<DeclaredAggLayout>, ModuleLirError> {
    match ty {
        Ty::Struct(sid) => {
            let def = module.struct_def(*sid).ok_or_else(|| {
                refuse(format!(
                    "aggregate Ty::Struct({}) has no StructDef in the module table",
                    sid.as_usize()
                ))
            })?;
            match (def.size, def.align) {
                (Some(size), Some(align)) => {
                    let offsets = def
                        .fields
                        .iter()
                        .map(|field| {
                            field.offset.ok_or_else(|| {
                                refuse(format!(
                                    "struct `{}` declares size {size} / align {align} but no offset \
                                     for field `{}`",
                                    def.name, field.name
                                ))
                            })
                        })
                        .collect::<Result<Vec<u64>, _>>()?;
                    Ok(Some(DeclaredAggLayout { size, align, offsets }))
                }
                (None, None) => match def.fields.iter().find(|field| field.offset.is_some()) {
                    Some(field) => Err(refuse(format!(
                        "struct `{}` declares an offset for field `{}` but no size or alignment",
                        def.name, field.name
                    ))),
                    None => Ok(None),
                },
                (Some(_), None) | (None, Some(_)) => Err(refuse(format!(
                    "struct `{}` declares a size without an alignment, or the reverse",
                    def.name
                ))),
            }
        }
        Ty::Tuple(elems) => {
            if module.tuple_layouts.is_empty() {
                return Ok(None);
            }
            module
                .validate_tuple_layouts()
                .map_err(|e| refuse(format!("the module's tuple layout table is invalid: {e}")))?;
            let Some(desc) = module.tuple_layout_descriptor(ty).map_err(|e| {
                refuse(format!("tuple {ty:?} has no unambiguous layout descriptor: {e}"))
            })?
            else {
                return Ok(None);
            };
            if desc.field_offsets.len() != elems.len() {
                return Err(refuse(format!(
                    "tuple {ty:?} has {} elements but its layout descriptor names {} offsets",
                    elems.len(),
                    desc.field_offsets.len()
                )));
            }
            Ok(Some(DeclaredAggLayout {
                size: desc.size,
                align: desc.align,
                offsets: desc.field_offsets.clone(),
            }))
        }
        other => Err(refuse(format!(
            "aggregate-memory layout is only computed for Ty::Tuple / Ty::Struct; got {other:?}"
        ))),
    }
}

/// Compute the [`AggMemLayout`] of a slot holding a `Ty::Tuple`/`Ty::Struct` of
/// scalar fields: the trust-ir interpreter's own layout of that type, byte for
/// byte (CG-DECLARED-LAYOUT-1).
///
/// * A DECLARED layout ([`declared_aggregate_layout`]) is read verbatim and
///   re-validated as the interpreter's `declared_struct_layout` validates it for
///   `repr(Rust)`: a power-of-two alignment, a size that is a multiple of it, and
///   every field at an offset that is a multiple of its own alignment, no wider
///   aligned than the aggregate, inside the size, and overlapping no other field.
///   A declaration that fails any of these is refused, never repaired.
/// * Otherwise the interpreter's declaration-order `aggregate_layout`: each field
///   at the next offset aligned up to its natural alignment, the size rounded up
///   to the aggregate alignment (max field alignment, min 1).
///
/// FAIL-CLOSED on a non-aggregate type, a non-scalar field, a declaration the
/// interpreter refuses, or a zero-field aggregate (there is nothing to round-trip
/// and the bridge never emits one for a promoted local).
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
    // scalar_field_size_align FAILS CLOSED on any non-scalar field (nested
    // struct/tuple, float, i128, pointer), so a struct-of-struct / float /
    // i128-field aggregate never lays out under this slice.
    let scalars = fields
        .iter()
        .map(|field_ty| scalar_field_size_align(field_ty, module, name))
        .collect::<Result<Vec<_>, _>>()?;
    match declared_aggregate_layout(ty, module, name)? {
        Some(declared) => declared_slot_layout(ty, &declared, scalars, name),
        None => {
            let mut offset: u32 = 0;
            let mut max_align: u32 = 1;
            let mut field_offsets = Vec::with_capacity(scalars.len());
            for (f_size, f_align, f_lir) in scalars {
                offset = align_up_u32(offset, f_align);
                field_offsets.push((offset, f_lir));
                offset += f_size;
                max_align = max_align.max(f_align);
            }
            let size = align_up_u32(offset, max_align);
            Ok(AggMemLayout { size, align: max_align, field_offsets })
        }
    }
}

/// The slot layout of a DECLARED aggregate layout, after the re-validation
/// [`aggregate_mem_layout`] lists. `scalars` are the fields' `(size, align,
/// lir_type)` in declaration order.
///
/// The declared alignment is the slot's. trust-cg's frame guarantees a slot base
/// only 16-byte alignment, so an over-aligned declaration (`repr(align(32))`) can
/// get an under-aligned base; nothing admitted observes the base (step 1b: a
/// field pointer is only ever the address of a field access, never compared,
/// stored, cast or returned), and every field access stays aligned to its own
/// width, which is at most 8.
fn declared_slot_layout(
    ty: &Ty,
    declared: &DeclaredAggLayout,
    scalars: Vec<(u32, u32, LirType)>,
    name: &str,
) -> Result<AggMemLayout, ModuleLirError> {
    let refuse = |detail: String| ModuleLirError::UnsupportedAggregate {
        name: name.to_string(),
        detail: format!("declared layout of {ty:?}: {detail}"),
    };
    if declared.offsets.len() != scalars.len() {
        return Err(refuse(format!(
            "{} declared offsets for {} fields",
            declared.offsets.len(),
            scalars.len()
        )));
    }
    let size = u32::try_from(declared.size)
        .map_err(|_| refuse(format!("size {} exceeds u32", declared.size)))?;
    let align = u32::try_from(declared.align)
        .map_err(|_| refuse(format!("alignment {} exceeds u32", declared.align)))?;
    if !align.is_power_of_two() || !size.is_multiple_of(align) {
        return Err(refuse(format!("incoherent size {size} / alignment {align}")));
    }
    let mut field_offsets: Vec<(u32, LirType)> = Vec::with_capacity(scalars.len());
    let mut extents: Vec<(u32, u32)> = Vec::with_capacity(scalars.len());
    for (index, (&offset, (f_size, f_align, f_lir))) in
        declared.offsets.iter().zip(scalars).enumerate()
    {
        let in_bounds = u32::try_from(offset)
            .ok()
            .filter(|off| off.checked_add(f_size).is_some_and(|end| end <= size));
        let Some(offset) = in_bounds else {
            return Err(refuse(format!(
                "field {index} at offset {offset} ({f_size} bytes) overruns the declared size \
                 {size}"
            )));
        };
        if !offset.is_multiple_of(f_align) || f_align > align {
            return Err(refuse(format!(
                "field {index} at offset {offset} (align {f_align}) is misaligned or over-aligned \
                 for declared alignment {align}"
            )));
        }
        if let Some(other) = extents
            .iter()
            .position(|&(o, s)| offset < o.saturating_add(s) && o < offset.saturating_add(f_size))
        {
            return Err(refuse(format!("fields {other} and {index} overlap")));
        }
        extents.push((offset, f_size));
        field_offsets.push((offset, f_lir));
    }
    Ok(AggMemLayout { size, align, field_offsets })
}

/// The TAG-CARRIER read view of an ENUM-typed struct field, or `None` when
/// the enum's recorded layout cannot support one.
///
/// A FIELDLESS enum's value IS its tag ([`fieldless_enum_carrier`]). A
/// PAYLOAD-carrying enum is admitted for READING ONLY through its tag: the
/// producer-recorded [`trust_ir::EnumLayoutDescriptor`] must place a `Direct`
/// tag at offset 0, and the canonical tag repr names the carrier scalar. The
/// PAYLOAD region is never loaded — and every way the whole enum value could
/// escape (return, call argument, store) already fails closed on the enum
/// type in the scalar type maps, so a tag-only read cannot masquerade as the
/// full value anywhere it would matter. Returns
/// `(carrier_ty, full_size, full_align)`; `full_size` is the ENUM's recorded
/// size (for bounds checks), not the carrier's.
fn enum_tag_read_view(module: &Module, ty: &Ty) -> Option<(Ty, u64, u64)> {
    if let Some(carrier) = fieldless_enum_carrier(module, ty) {
        let Ty::Enum(id) = ty else { return None };
        let layout = module.enums.get(id.as_usize())?.layout.as_ref()?;
        return Some((carrier, layout.size, layout.align));
    }
    let Ty::Enum(id) = ty else { return None };
    let def = module.enums.get(id.as_usize())?;
    let layout = def.layout.as_ref()?;
    if !matches!(layout.encoding, trust_ir::EnumTagEncoding::Direct { tag_offset: 0 }) {
        return None;
    }
    let repr = def.canonical_tag_repr()?;
    Some((repr.ty(), layout.size, layout.align))
}

/// The TWO-SLOT REGISTER VIEW of a small Direct-tagged enum — `Option<u64>`,
/// `Option<&T>`-without-niche, small `Result` shapes: `(tag, payload)`.
///
/// Demands, all from the PRODUCER-RECORDED descriptor (nothing guessed):
/// * a recorded [`trust_ir::EnumLayoutDescriptor`] with `Direct { tag_offset: 0 }`
///   (a NICHE encoding has no separate tag lane — refused);
/// * a canonical tag repr naming the tag scalar;
/// * total size <= 16 bytes (the machine value is a register ScalarPair);
/// * every variant carries AT MOST ONE field, and every fielded variant's
///   field is the SAME plain scalar type (they share the payload lane).
///
/// The trust-ir field-index convention over such a value is the producer's:
/// `extractfield 0` = the tag, `extractfield 1` = the payload.
struct PairEnumView {
    tag: LirType,
    payload: LirType,
}

fn pair_enum_view(module: &Module, ty: &Ty) -> Option<PairEnumView> {
    let Ty::Enum(id) = ty else { return None };
    let def = module.enums.get(id.as_usize())?;
    let layout = def.layout.as_ref()?;
    if !matches!(layout.encoding, trust_ir::EnumTagEncoding::Direct { tag_offset: 0 }) {
        return None;
    }
    if layout.size > 16 {
        return None;
    }
    let repr = def.canonical_tag_repr()?;
    let tag = map_scalar_int_ty(&repr.ty(), "pair-enum tag").ok()?;
    let mut payload: Option<LirType> = None;
    for variant in &def.variants {
        match variant.fields.as_slice() {
            [] => {}
            [f] => {
                let lir = map_scalar_int_ty(f, "pair-enum payload").ok()?;
                match &payload {
                    None => payload = Some(lir),
                    Some(existing) if *existing == lir => {}
                    Some(_) => return None,
                }
            }
            _ => return None,
        }
    }
    // A payload-less def is the fieldless-enum lane's business, not this one.
    let payload = payload?;
    Some(PairEnumView { tag, payload })
}

/// The RUSTC-RECORDED memory layout of a `Ty::Struct` — for reading memory a
/// CALLER laid out (the incoming-pointer aggregate lane).
///
/// SOUNDNESS — this is deliberately NOT [`aggregate_mem_layout`]. That one is
/// the interpreter's layout of a slot this converter itself allocates, fills and
/// reads WHOLE (PASS 1.7 step 1b), and for a type that declares no layout it is
/// the canonical declaration-order layout; memory
/// reached through an INCOMING pointer was laid out by rustc, and repr(Rust)
/// reorders fields, so canonical offsets can read the wrong bytes. This
/// function therefore uses only what the PRODUCER recorded off rustc's layout
/// — the struct's `size`/`align` and every field's `offset` — and FAILS
/// CLOSED when any of them is absent (degraded defs, e.g. a `Vec` field
/// spelled `()`), and on `Ty::Tuple` entirely (this function reads no
/// `Module::tuple_layouts` descriptor, and rustc reorders tuples too).
fn recorded_struct_mem_layout(
    ty: &Ty,
    module: &Module,
    name: &str,
) -> Result<AggMemLayout, ModuleLirError> {
    let Ty::Struct(sid) = ty else {
        return Err(ModuleLirError::UnsupportedAggregate {
            name: name.to_string(),
            detail: format!(
                "incoming-pointer aggregate load needs a rustc-recorded layout; {ty:?} carries \
                 none (repr(Rust) may reorder fields, so a canonical guess could read the wrong \
                 bytes)"
            ),
        });
    };
    let def =
        module.structs.get(sid.as_usize()).ok_or_else(|| ModuleLirError::UnsupportedAggregate {
            name: name.to_string(),
            detail: format!("struct id {} not in module", sid.as_usize()),
        })?;
    let (Some(size), Some(align)) = (def.size, def.align) else {
        return Err(ModuleLirError::UnsupportedAggregate {
            name: name.to_string(),
            detail: format!(
                "struct `{}` has no recorded size/align; refusing to guess a caller layout",
                def.name
            ),
        });
    };
    let size = u32::try_from(size).map_err(|_| ModuleLirError::UnsupportedAggregate {
        name: name.to_string(),
        detail: format!("struct `{}` size exceeds u32", def.name),
    })?;
    let align = u32::try_from(align).map_err(|_| ModuleLirError::UnsupportedAggregate {
        name: name.to_string(),
        detail: format!("struct `{}` align exceeds u32", def.name),
    })?;
    let mut field_offsets = Vec::with_capacity(def.fields.len());
    for field in &def.fields {
        let Some(offset) = field.offset else {
            return Err(ModuleLirError::UnsupportedAggregate {
                name: name.to_string(),
                detail: format!(
                    "struct `{}` field `{}` has no recorded offset; refusing to guess a caller \
                     layout",
                    def.name, field.name
                ),
            });
        };
        let offset = u32::try_from(offset).map_err(|_| ModuleLirError::UnsupportedAggregate {
            name: name.to_string(),
            detail: format!("struct `{}` field offset exceeds u32", def.name),
        })?;
        // An ENUM field reads through its TAG CARRIER (fieldless: the whole
        // value; payload-carrying: the tag lane at offset 0 — the payload is
        // never loaded, see enum_tag_read_view). The bounds check uses the
        // enum's FULL recorded size. Every other non-scalar field keeps
        // failing closed in scalar_field_size_align.
        let (field_scalar_ty, bounds_size) = match enum_tag_read_view(module, &field.ty) {
            Some((carrier, full_size, _)) => {
                let full =
                    u32::try_from(full_size).map_err(|_| ModuleLirError::UnsupportedAggregate {
                        name: name.to_string(),
                        detail: format!(
                            "struct `{}` enum field `{}` size exceeds u32",
                            def.name, field.name
                        ),
                    })?;
                (carrier, Some(full))
            }
            None => (field.ty.clone(), None),
        };
        let (f_size, _f_align, f_lir) = scalar_field_size_align(&field_scalar_ty, module, name)?;
        let f_size = bounds_size.unwrap_or(f_size).max(f_size);
        if offset.checked_add(f_size).is_none_or(|end| end > size) {
            return Err(ModuleLirError::UnsupportedAggregate {
                name: name.to_string(),
                detail: format!(
                    "struct `{}` field `{}` at recorded offset {offset} overruns the recorded \
                     size {size}",
                    def.name, field.name
                ),
            });
        }
        field_offsets.push((offset, f_lir));
    }
    if field_offsets.is_empty() {
        return Err(ModuleLirError::UnsupportedAggregate {
            name: name.to_string(),
            detail: format!("zero-field struct `{}` has nothing to load", def.name),
        });
    }
    Ok(AggMemLayout { size, align, field_offsets })
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
    lower_module_to_lir_maybe_cross_checked(module, func_id, None)
}

/// [`lower_module_to_lir`] with a [`AbiPassModeCrossCheck`] attached.
///
/// The token is the ONLY thing that admits a module declaring
/// `StructPassingPolicy::Unclassified` whose call edges carry a by-value
/// aggregate — see [`ModuleLirError::UnclassifiedAggregateAbi`] for why the
/// bare entry point must refuse such a module instead of classifying it. It
/// admits nothing else: a by-value aggregate edge under `NativeC` or
/// `AlwaysMemory`, and a recorded `ParamAttrs.pass` / `ParamAttrs.ext` /
/// `FuncAttrs.ret` fact under any policy, are refused with or without it
/// (trust-ir SPEC §17; see [`AbiPassModeCrossCheck`]).
///
/// Call this only from a consumer that has ALREADY checked every aggregate
/// argument and the return against the target's real pass modes; the token
/// records that claim, it does not verify it.
pub fn lower_module_to_lir_with_abi_cross_check(
    module: &Module,
    func_id: trust_ir::value::FuncId,
    cross_check: &AbiPassModeCrossCheck,
) -> Result<LirFunction, ModuleLirError> {
    lower_module_to_lir_maybe_cross_checked(module, func_id, Some(cross_check))
}

/// [`lower_module_to_lir`] with the cross-check CARRIED rather than named: for a
/// consumer that stores an `Option<AbiPassModeCrossCheck>` alongside the module
/// and re-lowers it later (the F1 proven-output gate does exactly this, so its
/// re-lowerings are admitted on the shipping path's evidence and on nothing
/// weaker). `None` behaves exactly like [`lower_module_to_lir`].
pub fn lower_module_to_lir_maybe_cross_checked(
    module: &Module,
    func_id: trust_ir::value::FuncId,
    cross_check: Option<&AbiPassModeCrossCheck>,
) -> Result<LirFunction, ModuleLirError> {
    let function =
        module.function_by_id(func_id).ok_or(ModuleLirError::MissingFunction(func_id.index()))?;
    lower_trust_ir_function_to_lir_impl(
        module,
        function,
        false,
        cross_check,
        AssertAdmission::Refuse,
    )
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
    lower_trust_ir_function_to_lir_impl(module, function, false, None, AssertAdmission::Refuse)
}

/// [`lower_trust_ir_function_to_lir`] with a [`AbiPassModeCrossCheck`] attached.
/// See [`lower_module_to_lir_with_abi_cross_check`].
pub fn lower_trust_ir_function_to_lir_with_abi_cross_check(
    module: &Module,
    function: &IrFunction,
    cross_check: &AbiPassModeCrossCheck,
) -> Result<LirFunction, ModuleLirError> {
    lower_trust_ir_function_to_lir_impl(
        module,
        function,
        false,
        Some(cross_check),
        AssertAdmission::Refuse,
    )
}

/// Like [`lower_trust_ir_function_to_lir`], but a `Call` to a LOCAL pure callee
/// in the gate's single-register AAPCS64 scalar fragment
/// ([`callee_is_real_call_composable`]) is lowered to a REAL LIR
/// `Opcode::Call { name, .. }` (ISel: `Bl` + an `ARM64_RELOC_BRANCH26` naming the
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
    lower_trust_ir_function_to_lir_impl(module, function, true, None, AssertAdmission::Refuse)
}

/// [`lower_trust_ir_function_to_lir_real_calls`] with a
/// [`AbiPassModeCrossCheck`] attached. The real-call arm emits a genuine
/// cross-function `Bl`, so it is the arm where an unclassified aggregate edge
/// would become a wrong ABI at a REAL boundary rather than an inlined one; it
/// carries the same admission, and the same way out.
/// See [`lower_module_to_lir_with_abi_cross_check`].
pub fn lower_trust_ir_function_to_lir_real_calls_with_abi_cross_check(
    module: &Module,
    function: &IrFunction,
    cross_check: &AbiPassModeCrossCheck,
) -> Result<LirFunction, ModuleLirError> {
    lower_trust_ir_function_to_lir_impl(
        module,
        function,
        true,
        Some(cross_check),
        AssertAdmission::Refuse,
    )
}

/// The indirect-return (`sret`) convention of `function`, read from trust-ir's
/// `ParamAttrs::sret` exactly as trust-cg's own adapter reads it
/// (trust-cg-lower `adapter.rs`, `[TCG-SRET-ABI]`), never re-derived from a
/// size rule. An aggregate that rustc returns through a caller-allocated buffer
/// (`PassMode::Indirect`) arrives as a LEADING pointer parameter marked `sret`
/// with an EMPTY return list (trust-ir validates that shape), and the selector
/// must bind that parameter from the indirect-result register (`X8` on AAPCS64)
/// instead of the first argument register. Dropping the marker is the
/// 2026-09-10 silent-wrong-value trust-cg 822fdc69 fixed: caller and callee each
/// self-consistent, disagreeing with every LLVM-compiled neighbour.
///
/// Returns the function's own marker (only a leading hidden parameter is
/// lowered; any other position fails closed, as the adapter does) and the
/// names of the DIRECT callees whose argument 0 is such a buffer, so ISel
/// classifies those calls' remaining arguments as if it were absent.
#[allow(rustc::default_hash_types)]
#[allow(rustc::default_hash_types)]
fn sret_convention(
    module: &Module,
    function: &IrFunction,
    name: &str,
) -> Result<
    (Option<AbiSretParam>, std::collections::HashSet<String>, std::collections::HashSet<Value>),
    ModuleLirError,
> {
    fn leading_sret(attrs: &trust_ir::FuncAttrs, symbol: &str) -> Result<bool, String> {
        match attrs.params.iter().position(|pa| pa.sret) {
            None => Ok(false),
            Some(0) => Ok(true),
            Some(index) => Err(format!(
                "[TCG-SRET-ABI] `{symbol}` declares its hidden return-buffer (sret) parameter \
                 at index {index}; only a LEADING hidden parameter is lowered. Failing closed \
                 rather than choosing an indirect-result register for it."
            )),
        }
    }
    let unsupported =
        |detail: String| ModuleLirError::UnsupportedSignature { name: name.to_string(), detail };
    let abi_sret_param = leading_sret(&function.attrs, name)
        .map_err(unsupported)?
        .then_some(AbiSretParam { param_index: 0 });
    // Callee scan. `function_by_id` is the resolver the real-call arm and the
    // inliner use, so what is marked is what is emitted. The fail-closed arm is a
    // defensive mirror of the adapter's: an sret callee has an EMPTY return list,
    // and this path only ever emits a real `Opcode::Call` to a callee returning
    // one single-register scalar, so such a call is refused as unsupported before
    // this scan runs.
    let mut sret_arg_callees = std::collections::HashSet::new();
    for node in function.blocks.iter().flat_map(|block| block.body.iter()) {
        if let Inst::Call { callee, .. } = &node.inst
            && let Some(callee_fn) = module.function_by_id(*callee)
            && leading_sret(&callee_fn.attrs, &callee_fn.name).map_err(unsupported)?
        {
            sret_arg_callees.insert(callee_fn.name.clone());
        }
    }
    // Indirect half (trust-cg de95c72d6, `Function::sret_arg_indirect_callees`):
    // the adapter records, keyed by LIR callee value, every `CallIndirect` whose
    // fn-pointer trust-ir's own provenance resolves to a declaration carrying a
    // leading `sret`, and lowers an unresolvable pointer as the ordinary call its
    // signature declares. This converter's real-call arm admits an indirect
    // callee only when it is a KNOWN, composable local pure function returning
    // exactly one single-register scalar; an sret callee has an EMPTY return
    // list, so it can never be emitted here, and an OPEN pointer carries no
    // expressible hidden-buffer fact on either side. The set is therefore
    // provably empty for every LIR this converter produces. The scan below is
    // the defensive mirror of the adapter's: a statically resolvable sret callee
    // behind an indirect call is refused by name BEFORE emission, rather than
    // reaching the real-call arm's generic "not composable" refusal with the ABI
    // fact silently dropped. `resolve` is the coarse chain walk (it may resolve
    // where the exact typed query would not), which is the safe direction for a
    // refusal.
    let sret_arg_indirect_callees: std::collections::HashSet<Value> =
        std::collections::HashSet::new();
    let provenance = trust_ir::analysis::StaticFunctionPointerAnalysis::new(function);
    for node in function.blocks.iter().flat_map(|block| block.body.iter()) {
        if let Inst::CallIndirect { callee, .. } = &node.inst
            && let Some(callee_fn) =
                resolve_static_indirect_callee(module, function, &provenance, *callee)
            && leading_sret(&callee_fn.attrs, &callee_fn.name).map_err(unsupported)?
        {
            return Err(unsupported(format!(
                "[TCG-SRET-ABI] an indirect call in `{name}` resolves statically to `{}`, \
                 whose declaration passes a hidden return-buffer (sret) pointer as argument \
                 0; this converter's composable indirect-call fragment admits only callees \
                 returning one single-register scalar, so the edge is refused before \
                 emission rather than lowered without the convention trust-cg's \
                 `Function::sret_arg_indirect_callees` would carry for it",
                callee_fn.name
            )));
        }
    }
    Ok((abi_sret_param, sret_arg_callees, sret_arg_indirect_callees))
}

/// Evidence — supplied by the CALLER of a lowering, never derived inside it —
/// that every by-value aggregate crossing a call edge in the module was
/// classified against an authority OUTSIDE trust-ir: one that knows the
/// target's real parameter passing modes.
///
/// # Why a token, and why the caller must be the one to mint it
///
/// `StructPassingPolicy::Unclassified` is a producer saying "I performed no
/// aggregate classification". A consumer that then classifies anyway has
/// manufactured an ABI out of nothing, and the failure mode is not a bad
/// diagnostic — it is a self-consistent object that disagrees with every
/// LLVM-compiled neighbour. Nothing INSIDE this crate can repair that: the
/// missing information (rustc's `PassMode` per argument and for the return) is
/// simply not in the `trust_ir::Module`. So the only sound admission is an
/// attestation from a caller that has the information and checked it.
///
/// The in-tree attester is `rustc_codegen_trust_cg`'s F1 frontend, which runs
/// `validate_codegen_instance_abi_trust_ir` — a per-argument and per-return
/// cross-check against rustc's `FnAbi`, refusing every `PassMode` outside its
/// audited set — on the very instance it is about to lower, immediately before
/// calling [`lower_module_to_lir_with_abi_cross_check`].
///
/// This token asserts NOTHING by itself and grants no proof authority: it
/// records WHO claimed the cross-check, so a refusal trail and a reader can see
/// which authority the admission rests on.
///
/// # What the token admits, and what it does not (trust-ir SPEC §17)
///
/// It admits a by-value aggregate edge ONLY in a module that declares
/// `StructPassingPolicy::Unclassified` — the one policy under which a consumer
/// places such a slot from an authority outside the module. Under `NativeC`
/// the module claims the target's C placement, which rustc's `FnAbi` does not
/// attest; under `AlwaysMemory` the module claims no such slot exists. Both
/// are refused whatever the token says, and so is a recorded
/// `ParamAttrs.pass` / `ParamAttrs.ext` / `FuncAttrs.ret` fact, which the token
/// (minted outside the module) says nothing about.
///
/// The in-tree attester mints it from rustc's `FnAbi` for the lowered INSTANCE
/// only, so it covers that function's own signature edge and no callee's.
/// Under it the admission still scans every `CallIndirect`'s declared `sig`
/// (`AggregateEdgeScan::IndirectEdgesOnly`): an indirect call is never spliced
/// inline, and the real-call arm realizes an OPEN one as a `BLR` after checking
/// only its arity and a scalar return, so an aggregate there is refused
/// (`UnclassifiedAggregateAbi`). What the token path does NOT scan is a direct
/// `Call`/`Invoke` callee edge. What keeps such an edge from becoming an
/// unattested ABI boundary is the lowering, not the admission. A direct call is
/// realized as a real `Bl` only for a callee in the single-register scalar
/// fragment (`callee_is_real_call_composable`, re-checked at the arm). Every
/// other direct call is spliced inline or refused, and `Invoke` is never
/// lowered. `a_token_does_not_admit_a_realized_aggregate_call_edge`
/// (`tests/module_to_lir_unclassified_aggregate_abi.rs`) pins both halves: the
/// direct-call half through `Call`, the indirect half through a known-target
/// and an open-target `CallIndirect`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiPassModeCrossCheck {
    authority: Cow<'static, str>,
    /// The CALLER-OWED INTEGER-EXTENSION facts of the cross-checked
    /// function's own parameter slots (WS7.13). `None` = NOT RECORDED, which
    /// every consumer treats as "no extension promise exists", never as a
    /// wildcard.
    param_extensions: Option<AbiParamExtensions>,
}

impl AbiPassModeCrossCheck {
    /// Record that `authority` cross-checked this module's aggregate call edges
    /// against the target's real pass modes.
    #[must_use]
    pub fn attested_by(authority: impl Into<Cow<'static, str>>) -> Self {
        Self { authority: authority.into(), param_extensions: None }
    }

    /// Attach the caller-owed extension facts of the cross-checked function's
    /// parameter slots (see [`AbiParamExtensions`]). Like the token itself,
    /// this is an ATTESTATION the caller of a lowering makes from information
    /// the `Module` does not carry (rustc's `ArgAttributes::arg_ext` per slot
    /// and the target's small-argument rule); the gate CONSUMES it and grants
    /// nothing on its own.
    #[must_use]
    pub fn with_param_extensions(mut self, extensions: AbiParamExtensions) -> Self {
        self.param_extensions = Some(extensions);
        self
    }

    /// The recorded authority, for diagnostics and provenance.
    #[must_use]
    pub fn authority(&self) -> &str {
        &self.authority
    }

    /// The recorded parameter-extension facts, if the attester recorded any.
    #[must_use]
    pub fn param_extensions(&self) -> Option<&AbiParamExtensions> {
        self.param_extensions.as_ref()
    }
}

/// rustc's `ArgExtension` for ONE argument slot, mirrored so the bridge (which
/// cannot see `rustc_target`) can carry it: does the CALLER owe the callee an
/// extended value above the slot's declared width?
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbiArgExtension {
    /// `ArgExtension::None` — the caller owes nothing above the declared
    /// width, and the callee may read nothing above it.
    None,
    /// `ArgExtension::Zext` — the caller zero-extends the value across the
    /// extension width the target ABI names (the `bool` contract on the Rust
    /// ABI: `arg_attrs_for_rust_scalar`, "Booleans are always a noundef i1
    /// that needs to be zero-extended").
    Zext,
    /// `ArgExtension::Sext` — the caller sign-extends.
    Sext,
}

/// The caller-owed extension facts for a function's parameter slots, in
/// signature order (WS7.13).
///
/// # Why the gate needs this, and why it must be RECORDED rather than inferred
///
/// A `bool` parameter arrives in a `W` register the CALLER wrote. rustc marks
/// every bool slot `arg_ext: Zext`, and on a target whose ABI makes the caller
/// perform that extension (Apple AArch64: "The caller of a function is
/// responsible for signing or zero-extending any argument with fewer than 32
/// bits") the callee may read the whole extended register and see exactly 0
/// or 1. The proven-output gate models a bool parameter ONLY under that
/// precondition (`W{k}[31:1] == 0`), and it can neither read `arg_ext` off a
/// `trust_ir::Module` (the Module has no such field) nor decide what the target
/// makes the caller owe. Both facts are therefore ATTESTED here by the caller
/// of the lowering — in-tree, `rustc_codegen_trust_cg`'s F1 frontend, which has
/// rustc's `FnAbi` and the session target in hand — and consumed by the gate as
/// a named trust assumption on every caller (C callers included), spelled into
/// the obligation's `ambient_pre` so it appears in the certificate's assumption
/// list and not only in the evidence grade.
///
/// A missing entry, an extension other than `Zext`, or a target that makes no
/// caller-side promise (`caller_extends_to_bits: None`, e.g. generic AAPCS64,
/// where the callee may not assume the caller extended) leaves a bool
/// parameter `Unknown` — the pre-WS7.13 fail-closed answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiParamExtensions {
    /// One entry per PARAMETER of the cross-checked function's signature (the
    /// same count the ABI validator pins against rustc's `FnAbi.args`).
    /// `None` = the slot's extension was NOT RECORDED (a non-`Direct` pass
    /// mode has no single extension attribute); it is never read as
    /// [`AbiArgExtension::None`].
    pub per_param: Vec<Option<AbiArgExtension>>,
    /// The width, in bits, to which the target ABI makes the CALLER extend a
    /// `Zext`/`Sext` small argument — `Some(32)` on Apple AArch64. `None` means
    /// the target makes no such promise and the callee owns the extension.
    pub caller_extends_to_bits: Option<u32>,
}

impl AbiParamExtensions {
    /// The extension recorded for parameter `index`, if any.
    #[must_use]
    pub fn extension_of(&self, index: usize) -> Option<AbiArgExtension> {
        self.per_param.get(index).copied().flatten()
    }
}

/// Does `ty` cross a call edge as a BY-VALUE AGGREGATE, for the purposes of the
/// `struct_passing` admission?
///
/// This is the PRODUCER's predicate, held identical on purpose:
/// `trust_thir_lower::stamp_target_info_if_vacuous`'s own
/// `crosses_by_value_aggregate` allow-lists exactly these non-aggregates and
/// treats everything else — *including any variant added to `Ty` later* — as an
/// aggregate. Keeping one predicate on both sides means the consumer refuses
/// exactly the set the producer declined to classify; an over-permissive copy
/// here would admit precisely the modules the ruling exists to stop, so unknown
/// must mean "aggregate".
///
/// It is a FAIL-CLOSED SUPERSET of the predicate trust-ir now states once
/// (SPEC §17, `Module::is_by_value_aggregate_slot`: through one `Refine`, a
/// `Struct`, `Tuple`, `Array`, `Enum`, `Record`, `Sequence`, `Set`, `Closure`
/// or `Vector`). Every slot §17 calls an aggregate is non-scalar and so is
/// refused here too; this copy also counts thin typed pointers, `FatPtr`,
/// `Handle` and a refined scalar, which §17 places by non-aggregate rules —
/// refusing more than the format requires, never less. Reading the format's
/// predicate instead waits on the `first-party/trust-ir` gitlink reaching that
/// ratification; the pinned revision predates it.
fn crosses_by_value_aggregate(ty: &Ty) -> bool {
    !matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never
    )
}

/// The module function a `CallIndirect`'s callee operand names STATICALLY, or
/// `None` when it cannot be resolved.
///
/// Two static shapes name a callee: trust-ir's own (`Const FnDef` through
/// `Copy` / `ReifyFnPointer`, the adapter's source), and this converter's
/// KNOWN-target shape (`GlobalAddr` of a module global whose NAME is the
/// function symbol, exactly what the real-call arm's `global_addr_provenance`
/// resolves through `function_by_name`). `resolve` is the coarse chain walk (it
/// may resolve where the exact typed query would not), which is the safe
/// direction for the refusals that use it.
fn resolve_static_indirect_callee<'m>(
    module: &'m Module,
    function: &IrFunction,
    provenance: &trust_ir::analysis::StaticFunctionPointerAnalysis<'_>,
    callee: ValueId,
) -> Option<&'m IrFunction> {
    if let Some(target) = provenance.resolve(callee) {
        return module.function_by_id(target);
    }
    let defining = function
        .blocks
        .iter()
        .flat_map(|block| block.body.iter())
        .find(|node| node.results.contains(&callee))?;
    let Inst::GlobalAddr { global } = &defining.inst else {
        return None;
    };
    let global = module.globals.get(global.index() as usize)?;
    module.function_by_name(&global.name)
}

/// REFUSE BY NAME a recorded slot ABI fact this converter does not read:
/// `ParamAttrs.pass`, a non-`None` `ParamAttrs.ext`, or any `FuncAttrs.ret`
/// fact. See [`ModuleLirError::RecordedAbiSlotFact`].
///
/// Reads the lowered function's own attributes (its callers' edge), every
/// resolvable direct `Call`/`Invoke` callee's, and every `CallIndirect` callee
/// that resolves statically ([`resolve_static_indirect_callee`]); a
/// `CallIndirect` through an open pointer names only a `FuncTy`, which carries
/// no attributes. Runs under every policy and with or without a pinned target.
fn refuse_recorded_abi_slot_facts(
    module: &Module,
    function: &IrFunction,
) -> Result<(), ModuleLirError> {
    let refuse = |detail: String| ModuleLirError::RecordedAbiSlotFact {
        name: function.name.clone(),
        detail,
    };
    let check = |subject: &IrFunction, edge: &str| -> Result<(), ModuleLirError> {
        let attrs = &subject.attrs;
        for (index, param) in attrs.params.iter().enumerate() {
            if let Some(mode) = &param.pass {
                return Err(refuse(format!(
                    "{edge} records `ParamAttrs.pass = {}` on parameter {index}",
                    mode.token()
                )));
            }
            if let Some(token) = param.ext.token() {
                return Err(refuse(format!(
                    "{edge} records `ParamAttrs.ext = {token}` on parameter {index}"
                )));
            }
        }
        if !attrs.ret.is_empty() {
            return Err(refuse(format!(
                "{edge} records a `FuncAttrs.ret` return-slot fact ({:?})",
                attrs.ret
            )));
        }
        Ok(())
    };

    check(function, "the function's own signature (the edge its callers use)")?;
    let provenance = trust_ir::analysis::StaticFunctionPointerAnalysis::new(function);
    for node in function.blocks.iter().flat_map(|block| block.body.iter()) {
        match &node.inst {
            Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => {
                if let Some(callee_fn) = module.function_by_id(*callee) {
                    check(callee_fn, &format!("the call edge to `{}`", callee_fn.name))?;
                }
            }
            Inst::CallIndirect { callee, .. } => {
                if let Some(callee_fn) =
                    resolve_static_indirect_callee(module, function, &provenance, *callee)
                {
                    check(
                        callee_fn,
                        &format!(
                            "an indirect call edge that resolves statically to `{}`",
                            callee_fn.name
                        ),
                    )?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Which call edges [`first_by_value_aggregate_edge`] reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AggregateEdgeScan {
    /// Every edge the lowering reads: the function's own signature, every
    /// direct `Call`/`Invoke` callee's, and every `CallIndirect`'s declared
    /// `sig`. The scan when no [`AbiPassModeCrossCheck`] places anything.
    Every,
    /// Only the edges an [`AbiPassModeCrossCheck`] leaves OPEN under
    /// `Unclassified`: every `CallIndirect`'s declared `sig`.
    ///
    /// The token places the lowered instance's OWN signature edge and nothing
    /// else. A direct `Call` edge carrying an aggregate is never realized — the
    /// real-call arm emits a `Bl` only for a callee that passes
    /// [`callee_is_real_call_composable`] (every parameter and the return a
    /// single-register scalar), re-checked at the arm itself, and every other
    /// direct call is spliced inline or refused (`Invoke` is never lowered).
    /// A `CallIndirect` is NEVER spliced, and the real-call arm realizes an
    /// OPEN one as a `BLR` after checking only its arity and a scalar return;
    /// so an aggregate on its declared `sig` is a slot nobody placed, and it is
    /// scanned exactly as without a token.
    IndirectEdgesOnly,
}

/// The first call edge of `function` that carries a by-value aggregate
/// ([`crosses_by_value_aggregate`]) or whose signature cannot be resolved, as
/// the refusal's detail; `None` when no edge the scan reads carries one.
///
/// THE SCAN IS A FAIL-CLOSED SUPERSET of the edges the lowering realizes. It
/// runs BEFORE the inline pre-pass, so a call the inliner would have spliced
/// away still counts: an inlined edge is not an ABI boundary, but deciding that
/// here would make the admission depend on a later pass's success, and the
/// direction of the error would be "admitted something it should have refused".
/// Under [`AggregateEdgeScan::Every`] it reads the function's own signature (its
/// callers' edge), every direct `Call`/`Invoke` callee's declared signature, and
/// every `CallIndirect`'s declared `sig`; under
/// [`AggregateEdgeScan::IndirectEdgesOnly`] only the last. An edge whose
/// signature cannot be RESOLVED is reported rather than skipped.
fn first_by_value_aggregate_edge(
    module: &Module,
    function: &IrFunction,
    scan: AggregateEdgeScan,
) -> Option<String> {
    let check_edge = |ty_id: trust_ir::value::FuncTyId, edge: &str| -> Option<String> {
        let Some(ft) = module.func_types.get(ty_id.as_usize()) else {
            return Some(format!(
                "{edge} names func_type id {} which the module does not carry, so whether an \
                 aggregate crosses it cannot be decided",
                ty_id.as_usize()
            ));
        };
        for (index, param) in ft.params.iter().enumerate() {
            if crosses_by_value_aggregate(param) {
                return Some(format!(
                    "{edge} passes parameter {index} ({param:?}) BY VALUE, and that is an \
                     aggregate crossing an ABI boundary"
                ));
            }
        }
        for (index, ret) in ft.returns.iter().enumerate() {
            if crosses_by_value_aggregate(ret) {
                return Some(format!(
                    "{edge} returns result {index} ({ret:?}) BY VALUE, and that is an aggregate \
                     crossing an ABI boundary"
                ));
            }
        }
        None
    };

    let direct_edges = scan == AggregateEdgeScan::Every;
    if direct_edges
        && let Some(detail) =
            check_edge(function.ty, "the function's own signature (the edge its callers use)")
    {
        return Some(detail);
    }
    for node in function.blocks.iter().flat_map(|block| block.body.iter()) {
        let found = match &node.inst {
            Inst::Call { callee, .. } | Inst::Invoke { callee, .. } if direct_edges => {
                match module.function_by_id(*callee) {
                    Some(callee_fn) => {
                        check_edge(callee_fn.ty, &format!("the call edge to `{}`", callee_fn.name))
                    }
                    None => Some(format!(
                        "a call names callee id {} which is not in the module, so the edge's \
                         signature cannot be read",
                        callee.index()
                    )),
                }
            }
            Inst::CallIndirect { sig, .. } => {
                check_edge(*sig, "an indirect call edge's declared signature").map(|detail| {
                    if direct_edges {
                        detail
                    } else {
                        format!(
                            "{detail} — and the pass-mode cross-check attached to this lowering \
                             places only the lowered function's OWN signature edge: an indirect \
                             call edge is never spliced inline, so no authority placed this slot"
                        )
                    }
                })
            }
            _ => None,
        };
        if found.is_some() {
            return found;
        }
    }
    None
}

/// REFUSE BY NAME rather than guess: the `struct_passing` admission (trust-ir
/// SPEC §17, ratified 2026-09-27).
///
/// ONE RULE: a by-value aggregate edge is admitted ONLY in a module declaring
/// `StructPassingPolicy::Unclassified` AND lowered with an
/// [`AbiPassModeCrossCheck`] — the one case where the placement comes from an
/// authority outside the module (rustc's `FnAbi`, per the token's attester).
/// The token places the lowered instance's OWN signature edge, so under it the
/// scan narrows to [`AggregateEdgeScan::IndirectEdgesOnly`]: a direct callee
/// edge with an aggregate is spliced inline or refused, never realized, while a
/// `CallIndirect` edge is never spliced and stays refused. Every other pinned
/// case refuses the first such edge by the policy's own variant:
///
/// * `Unclassified` without a token — and, with one, an aggregate on a
///   `CallIndirect`'s declared `sig` — [`ModuleLirError::UnclassifiedAggregateAbi`];
/// * `NativeC`, with or without a token —
///   [`ModuleLirError::NativeCAggregateAbiUnsupported`] (this converter
///   implements no native-C aggregate ruleset);
/// * `AlwaysMemory`, with or without a token —
///   [`ModuleLirError::AlwaysMemoryByValueAggregate`] (the module contradicts
///   its own policy).
///
/// Before that, and under EVERY policy (a pinned target or none, a token or
/// none), a recorded `ParamAttrs.pass` / `ParamAttrs.ext` / `FuncAttrs.ret`
/// fact is refused ([`ModuleLirError::RecordedAbiSlotFact`]).
///
/// `target_info: None` is a module that pins no target and so states no
/// policy; the aggregate half stays out of scope for it
/// (`an_unpinned_target_is_out_of_this_gate_s_scope`), a residual trust-ir's
/// §17 names. The exhaustive `match` below is deliberate: a policy variant
/// added to trust-ir (the proposed `PreLowered`) fails to compile here until
/// someone decides what it admits.
fn admit_struct_passing_policy(
    module: &Module,
    function: &IrFunction,
    cross_check: Option<&AbiPassModeCrossCheck>,
) -> Result<(), ModuleLirError> {
    refuse_recorded_abi_slot_facts(module, function)?;

    let Some(target) = module.target_info.as_ref() else {
        return Ok(());
    };
    let policy = target.struct_passing;
    // The caller has the pass modes and says it checked them — for the lowered
    // instance's own signature, which is all rustc's `FnAbi` for that instance
    // covers. Recorded, not re-derived — there is nothing in the Module to
    // re-derive it from — and honoured under `Unclassified` ONLY. It narrows the
    // scan; it never ends it (an indirect call edge is not the instance's own).
    let scan = if policy == trust_ir::StructPassingPolicy::Unclassified && cross_check.is_some() {
        AggregateEdgeScan::IndirectEdgesOnly
    } else {
        AggregateEdgeScan::Every
    };
    let Some(detail) = first_by_value_aggregate_edge(module, function, scan) else {
        return Ok(());
    };
    let name = function.name.clone();
    Err(match policy {
        trust_ir::StructPassingPolicy::Unclassified => {
            ModuleLirError::UnclassifiedAggregateAbi { name, detail }
        }
        trust_ir::StructPassingPolicy::NativeC => {
            ModuleLirError::NativeCAggregateAbiUnsupported { name, detail }
        }
        trust_ir::StructPassingPolicy::AlwaysMemory => {
            ModuleLirError::AlwaysMemoryByValueAggregate { name, detail }
        }
    })
}

/// Whether a lowering refuses `Inst::Assert` (every codegen entry point) or
/// lowers it to the bare trap (the test oracle only).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AssertAdmission {
    /// Refuse the function: [`ModuleLirError::ImplicitPanicUnfaithful`].
    Refuse,
    /// Lower `Assert` to `Brif(cond, cont, trap)` — the pre-2026-09-30
    /// behaviour, reachable only through
    /// `lower_trust_ir_function_to_lir_trap_assert_oracle`.
    #[cfg_attr(not(any(test, feature = "test-hooks")), allow(dead_code))]
    TrapOracle,
}

/// TEST ORACLE — NOT A CODEGEN ENTRY POINT. Lowers `function` exactly as every
/// other entry point does, EXCEPT that an `Inst::Assert` is lowered to the
/// bare `Brif(cond, cont, trap)` that [`ModuleLirError::ImplicitPanicUnfaithful`]
/// refuses everywhere else (`real_calls` selects the real-call arm, as
/// [`lower_trust_ir_function_to_lir_real_calls`] does).
///
/// It exists so the trap lowering and the proven-output gate's `Assert`-reach
/// model — both kept for plan §5 item P — stay under test while no codegen
/// consumer may reach them. Its bytes are faithful to trust-ir (where a failed
/// `Assert` IS a divergence) and unfaithful to Rust (no panic message, no hook,
/// SIGTRAP), which is exactly why nothing that ships may call it: it is
/// `#[doc(hidden)]`, compiled only for this crate's unit tests and under the
/// non-default `test-hooks` feature (which the compiler never enables; the
/// census tripwire `compiler_consumer::census::no_compiler_caller` checks the
/// plugin's, `crates/`' and `targo-trust/`'s sources and manifests for it).
///
/// Every call also CROSS-CHECKS the shipping path on the same input, so each
/// test that lowers through the oracle pins the shipping refusal too: when
/// `function` carries an `Assert` of its own, the shipping lowering must refuse
/// it as [`ModuleLirError::ImplicitPanicUnfaithful`]; and whenever the oracle
/// lowers successfully, the shipping lowering must either succeed (no `Assert`
/// even after inlining) or refuse by exactly that name — never fail some other
/// way. A violation panics: this function exists only for tests.
///
/// # Errors
///
/// Every [`ModuleLirError`] the shipping entry points return, except
/// [`ModuleLirError::ImplicitPanicUnfaithful`].
///
/// # Panics
///
/// When the shipping lowering disagrees with the oracle as described above.
#[cfg(any(test, feature = "test-hooks"))]
#[doc(hidden)]
pub fn lower_trust_ir_function_to_lir_trap_assert_oracle(
    module: &Module,
    function: &IrFunction,
    real_calls: bool,
) -> Result<LirFunction, ModuleLirError> {
    let oracle = lower_trust_ir_function_to_lir_impl(
        module,
        function,
        real_calls,
        None,
        AssertAdmission::TrapOracle,
    );
    let shipping = lower_trust_ir_function_to_lir_impl(
        module,
        function,
        real_calls,
        None,
        AssertAdmission::Refuse,
    );
    let refused_by_name = matches!(&shipping, Err(ModuleLirError::ImplicitPanicUnfaithful { .. }));
    assert!(
        !function_has_unfaithful_assert(function) || refused_by_name,
        "trap oracle cross-check: `{}` carries an `Assert`, but the SHIPPING lowering did not \
         refuse it as ImplicitPanicUnfaithful: {:?}",
        function.name,
        shipping.as_ref().map(|_| "Ok(..)").map_err(ModuleLirError::to_string),
    );
    if oracle.is_ok() {
        assert!(
            shipping.is_ok() || refused_by_name,
            "trap oracle cross-check: `{}` lowers under the oracle, but the SHIPPING lowering \
             failed for another reason: {:?}",
            function.name,
            shipping.as_ref().map(|_| "Ok(..)").map_err(ModuleLirError::to_string),
        );
    }
    oracle
}

fn lower_trust_ir_function_to_lir_impl(
    module: &Module,
    function: &IrFunction,
    real_calls: bool,
    cross_check: Option<&AbiPassModeCrossCheck>,
    assert_admission: AssertAdmission,
) -> Result<LirFunction, ModuleLirError> {
    // PRE-PASS: inline admitted local pure leaf calls. Returns the original
    // function unchanged when it contains no inlinable call. When `real_calls` is
    // set, a call to a gate-composable local pure callee is DEFERRED (left in
    // place) so the body lowering below emits a REAL `Opcode::Call` for it; all
    // other calls still go through the inliner.
    // Trust: affirmative producer gate, checked BEFORE the inline pre-pass so a
    // Clean body is refused by name rather than by whatever shape it happens to
    // have. See `ModuleLirError::CleanOriginBelowCodegenGate`.
    if function.producer == Some(trust_ir::Producer::Clean) {
        return Err(ModuleLirError::CleanOriginBelowCodegenGate {
            name: function.name.clone(),
            detail: "it is the function being lowered".to_string(),
        });
    }
    // Trust (bridge-abi): the `struct_passing` admission. Checked BEFORE the
    // inline pre-pass so an `Unclassified` module carrying an aggregate call
    // edge is refused BY NAME, rather than reaching the size-rule classifiers
    // below and being given a convention nobody declared. See
    // `ModuleLirError::UnclassifiedAggregateAbi`.
    admit_struct_passing_policy(module, function, cross_check)?;
    // Trust (plan §5 fail-open item 1): an implicit panic has no faithful
    // lowering here, so a body carrying an `Assert` is refused BY NAME before
    // anything is lowered — first the function's own, then (after the inline
    // pre-pass, which admits `Assert` in a spliced callee) one an inlined
    // callee brought in. See `ModuleLirError::ImplicitPanicUnfaithful`.
    let refuse_asserts = assert_admission == AssertAdmission::Refuse;
    if let Some(site) = unfaithful_assert_site(function).filter(|_| refuse_asserts) {
        return Err(ModuleLirError::ImplicitPanicUnfaithful {
            name: function.name.clone(),
            detail: format!(
                "its own body carries an `Assert` (block {}, node {})",
                site.block.index(),
                site.index
            ),
        });
    }
    let inlined = inline_local_pure_leaf_calls(module, function, real_calls)?;
    let function: &IrFunction = inlined.as_ref();
    let name = &function.name;
    if refuse_asserts && function_has_unfaithful_assert(function) {
        return Err(ModuleLirError::ImplicitPanicUnfaithful {
            name: name.clone(),
            detail: "a callee the inline pre-pass spliced into it carries an `Assert`".to_string(),
        });
    }

    // The sret convention (own hidden-return parameter, direct sret callees,
    // and the indirect scan's by-name refusal) is read from the declarations
    // BEFORE any block is lowered: the real-call arm below refuses a
    // non-composable indirect callee generically, and the ABI fact must be
    // named ahead of that generic refusal, not lost behind it.
    let (abi_sret_param, sret_arg_callees, sret_arg_indirect_callees) =
        sret_convention(module, function, name)?;

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
    // FAT SLICE PARAMETERS (`&[T]`): rustc passes a slice reference as a
    // ScalarPair — data pointer in one GPR slot, length in the next — and the
    // AArch64 classifier assigns two consecutive I64 params exactly those
    // slots. So a `FatPtr(Slice(elem))` formal SPLITS into two I64 LIR params
    // in place, provided the element is a scalar the memory slice can load;
    // every other fat-pointer position (returns, block params, values) stays
    // fail-closed. `Str` and trait objects stay refused here too — only the
    // measured slice shape is admitted.
    let mut params = Vec::with_capacity(func_ty.params.len());
    let mut fat_param_sig: Vec<Option<LirType>> = Vec::with_capacity(func_ty.params.len());
    // Positional record of UNIT (`()`) formals. A unit value is a ZST with no
    // machine content: rustc's ABI ignores it (PassMode::Ignore), so it
    // occupies NO LIR parameter slot — the contraction twin of the fat-slice
    // expansion above. The param's ValueId is deliberately left UNBOUND, so
    // any body use of the unit value fails closed as an undefined value; the
    // measured shape (a captureless closure's `()` environment formal) never
    // reads it.
    let mut unit_param_sig: Vec<bool> = Vec::with_capacity(func_ty.params.len());
    // Positional record of BY-VALUE INDIRECT struct formals (the recorded
    // layout of each; `None` for every other param kind).
    let mut indirect_struct_sig: Vec<Option<AggMemLayout>> =
        Vec::with_capacity(func_ty.params.len());
    // Positional record of BY-VALUE PAIR struct formals (<=16 bytes, exactly
    // two plain-scalar fields).
    let mut pair_struct_sig: Vec<Option<AggMemLayout>> = Vec::with_capacity(func_ty.params.len());
    // Positional record of BY-VALUE NEWTYPE struct formals (one plain-scalar
    // field riding Direct as the field scalar).
    let mut newtype_struct_sig: Vec<Option<LirType>> = Vec::with_capacity(func_ty.params.len());
    // Positional record of PAIR-ENUM formals ((tag, payload) register pairs).
    let mut pair_enum_sig: Vec<Option<PairEnumView>> = Vec::with_capacity(func_ty.params.len());
    for p in &func_ty.params {
        if matches!(p, Ty::Unit) {
            fat_param_sig.push(None);
            unit_param_sig.push(true);
            indirect_struct_sig.push(None);
            pair_struct_sig.push(None);
            newtype_struct_sig.push(None);
            pair_enum_sig.push(None);
            continue;
        }
        unit_param_sig.push(false);
        if let Ty::FatPtr(trust_ir::ty::FatPtrKind::Slice(elem_tid)) = p {
            let elem_ty = module.types.get(elem_tid.as_usize()).ok_or_else(|| {
                ModuleLirError::UnsupportedSignature {
                    name: name.clone(),
                    detail: format!(
                        "slice parameter names element type id {} the module lacks",
                        elem_tid.as_usize()
                    ),
                }
            })?;
            let elem = map_scalar_mem_ty(elem_ty, name, "slice element")?;
            params.push(LirType::I64); // data pointer
            params.push(LirType::I64); // length
            fat_param_sig.push(Some(elem));
            indirect_struct_sig.push(None);
            pair_struct_sig.push(None);
            newtype_struct_sig.push(None);
            pair_enum_sig.push(None);
        } else if let Some(view) = pair_enum_view(module, p) {
            // A small Direct-tagged enum rides rustc's ScalarPair: (tag,
            // payload) in two register formals — `Option<u64>`-class shapes.
            params.push(view.tag.clone());
            params.push(view.payload.clone());
            pair_enum_sig.push(Some(view));
            fat_param_sig.push(None);
            indirect_struct_sig.push(None);
            pair_struct_sig.push(None);
            newtype_struct_sig.push(None);
            continue;
        } else if let Ty::Struct(_) = p {
            // A BY-VALUE struct larger than 16 bytes: AAPCS64 passes it
            // INDIRECTLY (a hidden pointer in one GPR). The recorded rustc
            // layout is required (field reads go through the pointer at
            // recorded offsets), and the F1 ABI validator independently
            // refuses the item unless rustc's real PassMode is Indirect —
            // a converter/ABI disagreement is a refusal, never a miscompile.
            // A <=16-byte struct (Direct/Pair modes) stays refused, and a
            // layout the recorded lane cannot admit carries ITS OWN reason.
            let layout = recorded_struct_mem_layout(p, module, name).map_err(|e| {
                ModuleLirError::UnsupportedSignature {
                    name: name.clone(),
                    detail: format!("by-value struct parameter not admitted: {e}"),
                }
            })?;
            if layout.size <= 16 {
                // EXACTLY TWO plain-scalar fields ride rustc's PassMode::Pair:
                // two register formals in LAYOUT (offset) order. The
                // declaration-order mapping absorbs a repr(Rust) reorder.
                // Anything else at <=16 bytes (1 or 3+ fields, enum-typed
                // fields whose register scalar is a niche encoding) stays
                // refused by name.
                // A SINGLE plain-scalar field is a newtype: rustc passes it
                // Direct as the field scalar itself — one formal.
                if layout.field_offsets.len() == 1 {
                    let field_plain = match p {
                        Ty::Struct(sid) => module.structs.get(sid.as_usize()).is_some_and(|def| {
                            def.fields
                                .iter()
                                .all(|f| scalar_field_size_align(&f.ty, module, name).is_ok())
                        }),
                        _ => false,
                    };
                    if !field_plain {
                        return Err(ModuleLirError::UnsupportedSignature {
                            name: name.clone(),
                            detail: "by-value newtype struct parameter has a non-plain-scalar \
                                     field"
                                .to_string(),
                        });
                    }
                    params.push(layout.field_offsets[0].1.clone());
                    newtype_struct_sig.push(Some(layout.field_offsets[0].1.clone()));
                    pair_enum_sig.push(None);
                    pair_struct_sig.push(None);
                    indirect_struct_sig.push(None);
                    fat_param_sig.push(None);
                    continue;
                }
                if layout.field_offsets.len() != 2 {
                    return Err(ModuleLirError::UnsupportedSignature {
                        name: name.clone(),
                        detail: format!(
                            "by-value struct parameter of {} bytes with {} fields does not ride \
                             the two-register Pair form this lane admits",
                            layout.size,
                            layout.field_offsets.len()
                        ),
                    });
                }
                let field_tys_plain = match p {
                    Ty::Struct(sid) => module.structs.get(sid.as_usize()).is_some_and(|def| {
                        def.fields
                            .iter()
                            .all(|f| scalar_field_size_align(&f.ty, module, name).is_ok())
                    }),
                    _ => false,
                };
                if !field_tys_plain {
                    return Err(ModuleLirError::UnsupportedSignature {
                        name: name.clone(),
                        detail: "by-value Pair struct parameter has a non-plain-scalar field \
                                 (an enum's register scalar may be a niche encoding this lane \
                                 cannot decode)"
                            .to_string(),
                    });
                }
                pair_struct_sig.push(Some(layout.clone()));
                newtype_struct_sig.push(None);
                pair_enum_sig.push(None);
                // Formals in LAYOUT order.
                let mut order: Vec<usize> = vec![0, 1];
                order.sort_by_key(|&i| layout.field_offsets[i].0);
                for &i in &order {
                    params.push(layout.field_offsets[i].1.clone());
                }
                indirect_struct_sig.push(None);
                fat_param_sig.push(None);
                continue;
            }
            params.push(LirType::I64); // hidden pointer to the caller's copy
            indirect_struct_sig.push(Some(layout));
            pair_struct_sig.push(None);
            newtype_struct_sig.push(None);
            pair_enum_sig.push(None);
            fat_param_sig.push(None);
            continue;
        } else if matches!(p, Ty::FatPtr(trust_ir::ty::FatPtrKind::Str)) {
            // `&str` is `&[u8]` at the machine level: the SAME ScalarPair
            // (data pointer, byte length) in two consecutive GPR slots, with
            // BYTE element loads through the data pointer. UTF-8 validity is a
            // producer-side type-system fact, not a machine-level one — no
            // byte this lane can load or compare depends on it.
            params.push(LirType::I64); // data pointer
            params.push(LirType::I64); // byte length
            fat_param_sig.push(Some(LirType::I8));
            indirect_struct_sig.push(None);
            pair_struct_sig.push(None);
            newtype_struct_sig.push(None);
            pair_enum_sig.push(None);
        } else {
            params.push(map_scalar_int_ty_in(module, p, "function parameter")?);
            fat_param_sig.push(None);
            indirect_struct_sig.push(None);
            pair_struct_sig.push(None);
            newtype_struct_sig.push(None);
            pair_enum_sig.push(None);
        }
    }
    // ZERO returns is a VOID function (`fn f()` is `(…) -> ()` with an empty
    // returns list): the established MIR path already emits these as an empty
    // LIR `returns` plus a bare `Opcode::Return` (see lower.rs
    // `ordinary_unit_function_remains_void`), so the shape is backend-proven.
    // ONE return maps through the scalar slice; more than one stays refused.
    let signature = match func_ty.returns.as_slice() {
        [] => Signature { params, returns: vec![] },
        [r] if pair_enum_view(module, r).is_some() => {
            // A small Direct-tagged enum RETURNS as its (tag, payload)
            // register pair — x0/x1, exactly the ScalarPair rustc assigns.
            let view = pair_enum_view(module, r).expect("guarded");
            Signature { params, returns: vec![view.tag, view.payload] }
        }
        [r] => {
            let return_ty = map_scalar_int_ty_in(module, r, "function return")?;
            Signature { params, returns: vec![return_ty] }
        }
        more => {
            return Err(ModuleLirError::UnsupportedSignature {
                name: name.clone(),
                detail: format!("expected at most 1 return value, got {}", more.len()),
            });
        }
    };

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
    let mut entry_fat_params: HashMap<ValueId, FatSliceParam> = HashMap::new();
    let mut entry_indirect_structs: HashMap<ValueId, IndirectStructParam> = HashMap::new();
    let mut entry_pair_structs: HashMap<ValueId, PairStructParam> = HashMap::new();
    let mut entry_newtype_structs: HashMap<ValueId, LirType> = HashMap::new();
    // PAIR-ENUM SSA values: trust-ir ValueId -> (tag LIR value, payload LIR
    // value). Params, block params, and instruction results all register
    // here; any use of a pair-enum value outside the supported arms fails
    // closed as an undefined value (the id is never in the ValueMap).
    let mut pair_enum_values: HashMap<ValueId, (Value, Value)> = HashMap::new();
    // FIELDLESS-ENUM tag carriers, by trust-ir ValueId. A value recorded here
    // was admitted through `fieldless_enum_carrier` (its whole machine value IS
    // the discriminant tag), so an `ExtractField { field: 0 }` typed at the tag
    // repr is an identity read — see the ExtractField arm in
    // `lower_value_inst`. Only param/block-param bindings populate it; every
    // other enum-typed position keeps failing closed.
    let mut enum_tag_values: HashMap<ValueId, LirType> = HashMap::new();
    // Entry params of opaque pointer type (`Ty::Ptr` — `&self`, `&T` thin
    // references). The aggregate slice admits WHOLE-AGGREGATE LOADS through
    // these as read-only roots (the aggregate analogue of the fat-slice
    // element loads); stores through them stay fail-closed.
    let mut ptr_params: std::collections::HashSet<ValueId> = std::collections::HashSet::new();
    for (index, ((param_id, param_ty), sig_ty)) in
        entry_block.params.iter().zip(&func_ty.params).enumerate()
    {
        if param_ty != sig_ty {
            return Err(ModuleLirError::UnsupportedSignature {
                name: name.clone(),
                detail: format!(
                    "entry block param type {param_ty:?} disagrees with signature {sig_ty:?}"
                ),
            });
        }
        // A UNIT (`()`) param binds NOTHING: no LIR slot, no Value. Any body
        // use of it fails closed as an undefined value.
        if unit_param_sig.get(index).copied().unwrap_or(false) {
            continue;
        }
        // A PAIR-ENUM param binds TWO anonymous formals: (tag, payload).
        if pair_enum_sig.get(index).and_then(|o| o.as_ref()).is_some() {
            let tag = vmap.define_anonymous();
            let pay = vmap.define_anonymous();
            let view = pair_enum_sig[index].as_ref().expect("guarded");
            value_types.insert(tag, view.tag.clone());
            value_types.insert(pay, view.payload.clone());
            pair_enum_values.insert(*param_id, (tag, pay));
            continue;
        }
        // A BY-VALUE NEWTYPE struct param binds ONE value of the field's
        // scalar type; `ExtractField 0` is a Copy of it.
        if let Some(field_lir) = newtype_struct_sig.get(index).and_then(|o| o.clone()) {
            let v = vmap.define(*param_id);
            value_types.insert(v, field_lir.clone());
            entry_newtype_structs.insert(*param_id, field_lir);
            continue;
        }
        // A BY-VALUE PAIR struct param binds TWO anonymous formals (layout
        // order); the param's own ValueId maps extracts to them by
        // declaration index and any whole-value use fails closed.
        if let Some(layout) = pair_struct_sig.get(index).and_then(|o| o.clone()) {
            let mut order: Vec<usize> = vec![0, 1];
            order.sort_by_key(|&i| layout.field_offsets[i].0);
            let mut by_decl: [Value; 2] = [Value(u32::MAX); 2];
            let mut tys: [LirType; 2] =
                [layout.field_offsets[0].1.clone(), layout.field_offsets[1].1.clone()];
            for &decl_idx in &order {
                let v = vmap.define_anonymous();
                value_types.insert(v, layout.field_offsets[decl_idx].1.clone());
                by_decl[decl_idx] = v;
                tys[decl_idx] = layout.field_offsets[decl_idx].1.clone();
            }
            entry_pair_structs.insert(
                *param_id,
                PairStructParam { by_decl_index: by_decl, tys, layout_order: [order[0], order[1]] },
            );
            continue;
        }
        // A BY-VALUE INDIRECT struct param binds ONE I64 value (the hidden
        // pointer). The trust-ir param id maps to that pointer; ExtractField
        // loads fields through it at the recorded offsets, and every other
        // use of the whole-struct value fails closed.
        if let Some(layout) = indirect_struct_sig.get(index).and_then(|o| o.clone()) {
            let field_tys = match param_ty {
                Ty::Struct(sid) => module
                    .structs
                    .get(sid.as_usize())
                    .map(|def| def.fields.iter().map(|f| f.ty.clone()).collect::<Vec<_>>())
                    .unwrap_or_default(),
                _ => Vec::new(),
            };
            let v = vmap.define(*param_id);
            value_types.insert(v, LirType::I64);
            entry_indirect_structs
                .insert(*param_id, IndirectStructParam { ptr: v, layout, field_tys });
            continue;
        }
        // A fat slice param binds TWO anonymous dense values (data, len) at its
        // positional slots; the fat pointer's own ValueId is deliberately NOT
        // bound, so any use outside the PtrData/PtrMetadata lanes fails closed.
        if let Some(elem) = fat_param_sig.get(index).and_then(|o| o.clone()) {
            let data = vmap.define_anonymous();
            let len = vmap.define_anonymous();
            value_types.insert(data, LirType::I64);
            value_types.insert(len, LirType::I64);
            entry_fat_params.insert(*param_id, FatSliceParam { data, len, elem });
            continue;
        }
        let lir_ty = map_scalar_int_ty_in(module, param_ty, "entry block param")?;
        if fieldless_enum_carrier(module, param_ty).is_some() {
            enum_tag_values.insert(*param_id, lir_ty.clone());
        }
        if matches!(param_ty, Ty::Ptr) {
            ptr_params.insert(*param_id);
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
                if let Some(view) = pair_enum_view(module, param_ty) {
                    let tag = vmap.define_anonymous();
                    let pay = vmap.define_anonymous();
                    value_types.insert(tag, view.tag.clone());
                    value_types.insert(pay, view.payload.clone());
                    pair_enum_values.insert(*param_id, (tag, pay));
                    continue;
                }
                let lir_ty = map_scalar_int_ty_in(module, param_ty, "block param")?;
                if fieldless_enum_carrier(module, param_ty).is_some() {
                    enum_tag_values.insert(*param_id, lir_ty.clone());
                }
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
    // TUPLE, read back by `ExtractField`. Since BMC-LANE-1 (2026-11-06) the
    // bridge builds it with one complete `make_aggregate (Int,Bool)`; the
    // legacy spelling, an `undef (Int,Bool)` seed plus two `InsertField`s, is
    // still decomposed. This pre-pass PROVES the tuple can be decomposed into the
    // two scalar SSA Values it carries (NO tuple-in-memory: a checked pair
    // stored to memory fails closed), returning the seed/insert/
    // extract bookkeeping the body lowering consumes. Run BEFORE the scalar
    // Undef analysis so its admitted `Tuple` seeds are excluded from the scalar
    // memory-merge scan. Fail-closes on any non-decomposable aggregate.
    let tuple_decompose = analyze_checked_arith_tuples(&order, &blocks_by_id, name)?;

    // PASS 1.7 — AGGREGATE-IN-MEMORY DECOMPOSITION (fail-closed). The BRIDGE
    // promotes a multi-block-written aggregate local to a WHOLE-aggregate stack
    // slot and round-trips it through that slot as a unit (`Alloca` + `Store` +
    // `Load` at the aggregate type, fields built/read by `InsertField`/
    // `ExtractField`). This pre-pass admits a slot whose pointee is a `Ty::Tuple`,
    // or a `repr(Rust)` `Ty::Struct`, of scalar fields, laid out at the
    // interpreter's own layout of that type (`aggregate_mem_layout`,
    // CG-DECLARED-LAYOUT-1: a declared `StructDef` size/align/offset triple or
    // `Module::tuple_layouts` descriptor read and re-validated, declaration order
    // only for a type that declares none), and used only as the pointer of a
    // whole-aggregate Store/Load at the slot's own type (step 1b). It returns the
    // slot-layout + seed/insert/store/load/extract bookkeeping the body lowering
    // consumes. Run AFTER the
    // checked-arith tuple analysis so its admitted pure-SSA pairs are excluded,
    // and BEFORE the scalar Undef analysis so the aggregate `Undef`/`Const` seeds
    // are excluded from the scalar memory-merge scan. Fail-closes on any aggregate
    // it cannot decompose that way.
    let agg_mem = analyze_aggregate_memory(
        module,
        &order,
        &blocks_by_id,
        &tuple_decompose,
        &ptr_params,
        name,
    )?;

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
    let mut next_edge_block =
        FreshIdCursor::after(order.iter().copied().max().unwrap_or(0), "block", name)?;
    // Fresh-value allocator for cycle-breaking edge-copy temporaries; starts past
    // every SSA-bound value so a temp never aliases a real value.
    let mut next_value: u32 = vmap.next_value();

    // Function-scoped memory state: stack slots accumulate across all blocks and
    // alloca-pointer provenance flows along the straight-line bodies.
    let mut mem = MemoryCtx::new();
    mem.fat_params = entry_fat_params;
    mem.indirect_struct_params = entry_indirect_structs;
    mem.pair_struct_params = entry_pair_structs;
    mem.newtype_struct_params = entry_newtype_structs;

    // DIRECT-GLOBAL provenance: every `GlobalAddr` result is recorded, while
    // function-symbol proxies and data symbols remain distinct. A direct data
    // address passed to `CallIndirect` must fail closed; only a value with no
    // direct-global provenance at all is an OPEN target.
    let mut global_addr_provenance: HashMap<Value, GlobalAddrProvenance> = HashMap::new();

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
    //
    // Trust (plan §5 fail-open item 1): UNREACHABLE from every codegen entry
    // point while `ModuleLirError::ImplicitPanicUnfaithful` stands — the prologue
    // refuses any body (own or inlined) that carries an `Assert`, because a bare
    // trap is not Rust's panic. Only the test oracle
    // (`lower_trust_ir_function_to_lir_trap_assert_oracle`) reaches it. Kept, not
    // deleted, so item P (a faithful panic lowering) can replace the `Trap` with a
    // call to the panic entry point and lift the refusal in one place.
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
            // Trust (trust-ir v52/v54): the trap carries no panic message, so
            // the check's kind is not lowered (as for every assert before
            // v52). A SITED assert (v54) names the entry its failure calls;
            // a trap is not that call, so it is not taken here and falls to
            // `lower_inst`, which refuses it by name.
            if let Inst::Assert { cond, kind: _, site: None } = &node.inst {
                // The assert condition is `ok` (== !overflowed): branch to the
                // continuation when true, to the shared trap block when false.
                let cond_v = vmap.resolve(*cond, name)?;
                let trap = if let Some(trap) = trap_block {
                    trap
                } else {
                    let b = Block(next_edge_block.take(name)?);
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
                    trap_block = Some(b);
                    b
                };
                let cont = Block(next_edge_block.take(name)?);

                seg.push(Instruction {
                    opcode: Opcode::Brif { cond: cond_v, then_dest: cont, else_dest: trap },
                    args: vec![cond_v],
                    results: vec![],
                });

                // Finalize the current segment.
                let seg_params: Vec<(Value, LirType)> = if is_first_segment {
                    let mut out = Vec::with_capacity(block.params.len());
                    for (pid, pty) in &block.params {
                        if matches!(pty, Ty::Unit) {
                            continue;
                        }
                        if let Some(fat) = mem.fat_params.get(pid) {
                            out.push((fat.data, LirType::I64));
                            out.push((fat.len, LirType::I64));
                            continue;
                        }
                        if let Some(psp) = mem.pair_struct_params.get(pid) {
                            // Formals in LAYOUT order (the smaller offset
                            // first) — the same order the signature emitted.
                            for &i in &psp.layout_order {
                                out.push((psp.by_decl_index[i], psp.tys[i].clone()));
                            }
                            continue;
                        }
                        if let Some((tag, pay)) = pair_enum_values.get(pid) {
                            let tag_ty = value_types.get(tag).cloned().unwrap_or(LirType::I64);
                            let pay_ty = value_types.get(pay).cloned().unwrap_or(LirType::I64);
                            out.push((*tag, tag_ty));
                            out.push((*pay, pay_ty));
                            continue;
                        }
                        let v = vmap.resolve(*pid, name)?;
                        if mem.indirect_struct_params.contains_key(pid) {
                            out.push((v, LirType::I64));
                            continue;
                        }
                        if let Some(field_lir) = mem.newtype_struct_params.get(pid) {
                            out.push((v, field_lir.clone()));
                            continue;
                        }
                        let lty = map_scalar_int_ty_in(module, pty, "block param")?;
                        out.push((v, lty));
                    }
                    out
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
                &mut global_addr_provenance,
                &mut seg,
                &mut next_value,
                &admitted_undef_seeds,
                &tuple_decompose,
                &agg_mem,
                &mut agg_field_values,
                &mut enum_tag_values,
                &mut pair_enum_values,
                real_calls,
                name,
            )?;
        }

        // Terminator goes into the final segment.
        lower_terminator(
            terminator,
            &vmap,
            &value_types,
            &pair_enum_values,
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
            let mut out: Vec<(Value, LirType)> = Vec::with_capacity(block.params.len());
            for (pid, pty) in &block.params {
                // A fat slice ENTRY param expands to its two split halves
                // (data, len) at the same positional slots the signature
                // declared. Only the entry block can carry one (non-entry
                // fat block params already failed pre-allocation).
                if matches!(pty, Ty::Unit) {
                    continue;
                }
                if let Some(fat) = mem.fat_params.get(pid) {
                    out.push((fat.data, LirType::I64));
                    out.push((fat.len, LirType::I64));
                    continue;
                }
                if let Some(isp) = mem.indirect_struct_params.get(pid) {
                    out.push((isp.ptr, LirType::I64));
                    continue;
                }
                if let Some(psp) = mem.pair_struct_params.get(pid) {
                    for &i in &psp.layout_order {
                        out.push((psp.by_decl_index[i], psp.tys[i].clone()));
                    }
                    continue;
                }
                if let Some((tag, pay)) = pair_enum_values.get(pid) {
                    let tag_ty = value_types.get(tag).cloned().unwrap_or(LirType::I64);
                    let pay_ty = value_types.get(pay).cloned().unwrap_or(LirType::I64);
                    out.push((*tag, tag_ty));
                    out.push((*pay, pay_ty));
                    continue;
                }
                let v = vmap.resolve(*pid, name)?;
                if let Some(field_lir) = mem.newtype_struct_params.get(pid) {
                    out.push((v, field_lir.clone()));
                    continue;
                }
                let lty = map_scalar_int_ty_in(module, pty, "block param")?;
                out.push((v, lty));
            }
            out
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
        // Read from trust-ir `ParamAttrs::sret` (see `sret_convention`), never
        // defaulted: trust-ir carries the marker (its validator requires the
        // leading pointer parameter and the empty return list), and an absent
        // marker on an indirect-return function is a wrong ABI, not a
        // conservative one.
        abi_sret_param,
        sret_arg_callees,
        // trust-cg de95c72d6 (L01-P5): the indirect half of the sret convention,
        // keyed by the LIR callee value. Computed by the same scan, never
        // defaulted — see `sret_convention` for why it is provably empty for
        // everything this converter emits and how the impossible case refuses.
        sret_arg_indirect_callees,
        debug_meta: Default::default(),
        debug_value_bindings: vec![],
        stack_protector: Default::default(),
        param_pointee_types: Vec::new(),
        eh_info: Default::default(),
        // No landing pad is lowered (`eh_info` is empty), so no catch type index exists and
        // the empty typed-catch table is exact.
        eh_type_table: Default::default(),
        // trust-cg U10: a prologue stack-limit check is requested by the
        // producer's reserved function tags and acknowledged positively, never
        // inferred from a tag (`docs/u10-prologue-stack-limit.md` §1). This
        // converter decodes no such tag, so it requests none.
        stack_limit: None,
        // trust-cg L03-P9: the target features a function may assume, as an
        // adapter ADMITTED them against its target vocabulary. This converter
        // admits none (it never read trust-ir `FuncAttrs.target_features`), so
        // ISel keeps the profile's baseline instructions, as before the field.
        target_features: Vec::new(),
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
//   * ACYCLIC  — the callee is not the caller itself, and a call CYCLE is
//                broken by the recursive-flatten stack: a non-leaf callee is
//                first flattened by this same inliner (its own admitted calls
//                spliced away) and the splice runs against that call-free
//                copy, but a callee already on the flatten path is never
//                flattened again — its call survives and fail-closes.
//   * SINGLE-BLOCK fast path — a one-block callee takes the straight-line
//                splice; a multi-block callee takes the block-cloning splice
//                (`try_inline_call_multiblock`) with the caller block split at
//                the call site.
//   * SINGLE-RETURN — every `Return` carries exactly one value.
//   * LEAF + PURE — every non-terminator instruction in the (possibly
//                flattened) callee body is a value-producing op with NO
//                observable effect and NO nested call: it is drawn from the
//                remappable pure-scalar set
//                {Const, BinOp, UnOp, ICmp, Cast, Copy, Select} (the
//                multi-block splice additionally admits Overflow, Undef,
//                Insert/ExtractField, Assume, Assert). Anything else
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
/// Runs [`inline_local_pure_leaf_calls_one_pass`] to a FIXPOINT: a pass
/// handles at most one call per block, so a block carrying two calls (the
/// producer emits `f(g(x), y)` as two `Inst::Call`s in ONE block) — or a
/// multi-block splice whose continuation block still carries the next call —
/// needs another pass over the rewritten function. Termination is structural:
/// an admitted callee is a LEAF (its spliced body contains no `Call`), so
/// every successful inline strictly decreases the function's total `Call`
/// count and no pass ever increases it; the loop exits as soon as a pass makes
/// no progress (only inadmissible or real-call-deferred calls remain).
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
    // The flatten stack carries every FuncId on the current recursive-flatten
    // path (see `inline_local_pure_leaf_calls_with_stack`); seeding it with the
    // root function also re-states the no-self-recursion rule.
    let mut flatten_stack = vec![function.id];
    inline_local_pure_leaf_calls_with_stack(module, function, real_calls, &mut flatten_stack)
}

/// The fixpoint driver behind [`inline_local_pure_leaf_calls`], carrying the
/// recursive-flatten cycle guard. `flatten_stack` holds the `FuncId`s currently
/// being flattened (root caller included): a callee already on the stack is
/// NEVER flattened again, which breaks direct and mutual recursion — the
/// recursive call is left in the body and fail-closes downstream. Termination:
/// the stack grows strictly along a flatten path and is bounded by the number
/// of functions in the module, and each fixpoint pass strictly decreases the
/// (finite) call count of its own function copy.
fn inline_local_pure_leaf_calls_with_stack<'a>(
    module: &Module,
    function: &'a IrFunction,
    real_calls: bool,
    flatten_stack: &mut Vec<FuncId>,
) -> Result<Cow<'a, IrFunction>, ModuleLirError> {
    fn count_calls(f: &IrFunction) -> usize {
        f.blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .filter(|n| matches!(n.inst, Inst::Call { .. }))
            .count()
    }

    // Fast path: no calls anywhere -> borrow unchanged.
    let mut remaining = count_calls(function);
    if remaining == 0 {
        return Ok(Cow::Borrowed(function));
    }

    let mut current =
        inline_local_pure_leaf_calls_one_pass(module, function, real_calls, flatten_stack)?;
    loop {
        let after = count_calls(&current);
        if after == 0 || after >= remaining {
            // Call-free, or no progress (the residue is inadmissible / deferred
            // real calls): either way this pass is the fixpoint.
            break;
        }
        remaining = after;
        current =
            inline_local_pure_leaf_calls_one_pass(module, &current, real_calls, flatten_stack)?;
    }
    Ok(Cow::Owned(current))
}

/// One inlining pass: handle at most the FIRST admitted call in each block.
/// See [`inline_local_pure_leaf_calls`] for the fixpoint driver and the
/// admission predicate above for what qualifies.
fn inline_local_pure_leaf_calls_one_pass(
    module: &Module,
    function: &IrFunction,
    real_calls: bool,
    flatten_stack: &mut Vec<FuncId>,
) -> Result<IrFunction, ModuleLirError> {
    // Fresh-ValueId / fresh-BlockId allocators: start past every id mentioned
    // anywhere in the caller so a spliced callee id can never alias a caller id
    // (or a previously-spliced callee id, since the counters only grow).
    let mut next_value = FreshIdCursor::after(max_value_id(function), "value", &function.name)?;
    let mut next_block = FreshIdCursor::after(max_block_id(function), "block", &function.name)?;

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
    // (the first admitted one). The bridge-produced MIR call shape places the
    // call in its own block (the MIR call terminator becomes `Inst::Call` + a
    // `Br`), but the direct THIR producer emits nested calls (`f(g(x), y)`) as
    // consecutive `Inst::Call`s in ONE block. A call this pass does not reach
    // is picked up by the caller's fixpoint loop re-running the pass over the
    // rewritten function; a call NO pass admits is left verbatim for the
    // converter to fail-close on (it is NOT mis-inlined).
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

        // Resolve the callee once. A NON-LOCAL callee (no `Function` in this
        // Module) can never be inlined: leave the Call in place so the
        // converter fail-closes on it.
        let Some(callee_fn) = module.function_by_id(*callee) else {
            out_blocks.push(block);
            continue;
        };

        // Trust: a `Producer::Clean` callee is NEVER spliced into a Rust
        // caller's object, and the refusal names the reason instead of leaving
        // the call for the converter's shape-blind `UnsupportedInst { Call }`.
        // (IR-5 re-points Rust->Clean call edges at the appended Clean row, so
        // without this check a pure-leaf Clean body — a `projection` or
        // `select` row at tier `structural`, carrier faithfulness NOT
        // established — would inline straight into machine code.)
        if callee_fn.producer == Some(trust_ir::Producer::Clean) {
            return Err(ModuleLirError::CleanOriginBelowCodegenGate {
                name: callee_fn.name.clone(),
                detail: format!("it is a callee of `{name}` and would have been inlined"),
            });
        }

        // RECURSIVE FLATTEN. A local NON-LEAF callee (its body itself calls)
        // fails the splices' leaf check as-is — but if its own calls inline
        // away, the flattened copy is a legitimate leaf and the ordinary
        // splice admission runs against THAT. The flatten stack breaks call
        // cycles (a callee already being flattened is skipped, so its call
        // survives and fail-closes); a flatten that errors or makes no
        // progress declines soundly — the original call stays for the
        // converter to reject. The flatten itself always runs with
        // `real_calls=false`: a body about to be spliced inline must become
        // call-FREE, so deferring composable calls inside it would only
        // manufacture admission failures.
        let flattened: Option<IrFunction> = if callee_fn.id != function.id
            && !flatten_stack.contains(&callee_fn.id)
            && callee_fn
                .blocks
                .iter()
                .flat_map(|b| b.body.iter())
                .any(|n| matches!(n.inst, Inst::Call { .. }))
        {
            flatten_stack.push(callee_fn.id);
            let out =
                inline_local_pure_leaf_calls_with_stack(module, callee_fn, false, flatten_stack);
            flatten_stack.pop();
            match out {
                Ok(Cow::Owned(f)) => Some(f),
                Ok(Cow::Borrowed(_)) => None,
                Err(error @ ModuleLirError::FreshIdExhausted { .. }) => return Err(error),
                Err(_) => None,
            }
        } else {
            None
        };
        let callee_view: &IrFunction = flattened.as_ref().unwrap_or(callee_fn);

        // SINGLE-BLOCK fast path (the established, prior-slice-preserving splice):
        // splice the callee body inline, replacing just the call node.
        match try_inline_call(module, function, callee_view, args, &call_node, &mut next_value) {
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
                if let Some(error) = next_value.failure(&name) {
                    return Err(error);
                }
                // Not a single-block inline; try the MULTI-BLOCK splice.
            }
        }

        // MULTI-BLOCK splice. On success this appends the split caller block,
        // the cloned callee blocks, and the continuation block to `out_blocks`.
        match try_inline_call_multiblock(
            module,
            function,
            callee_view,
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
                if let Some(error) = next_value.failure(&name).or_else(|| next_block.failure(&name))
                {
                    return Err(error);
                }
                // Neither single- nor multi-block inline is admissible: leave the
                // Call in place verbatim so the converter fail-closes on it. We
                // never produce a wrong splice.
                out_blocks.push(block);
            }
        }
    }

    new_function.blocks = out_blocks;

    // Any Call that REMAINS is either one this pass could not reach (a second
    // call in a block, or a call in a freshly spliced continuation block — the
    // fixpoint caller re-runs the pass for those) or an inadmissible one we
    // intentionally left for the converter to reject — the designed fail-closed
    // boundary, NOT an inliner error.
    let _ = &name;
    Ok(new_function)
}

/// A checked cursor for sparse source IDs and synthetic block IDs. The
/// following index must be representable before the current one is reserved;
/// u32::MAX is therefore an exhaustion sentinel, never a wrapped alias.
struct FreshIdCursor {
    next: u32,
    space: &'static str,
    exhausted: bool,
}

impl FreshIdCursor {
    fn after(maximum: u32, space: &'static str, name: &str) -> Result<Self, ModuleLirError> {
        let next = maximum
            .checked_add(1)
            .ok_or_else(|| ModuleLirError::FreshIdExhausted { name: name.to_string(), space })?;
        Ok(Self { next, space, exhausted: false })
    }

    fn take(&mut self, name: &str) -> Result<u32, ModuleLirError> {
        let Some(following) = self.next.checked_add(1) else {
            self.exhausted = true;
            return Err(ModuleLirError::FreshIdExhausted {
                name: name.to_string(),
                space: self.space,
            });
        };
        let fresh = self.next;
        self.next = following;
        Ok(fresh)
    }

    // The private splice helpers return ordinary shape-refusal strings. Keep
    // exhaustion typed independently so their fallback cannot swallow it.
    fn failure(&self, name: &str) -> Option<ModuleLirError> {
        self.exhausted
            .then(|| ModuleLirError::FreshIdExhausted { name: name.to_string(), space: self.space })
    }
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
        Inst::Invoke { normal_dest, unwind_dest, .. }
        | Inst::AssertInvoke { normal_dest, unwind_dest, .. }
        | Inst::DropInvoke { normal_dest, unwind_dest, .. }
        | Inst::InvokeIndirect { normal_dest, unwind_dest, .. } => vec![*normal_dest, *unwind_dest],
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
    // The callee VIEW: the module's function, or the caller pass's recursively
    // flattened copy of it (same id/ty, call-free body). Locality was already
    // established by the caller pass's lookup.
    callee: &IrFunction,
    args: &[ValueId],
    call_node: &InstrNode,
    next_value: &mut FreshIdCursor,
) -> Result<Vec<InstrNode>, String> {
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
        let fresh = ValueId::new(next_value.take(&caller.name).map_err(|error| error.to_string())?);
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
//                      converter-supported, side-effect-free set
//                      (`is_multiblock_inlinable_value` is the authority):
//                        value ops {Const, BinOp, UnOp, Overflow, ICmp, Cast,
//                                   Copy, Select, Undef, InsertField,
//                                   MakeAggregate, ExtractField},
//                        proof obligations {Assume, Assert without a site} (a
//                          failed assert is a DIVERGENCE/trap, not an
//                          observable side effect),
//                        the read-only slice lane {PtrData, PtrMetadata, GEP,
//                          Load} (no write: see the predicate's note),
//                        terminators {Br, CondBr, Switch, Return, Unreachable}.
//                      Anything else — a nested Call/CallIndirect/Invoke, a
//                      memory write or allocation (Store/Alloca — would need
//                      slot provenance threaded across the splice), atomics,
//                      borrow/ARC, dealloc, frames, coroutine, EH, or dialect —
//                      makes the callee inadmissible and FAILS CLOSED.
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
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::Cast { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::Undef { .. }
            | Inst::InsertField { .. }
            | Inst::MakeAggregate { .. }
            | Inst::ExtractField { .. }
            // Proof obligations: a failed Assert is a divergence (trap), not an
            // observable side effect; Assume is a pure constraint. Both are in
            // the converter's supported set. A SITED assert (trust-ir v54) is
            // not: its failure calls the site's entry.
            | Inst::Assume { .. }
            | Inst::Assert { site: None, .. }
            // The READ-ONLY slice lane: a slice-taking callee's body is
            // PtrData/PtrMetadata on its fat formal (which the splice rebinds
            // to the CALLER's fat formal), GEP off the data root, and element
            // Loads. All single-result, none writes. SOUNDNESS of admitting
            // the memory reads: `Alloca` and `Store` stay OUT of this set, so
            // a spliced Load's pointer can only root at a fat formal the
            // caller's own lowering recognizes — any other rooting reaches
            // the converter as an unresolvable pointer and fails closed —
            // and splicing preserves program order, so a read cannot move
            // across the caller's own stores.
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::GEP { .. }
            | Inst::Load { .. }
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
        Inst::UnOp { op, ty, operand } => {
            Inst::UnOp { op: *op, ty: ty.clone(), operand: resolve(*operand)? }
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
        Inst::MakeAggregate { ty, variant, fields } => Inst::MakeAggregate {
            ty: ty.clone(),
            variant: *variant,
            fields: fields.iter().map(|field| resolve(*field)).collect::<Result<_, _>>()?,
        },
        Inst::ExtractField { ty, aggregate, field } => {
            Inst::ExtractField { ty: ty.clone(), aggregate: resolve(*aggregate)?, field: *field }
        }
        Inst::Assume { cond } => Inst::Assume { cond: resolve(*cond)? },
        Inst::Assert { cond, kind, site: None } => {
            // A kind's operands (trust-ir v52) are values of the callee too.
            let mut kind = *kind;
            if let Some(operands) = kind.operands_mut() {
                for operand in operands {
                    *operand = resolve(*operand)?;
                }
            }
            Inst::Assert { cond: resolve(*cond)?, kind, site: None }
        }
        // The read-only slice lane (see `is_multiblock_inlinable_value`).
        Inst::PtrData { ptr_ty, ptr } => {
            Inst::PtrData { ptr_ty: ptr_ty.clone(), ptr: resolve(*ptr)? }
        }
        Inst::PtrMetadata { ptr_ty, metadata_ty, ptr } => Inst::PtrMetadata {
            ptr_ty: ptr_ty.clone(),
            metadata_ty: metadata_ty.clone(),
            ptr: resolve(*ptr)?,
        },
        Inst::GEP { pointee_ty, base, indices, inbounds } => Inst::GEP {
            pointee_ty: pointee_ty.clone(),
            base: resolve(*base)?,
            indices: indices.iter().map(|i| resolve(*i)).collect::<Result<_, _>>()?,
            inbounds: *inbounds,
        },
        Inst::Load { ty, ptr, volatile, align } => {
            Inst::Load { ty: ty.clone(), ptr: resolve(*ptr)?, volatile: *volatile, align: *align }
        }
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
    // The callee VIEW: the module's function, or the caller pass's recursively
    // flattened copy of it (same id/ty, call-free body). Locality was already
    // established by the caller pass's lookup.
    callee: &IrFunction,
    args: &[ValueId],
    call_node: &InstrNode,
    caller_block: &trust_ir::Block,
    call_pos: usize,
    next_value: &mut FreshIdCursor,
    next_block: &mut FreshIdCursor,
) -> Result<Vec<trust_ir::Block>, String> {
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
    let cont_id = BlockId::new(next_block.take(&caller.name).map_err(|error| error.to_string())?);

    // ---- BlockId remap: every callee block -> a fresh BlockId. ----
    let mut block_remap: HashMap<BlockId, BlockId> = HashMap::new();
    for block in &callee.blocks {
        let fresh = BlockId::new(next_block.take(&caller.name).map_err(|error| error.to_string())?);
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
                let fresh =
                    ValueId::new(next_value.take(&caller.name).map_err(|error| error.to_string())?);
                remap.insert(*param_id, fresh);
            }
        }
        for node in &block.body {
            for r in &node.results {
                let fresh =
                    ValueId::new(next_value.take(&caller.name).map_err(|error| error.to_string())?);
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
            | Inst::UnOp { .. }
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
        Inst::UnOp { op, ty, operand } => {
            Inst::UnOp { op: *op, ty: ty.clone(), operand: resolve(*operand)? }
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

/// The SSA operands read by an instruction, including constructs this bridge
/// refuses to lower. Use the shared exhaustive walk so a new IR instruction
/// cannot silently omit a read from the inliner's fresh-value scan.
fn inst_value_operands(inst: &Inst) -> Vec<ValueId> {
    let mut operands = Vec::new();
    inst.visit_value_operands(|operand| operands.push(operand));
    operands
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
// LIR `Opcode::Call { name, .. }` (which ISel lowers to `Bl` + an
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
    // Trust: a `Producer::Clean` callee is never deferred to a real `Bl` edge
    // either; it falls through to the inliner, which refuses it by name
    // (`ModuleLirError::CleanOriginBelowCodegenGate`).
    if callee.producer == Some(trust_ir::Producer::Clean) {
        return false;
    }
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
/// field offsets of `AggMemDecompose.agg_alloca_layout` (the trust-ir
/// interpreter's own layout of the slot's type, [`aggregate_mem_layout`]):
///   * `Alloca(Tuple)`   -> one sized stack slot; record its layout/field offsets.
///   * `Const::Aggregate`-> materialize each field constant as an `Iconst`; record
///                          the per-field LIR Values (NO whole-aggregate LIR).
///   * `Undef(Tuple)`    -> register an empty field map (fields filled by Insert).
///   * `MakeAggregate`   -> record every field's LIR Value; NO LIR.
///   * `InsertField`     -> set field k's LIR Value (clone source map); NO LIR.
///   * `Store(Tuple)`    -> per-field Str at each field offset.
///   * `Load(Tuple)`     -> per-field Ldr at each field offset; record the loaded
///                          field Values as the result aggregate's fields.
///   * `ExtractField`    -> `Copy` of the resolved field's LIR Value.
///   * field-pointer `GEP` -> `ArrayGep i8` off the slot by the field's layout
///     offset (an `Iconst`), its pointee the field's LIR type, so the scalar
///     `Load`/`Store` arms check the access width against the field
///     (F1-FIELD-POINTER-AGREEMENT-1).
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
    // The tracked-aggregate arms below are guarded by `result0.is_some_and(..)`,
    // so their result, and the map entry a guard looked up, are present; should
    // a guard and its arm ever disagree, the lowering refuses instead of panicking.
    let guarded_result = |arm: &str| {
        result0.ok_or_else(|| ModuleLirError::UnsupportedAggregate {
            name: name.to_string(),
            detail: format!("guarded aggregate {arm} has no result"),
        })
    };

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
            let result = guarded_result("Undef seed")?;
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
        // ---- MakeAggregate of a tracked aggregate -> every field (NO LIR). ----
        Inst::MakeAggregate { fields: lanes, .. }
            if result0.is_some_and(|r| agg_mem.agg_make_results.contains(&r)) =>
        {
            let result = result0.ok_or_else(|| ModuleLirError::UnsupportedAggregate {
                name: name.to_string(),
                detail: "tracked MakeAggregate has no result".into(),
            })?;
            let field_vals = lanes
                .iter()
                .map(|lane| vmap.resolve(*lane, name))
                .collect::<Result<Vec<_>, _>>()?;
            agg_field_values.insert(result, field_vals);
            Ok(true)
        }
        // ---- InsertField builds a tracked aggregate -> set one field (NO LIR). --
        Inst::InsertField { aggregate, field, value, .. }
            if result0.is_some_and(|r| agg_mem.agg_insert_results.contains(&r)) =>
        {
            let result = guarded_result("InsertField")?;
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
        // ---- Whole-aggregate Load through an INCOMING read-only root ->
        //      per-field Ldr at `ptr + offset`. ----
        Inst::Load { ty: Ty::Tuple(_) | Ty::Struct(_), ptr, .. }
            if result0.is_some_and(|r| agg_mem.agg_incoming_load_layout.contains_key(&r)) =>
        {
            let result = guarded_result("incoming Load")?;
            let layout =
                agg_mem.agg_incoming_load_layout.get(&result).cloned().ok_or_else(|| {
                    ModuleLirError::UnsupportedAggregate {
                        name: name.to_string(),
                        detail: "guarded aggregate incoming Load has no layout".to_string(),
                    }
                })?;
            let base = vmap.resolve(*ptr, name)?;
            let mut loaded = Vec::with_capacity(layout.field_offsets.len());
            for (offset, lir_ty) in &layout.field_offsets {
                // addr = base + offset (byte GEP, offset 0 folds away).
                let addr = if *offset == 0 {
                    base
                } else {
                    let idx = Value(*next_value);
                    *next_value += 1;
                    value_types.insert(idx, LirType::I64);
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(*offset) },
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
                };
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
        // ---- Whole-aggregate Load -> per-field Ldr at field offsets. ----
        Inst::Load { ty: Ty::Tuple(_) | Ty::Struct(_), ptr, .. }
            if result0.is_some_and(|r| agg_mem.agg_load_results.contains(&r)) =>
        {
            let result = guarded_result("Load")?;
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
            let result = guarded_result("ExtractField")?;
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
        // ---- Admitted FIELD POINTER -> slot base + the field's layout offset. ----
        // Step 1b proved this GEP's constant byte offset starts exactly field
        // `k` of the slot's layout (the interpreter's own) and that the result is
        // only ever the pointer of a non-volatile Load/Store at field `k`'s type.
        // The address is materialized from the LAYOUT offset, the one the whole
        // Store/Load arms address field `k` at, not from the trust-ir index value.
        // The pointee is field `k`'s LIR type, so the scalar arms' width check
        // runs against the field (the scalar GEP arm would record `I8`).
        Inst::GEP { base, .. }
            if result0.is_some_and(|r| agg_mem.agg_field_ptrs.contains_key(&r)) =>
        {
            let result = guarded_result("field-pointer GEP")?;
            let field = agg_mem.agg_field_ptrs.get(&result).ok_or_else(|| {
                ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: "guarded aggregate field-pointer GEP has no field".to_string(),
                }
            })?;
            let base_v = vmap.resolve(*base, name)?;
            let slot =
                *mem.slot_of.get(&base_v).ok_or_else(|| ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: format!(
                        "field pointer {} has no allocated aggregate slot for its base {}",
                        result.index(),
                        base.index()
                    ),
                })?;
            let offset = Value(*next_value);
            *next_value += 1;
            value_types.insert(offset, LirType::I64);
            instructions.push(Instruction {
                opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(field.offset) },
                args: vec![],
                results: vec![offset],
            });
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, LirType::I64);
            mem.slot_of.insert(dst, slot);
            mem.pointee_ty.insert(dst, field.lir.clone());
            instructions.push(Instruction {
                opcode: Opcode::ArrayGep { elem_ty: LirType::I8 },
                args: vec![base_v, offset],
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
    global_addr_provenance: &mut HashMap<Value, GlobalAddrProvenance>,
    instructions: &mut Vec<Instruction>,
    next_value: &mut u32,
    admitted_undef_seeds: &std::collections::HashSet<ValueId>,
    tuple_decompose: &TupleDecompose,
    agg_mem: &AggMemDecompose,
    agg_field_values: &mut HashMap<ValueId, Vec<Value>>,
    enum_tag_values: &mut HashMap<ValueId, LirType>,
    pair_enum_values: &mut HashMap<ValueId, (Value, Value)>,
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
            || tuple_decompose.make_results.contains(result)
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
        // ---- FIELDLESS-ENUM tag read: `ExtractField { field: 0 }` on a value
        // admitted through `fieldless_enum_carrier` (a param or block param whose
        // enum type IS its tag — offset 0, whole size). The extract is an
        // IDENTITY at the machine level, so it lowers to a `Copy` of the carrier
        // value. Fail-closed on any other field index and on a field type whose
        // LIR carrier disagrees with the admitted one (the producer types the
        // tag read at the def's canonical repr, so a mismatch is a producer/def
        // drift this converter must not paper over). This is the
        // `fn f(e: FieldlessEnum)` + `extractfield u8 %e, 0` + `switch` shape.
        Inst::ExtractField { ty, aggregate, field } if enum_tag_values.contains_key(aggregate) => {
            let result = expect_single_result(node, name)?;
            if *field != 0 {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "ExtractField field {field} on a fieldless-enum value (only the tag at \
                         field 0 exists)"
                    ),
                });
            }
            let carrier = enum_tag_values[aggregate].clone();
            let field_lir = map_scalar_int_ty(ty, "fieldless-enum tag ExtractField")?;
            if field_lir != carrier {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "fieldless-enum tag ExtractField typed {field_lir:?} but the admitted \
                         carrier is {carrier:?}"
                    ),
                });
            }
            let src = vmap.resolve(*aggregate, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, field_lir);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![src],
                results: vec![dst],
            });
        }
        // ---- PAIR-ENUM constant: `const enum.N { tag }` (payload-less
        // variant) or `const enum.N { tag, payload }`. The value is a
        // (tag, payload) register pair; a payload-less constant materializes
        // a DEFINED zero payload — a sound refinement of the ABI's undef
        // payload lane (type safety forbids reading the payload under that
        // tag, and copying propagates a defined value either way). ----
        Inst::Const { ty, value: Constant::Aggregate(fields) }
            if pair_enum_view(module, ty).is_some() =>
        {
            let result = expect_single_result(node, name)?;
            let view = pair_enum_view(module, ty).expect("guarded");
            let (tag_const, payload_const) = match fields.as_slice() {
                [Constant::Int(t)] => (*t, 0),
                [Constant::Int(t), Constant::Int(p)] => (*t, *p),
                _ => {
                    return Err(ModuleLirError::UnsupportedConstant { name: name.to_string() });
                }
            };
            let tag_v = Value(*next_value);
            *next_value += 1;
            value_types.insert(tag_v, view.tag.clone());
            instructions.push(Instruction {
                opcode: Opcode::Iconst { ty: view.tag.clone(), imm: i128_to_i64(tag_const, name)? },
                args: vec![],
                results: vec![tag_v],
            });
            let pay_v = Value(*next_value);
            *next_value += 1;
            value_types.insert(pay_v, view.payload.clone());
            instructions.push(Instruction {
                opcode: Opcode::Iconst {
                    ty: view.payload.clone(),
                    imm: i128_to_i64(payload_const, name)?,
                },
                args: vec![],
                results: vec![pay_v],
            });
            pair_enum_values.insert(result, (tag_v, pay_v));
            return Ok(());
        }
        // ---- PAIR-ENUM insertfield: replace one lane of a tracked pair. ----
        Inst::InsertField { ty, aggregate, field, value }
            if pair_enum_values.contains_key(aggregate) && pair_enum_view(module, ty).is_some() =>
        {
            let result = expect_single_result(node, name)?;
            let (tag_v, pay_v) = pair_enum_values[aggregate];
            let new_v = vmap.resolve(*value, name)?;
            let pair = match field {
                0 => (new_v, pay_v),
                1 => (tag_v, new_v),
                other => {
                    return Err(ModuleLirError::UnsupportedAggregate {
                        name: name.to_string(),
                        detail: format!("InsertField field {other} on a (tag, payload) pair enum"),
                    });
                }
            };
            pair_enum_values.insert(result, pair);
            return Ok(());
        }
        // ---- PAIR-ENUM extractfield: 0 = tag, 1 = payload — a Copy. ----
        Inst::ExtractField { ty, aggregate, field } if pair_enum_values.contains_key(aggregate) => {
            let result = expect_single_result(node, name)?;
            let (tag_v, pay_v) = pair_enum_values[aggregate];
            let src = match field {
                0 => tag_v,
                1 => pay_v,
                other => {
                    return Err(ModuleLirError::UnsupportedAggregate {
                        name: name.to_string(),
                        detail: format!("ExtractField field {other} on a (tag, payload) pair enum"),
                    });
                }
            };
            let declared_lir = map_scalar_int_ty_in(module, ty, "pair-enum lane")?;
            let carried = value_types.get(&src).cloned();
            if carried.as_ref() != Some(&declared_lir) {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "pair-enum lane {field} declared {declared_lir:?} but carries {carried:?}"
                    ),
                });
            }
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, declared_lir);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![src],
                results: vec![dst],
            });
            return Ok(());
        }
        // ---- Field read on a BY-VALUE NEWTYPE struct param: the param's own
        // value IS the single field. ----
        Inst::ExtractField { ty, aggregate, field }
            if mem.newtype_struct_params.contains_key(aggregate) =>
        {
            let result = expect_single_result(node, name)?;
            if *field != 0 {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "ExtractField field {field} on a single-field newtype struct param"
                    ),
                });
            }
            let carried = mem.newtype_struct_params[aggregate].clone();
            let declared_lir = map_scalar_int_ty_in(module, ty, "newtype struct field")?;
            if declared_lir != carried {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "newtype struct field declared {declared_lir:?} but the formal carries \
                         {carried:?}"
                    ),
                });
            }
            let src = vmap.resolve(*aggregate, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, declared_lir);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![src],
                results: vec![dst],
            });
            return Ok(());
        }
        // ---- Field read on a BY-VALUE PAIR struct param: a Copy of the
        // mapped register formal (declaration index -> layout slot). ----
        Inst::ExtractField { ty, aggregate, field }
            if mem.pair_struct_params.contains_key(aggregate) =>
        {
            let result = expect_single_result(node, name)?;
            let psp = &mem.pair_struct_params[aggregate];
            let idx = *field as usize;
            if idx >= 2 {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "ExtractField field {idx} out of range for the two-field Pair struct \
                         param"
                    ),
                });
            }
            let declared_lir = map_scalar_int_ty_in(module, ty, "pair struct field")?;
            if declared_lir != psp.tys[idx] {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "pair struct field {idx} declared {declared_lir:?} but the formal \
                         carries {:?}",
                        psp.tys[idx]
                    ),
                });
            }
            let src = psp.by_decl_index[idx];
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, declared_lir);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![src],
                results: vec![dst],
            });
            return Ok(());
        }
        // ---- Field read on a BY-VALUE INDIRECT struct param: one Ldr through
        // the hidden pointer at the field's RECORDED offset. A field whose
        // type is a fieldless enum registers its result as a tag carrier, so
        // the follow-on `extractfield <tag> %field, 0` lowers as the identity
        // read above. ----
        Inst::ExtractField { ty, aggregate, field }
            if mem.indirect_struct_params.contains_key(aggregate) =>
        {
            let result = expect_single_result(node, name)?;
            let isp = &mem.indirect_struct_params[aggregate];
            let idx = *field as usize;
            let Some((offset, field_lir)) = isp.layout.field_offsets.get(idx).cloned() else {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "ExtractField field {idx} out of range for the indirect struct param \
                         ({} recorded fields)",
                        isp.layout.field_offsets.len()
                    ),
                });
            };
            // The declared field type must map to the SAME carrier the
            // recorded layout laid out (an enum maps through its tag carrier,
            // payload enums included — see enum_tag_read_view) — a mismatch
            // is producer/def drift, fail closed.
            let declared_lir = match enum_tag_read_view(module, ty) {
                Some((carrier, _, _)) => map_scalar_int_ty(&carrier, "indirect struct field")?,
                None => map_scalar_int_ty_in(module, ty, "indirect struct field")?,
            };
            if declared_lir != field_lir {
                return Err(ModuleLirError::UnsupportedAggregate {
                    name: name.to_string(),
                    detail: format!(
                        "indirect struct field {idx} declared {declared_lir:?} but the recorded \
                         layout carries {field_lir:?}"
                    ),
                });
            }
            let base = isp.ptr;
            let addr = if offset == 0 {
                base
            } else {
                let off = Value(*next_value);
                *next_value += 1;
                value_types.insert(off, LirType::I64);
                instructions.push(Instruction {
                    opcode: Opcode::Iconst { ty: LirType::I64, imm: i64::from(offset) },
                    args: vec![],
                    results: vec![off],
                });
                let addr = Value(*next_value);
                *next_value += 1;
                value_types.insert(addr, LirType::I64);
                instructions.push(Instruction {
                    opcode: Opcode::ArrayGep { elem_ty: LirType::I8 },
                    args: vec![base, off],
                    results: vec![addr],
                });
                addr
            };
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, field_lir.clone());
            instructions.push(Instruction {
                opcode: Opcode::Load { ty: field_lir, align: None },
                args: vec![addr],
                results: vec![dst],
            });
            if isp.field_tys.get(idx).is_some_and(|fty| enum_tag_read_view(module, fty).is_some()) {
                enum_tag_values.insert(result, declared_lir);
            }
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
            let lir_ty = map_scalar_int_ty_in(module, ty, "Const")?;
            // A 128-bit constant takes the register-pair materialization
            // (`Iconst128 { lo, hi }` — the ISel's `select_i128_iconst_wide`),
            // which carries the FULL value; the i64-immediate carrier below is
            // for the single-register widths.
            if matches!(lir_ty, LirType::I128) {
                let Constant::Int(v) = value else {
                    return Err(ModuleLirError::UnsupportedConstant { name: name.to_string() });
                };
                let bits = *v as u128;
                let dst = vmap.resolve(result, name)?;
                value_types.insert(dst, LirType::I128);
                instructions.push(Instruction {
                    opcode: Opcode::Iconst128 {
                        lo: (bits as u64) as i64,
                        hi: ((bits >> 64) as u64) as i64,
                    },
                    args: vec![],
                    results: vec![dst],
                });
                return Ok(());
            }
            let imm = match value {
                Constant::Int(v) => i128_const_to_i64_imm(*v, ty, name)?,
                Constant::Bool(b) => i64::from(*b),
                // A FIELDLESS-ENUM literal. The producer spells it as the
                // canonical `(Ty::Enum, Aggregate([Int(disc), fields...]))` seed
                // whose field 0 is the DISCRIMINANT typed at the def's canonical
                // tag repr (`trust_thir_lower`'s enum registration contract). For
                // a fieldless def there are no further fields, so the whole value
                // is that one tag — and it must be a DECLARED discriminant, or
                // this constant would materialize an invalid value of the type.
                Constant::Aggregate(fields)
                    if fields.len() == 1
                        && fieldless_enum_carrier(module, ty).is_some()
                        && matches!(fields[0], Constant::Int(d)
                            if fieldless_enum_has_discriminant(module, ty, d)) =>
                {
                    let Constant::Int(d) = fields[0] else {
                        return Err(ModuleLirError::UnsupportedConstant { name: name.to_string() });
                    };
                    i128_to_i64(d, name)?
                }
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

            // ---- NARROW CHECKED ARITHMETIC via exact i64 widening. ----
            //
            // Two ISel envelopes force this lane: `CheckedSmul`/`CheckedUmul`
            // lower only at I64 (SMULH/UMULH are 64-bit), and
            // `CheckedS/Uadd`/`sub` lower only at I32/I64 (the flag-setting
            // ADDS/SUBS+CSET idiom — MEASURED: emit_object refuses I16 with
            // "checked add/sub requires I32 or I64 operands", the
            // trust-checksum `fletcher_pack` blocker). Rather than change the
            // pinned ISel, widen the narrow op into a plain i64 op whose
            // result is EXACT, then detect overflow as a WIDTH-RANGE check:
            //
            //   signed   (iN): a64 = sext a; b64 = sext b; r = a64 <op> b64
            //                  value    = trunc_iN(r)
            //                  overflow = (r < iN::MIN) OR (r > iN::MAX)
            //   unsigned (uN): a64 = zext a; b64 = zext b; r = a64 <op> b64
            //                  value    = trunc_iN(r)             (low N bits)
            //                  overflow = (r > uN::MAX)           (unsigned cmp)
            //
            // SOUNDNESS: for signed iN (N <= 32), |a op b| <= (2^31)^2 = 2^62
            // < 2^63, so the 64-bit two's-complement result is the exact
            // mathematical result; iN overflow ⟺ it falls outside
            // [iN::MIN, iN::MAX], and the low N bits are the wrapping value.
            // For uN mul/add, the result <= (2^32-1)^2 < 2^64 is exact as an
            // UNSIGNED quantity (the u32 corner product may set bit 63; the
            // overflow compare below is unsigned, so that is still classified
            // correctly); uN overflow ⟺ result > uN::MAX. For uN SUB, a-b < 0
            // (the borrow case) yields a NEGATIVE i64 whose unsigned reading
            // exceeds 2^63 > uN::MAX, so the same unsigned compare flags it,
            // and the truncated low N bits are exactly the wrapping
            // difference. A wrong bound/compare-direction here would
            // miscompile, so this is gated by the proven-output test.
            //
            // Widths: mul widens at I8/I16/I32 (no narrow Checked*mul at
            // all); add/sub widen at I8/I16 only (I32 is first-class).
            let needs_widening = match op {
                OverflowOp::MulOverflow => {
                    matches!(value_lir_ty, LirType::I8 | LirType::I16 | LirType::I32)
                }
                OverflowOp::AddOverflow | OverflowOp::SubOverflow => {
                    matches!(value_lir_ty, LirType::I8 | LirType::I16)
                }
            };
            if needs_widening {
                let signed = ty.is_signed();
                let wide_opcode = match op {
                    OverflowOp::MulOverflow => Opcode::Imul,
                    OverflowOp::AddOverflow => Opcode::Iadd,
                    OverflowOp::SubOverflow => Opcode::Isub,
                };
                // Fresh I64 temps for the widened operands and the exact result.
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
                // a64 = {s,z}ext_iN->i64 a ; b64 = {s,z}ext_iN->i64 b
                instructions.push(Instruction {
                    opcode: ext_opcode(value_lir_ty.clone(), LirType::I64),
                    args: vec![a],
                    results: vec![a64],
                });
                instructions.push(Instruction {
                    opcode: ext_opcode(value_lir_ty.clone(), LirType::I64),
                    args: vec![b],
                    results: vec![b64],
                });
                // prod = a64 <op> b64   (exact 64-bit result)
                instructions.push(Instruction {
                    opcode: wide_opcode,
                    args: vec![a64, b64],
                    results: vec![prod],
                });
                // value = trunc_i64->iN(prod)   (the wrapping low N bits)
                value_types.insert(value_dst, value_lir_ty.clone());
                instructions.push(Instruction {
                    opcode: Opcode::Trunc { to_ty: value_lir_ty.clone() },
                    args: vec![prod],
                    results: vec![value_dst],
                });

                // The width-dependent range bounds for the overflow check.
                let (signed_lo, signed_hi, unsigned_hi) = match value_lir_ty {
                    LirType::I8 => (i8::MIN as i64, i8::MAX as i64, u8::MAX as i64),
                    LirType::I16 => (i16::MIN as i64, i16::MAX as i64, u16::MAX as i64),
                    _ => (i32::MIN as i64, i32::MAX as i64, u32::MAX as i64),
                };

                // overflow flag (B1).
                if signed {
                    // overflow = (prod < iN::MIN) OR (prod > iN::MAX)
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
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: signed_lo },
                        args: vec![],
                        results: vec![lo_bound],
                    });
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: signed_hi },
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
                    // overflow = (prod > uN::MAX)   (unsigned compare; prod is
                    // the exact unsigned product)
                    let hi_bound = Value(*next_value);
                    *next_value += 1;
                    value_types.insert(hi_bound, LirType::I64);
                    instructions.push(Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I64, imm: unsigned_hi },
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
            // Three admitted rootings: an Alloca-rooted stack slot; an INCOMING
            // READ-ONLY slice root; or a direct immutable assembled-global root.
            // Global roots deliberately do not flow through GEP/Copy/Store in
            // this first object-relocation rung.
            let ptr_v = vmap.resolve(*ptr, name)?;
            if mem.slot_of.contains_key(&ptr_v) {
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
            } else if let Some(elem) = mem.incoming_pointee.get(&ptr_v) {
                if *elem != lir_ty {
                    return Err(ModuleLirError::UnsupportedMemory {
                        name: name.to_string(),
                        detail: format!(
                            "Load width {lir_ty:?} does not match the slice element {elem:?}"
                        ),
                    });
                }
            } else if let Some(elem) = mem.global_pointee.get(&ptr_v) {
                if *elem != lir_ty {
                    return Err(ModuleLirError::UnsupportedMemory {
                        name: name.to_string(),
                        detail: format!(
                            "Load width {lir_ty:?} does not match assembled global element \
                             {elem:?}"
                        ),
                    });
                }
            } else {
                return Err(ModuleLirError::NonLocalPointer {
                    name: name.to_string(),
                    value: ptr.index(),
                });
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
            // Same two rootings as `Load`: an Alloca-rooted slot, or an
            // incoming read-only slice-data root (result inherits the root
            // kind and pointee).
            let base_v = vmap.resolve(*base, name)?;
            let incoming = mem.incoming_pointee.get(&base_v).cloned();
            if !mem.slot_of.contains_key(&base_v) && incoming.is_none() {
                return Err(ModuleLirError::NonLocalPointer {
                    name: name.to_string(),
                    value: base.index(),
                });
            }
            let index_v = vmap.resolve(*index, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, LirType::I64);
            if let Some(&slot) = mem.slot_of.get(&base_v) {
                mem.slot_of.insert(dst, slot);
                mem.pointee_ty.insert(dst, elem_ty.clone());
            }
            if incoming.is_some() {
                mem.incoming_pointee.insert(dst, elem_ty.clone());
            }
            instructions.push(Instruction {
                opcode: Opcode::ArrayGep { elem_ty },
                args: vec![base_v, index_v],
                results: vec![dst],
            });
        }
        // ---- Fat slice parameter lanes: PtrData / PtrMetadata. ----
        //
        // The ONLY admitted fat-pointer source is a `&[T]` FORMAL, whose two
        // split halves the entry binding placed in `mem.fat_params` (the fat
        // pointer's own ValueId is unbound, so every other use of it fails
        // closed as an undefined value — including these two lanes when the
        // operand is anything but a fat formal).
        Inst::PtrData { ptr, .. } => {
            let result = expect_single_result(node, name)?;
            let Some(fat) = mem.fat_params.get(ptr) else {
                return Err(ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: "PtrData on a value that is not a fat slice formal (only the \
                             split `&[T]` parameter lane is mapped)"
                        .to_string(),
                });
            };
            let (data, elem) = (fat.data, fat.elem.clone());
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, LirType::I64);
            // The data pointer is an INCOMING READ-ONLY root for later GEP/Load.
            mem.incoming_pointee.insert(dst, elem);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![data],
                results: vec![dst],
            });
        }
        Inst::PtrMetadata { ptr, metadata_ty, .. } => {
            let result = expect_single_result(node, name)?;
            let Some(fat) = mem.fat_params.get(ptr) else {
                return Err(ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: "PtrMetadata on a value that is not a fat slice formal (only the \
                             split `&[T]` parameter lane is mapped)"
                        .to_string(),
                });
            };
            let lir_ty = map_scalar_int_ty(metadata_ty, "PtrMetadata result")?;
            if lir_ty != LirType::I64 {
                return Err(ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: format!(
                        "slice length metadata must be the 64-bit count, got {lir_ty:?}"
                    ),
                });
            }
            let len = fat.len;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, LirType::I64);
            instructions.push(Instruction {
                opcode: Opcode::Copy,
                args: vec![len],
                results: vec![dst],
            });
        }
        // ---- GlobalAddr -> Opcode::GlobalRef. ----
        //
        // A `GlobalAddr { global }` materializes the address of a module global
        // into a register. ISel lowers `Opcode::GlobalRef { name }` to
        // `ADRP Xd, name@PAGE` (`ARM64_RELOC_PAGE21`) + `ADD Xd, Xd, name@PAGEOFF`
        // (`ARM64_RELOC_PAGEOFF12`) — the LINKER-resolved address of the named
        // LOCAL symbol. This is the foundation for a KNOWN-target indirect call: a
        // subsequent `CallIndirect` through this register BLRs to the callee.
        //
        // We record every direct-global result in `global_addr_provenance`, with
        // function-symbol proxies distinct from data. That lets `CallIndirect`
        // trace a legitimate function pointer while rejecting a known data address
        // instead of misclassifying it as an OPEN target.
        //
        // The result is an I64 pointer. Existing function-symbol proxy globals
        // retain their CallIndirect provenance. Separately, the exact first data
        // slice — immutable initialized non-TLS Internal/Private u64 — receives
        // read-only provenance so one or more direct exact-width Loads can lower.
        // No Store/GEP/Copy provenance is granted, and object emission rechecks
        // the same shape through the canonical Trust-IR global encoder.
        Inst::GlobalAddr { global } => {
            let g = module.globals.get(global.as_usize()).ok_or_else(|| {
                ModuleLirError::MissingGlobal { name: name.to_string(), global: global.index() }
            })?;
            let result = expect_single_result(node, name)?;
            let dst = vmap.resolve(result, name)?;
            value_types.insert(dst, LirType::I64);
            let assembled_read_only_data = !g.mutable
                && g.initializer.is_some()
                && g.tls.is_none()
                && matches!(g.linkage, trust_ir::Linkage::Internal | trust_ir::Linkage::Private)
                && g.ty == Ty::U64
                && g.align.is_none_or(|align| align >= 8 && align.is_power_of_two());
            if assembled_read_only_data {
                mem.global_pointee.insert(dst, LirType::I64);
            }
            if crate::codegen_backend::function_symbol_proxy(module, g) {
                // Legacy function-symbol proxies have no initializer and are
                // used only to identify a known indirect-call target. Keep
                // that provenance disjoint from real data definitions.
                global_addr_provenance
                    .insert(dst, GlobalAddrProvenance::FunctionSymbol(g.name.clone()));
            } else {
                global_addr_provenance.insert(dst, GlobalAddrProvenance::DataSymbol);
            }
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
        // whether the fn-pointer traces (via `global_addr_provenance`) to a concrete
        // GlobalAddr'd symbol:
        //
        //  * KNOWN target (a function-symbol provenance entry naming a LOCAL pure fn in
        //    the SAME gate-composable fragment as the direct-call path,
        //    `callee_is_real_call_composable`): emit `Opcode::CallIndirect` (args[0]
        //    = fn ptr, args[1..] = the call args) -> `BLR <fn-ptr-reg>` (a genuine
        //    INDIRECT branch, not a direct `Bl`). The executor COMPOSES it exactly
        //    like the direct case: trace the BLR's target register to its GlobalRef
        //    symbol via the emitted PAGE21/PAGEOFF12 relocations, substitute that
        //    callee's derived pure output into X0, havoc caller-saved registers.
        //    A direct data-global provenance entry, or a function entry that resolves to an
        //    impure/nonlocal fn is a TRACEABLE-but-not-composable target and FAILS
        //    CLOSED (it is not OPEN — its identity is known, but a BLR into data or
        //    an effectful callee cannot be soundly modeled as a pure formula).
        //
        //  * OPEN target (a provenance MISS: an incoming fn-pointer arg, a
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
            match global_addr_provenance.get(&ptr_v) {
                // ---- KNOWN target: trace to a symbol. ----
                Some(GlobalAddrProvenance::FunctionSymbol(sym)) => {
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
                // A direct data address is traceable and definitely not an open
                // function pointer. Executing it as code would be unsound.
                Some(GlobalAddrProvenance::DataSymbol) => {
                    return Err(ModuleLirError::UnsupportedInst {
                        name: name.to_string(),
                        inst: inst_name(&node.inst),
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
        // fragment). We emit a genuine LIR `Opcode::Call { name, .. }` — ISel lowers it
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
            // `DirectCallBinding` arrived with the trust-cg pin advance. It is
            // `Interposable` here — the field's own `#[default]` and
            // `#[serde(default)]` — because that is exactly the semantics this
            // edge had before the field existed: resolve by the platform's
            // ordinary named-symbol rules.
            //
            // `ExactModuleFunction { function }` is the STRONGER claim ("resolve
            // only to this validated module-local function identity, or fail
            // closed"), and this producer has authenticated no such numeric
            // identity against the module. Even though `callee_fn` is
            // module-local, minting that claim here would assert an
            // authentication that never happened. Tightening this is a separate,
            // deliberate change that must first establish the identity.
            instructions.push(Instruction {
                opcode: Opcode::Call {
                    name: callee_fn.name.clone(),
                    binding: DirectCallBinding::Interposable,
                },
                args: arg_vals,
                results: vec![dst],
            });
        }
        // Named, not left to the fall-through: neither uniform array registers
        // nor runtime closure environments have a verified lowering here.
        // Refuse construction even when the result is never consumed.
        Inst::ArraySplat { .. } | Inst::MakeClosure { .. } => {
            return Err(ModuleLirError::UnsupportedInst {
                name: name.to_string(),
                inst: inst_name(&node.inst),
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
/// `global_addr_provenance` MISS (only `GlobalAddr` results are tagged), so a
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
        | Ty::I128
        | Ty::U128
        | Ty::Bool
        | Ty::Ptr => map_scalar_int_ty(ty, context),
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
    value_types: &HashMap<Value, LirType>,
    pair_enum_values: &HashMap<ValueId, (Value, Value)>,
    blocks_by_id: &HashMap<u32, &trust_ir::Block>,
    instructions: &mut Vec<Instruction>,
    edge_blocks: &mut Vec<(Block, LirBlock)>,
    next_edge_block: &mut FreshIdCursor,
    next_value: &mut u32,
    name: &str,
) -> Result<(), ModuleLirError> {
    match term {
        Inst::Return { values } => {
            // A VOID return (`ret` with no values) carries no args — the twin
            // of the empty `Signature::returns`; a single value resolves and
            // rides the return slot. More than one return value stays refused.
            // A PAIR-ENUM return carries both lanes: (tag, payload) — the
            // signature declared two returns for it.
            if let [v] = values.as_slice()
                && let Some((tag_v, pay_v)) = pair_enum_values.get(v)
            {
                instructions.push(Instruction {
                    opcode: Opcode::Return,
                    args: vec![*tag_v, *pay_v],
                    results: vec![],
                });
                return Ok(());
            }
            let args = match values.as_slice() {
                [] => vec![],
                [v] => vec![vmap.resolve(*v, name)?],
                _ => return Err(ModuleLirError::MalformedReturn { name: name.to_string() }),
            };
            instructions.push(Instruction { opcode: Opcode::Return, args, results: vec![] });
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
                pair_enum_values,
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
                pair_enum_values,
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
                pair_enum_values,
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
            // The LIR case constant is a function of the SELECTOR'S WIDTH, not
            // of the trust-ir constant alone: an 8/16-bit selector is compared
            // zero-extended, so `i8 -3` must be encoded as 253, and a 32-bit
            // selector wants its two's-complement value (see
            // `mapping::encode_switch_case`). Passing the signed trust-ir value
            // through verbatim made every NEGATIVE arm on a narrow selector —
            // e.g. `match g { G::A => .. }` for `enum G { A = -3, B = 7 }`,
            // whose tag is an i8 — unreachable, silently taking the default.
            let sel_ty =
                value_types.get(&sel).ok_or_else(|| ModuleLirError::UnencodableSwitchCase {
                    name: name.to_string(),
                    detail: format!(
                        "selector value {} has no recorded LIR type, so its compare width \
                         (and with it the case encoding) is unknown",
                        sel.0
                    ),
                })?;
            let mut raw_cases = Vec::with_capacity(cases.len());
            for case in cases {
                raw_cases.push(match &case.value {
                    Constant::Int(v) => *v,
                    Constant::Bool(b) => i128::from(*b),
                    _ => {
                        return Err(ModuleLirError::UnsupportedSwitchCase {
                            name: name.to_string(),
                        });
                    }
                });
            }
            let encoded_cases =
                crate::mapping::encode_switch_cases(raw_cases, sel_ty).map_err(|e| {
                    ModuleLirError::UnencodableSwitchCase {
                        name: name.to_string(),
                        detail: e.to_string(),
                    }
                })?;
            let mut lir_cases = Vec::with_capacity(cases.len());
            for (case, case_val) in cases.iter().zip(encoded_cases) {
                let dest = conditional_edge_dest(
                    case.target,
                    &case.args,
                    vmap,
                    pair_enum_values,
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
                pair_enum_values,
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
    pair_enum_values: &HashMap<ValueId, (Value, Value)>,
    blocks_by_id: &HashMap<u32, &trust_ir::Block>,
    edge_blocks: &mut Vec<(Block, LirBlock)>,
    next_edge_block: &mut FreshIdCursor,
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
    emit_edge_arg_copies(
        target,
        args,
        vmap,
        pair_enum_values,
        blocks_by_id,
        &mut tramp,
        next_value,
        name,
    )?;
    tramp.push(Instruction {
        opcode: Opcode::Jump { dest: Block(target.index()) },
        args: vec![],
        results: vec![],
    });
    let id = Block(next_edge_block.take(name)?);
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
    pair_enum_values: &HashMap<ValueId, (Value, Value)>,
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
        // A PAIR-ENUM edge argument copies BOTH lanes into the target's pair
        // params. Arg and param must agree on pairness — a mismatch is
        // producer type drift, fail closed.
        match (pair_enum_values.get(arg), pair_enum_values.get(param_id)) {
            (Some((s_tag, s_pay)), Some((d_tag, d_pay))) => {
                if s_tag != d_tag {
                    pending.push((*s_tag, *d_tag));
                }
                if s_pay != d_pay {
                    pending.push((*s_pay, *d_pay));
                }
                continue;
            }
            (None, None) => {}
            _ => {
                return Err(ModuleLirError::EdgeArgArity {
                    name: name.to_string(),
                    target: target.index(),
                    got: args.len(),
                    expected: target_block.params.len(),
                });
            }
        }
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
// overflow slice handled. Since BMC-LANE-1 (2026-11-06) the emitted shape
// (dumped from `trust_ir_bridge::lower_to_trust_ir` on the `CheckedBinaryOp` VF
// and pinned by `bridge_checked_mul_packs_the_pair_with_one_make_aggregate` in
// `tests/module_to_lir_checked_mul_proven_output.rs`) is:
//
//     %v, %o = add.overflow i32 %a, %b      ; Inst::Overflow  -> [value, flag]
//     %t  = make_aggregate (i32,bool) [%v, %o] ; the complete pair (FULL tuple)
//     ... extractfield bool %t, 1  -> the overflow flag (the assert reads this)
//     ... extractfield i32  %t, 0  -> the value         (the result reads this)
//
// Before BMC-LANE-1 the bridge built the pair from a poison seed, and this pass
// still decomposes that legacy spelling the same way:
//
//     %u  = undef (i32, bool)               ; TUPLE-typed Undef SEED
//     %t0 = insertfield (i32,bool) %u, 0, %v   ; field 0 <- value
//     %t  = insertfield (i32,bool) %t0, 1, %o  ; field 1 <- flag  (FULL tuple)
//
// The tuple is a PURE SSA value — never stored to memory — so we DECOMPOSE it
// into the two scalar SSA Values it carries (which already exist: the
// `Inst::Overflow` results) WITHOUT ever materializing a `Ty::Tuple` in memory
// (a checked pair stored to memory is out of this slice and fails closed). The
// constructor, or the `Undef` seed and its `InsertField`s, emit NO LIR; each
// `ExtractField` becomes a `Copy` of the resolved field Value.
//
// SOUNDNESS (a wrong checked-arith mapping miscompiles): this is a MUST analysis
// that admits a tuple ONLY when it can prove, for every tuple-typed SSA value:
//   * its def-chain roots at a `Tuple([_, _])`-typed `Undef` SEED, or it is a
//     complete pair `MakeAggregate` whose two lanes are not tracked tuples;
//   * every `InsertField` defines a DISTINCT in-range field exactly once (no
//     double-write, no out-of-range field);
//   * by the time ANY `ExtractField` reads field `k`, field `k` is DEFINED
//     (the constructor defines both fields at once; the legacy chain builds
//     field 0 then field 1 before either read; and trust_ir is SSA with
//     defs-before-uses, so the straight-line def order witnesses this);
//   * NO tuple-typed value is consumed by anything but `InsertField`/
//     `ExtractField` (no `Store`, `Return`, branch-arg, strict op, `Call`,
//     `MakeAggregate` lane, ...).
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
    /// `MakeAggregate` result ValueIds of a checked-arith pair, the complete
    /// constructor the bridge emits for it — these emit NO LIR; both fields are
    /// defined at the node.
    make_results: std::collections::HashSet<ValueId>,
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
/// (one `MakeAggregate`, or the legacy seed + two `InsertField`s) strictly
/// before any `ExtractField`, so a single
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
    let is_checked_arith_pair = |elems: &[Ty]| {
        elems.len() == 2
            && matches!(elems[1], Ty::Bool)
            && map_scalar_int_ty(&elems[0], "checked-arith value field").is_ok()
    };
    let mut tuple_field_count: Map<ValueId, usize> = Map::new();
    // The complete constructor of a checked-arith pair (`MakeAggregate` over the
    // `Inst::Overflow` value and flag): both fields are defined where it is built.
    let mut pair_makes: Set<ValueId> = Set::new();
    for &bid in order {
        let block = blocks_by_id[&bid];
        for node in &block.body {
            if let Inst::MakeAggregate { ty: Ty::Tuple(elems), variant: None, fields } = &node.inst
                && is_checked_arith_pair(elems)
                && fields.len() == 2
                && let [result] = node.results.as_slice()
            {
                pair_makes.insert(*result);
            }
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
                if !is_checked_arith_pair(elems) {
                    continue;
                }
                tuple_field_count.insert(*result, elems.len());
            }
        }
    }

    // Fast path: no checked-arith pair anywhere -> nothing to decompose.
    if tuple_field_count.is_empty() && pair_makes.is_empty() {
        return Ok(TupleDecompose {
            admitted_tuple_seeds: Set::new(),
            insert_results: Set::new(),
            make_results: Set::new(),
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
    let mut make_results: Set<ValueId> = Set::new();
    let mut extract_field_src: Map<ValueId, ValueId> = Map::new();

    for &bid in order {
        let block = blocks_by_id[&bid];
        for node in &block.body {
            match &node.inst {
                // The seed itself: already registered in `fields`. Nothing to do.
                Inst::Undef { ty: Ty::Tuple(_) } => {}
                // The complete constructor: every field is defined here. Its lanes
                // are the scalar value and flag, never a tracked tuple.
                Inst::MakeAggregate { fields: lanes, .. }
                    if node.results.first().is_some_and(|r| pair_makes.contains(r)) =>
                {
                    let result = node.results[0];
                    if lanes.iter().any(|lane| fields.contains_key(lane)) {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "checked-arith pair {} is built from a tracked tuple value",
                                result.index()
                            ),
                        });
                    }
                    fields.insert(result, lanes.iter().copied().map(Some).collect());
                    root.insert(result, result);
                    make_results.insert(result);
                }
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

    Ok(TupleDecompose { admitted_tuple_seeds, insert_results, make_results, extract_field_src })
}

// ===========================================================================
// AGGREGATE-IN-MEMORY DECOMPOSITION (fail-closed).
//
// The BRIDGE promotes a multi-block-written aggregate local to a whole-aggregate
// stack slot (`trust_ir_bridge::lower::promote_local_to_memory` +
// `ensure_local_storage`) and round-trips it through that ONE stack slot AS A
// UNIT. Since BMC-LANE-1 (2026-11-06) the emitted shape for a 2-field scalar
// `Ty::Tuple` (dumped from `lower_to_trust_ir` and pinned by
// `bridge_promoted_tuple_local_is_stored_from_a_make_aggregate` in
// `tests/module_to_lir_aggregate_mem_proven_output.rs`) is:
//
//     %slot = alloca (i32,i32)                        ; AGGREGATE stack slot
//                                                     ;   (no initializing store)
//     %t    = make_aggregate (i32,i32) [%a, %b]       ; a complete construction
//     store (i32,i32) %t -> *%slot                    ; whole-aggregate store
//     %ld   = load  (i32,i32) *%slot                  ; whole-aggregate load
//     %f0   = extractfield i32 %ld, 0                  ; (the bridge loads the
//     %f1   = extractfield i32 %ld, 1                  ;  slot again per read)
//
// The stored value may also be spelled as a seed under an `InsertField` chain,
// and this pass admits that the same way: `undef (i32,i32)` (the bridge's
// spelling of every construction before BMC-LANE-1; it now keeps the seed only
// for a partial construction and a by-value FnOnce closure environment) or
// `const (i32,i32) [0,0]`:
//
//     %base = const (i32,i32) [0,0]      ; or undef (i32,i32) seed
//     %t0   = insertfield (i32,i32) %base, 0, %a
//     %t    = insertfield (i32,i32) %t0,   1, %b      ; full SSA aggregate
//
// We DECOMPOSE the aggregate into its per-field scalar SSA values and lower the
// whole-aggregate Store/Load into PER-FIELD scalar Str/Ldr at the field OFFSETS
// of the trust-ir interpreter's own layout of the slot's type
// (`aggregate_mem_layout`, CG-DECLARED-LAYOUT-1). The aggregate value never
// materializes as a single machine register. For a struct with a declared
// size/align/offset triple, or a tuple with a `Module::tuple_layouts`
// descriptor, each field lands at its DECLARED offset (a reordered
// `S { a@4, b@0 }` stores `b` at the slot's base); for a type that declares
// none, at the declaration-order `aggregate_layout` offset. Either way that is
// exactly where the interpreter's `encode_value`/`decode_value` place them, so
// the slot image of the emitted bytes and of the reference interpreter agree.
//
// SOUNDNESS (a wrong aggregate lowering miscompiles): this is a MUST analysis
// that admits an aggregate slot ONLY when it can prove, for the whole function:
//   * the slot's `Alloca` pointee is a `Ty::Tuple`, or a `repr(Rust)`
//     `Ty::Struct` the module resolves, of scalar fields, laid out by
//     `aggregate_mem_layout` at the interpreter's own layout of that type (a
//     declared layout is re-validated and a declaration the interpreter refuses
//     is refused);
//   * EVERY use of that slot is the pointer of a `Store`/`Load` at the slot's
//     own WHOLE-aggregate type (step 1b, over trust-ir's exhaustive operand
//     visitor) — a partial/scalar access into the aggregate slot, a `GEP`
//     re-derived address into it (the GEP field-index idiom
//     `idx * byte_size(field)` does NOT in general equal the C-style offset), and
//     the slot escaping as any other operand all fail closed. This bullet was
//     claimed before step 1b enforced it (BMC-LANE-1 hostile review #19). The
//     one other admitted use is the base of a FIELD POINTER into a `Ty::Struct`
//     slot (F1-FIELD-POINTER-AGREEMENT-1): `gep i8 %slot, %c` with `%c` a
//     `const i64` equal to the start of exactly one field `k` in the slot's
//     layout, whose result is used ONLY as the pointer of a non-volatile
//     `Load`/`Store` at exactly field `k`'s type. Since the layout is the
//     interpreter's own, both programs read and write exactly field `k`'s bytes;
//     a tuple slot gets no field pointer (the producer emits none);
//   * every stored aggregate VALUE decomposes to a per-field scalar map rooted at
//     a `Const::Aggregate`/`Undef` base built by distinct single-write
//     `InsertField`s, OR is a complete `MakeAggregate` constructor of scalar
//     lanes, OR is itself a tracked aggregate `Load` result;
//   * every tracked aggregate value is consumed ONLY by `InsertField` (build),
//     `Store` (into a slot), or `ExtractField` (read) — a tuple escaping to a
//     return / branch-arg / strict op / `Call`, or used as a `MakeAggregate`
//     lane (a nested aggregate), fails closed.
// Any deviation FAILS CLOSED (`UnsupportedAggregate`/`UnsupportedMemory`), so an
// aggregate the converter cannot soundly decompose is never lowered.
// ===========================================================================

/// The bookkeeping the aggregate-memory lowering consumes.
struct AggMemDecompose {
    /// Aggregate `Alloca` result `ValueId` -> its slot layout (the interpreter's
    /// layout of the slot's type, [`aggregate_mem_layout`]). The
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
    /// `MakeAggregate` result `ValueId`s, complete constructors of a tracked
    /// aggregate — emit NO LIR; every field is defined at the node.
    agg_make_results: std::collections::HashSet<ValueId>,
    /// Whole-aggregate `Store` node positions (by stored-value `ValueId`) we have
    /// proven are aggregate-slot stores — lowered to per-field Str.
    agg_store_values: std::collections::HashSet<ValueId>,
    /// Aggregate `Load` result `ValueId`s — lowered to per-field Ldr producing a
    /// fresh tracked aggregate.
    agg_load_results: std::collections::HashSet<ValueId>,
    /// `ExtractField` result `ValueId`s that read a tracked aggregate — the field
    /// index they read (resolved against the live per-field map at lowering).
    agg_extract_field: std::collections::HashMap<ValueId, u32>,
    /// Whole-aggregate `Load` results whose POINTER is an incoming `Ty::Ptr`
    /// entry param (a read-only root: `&self`/`&T`). Lowered to per-field Ldr
    /// through the incoming pointer at the C-layout field offsets. The layout
    /// is keyed by the LOAD RESULT because the root has no slot.
    agg_incoming_load_layout: std::collections::HashMap<ValueId, AggMemLayout>,
    /// Admitted FIELD POINTERS (step 1b): `gep i8 %slot, <field start>` results
    /// -> the field's layout offset and LIR type.
    agg_field_ptrs: std::collections::HashMap<ValueId, AggFieldPtr>,
}

/// An admitted field pointer's lowering facts: where its field starts in the
/// slot's layout, and the field's LIR type (the pointee its accesses are
/// width-checked at).
struct AggFieldPtr {
    offset: u32,
    lir: LirType,
}

/// One admitted field pointer into a `Ty::Struct` aggregate slot (step 1b).
struct FieldPointer {
    /// The aggregate slot's `Alloca` result.
    slot: ValueId,
    /// The field's declaration index.
    index: usize,
    /// The field's trust-ir type: each access through the pointer is at exactly
    /// this type.
    ty: Ty,
    /// The field's offset in the slot's layout.
    offset: u32,
    /// The field's LIR type.
    lir: LirType,
}

/// The `gep i8 %slot, %c` results that address exactly ONE field of a
/// `Ty::Struct` aggregate slot (F1-FIELD-POINTER-AGREEMENT-1), the F1 producer's
/// `lower_field_of_local_addr` spelling of `&s.f` / `s.f = v` on a promoted
/// struct local.
///
/// A GEP qualifies only when ALL of these hold; any other GEP off a slot is left
/// out, so step 1b refuses it as a slot misuse:
/// * pointee `I8`, exactly one index, exactly one result;
/// * the index is the result of a `const i64` (a reachable `Inst::Const` of
///   type `Ty::I64` with an integer value `c`), and both it and the GEP result
///   have exactly one reachable definition (the address is lowered from the
///   layout offset, so the interpreter's runtime index must be `c`, and every
///   use of the result must see this GEP);
/// * the base is an admitted aggregate slot of type `Ty::Struct` (a `Ty::Tuple`
///   slot gets none: the producer emits no tuple field pointer, so none is
///   admitted);
/// * exactly one field `k` of the slot's layout starts at `c`. The layout is the
///   interpreter's own ([`aggregate_mem_layout`]): validated non-overlapping,
///   in-bounds, naturally aligned scalar fields. So `c` in padding, inside a
///   field, at or past the end, or negative starts no field and is refused.
///
/// Field `k`'s type and LIR type come from the `StructDef` and the layout; the
/// walk in step 1b then requires every use of the result to be the pointer of
/// a non-volatile Load/Store at exactly that type.
fn aggregate_field_pointers(
    module: &Module,
    order: &[u32],
    blocks_by_id: &HashMap<u32, &trust_ir::Block>,
    agg_alloca_ty: &HashMap<ValueId, Ty>,
    agg_alloca_layout: &HashMap<ValueId, AggMemLayout>,
) -> HashMap<ValueId, FieldPointer> {
    let mut const_i64: HashMap<ValueId, i128> = HashMap::new();
    let mut definitions: HashMap<ValueId, usize> = HashMap::new();
    for &bid in order {
        let block = blocks_by_id[&bid];
        for (param, _) in &block.params {
            *definitions.entry(*param).or_default() += 1;
        }
        for node in &block.body {
            for result in &node.results {
                *definitions.entry(*result).or_default() += 1;
            }
            if let (Inst::Const { ty: Ty::I64, value: Constant::Int(c) }, [result]) =
                (&node.inst, node.results.as_slice())
            {
                const_i64.insert(*result, *c);
            }
        }
    }
    let defined_once = |v: &ValueId| definitions.get(v) == Some(&1);
    let mut pointers = HashMap::new();
    for &bid in order {
        for node in &blocks_by_id[&bid].body {
            let Inst::GEP { pointee_ty: Ty::I8, base, indices, inbounds: _ } = &node.inst else {
                continue;
            };
            let ([index], [result]) = (indices.as_slice(), node.results.as_slice()) else {
                continue;
            };
            if !defined_once(index) || !defined_once(result) {
                continue;
            }
            let (Some(Ty::Struct(sid)), Some(layout), Some(&c)) =
                (agg_alloca_ty.get(base), agg_alloca_layout.get(base), const_i64.get(index))
            else {
                continue;
            };
            let Some(def) = module.struct_def(*sid) else { continue };
            if def.fields.len() != layout.field_offsets.len() {
                continue;
            }
            let mut starting =
                layout.field_offsets.iter().enumerate().filter(|(_, (o, _))| i128::from(*o) == c);
            let (Some((k, (offset, lir))), None) = (starting.next(), starting.next()) else {
                continue;
            };
            pointers.insert(
                *result,
                FieldPointer {
                    slot: *base,
                    index: k,
                    ty: def.fields[k].ty.clone(),
                    offset: *offset,
                    lir: lir.clone(),
                },
            );
        }
    }
    pointers
}

impl AggMemDecompose {
    fn empty() -> Self {
        Self {
            agg_alloca_layout: std::collections::HashMap::new(),
            agg_const_seeds: std::collections::HashMap::new(),
            agg_undef_seeds: std::collections::HashSet::new(),
            agg_insert_results: std::collections::HashSet::new(),
            agg_make_results: std::collections::HashSet::new(),
            agg_store_values: std::collections::HashSet::new(),
            agg_load_results: std::collections::HashSet::new(),
            agg_extract_field: std::collections::HashMap::new(),
            agg_incoming_load_layout: std::collections::HashMap::new(),
            agg_field_ptrs: std::collections::HashMap::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.agg_alloca_layout.is_empty() && self.agg_incoming_load_layout.is_empty()
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
    ptr_params: &std::collections::HashSet<ValueId>,
    name: &str,
) -> Result<AggMemDecompose, ModuleLirError> {
    use std::collections::{HashMap as Map, HashSet as Set};

    // ---- 1. Find aggregate Alloca slots (self-describing Ty::Tuple, or a
    // Ty::Struct whose StructDef the module resolves). A scalar Alloca is left to
    // the scalar memory slice. Only an aggregate pointee enters here; its layout
    // (`aggregate_mem_layout`, resolving struct fields via the module) is the
    // interpreter's own layout of the type: a declared one read and re-validated,
    // declaration order only when the type declares none (CG-DECLARED-LAYOUT-1).
    // We record the slot's aggregate type so every access can be checked against
    // the WHOLE-aggregate type (step 1b). The resolved field count (N, generalized
    // from the initial 2-field slice) that Store/Load check against comes from the
    // layout's `field_offsets.len()`.
    let mut agg_alloca_layout: Map<ValueId, AggMemLayout> = Map::new();
    let mut agg_alloca_ty: Map<ValueId, Ty> = Map::new();
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
                agg_alloca_ty.insert(*result, ty.clone());
            }
        }
    }

    // ---- 1b. An aggregate slot is used ONLY as the POINTER of a whole-aggregate
    // `Store`/`Load` at the slot's own type. Trust (BMC-LANE-1 hostile review #19):
    // the Store/Load arms below check only the accesses that ARE whole-aggregate;
    // a scalar `Load`/`Store` through the slot, a `GEP` off it, or the slot as any
    // other operand (a call argument, a returned pointer, a branch argument, a
    // stored pointer value) used to fall through to the scalar memory slice. That
    // slice resolves the slot through `slot_of` with no recorded pointee type, so
    // its width check never fired and its `GEP` arm addresses the slot at
    // `index * size_of(pointee)`: a valid module was miscompiled (a declared-layout
    // `S { a@4, b@0 }` read field `a`'s bytes where the interpreter reads `b`'s).
    // The per-field lowering is sound only for a slot that is written and read
    // WHOLE at its own type, so every other use fails closed here. The walk is
    // trust-ir's canonical exhaustive operand visitor, so an instruction added to
    // trust-ir cannot slip past it.
    //
    // Trust (F1-FIELD-POINTER-AGREEMENT-1): the one partial access admitted is a
    // FIELD POINTER, the F1 producer's `lower_field_of_local_addr` spelling of
    // `&s.f` / `s.f = v` on a promoted struct local: `gep i8 %slot, %c` off a
    // `Ty::Struct` slot with `%c` a `const i64` that starts exactly one field
    // `k` of the slot's layout (`aggregate_field_pointers`). Since
    // CG-DECLARED-LAYOUT-1 that layout is the interpreter's own, so `%slot + c`
    // is field `k`'s address in both programs. Every use of such a pointer must
    // then be the pointer of a non-volatile `Load`/`Store` at exactly field `k`'s
    // type (the second walk below): both programs then read and write exactly
    // field `k`'s bytes, which no other field shares, and the whole-aggregate
    // Store/Load arms address field `k` at the same offset. Any other offset
    // (padding, mid-field, past the end, non-constant), pointee, index count,
    // base type or use is still refused: a field pointer whose offset is not the
    // layout's would reproduce the p4 miscompile class.
    let field_ptrs =
        aggregate_field_pointers(module, order, blocks_by_id, &agg_alloca_ty, &agg_alloca_layout);
    for &bid in order {
        for node in &blocks_by_id[&bid].body {
            let whole_access_ptr = match &node.inst {
                Inst::Store { ty, ptr, value, .. }
                    if value != ptr && agg_alloca_ty.get(ptr) == Some(ty) =>
                {
                    Some(*ptr)
                }
                Inst::Load { ty, ptr, .. } if agg_alloca_ty.get(ptr) == Some(ty) => Some(*ptr),
                Inst::GEP { base, .. }
                    if node.results.first().is_some_and(|r| field_ptrs.contains_key(r)) =>
                {
                    Some(*base)
                }
                _ => None,
            };
            let mut misuse = None;
            node.inst.visit_value_operands(|operand| {
                if misuse.is_none()
                    && agg_alloca_ty.contains_key(&operand)
                    && Some(operand) != whole_access_ptr
                {
                    misuse = Some(operand);
                }
            });
            if let Some(slot) = misuse {
                return Err(ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: format!(
                        "aggregate slot {} is used by `{}` other than as the pointer of a \
                         whole-aggregate Store/Load at the slot's own type",
                        slot.index(),
                        inst_name(&node.inst)
                    ),
                });
            }
            // A field pointer is used ONLY as the pointer of a non-volatile
            // Load/Store at exactly its field's type: never stored, passed,
            // returned, compared, cast, copied, re-derived or accessed at another
            // type or width.
            let field_access_ptr = match &node.inst {
                Inst::Store { ty, ptr, value, volatile: false, .. }
                    if value != ptr && field_ptrs.get(ptr).is_some_and(|f| &f.ty == ty) =>
                {
                    Some(*ptr)
                }
                Inst::Load { ty, ptr, volatile: false, .. }
                    if field_ptrs.get(ptr).is_some_and(|f| &f.ty == ty) =>
                {
                    Some(*ptr)
                }
                _ => None,
            };
            let mut field_misuse = None;
            node.inst.visit_value_operands(|operand| {
                if field_misuse.is_none()
                    && field_ptrs.contains_key(&operand)
                    && Some(operand) != field_access_ptr
                {
                    field_misuse = Some(operand);
                }
            });
            if let Some(pointer) = field_misuse {
                let field = &field_ptrs[&pointer];
                return Err(ModuleLirError::UnsupportedMemory {
                    name: name.to_string(),
                    detail: format!(
                        "field pointer {} (field {} of aggregate slot {}) is used by `{}` other \
                         than as the pointer of a non-volatile Load/Store at the field's type \
                         {:?}",
                        pointer.index(),
                        field.index,
                        field.slot.index(),
                        inst_name(&node.inst),
                        field.ty
                    ),
                });
            }
        }
    }

    // Fast path: no aggregate slot AND no incoming-root aggregate load ->
    // nothing to decompose (the scalar/checked slices handle everything).
    let has_incoming_agg_load = order.iter().any(|bid| {
        blocks_by_id[bid].body.iter().any(|node| {
            matches!(&node.inst,
                Inst::Load { ty: Ty::Tuple(_) | Ty::Struct(_), ptr, volatile: false, .. }
                    if ptr_params.contains(ptr))
        })
    });
    if agg_alloca_layout.is_empty() && !has_incoming_agg_load {
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
    let mut agg_make_results: Set<ValueId> = Set::new();
    let mut agg_store_values: Set<ValueId> = Set::new();
    let mut agg_load_results: Set<ValueId> = Set::new();
    let mut agg_extract_field: Map<ValueId, u32> = Map::new();
    let mut agg_incoming_load_layout: Map<ValueId, AggMemLayout> = Map::new();

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
                        scalar_field_size_align(fty, module, name)?;
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
                        scalar_field_size_align(fty, module, name)?;
                    }
                    fields.insert(*result, vec![None; field_tys.len()]);
                    agg_undef_seeds.insert(*result);
                }
                // ---- MakeAggregate: a complete constructor, every field defined.
                Inst::MakeAggregate {
                    ty: ty @ (Ty::Tuple(_) | Ty::Struct(_)),
                    variant: None,
                    fields: lanes,
                } if node
                    .results
                    .first()
                    .is_some_and(|r| !tuple_decompose.make_results.contains(r)) =>
                {
                    let [result] = node.results.as_slice() else {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: "MakeAggregate must bind one result".to_string(),
                        });
                    };
                    let field_tys = aggregate_field_types(ty, module, name)?;
                    if lanes.len() != field_tys.len() {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "MakeAggregate has {} lanes but type has {} fields",
                                lanes.len(),
                                field_tys.len()
                            ),
                        });
                    }
                    for fty in &field_tys {
                        scalar_field_size_align(fty, module, name)?;
                    }
                    if let Some(lane) = lanes.iter().find(|lane| fields.contains_key(lane)) {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: format!(
                                "tracked aggregate value {} is a lane of MakeAggregate (a nested \
                                 aggregate is out of the slice)",
                                lane.index()
                            ),
                        });
                    }
                    fields.insert(*result, lanes.iter().copied().map(Some).collect());
                    agg_make_results.insert(*result);
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
                Inst::Load { ty, ptr, volatile, align: _ }
                    if matches!(ty, Ty::Tuple(_) | Ty::Struct(_)) && ptr_params.contains(ptr) =>
                {
                    // INCOMING READ-ONLY ROOT: a whole-aggregate load through a
                    // `Ty::Ptr` entry param (`&self`, `&T`). The layout comes from
                    // the LOAD's own aggregate type (the opaque pointer carries
                    // none); every field must be a scalar the slice lays out.
                    // Stores through the same root stay fail-closed below (an
                    // incoming pointer is never a slot).
                    if *volatile {
                        return Err(ModuleLirError::UnsupportedMemory {
                            name: name.to_string(),
                            detail: "volatile aggregate Load is out of the slice".to_string(),
                        });
                    }
                    let [result] = node.results.as_slice() else {
                        return Err(ModuleLirError::UnsupportedAggregate {
                            name: name.to_string(),
                            detail: "aggregate Load must bind one result".to_string(),
                        });
                    };
                    let layout = recorded_struct_mem_layout(ty, module, name)?;
                    let n = layout.field_offsets.len();
                    fields.insert(*result, vec![Some(*result); n]);
                    agg_load_results.insert(*result);
                    agg_incoming_load_layout.insert(*result, layout);
                }
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
        agg_make_results,
        agg_store_values,
        agg_load_results,
        agg_extract_field,
        agg_incoming_load_layout,
        agg_field_ptrs: field_ptrs
            .into_iter()
            .map(|(pointer, field)| (pointer, AggFieldPtr { offset: field.offset, lir: field.lir }))
            .collect(),
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

/// Like [`i128_to_i64`], but TYPE-AWARE for a scalar `Inst::Const`: a `u64`
/// (or 64-bit-target `usize`) literal in `(i64::MAX, u64::MAX]` — e.g. the
/// ubiquitous `u64::MAX` sentinel — is representable in the LIR `Iconst` i64
/// carrier as its two's-complement BIT PATTERN, which is exactly what the
/// backend materializes into a 64-bit register. Every other overflow (a wide
/// i128 constant, an unsigned literal exceeding u64) stays fail-closed. A
/// 32-bit-target `usize` can never validly exceed `i64::MAX`, so the unsigned
/// branch is unreachable for it and the plain conversion already covers it.
fn i128_const_to_i64_imm(v: i128, ty: &Ty, name: &str) -> Result<i64, ModuleLirError> {
    if let Ok(x) = i64::try_from(v) {
        return Ok(x);
    }
    if matches!(ty, Ty::U64 | Ty::Usize) {
        if let Ok(x) = u64::try_from(v) {
            return Ok(x as i64);
        }
    }
    Err(ModuleLirError::UnsupportedConstant { name: name.to_string() })
}

#[cfg(test)]
mod tests {
    use trust_ir::Block;
    use trust_ir::inst::ICmpOp;
    use trust_ir::node::InstrNode;
    use trust_ir::ty::{EnumTagRepr, FuncTy};
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
            abi: None,
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

    /// A `u64` literal above `i64::MAX` (here the ubiquitous `u64::MAX`
    /// sentinel, the trust-checksum `message_bit_len` blocker) lowers as its
    /// two's-complement bit pattern in the i64 `Iconst` carrier; a wide i128
    /// constant stays fail-closed.
    #[test]
    fn maps_u64_max_const_as_bit_pattern() {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::U64, Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "umax", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::U64));
        block.params.push((ValueId::new(1), Ty::U64));
        block.body = vec![
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(u64::MAX as i128) })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        f.blocks.push(block);
        module.functions.push(f);

        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("u64::MAX const maps");
        let imm = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .find_map(|i| match i.opcode {
                Opcode::Iconst { imm, .. } => Some(imm),
                _ => None,
            })
            .expect("an Iconst was emitted");
        assert_eq!(imm, -1i64, "u64::MAX must materialize as the all-ones bit pattern");

        // CAPABILITY (was a refusal boundary): a genuinely wide i128
        // constant now materializes through the register-pair
        // `Iconst128 { lo, hi }` the ISel's `select_i128_iconst_wide`
        // consumes, carrying the full value.
        let mut wide = Module::new("t");
        wide.func_types.push(FuncTy {
            params: vec![Ty::U64, Ty::U64],
            returns: vec![Ty::I128],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "wide", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::U64));
        block.params.push((ValueId::new(1), Ty::U64));
        block.body = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I128,
                value: Constant::Int(u64::MAX as i128 + 1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        f.blocks.push(block);
        wide.functions.push(f);
        let lir = lower_module_to_lir(&wide, FuncId::new(0)).expect("wide i128 const maps");
        let (lo, hi) = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .find_map(|i| match i.opcode {
                Opcode::Iconst128 { lo, hi } => Some((lo, hi)),
                _ => None,
            })
            .expect("an Iconst128 was emitted");
        assert_eq!(lo, 0, "u64::MAX + 1 has a zero low half");
        assert_eq!(hi, 1, "u64::MAX + 1 has a one high half");
    }

    /// A VOID function (`(…) -> ()`, empty returns list, bare `ret`) lowers to
    /// an empty LIR `returns` and a no-arg `Opcode::Return` — the same shape
    /// the established MIR path emits for unit functions.
    #[test]
    fn maps_void_function_bare_return() {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "void_fn", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::I32));
        block.params.push((ValueId::new(1), Ty::I32));
        block.body = vec![
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ule,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            // (An `Assert { cond: %2 }` stood here until 2026-09-30; a body
            // carrying one is now refused as an unfaithful implicit panic, and
            // this test is about the bare `Return`, not the guard.)
            InstrNode::new(Inst::Return { values: vec![] }),
        ];
        f.blocks.push(block);
        module.functions.push(f);

        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("void function lowers");
        assert_eq!(lir.signature.returns, Vec::<LirType>::new());
        let bare_return = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .any(|i| matches!(i.opcode, Opcode::Return) && i.args.is_empty());
        assert!(bare_return, "a no-arg Return must be emitted");
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
    fn boolean_connectives_fail_closed_on_integer_lane_with_distinct_diagnostics() {
        // These are Bool-only trust-ir operations. `map_int_binop` must neither
        // accept them as the similarly named integer bitwise operations nor
        // collapse their diagnostics onto And/Or/Xor.
        for (op, diagnostic) in [(BinOp::BAnd, "band"), (BinOp::BOr, "bor"), (BinOp::BXor, "bxor")]
        {
            assert_eq!(
                map_int_binop(op, &Ty::I32, "logical-on-int"),
                Err(ModuleLirError::UnsupportedBinOp {
                    name: "logical-on-int".to_string(),
                    op: diagnostic,
                }),
                "{op:?} must fail closed with its logical-connective diagnostic"
            );
        }
    }

    #[test]
    fn newly_pinned_ir_ops_fail_closed_until_codegen_is_verified() {
        for (op, diagnostic) in
            [(BinOp::RotL, "rotl"), (BinOp::RotR, "rotr"), (BinOp::FCopySign, "fcopysign")]
        {
            assert_eq!(
                map_int_binop(op, &Ty::I32, "new-binop"),
                Err(ModuleLirError::UnsupportedBinOp {
                    name: "new-binop".to_string(),
                    op: diagnostic,
                })
            );
        }
        for (op, diagnostic) in [
            (UnOp::CtLz, "ctlz"),
            (UnOp::CtTz, "cttz"),
            (UnOp::BSwap, "bswap"),
            (UnOp::BitReverse, "bitreverse"),
        ] {
            assert_eq!(
                map_int_unop(op, &Ty::I32, "new-unop"),
                Err(ModuleLirError::UnsupportedUnOp {
                    name: "new-unop".to_string(),
                    op: diagnostic,
                })
            );
        }
        let id = ValueId::new(0);
        assert_eq!(
            inst_name(&Inst::MemCopy { dst: id, src: id, bytes: id, overlap: false }),
            "MemCopy"
        );
        assert_eq!(inst_name(&Inst::MemSet { dst: id, byte: id, bytes: id }), "MemSet");
        assert_eq!(inst_name(&Inst::Drop { ty: Ty::I32, ptr: id }), "Drop");
        assert_eq!(inst_name(&Inst::ArraySplat { ty: Ty::I32, value: id }), "ArraySplat");
    }

    #[test]
    fn runtime_closure_capture_scan_preserves_order_duplicates_and_maximum() {
        // This scan also runs before validity/refusal decisions. An operand-only
        // high id must reserve the numbering range even in malformed input.
        let captures = vec![ValueId::new(7), ValueId::new(2), ValueId::new(7)];
        let constructor = Inst::MakeClosure {
            ty: trust_ir::value::ClosureTyId::new(0),
            func: FuncId::new(0),
            captures: captures.clone(),
        };
        assert_eq!(inst_value_operands(&constructor), captures);
        let module = module_with_body(
            "numbering",
            vec![],
            vec![
                InstrNode::new(constructor).with_result(ValueId::new(3)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        );
        assert_eq!(max_value_id(&module.functions[0]), 7);
    }

    #[test]
    fn runtime_closure_is_named_and_refused_even_when_unused() {
        use trust_ir::interpret::{InterpretValue, Interpreter};

        let mut module = module_with_body("runtime_closure", vec![Ty::I32], Vec::new());
        let apparent = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                is_vararg: false,
                abi: None,
            })
            .expect("apparent closure signature");
        let closure_ty = module
            .add_closure_type(trust_ir::ClosureTy { func: apparent, captures: vec![Ty::I32; 2] })
            .expect("ordered capture declaration");
        let mut target =
            IrFunction::new(FuncId::new(1), "closure_target", FuncTyId::new(0), BlockId::new(0));
        let mut target_block = Block::new(BlockId::new(0));
        target_block.params = vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)];
        target_block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        target.blocks.push(target_block);
        module.try_add_function(target).expect("physical capture-prefix target");
        let captures = vec![ValueId::new(1), ValueId::new(0)];
        let constructor =
            Inst::MakeClosure { ty: closure_ty, func: FuncId::new(1), captures: captures.clone() };
        assert_eq!(inst_name(&constructor), "MakeClosure");
        assert_eq!(
            inst_value_operands(&constructor),
            captures,
            "capture order is an SSA-read fact"
        );
        module.functions[0].blocks[0].body = vec![
            InstrNode::new(constructor).with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }),
        ];
        let args = vec![
            InterpretValue::int(Ty::I32, 4).unwrap(),
            InterpretValue::int(Ty::I32, 7).unwrap(),
        ];
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), args.clone())
            .expect("reachable unused closure construction is valid executable IR");
        assert_eq!(outcome.returns, vec![InterpretValue::int(Ty::I32, 7).unwrap()]);
        assert_eq!(outcome.host_calls, 0);
        let refusal = lower_module_to_lir(&module, FuncId::new(0))
            .expect_err("unused runtime capture construction must not be dropped");
        assert_eq!(
            refusal,
            ModuleLirError::UnsupportedInst {
                name: "runtime_closure".to_string(),
                inst: "MakeClosure",
            }
        );

        module.functions[0].blocks[0].body.remove(0);
        let scalar = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), args)
            .expect("scalar twin executes");
        assert_eq!(scalar.returns, outcome.returns);
        let lir =
            lower_module_to_lir(&module, FuncId::new(0)).expect("scalar twin remains supported");
        assert_eq!(lir.signature.returns, vec![LirType::I32]);
        assert!(
            lir.blocks
                .values()
                .flat_map(|block| &block.instructions)
                .any(|inst| matches!(inst.opcode, Opcode::Return))
        );
    }

    /// trust-ir v47's `Drop` runs a destructor and v50's `ArraySplat` builds an
    /// array: neither is in this bridge's slice, and a destructor treated as a
    /// no-op would model a different program. Both are refused by name.
    #[test]
    fn fail_closed_on_drop_and_array_splat() {
        for want in ["Drop", "ArraySplat"] {
            let mut module = module_with_body("new_inst", vec![Ty::I32], Vec::new());
            let node = if want == "Drop" {
                InstrNode::new(Inst::Drop { ty: Ty::I32, ptr: ValueId::new(0) })
            } else {
                let elem = module.add_type(Ty::I32).expect("Module::add_type: test fixture");
                InstrNode::new(Inst::ArraySplat { ty: Ty::Array(elem, 4), value: ValueId::new(0) })
                    .with_result(ValueId::new(2))
            };
            assert!(inst_value_operands(&node.inst).contains(&ValueId::new(0)));
            module.functions[0].blocks[0].body =
                vec![node, InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] })];
            let lowered = lower_module_to_lir(&module, FuncId::new(0));
            assert!(
                matches!(&lowered, Err(ModuleLirError::UnsupportedInst { inst, .. }) if *inst == want),
                "{want} must be refused by name, got {lowered:?}"
            );
        }
    }

    #[test]
    fn fail_closed_on_box_deref_without_erasing_its_operand() {
        use trust_ir::box_validity::{
            BoxDerefSite, BoxFactSession, BoxPointee, BoxValidityFact, PremiseRoot,
        };

        let operand = ValueId::new(0);
        let inst = Inst::BoxDeref {
            ptr_ty: Ty::Ptr,
            pointee: BoxPointee::Sized { ty: Ty::I32 },
            operand,
            fact: Box::new(BoxValidityFact::premise(
                BoxDerefSite { item: [7; 16], ordinal: 0 },
                BoxFactSession::PROOF_SNAPSHOT,
                PremiseRoot::ParamByValue,
            )),
        };
        assert_eq!(inst_value_operands(&inst), vec![operand]);
        let mut module = module_with_body("box_deref", vec![Ty::Ptr], Vec::new());
        module.func_types[0].params = vec![Ty::Ptr];
        module.functions[0].blocks[0].params = vec![(operand, Ty::Ptr)];
        module.functions[0].blocks[0].body = vec![
            InstrNode::new(inst).with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        let lowered = lower_module_to_lir(&module, FuncId::new(0));
        assert!(
            matches!(&lowered, Err(ModuleLirError::UnsupportedInst { inst, .. })
                if *inst == "BoxDeref"),
            "Box validity evidence must not be discarded by lowering: {lowered:?}"
        );
    }

    #[cfg(feature = "ay-proofs")]
    #[test]
    fn fail_closed_on_box_deref_even_when_unused() {
        use trust_ir::box_validity::{
            BoxDerefSite, BoxFactSession, BoxPointee, BoxValidityFact, PremiseRoot,
        };

        for returned in [ValueId::new(0), ValueId::new(2)] {
            let fact = BoxValidityFact::premise(
                BoxDerefSite { item: [0x5a; 16], ordinal: 7 },
                BoxFactSession::PROOF_SNAPSHOT,
                PremiseRoot::ParamByValue,
            );
            let mut module = module_with_body(
                "box_deref",
                vec![Ty::Ptr],
                vec![
                    InstrNode::new(Inst::BoxDeref {
                        ptr_ty: Ty::Ptr,
                        pointee: BoxPointee::Sized { ty: Ty::U8 },
                        operand: ValueId::new(0),
                        fact: Box::new(fact),
                    })
                    .with_result(ValueId::new(2)),
                    InstrNode::new(Inst::Return { values: vec![returned] }),
                ],
            );
            module.func_types[0].params = vec![Ty::Ptr, Ty::Ptr];
            module.functions[0].blocks[0].params =
                vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::Ptr)];
            assert!(trust_ir_build::validate_module(&module).is_empty());
            assert!(matches!(
                lower_module_to_lir(&module, FuncId::new(0)),
                Err(ModuleLirError::UnsupportedInst { inst: "BoxDeref", .. })
            ));
        }
    }

    /// trust-ir v67-v69's tensor operations compute over a run-time-shaped
    /// tensor value this bridge has no layout for: each is refused by name.
    #[test]
    fn fail_closed_on_tensor_ops() {
        let tensor = Ty::Tensor(Box::new(Ty::I32), 1);
        let v = ValueId::new(0);
        let cases = [
            (
                "TensorContract",
                Inst::TensorContract {
                    ty: tensor.clone(),
                    lhs: v,
                    rhs: v,
                    batch: Vec::new(),
                    contract: vec![(0, 0)],
                },
            ),
            ("TensorMap", Inst::TensorMap { ty: tensor.clone(), args: vec![v], body: Vec::new() }),
            (
                "TensorReduce",
                Inst::TensorReduce {
                    ty: tensor.clone(),
                    src: v,
                    op: trust_ir::TensorReduceOp::Add,
                    axes: vec![0],
                    order: trust_ir::TensorReduceOrder::RowMajor,
                },
            ),
            (
                "TensorView",
                Inst::TensorView {
                    ty: tensor.clone(),
                    src: v,
                    params: Vec::new(),
                    exprs: Vec::new(),
                    shape: vec![1],
                    index: Vec::new(),
                    fill: None,
                },
            ),
            ("TensorGather", Inst::TensorGather { ty: tensor.clone(), data: v, coords: vec![v] }),
            (
                "TensorScatter",
                Inst::TensorScatter { ty: tensor.clone(), init: v, src: v, coords: vec![v] },
            ),
        ];
        for (want, inst) in cases {
            assert_eq!(inst_name(&inst), want);
            let mut module = module_with_body("tensor_inst", vec![Ty::I32], Vec::new());
            module.functions[0].blocks[0].body = vec![
                InstrNode::new(inst).with_result(ValueId::new(2)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
            ];
            let lowered = lower_module_to_lir(&module, FuncId::new(0));
            assert!(
                matches!(&lowered, Err(ModuleLirError::UnsupportedInst { inst, .. }) if *inst == want),
                "{want} must be refused by name, got {lowered:?}"
            );
        }
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

    /// The checked-arithmetic idiom WITHOUT its guard: Overflow -> [res, ovf]
    /// and the Select negation (`!overflowed`), returning the wrapped value.
    /// This is what the `Overflow` lowering is measured on now that the
    /// guarded MIR overflow shape — the same nodes plus `assert %6`, built by
    /// [`checked_add_assert_body`] — is refused as an unfaithful implicit panic
    /// (`ModuleLirError::ImplicitPanicUnfaithful`). Maps to CheckedSadd +
    /// Select with all prior arithmetic preserved, and NO Brif/Trap.
    fn checked_add_idiom_body(op: OverflowOp, ty: Ty) -> Vec<InstrNode> {
        let mut body = checked_add_assert_body(op, ty);
        body.retain(|node| !matches!(node.inst, Inst::Assert { .. }));
        body
    }

    /// The MIR-faithful GUARDED checked-arith idiom (debug overflow checks):
    /// Overflow -> [res, ovf], a Select negation, and a no-overflow Assert.
    fn checked_add_assert_body(op: OverflowOp, ty: Ty) -> Vec<InstrNode> {
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
            InstrNode::new(Inst::Assert {
                cond: ValueId::new(6),
                kind: trust_ir::AssertKind::Unspecified,
                site: None,
            }),
            // return %2
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ]
    }

    /// Narrow checked MULTIPLY (i16/u16/i8/u8) lowers via the same exact-i64
    /// widening as i32 — {s,z}ext + Imul + width-range Icmps — never via
    /// `Checked{S,U}mul` (whose ISel is I64-only) and never fail-closed. This
    /// is the trust-endian `u16_le`/`u16_be` and trust-hex `hex_pair_value`
    /// blocker.
    #[test]
    fn maps_checked_mul_overflow_idiom_narrow_widths() {
        for (ty, signed) in [(Ty::I16, true), (Ty::U16, false), (Ty::I8, true), (Ty::U8, false)] {
            let mut module = Module::new("t");
            module.func_types.push(FuncTy {
                params: vec![ty.clone(), ty.clone()],
                returns: vec![ty.clone()],
                is_vararg: false,
                abi: None,
            });
            let mut f = IrFunction::new(FuncId::new(0), "cmul", FuncTyId::new(0), BlockId::new(0));
            let mut block = Block::new(BlockId::new(0));
            block.params.push((ValueId::new(0), ty.clone()));
            block.params.push((ValueId::new(1), ty.clone()));
            block.body = checked_add_idiom_body(OverflowOp::MulOverflow, ty.clone());
            f.blocks.push(block);
            module.functions.push(f);

            let lir = lower_module_to_lir(&module, FuncId::new(0))
                .unwrap_or_else(|e| panic!("narrow checked-mul at {ty:?} maps: {e}"));

            let mut extends = 0;
            let mut imul = 0;
            let mut trunc = 0;
            let mut checked_mul = 0;
            for b in lir.blocks.values() {
                for inst in &b.instructions {
                    match inst.opcode {
                        Opcode::Sextend { .. } => {
                            assert!(signed, "{ty:?}: Sextend in an unsigned widening");
                            extends += 1;
                        }
                        Opcode::Uextend { .. } => {
                            assert!(!signed, "{ty:?}: Uextend in a signed widening");
                            extends += 1;
                        }
                        Opcode::Imul => imul += 1,
                        Opcode::Trunc { .. } => trunc += 1,
                        Opcode::CheckedSmul | Opcode::CheckedUmul => checked_mul += 1,
                        _ => {}
                    }
                }
            }
            assert_eq!(extends, 2, "{ty:?}: both operands widened");
            assert_eq!(imul, 1, "{ty:?}: exactly one exact i64 Imul");
            assert_eq!(trunc, 1, "{ty:?}: exactly one trunc to the value width");
            assert_eq!(checked_mul, 0, "{ty:?}: no I64-only Checked*mul emitted");
        }
    }

    /// Narrow checked ADD/SUB (i16/u16/i8/u8) lower via the same exact-i64
    /// widening as narrow mul — the ISel's flag-setting Checked{S,U}{add,sub}
    /// idiom exists at I32/I64 only (measured emit_object refusal:
    /// "checked add/sub requires I32 or I64 operands", the trust-checksum
    /// `fletcher_pack` blocker at u16).
    #[test]
    fn maps_checked_add_sub_narrow_widths_via_widening() {
        for (op, want_wide) in
            [(OverflowOp::AddOverflow, "Iadd"), (OverflowOp::SubOverflow, "Isub")]
        {
            for ty in [Ty::I16, Ty::U16, Ty::I8, Ty::U8] {
                let mut module = Module::new("t");
                module.func_types.push(FuncTy {
                    params: vec![ty.clone(), ty.clone()],
                    returns: vec![ty.clone()],
                    is_vararg: false,
                    abi: None,
                });
                let mut f =
                    IrFunction::new(FuncId::new(0), "cnarrow", FuncTyId::new(0), BlockId::new(0));
                let mut block = Block::new(BlockId::new(0));
                block.params.push((ValueId::new(0), ty.clone()));
                block.params.push((ValueId::new(1), ty.clone()));
                block.body = checked_add_idiom_body(op, ty.clone());
                f.blocks.push(block);
                module.functions.push(f);

                let lir = lower_module_to_lir(&module, FuncId::new(0))
                    .unwrap_or_else(|e| panic!("narrow checked {op:?} at {ty:?} maps: {e}"));
                let mut wide = 0;
                let mut checked = 0;
                for b in lir.blocks.values() {
                    for inst in &b.instructions {
                        match inst.opcode {
                            Opcode::Iadd if want_wide == "Iadd" => wide += 1,
                            Opcode::Isub if want_wide == "Isub" => wide += 1,
                            Opcode::CheckedSadd
                            | Opcode::CheckedUadd
                            | Opcode::CheckedSsub
                            | Opcode::CheckedUsub => checked += 1,
                            _ => {}
                        }
                    }
                }
                assert!(wide >= 1, "{op:?}@{ty:?}: the widened 64-bit op must be emitted");
                assert_eq!(checked, 0, "{op:?}@{ty:?}: no narrow Checked* op may be emitted");
            }
        }
    }

    #[test]
    fn maps_checked_add_overflow_idiom_i32() {
        let module = module_with_body(
            "cadd",
            vec![Ty::I32],
            checked_add_idiom_body(OverflowOp::AddOverflow, Ty::I32),
        );
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("checked-add idiom maps");

        // The lowered LIR must carry exactly one CheckedSadd and one Select —
        // and, with no `Assert` in the idiom, no Brif and no Trap: the shared
        // trap block is never materialized for an unguarded body.
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
        assert_eq!(brif, 0, "no Brif: nothing guards the unguarded idiom");
        assert_eq!(trap, 0, "no Trap: an Assert-free body never reaches the trap block");

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

    // NOTE: the historical `fail_closed_on_checked_mul_i16` pin is retired by
    // capability: narrow checked mul now lowers via the exact-i64 widening
    // (`maps_checked_mul_overflow_idiom_narrow_widths` is the positive twin).
    // The historical `fail_closed_on_checked_overflow_i128` ADD pin is likewise
    // retired by capability: checked i128 add/sub now map first-class to the
    // flag-setting carry chain. The surviving 128-bit fail-closed boundary is
    // checked MUL, pinned just below its positive add twin.

    #[test]
    fn maps_checked_add_overflow_idiom_i128() {
        // Checked i128 add maps first-class: one CheckedSadd over the pair
        // (the ISel expands it to ADDS lo; ADCS hi; CSET VS).
        let module = module_with_body(
            "cadd128",
            vec![Ty::I128],
            checked_add_idiom_body(OverflowOp::AddOverflow, Ty::I128),
        );
        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("checked-i128 add idiom maps first-class");
        let checked: Vec<_> = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::CheckedSadd))
            .collect();
        assert_eq!(checked.len(), 1, "exactly one CheckedSadd at I128");
        assert_eq!(checked[0].results.len(), 2, "CheckedSadd binds [value_i128, overflow_b1]");
    }

    #[test]
    fn fail_closed_on_checked_mul_i128() {
        // 128-bit checked MUL has no verified flag/high-half ISel idiom
        // (SMULH/UMULH produce one high half of a 64x64 product only).
        let module = module_with_body(
            "cmul128",
            vec![Ty::I32],
            checked_add_idiom_body(OverflowOp::MulOverflow, Ty::I128),
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
    fn fail_closed_on_scalar_bool_unary() {
        // A scalar-`Bool` `UnOp` must be REFUSED, not mapped. `map_scalar_int_ty`
        // maps `Ty::Bool` to the byte-wide `I8` carrier, so before this refusal a
        // bool `!` became `Bnot`/`MVN` — the bitwise complement of a 0/1 byte
        // (`!true -> 0xFE`), a silent MISCOMPILE of `!b`. The producer respells a
        // bool `!` as `ICmp Eq(x, false)` (`trust-ir-bridge`'s
        // `LoweringCtx::emit_unop`) and the sibling proof-of-output lane already
        // declines this shape ("UnOp on a bool carrier is not modeled"), so this
        // lane must decline it too rather than emit bytes its own verifier will
        // not model. BOTH ops are covered: `Ineg` on a bool is meaningless as well.
        for op in [UnOp::Not, UnOp::Neg] {
            let body = vec![
                InstrNode::new(Inst::UnOp { op, ty: Ty::Bool, operand: ValueId::new(0) })
                    .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
            ];
            let module = module_with_body("boolun", vec![Ty::I32], body);
            assert!(
                matches!(
                    lower_module_to_lir(&module, FuncId::new(0)),
                    Err(ModuleLirError::UnsupportedUnOp { .. })
                ),
                "a scalar-bool UnOp::{op:?} must be refused, got {:?}",
                lower_module_to_lir(&module, FuncId::new(0))
            );
        }
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
            abi: None,
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
    fn admits_make_aggregate_round_trip() {
        // BMC-LANE-1: the bridge builds a complete aggregate with ONE
        // `MakeAggregate`; the round trip decomposes exactly as the
        // Const-seeded one above does: one sized slot, per-field Str and Ldr.
        // The body returns `s.0 - s.1` (not commutative), and the test pins which
        // value each per-field store writes and which load each operand of the
        // subtraction reads, so a lowering that swapped or duplicated a lane fails.
        let tup = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let body = vec![
            InstrNode::new(Inst::MakeAggregate {
                ty: tup.clone(),
                variant: None,
                fields: vec![ValueId::new(0), ValueId::new(1)],
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
                op: BinOp::Sub,
                ty: Ty::I32,
                lhs: ValueId::new(7),
                rhs: ValueId::new(8),
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(9)] }),
        ];
        let module = module_with_body("agg_make", vec![Ty::I32], body);
        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("a MakeAggregate-built scalar aggregate round trip must lower");
        assert_eq!(lir.stack_slots.len(), 1);
        assert_eq!(lir.stack_slots[0].size, 8);
        let insts: Vec<&Instruction> = lir.blocks.values().flat_map(|b| &b.instructions).collect();
        let stores: Vec<_> =
            insts.iter().filter(|i| matches!(i.opcode, Opcode::Store { .. })).collect();
        let loads: Vec<_> =
            insts.iter().filter(|i| matches!(i.opcode, Opcode::Load { .. })).collect();
        assert_eq!(stores.len(), 2, "two per-field stores");
        assert_eq!(loads.len(), 2, "two per-field loads");
        // Entry params are `Value(0..n)` positionally; the per-field stores run in
        // offset order, so field 0 (offset 0) stores param 0 and field 1 param 1.
        assert_eq!(
            stores.iter().map(|store| store.args[0]).collect::<Vec<_>>(),
            vec![Value(0), Value(1)],
            "lane i of the constructor is stored to field i"
        );
        let sub = insts
            .iter()
            .find(|i| matches!(i.opcode, Opcode::Isub))
            .expect("the subtraction lowers to one Isub");
        // Each `ExtractField` lowers to a `Copy` of the field's loaded Value.
        let through_copy = |value: Value| {
            insts
                .iter()
                .find(|i| matches!(i.opcode, Opcode::Copy) && i.results == [value])
                .map_or(value, |copy| copy.args[0])
        };
        assert_eq!(
            sub.args.iter().map(|arg| through_copy(*arg)).collect::<Vec<_>>(),
            vec![loads[0].results[0], loads[1].results[0]],
            "`s.0 - s.1` reads field 0's load, then field 1's"
        );
    }

    #[test]
    fn fail_closed_on_make_aggregate_lane_count_mismatch() {
        // A constructor naming more lanes than its type has fields is not this
        // type's complete aggregate. The constructor is never stored, so only the
        // MakeAggregate arm's own lane-count check can refuse it (the unrelated
        // aggregate Alloca keeps the aggregate-memory analysis off its fast path).
        let tup = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let body = vec![
            InstrNode::new(Inst::MakeAggregate {
                ty: tup.clone(),
                variant: None,
                fields: vec![ValueId::new(0), ValueId::new(1), ValueId::new(0)],
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Alloca { ty: tup, count: None, align: None })
                .with_result(ValueId::new(5)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: ValueId::new(4),
                field: 2,
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(6)] }),
        ];
        let module = module_with_body("agg_make_long", vec![Ty::I32], body);
        match lower_module_to_lir(&module, FuncId::new(0)) {
            Err(ModuleLirError::UnsupportedAggregate { detail, .. }) => assert!(
                detail.contains("lanes but type has"),
                "refused by the lane-count check, not another arm: {detail}"
            ),
            other => panic!("a 3-lane constructor of a 2-field tuple must be refused: {other:?}"),
        }
    }

    #[test]
    fn fail_closed_on_a_make_aggregate_that_binds_two_results() {
        // A constructor binds exactly one value. This one names two results, so
        // PASS 1.6 (which claims a constructor only with one result) leaves it
        // unclaimed, and PASS 1.7's MakeAggregate arm, which selects it by its
        // first result, must refuse it rather than track result 4 and drop 5.
        // The unrelated aggregate Alloca keeps PASS 1.7 off its fast path.
        let tup = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let body = vec![
            InstrNode::new(Inst::MakeAggregate {
                ty: tup.clone(),
                variant: None,
                fields: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_results([ValueId::new(4), ValueId::new(5)]),
            InstrNode::new(Inst::Alloca { ty: tup, count: None, align: None })
                .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
        ];
        let module = module_with_body("agg_make_two_results", vec![Ty::I32], body);
        match lower_module_to_lir(&module, FuncId::new(0)) {
            Err(ModuleLirError::UnsupportedAggregate { detail, .. }) => {
                assert_eq!(detail, "MakeAggregate must bind one result")
            }
            other => panic!("a two-result constructor must be refused: {other:?}"),
        }
    }

    #[test]
    fn fail_closed_on_a_short_make_aggregate_stored_to_memory() {
        // A constructor naming fewer lanes than its type has is not a complete
        // aggregate; the slice refuses it rather than store an unset field.
        let tup = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let body = vec![
            InstrNode::new(Inst::MakeAggregate {
                ty: tup.clone(),
                variant: None,
                fields: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Alloca { ty: tup.clone(), count: None, align: None })
                .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Store {
                ty: tup,
                ptr: ValueId::new(5),
                value: ValueId::new(4),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
        ];
        let module = module_with_body("agg_make_short", vec![Ty::I32], body);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedAggregate { .. })
        ));
    }

    /// `%in = make_aggregate (i32,i32) [p0, p1]`, then `%out` built with `%in`
    /// as lane 0 (under the declared type `out_ty`), one `extractfield i32 %out,
    /// 1` returned, and an unrelated `(i32,i32)` Alloca that keeps the
    /// aggregate-memory analysis (PASS 1.7) off its fast path. `%in` is 4 and
    /// `%out` is 5.
    fn nested_make_aggregate_module(name: &str, out_ty: Ty) -> Module {
        let pair = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let body = vec![
            InstrNode::new(Inst::MakeAggregate {
                ty: pair.clone(),
                variant: None,
                fields: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::MakeAggregate {
                ty: out_ty,
                variant: None,
                fields: vec![ValueId::new(4), ValueId::new(0)],
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Alloca { ty: pair, count: None, align: None })
                .with_result(ValueId::new(6)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: ValueId::new(5),
                field: 1,
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(7)] }),
        ];
        module_with_body(name, vec![Ty::I32], body)
    }

    #[test]
    fn fail_closed_on_a_nested_make_aggregate_by_its_non_scalar_field_type() {
        // A well-typed nested constructor: `%out = make_aggregate ((i32,i32),i32)
        // [%in, p0]`. PASS 1.7's MakeAggregate arm checks every field TYPE before
        // it looks at the lanes, and field 0 is a tuple, so the scalar-layout
        // check refuses it. The arm's later "is a lane of MakeAggregate" check
        // cannot fire on a well-typed constructor: every value PASS 1.7 tracks is
        // aggregate-typed, so a tracked lane always sits in an aggregate-typed
        // field, which this check has already refused. That later check is
        // defence in depth for an ill-typed constructor (the next test).
        let module = nested_make_aggregate_module(
            "agg_make_nested",
            Ty::Tuple(vec![Ty::Tuple(vec![Ty::I32, Ty::I32]), Ty::I32]),
        );
        match lower_module_to_lir(&module, FuncId::new(0)) {
            Err(ModuleLirError::UnsupportedAggregate { detail, .. }) => assert_eq!(
                detail,
                "aggregate field type Tuple([I32, I32]) has no reproducible scalar C-layout in \
                 the i8..i64/Bool aggregate-memory slice"
            ),
            other => panic!("a constructor with a tuple-typed field must be refused: {other:?}"),
        }
    }

    #[test]
    fn fail_closed_on_a_tracked_aggregate_as_a_make_aggregate_lane() {
        // An ill-typed constructor: `%out = make_aggregate (i32,i32) [%in, p0]`
        // declares two i32 fields but names the tracked aggregate `%in` as lane 0.
        // The field types are scalar, so only the arm's lane check can refuse it;
        // without that check the arm would record the aggregate `%in` as
        // `%out`'s field-0 value.
        let module =
            nested_make_aggregate_module("agg_make_confused", Ty::Tuple(vec![Ty::I32, Ty::I32]));
        match lower_module_to_lir(&module, FuncId::new(0)) {
            Err(ModuleLirError::UnsupportedAggregate { detail, .. }) => assert_eq!(
                detail,
                "tracked aggregate value 4 is a lane of MakeAggregate (a nested aggregate is out \
                 of the slice)"
            ),
            other => panic!("a tracked aggregate as a scalar lane must be refused: {other:?}"),
        }
    }

    #[test]
    fn admits_make_aggregate_struct_round_trip_at_mixed_field_offsets_and_widths() {
        // A `Ty::Struct { a: u8, b: i32 }` built by ONE `MakeAggregate`, stored
        // whole, loaded whole and read back field by field; the body returns
        // `s.b - zext(s.a)`. The natural C layout puts `a` at offset 0 and `b` at
        // offset 4 in an 8-byte, 4-aligned slot. The fields differ in width, so
        // this pins which lane each per-field Store writes, at which offset and
        // at which width: a lowering that swapped the two lanes would store the
        // i32 parameter with a 1-byte Store at offset 0.
        let sid = trust_ir::value::StructId::new(0);
        let sty = Ty::Struct(sid);
        let mut module = Module::new("t");
        module.structs.push(trust_ir::StructDef {
            id: sid,
            name: "P".to_string(),
            fields: vec![
                trust_ir::ty::FieldDef { name: "a".to_string(), ty: Ty::U8, offset: None },
                trust_ir::ty::FieldDef { name: "b".to_string(), ty: Ty::I32, offset: None },
            ],
            size: None,
            align: None,
            repr: trust_ir::ty::StructRepr::Rust,
            origin: None,
        });
        module.func_types.push(FuncTy {
            params: vec![Ty::U8, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        });
        let mut f =
            IrFunction::new(FuncId::new(0), "agg_make_struct", FuncTyId::new(0), BlockId::new(0));
        let mut b0 = Block::new(BlockId::new(0));
        b0.params.push((ValueId::new(0), Ty::U8));
        b0.params.push((ValueId::new(1), Ty::I32));
        b0.body = vec![
            InstrNode::new(Inst::MakeAggregate {
                ty: sty.clone(),
                variant: None,
                fields: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Alloca { ty: sty.clone(), count: None, align: None })
                .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Store {
                ty: sty.clone(),
                ptr: ValueId::new(3),
                value: ValueId::new(2),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Load {
                ty: sty,
                ptr: ValueId::new(3),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::ExtractField { ty: Ty::U8, aggregate: ValueId::new(4), field: 0 })
                .with_result(ValueId::new(5)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: ValueId::new(4),
                field: 1,
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U8,
                dst_ty: Ty::I32,
                operand: ValueId::new(5),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I32,
                lhs: ValueId::new(6),
                rhs: ValueId::new(7),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(8)] }),
        ];
        f.blocks.push(b0);
        module.functions.push(f);

        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("a MakeAggregate-built {u8, i32} struct round trip must lower");
        assert_eq!(lir.stack_slots.len(), 1, "one aggregate slot");
        assert_eq!(lir.stack_slots[0].size, 8, "{{u8, i32}}: u8 @0, pad, i32 @4 -> 8 bytes");
        assert_eq!(lir.stack_slots[0].align, 4, "{{u8, i32}} aligns to its i32 field");

        let insts: Vec<&Instruction> = lir.blocks.values().flat_map(|b| &b.instructions).collect();
        let def = |value: Value| {
            insts
                .iter()
                .find(|i| i.results.contains(&value))
                .unwrap_or_else(|| panic!("{value:?} has no defining instruction"))
        };
        // A field address is the slot's `StackAddr` (offset 0) or
        // `ArrayGep<i8>(StackAddr, Iconst offset)`.
        let offset_of = |addr: Value| -> i64 {
            let addr_def = def(addr);
            match &addr_def.opcode {
                Opcode::StackAddr { .. } => 0,
                Opcode::ArrayGep { elem_ty: LirType::I8 } => {
                    assert!(
                        matches!(def(addr_def.args[0]).opcode, Opcode::StackAddr { .. }),
                        "the field address is based on the slot"
                    );
                    match &def(addr_def.args[1]).opcode {
                        Opcode::Iconst { imm, .. } => *imm,
                        other => panic!("field offset is not a constant: {other:?}"),
                    }
                }
                other => panic!("unexpected field address {other:?}"),
            }
        };
        let stores: Vec<(Value, i64, LirType)> = insts
            .iter()
            .filter_map(|i| match &i.opcode {
                Opcode::Store { ty, .. } => Some((i.args[0], offset_of(i.args[1]), ty.clone())),
                _ => None,
            })
            .collect();
        // Entry params are `Value(0)` (the u8) and `Value(1)` (the i32).
        assert_eq!(
            stores,
            vec![(Value(0), 0, LirType::I8), (Value(1), 4, LirType::I32)],
            "lane 0 (u8) is stored 1 byte wide at offset 0, lane 1 (i32) 4 bytes wide at offset 4"
        );
        let loads: Vec<(i64, LirType)> = insts
            .iter()
            .filter_map(|i| match &i.opcode {
                Opcode::Load { ty, .. } => Some((offset_of(i.args[0]), ty.clone())),
                _ => None,
            })
            .collect();
        assert_eq!(
            loads,
            vec![(0, LirType::I8), (4, LirType::I32)],
            "each field is loaded back at its own offset and width"
        );
    }

    #[test]
    fn admits_3field_aggregate_alloca_layout() {
        // GENERALIZED (N-field slice): a 3-field scalar aggregate is now IN the
        // aggregate-memory slice. Its C-layout is reproduced 1:1 (three i32 fields
        // -> size 12, align 4), byte-for-byte the interpreter's `aggregate_layout`
        // for this module, which declares no `tuple_layouts` descriptor.
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

    /// Trust: the `caller_calls_add_module` pair with the CALLEE's producer
    /// chosen by the test — `TRust` is the control, `Clean` the subject. The
    /// bodies are byte-identical, so any difference in outcome is the producer
    /// gate and nothing else.
    fn caller_calls_leaf_with_producer(producer: trust_ir::Producer) -> Module {
        let mut module = Module::new("clean_gate");
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        });
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        });
        let mut add = IrFunction::new(FuncId::new(1), "add", FuncTyId::new(1), BlockId::new(0))
            .with_producer(producer);
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

        let mut caller =
            IrFunction::new(FuncId::new(0), "caller", FuncTyId::new(0), BlockId::new(0))
                .with_producer(trust_ir::Producer::TRust);
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

    /// Trust: a `Producer::Clean` body is refused by the producer gate BEFORE
    /// any shape question is asked; the identical body under `TRust` lowers.
    #[test]
    fn clean_origin_leaf_is_refused_by_the_producer_gate() {
        let subject = caller_calls_leaf_with_producer(trust_ir::Producer::Clean);
        let err = lower_module_to_lir(&subject, FuncId::new(1))
            .expect_err("a Clean-producer body must never lower to LIR");
        match err {
            ModuleLirError::CleanOriginBelowCodegenGate { name, detail } => {
                assert_eq!(name, "add");
                assert!(detail.contains("function being lowered"), "{detail}");
            }
            other => panic!("wrong refusal: {other}"),
        }
        let control = caller_calls_leaf_with_producer(trust_ir::Producer::TRust);
        lower_module_to_lir(&control, FuncId::new(1)).expect("control: the TRust leaf lowers");
    }

    /// Trust: the inliner never splices a `Producer::Clean` callee into a Rust
    /// caller's object. Control first: the TRust leaf IS inlined (no `Call`
    /// survives), which is exactly the path the Clean subject is denied.
    #[test]
    fn clean_origin_callee_is_never_inlined_into_a_rust_caller() {
        let control = caller_calls_leaf_with_producer(trust_ir::Producer::TRust);
        let lir = lower_module_to_lir(&control, FuncId::new(0))
            .expect("control: the TRust pure leaf inlines into the caller");
        assert!(
            lir.blocks
                .values()
                .flat_map(|b| b.instructions.iter())
                .all(|i| !matches!(i.opcode, Opcode::Call { .. })),
            "control must inline (no Call left)"
        );

        let subject = caller_calls_leaf_with_producer(trust_ir::Producer::Clean);
        let err = lower_module_to_lir(&subject, FuncId::new(0))
            .expect_err("a Rust caller reaching a Clean callee must refuse, not splice");
        match err {
            ModuleLirError::CleanOriginBelowCodegenGate { name, detail } => {
                assert_eq!(name, "add");
                assert!(detail.contains("callee of `caller`"), "{detail}");
            }
            other => panic!("wrong refusal: {other}"),
        }
    }

    /// Trust: the real-call lane refuses too — a Clean callee is neither
    /// inlined nor deferred to a `Bl` edge the gate would then compose.
    #[test]
    fn clean_origin_callee_is_never_deferred_to_a_real_call() {
        let control = caller_calls_leaf_with_producer(trust_ir::Producer::TRust);
        let caller = control.function_by_id(FuncId::new(0)).expect("caller");
        let lir = lower_trust_ir_function_to_lir_real_calls(&control, caller)
            .expect("control: the TRust leaf is deferred to a real Call");
        assert!(
            lir.blocks
                .values()
                .flat_map(|b| b.instructions.iter())
                .any(|i| matches!(i.opcode, Opcode::Call { .. })),
            "control must carry a real Call edge"
        );

        let subject = caller_calls_leaf_with_producer(trust_ir::Producer::Clean);
        let caller = subject.function_by_id(FuncId::new(0)).expect("caller");
        assert!(matches!(
            lower_trust_ir_function_to_lir_real_calls(&subject, caller),
            Err(ModuleLirError::CleanOriginBelowCodegenGate { .. })
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
            abi: None,
        });
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
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

    // ── Plan §5 fail-open item 1: an implicit panic is refused BY NAME ──────

    fn assert_implicit_panic_refusal(result: Result<LirFunction, ModuleLirError>, detail: &str) {
        match result {
            Err(e @ ModuleLirError::ImplicitPanicUnfaithful { .. }) => {
                let ModuleLirError::ImplicitPanicUnfaithful { detail: got, .. } = &e else {
                    unreachable!()
                };
                assert!(got.contains(detail), "detail `{got}` must name `{detail}`");
                let text = e.to_string();
                assert!(text.contains("[implicit-panic-unfaithful]"), "{text}");
                assert!(text.contains("-Coverflow-checks=off"), "{text}");
                assert_eq!(e.class_name(), "ImplicitPanicUnfaithful");
            }
            other => panic!("expected ImplicitPanicUnfaithful, got {other:?}"),
        }
    }

    /// REGRESSION (R-8 audit finding 1): the guarded checked add — exactly the
    /// shape the THIR producer emits for `a + b` under debug overflow checks —
    /// used to lower to `Brif(ok, cont, trap)` + a shared `Trap` (a bare `brk`,
    /// SIGTRAP, no panic message or hook). Every entry point refuses it now.
    #[test]
    fn guarded_checked_add_is_refused_as_an_unfaithful_implicit_panic() {
        for ty in [Ty::I32, Ty::I64, Ty::U32] {
            let mut module = module_with_body(
                "cadd_guarded",
                vec![ty.clone()],
                checked_add_assert_body(OverflowOp::AddOverflow, ty.clone()),
            );
            module.func_types[0].params = vec![ty.clone(), ty.clone()];
            module.functions[0].blocks[0].params =
                vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())];
            let f = &module.functions[0];
            let token = AbiPassModeCrossCheck::attested_by("test");
            assert_implicit_panic_refusal(lower_module_to_lir(&module, FuncId::new(0)), "own body");
            assert_implicit_panic_refusal(
                lower_module_to_lir_with_abi_cross_check(&module, FuncId::new(0), &token),
                "own body",
            );
            assert_implicit_panic_refusal(lower_trust_ir_function_to_lir(&module, f), "own body");
            assert_implicit_panic_refusal(
                lower_trust_ir_function_to_lir_real_calls(&module, f),
                "own body",
            );
            assert_implicit_panic_refusal(
                lower_trust_ir_function_to_lir_real_calls_with_abi_cross_check(&module, f, &token),
                "own body",
            );
        }
    }

    /// NEGATIVE TWIN: the same nodes minus the `Assert` lower, and the LIR
    /// carries no `Trap` at all — the refusal is about the guard, not about
    /// the checked arithmetic around it.
    #[test]
    fn the_same_idiom_without_its_assert_lowers_with_no_trap() {
        let guarded = checked_add_assert_body(OverflowOp::AddOverflow, Ty::I32);
        let unguarded = checked_add_idiom_body(OverflowOp::AddOverflow, Ty::I32);
        assert_eq!(unguarded.len() + 1, guarded.len(), "the twins differ by the Assert alone");
        let module = module_with_body("cadd_unguarded", vec![Ty::I32], unguarded);
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("unguarded idiom lowers");
        assert!(
            !lir.blocks
                .values()
                .flat_map(|b| &b.instructions)
                .any(|i| matches!(i.opcode, Opcode::Trap)),
            "an Assert-free body must not carry a Trap"
        );
    }

    /// REGRESSION: the inline pre-pass admits `Assert` in a spliced callee, so
    /// a caller with no `Assert` of its own would have shipped the callee's
    /// trap. It is refused after the splice.
    #[test]
    fn an_assert_reached_only_through_an_inlined_callee_is_refused() {
        let mut module = caller_calls_add_module();
        let add = module.functions.iter_mut().find(|f| f.name == "add").expect("callee");
        let body = &mut add.blocks[0].body;
        // add(x, y) = x + y, guarded: `%13 = icmp ne %12, %10 ; assert %13`
        // (any bool condition: the refusal is syntactic).
        body.insert(
            1,
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: ValueId::new(12),
                rhs: ValueId::new(10),
            })
            .with_result(ValueId::new(13)),
        );
        body.insert(
            2,
            InstrNode::new(Inst::Assert {
                cond: ValueId::new(13),
                kind: trust_ir::AssertKind::Unspecified,
                site: None,
            }),
        );
        let caller = module.function_by_id(FuncId::new(0)).expect("caller");
        assert!(!function_has_unfaithful_assert(caller), "the caller itself is Assert-free");
        assert_implicit_panic_refusal(lower_module_to_lir(&module, FuncId::new(0)), "callee");
        // ...and the callee, lowered on its own, is refused for its own body.
        assert_implicit_panic_refusal(lower_module_to_lir(&module, FuncId::new(1)), "own body");
    }

    /// The predicate is syntactic: an `Assert` in a block no edge reaches is
    /// still found, and still refused (fail-closed; reachability is not this
    /// converter's to argue).
    #[test]
    fn an_assert_in_an_unreachable_block_is_still_refused() {
        let mut module = module_with_body(
            "dead_assert",
            vec![Ty::I32],
            vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] })],
        );
        let mut dead = Block::new(BlockId::new(7));
        dead.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(ValueId::new(5)),
        );
        dead.body.push(InstrNode::new(Inst::Assert {
            cond: ValueId::new(5),
            kind: trust_ir::AssertKind::Unspecified,
            site: None,
        }));
        dead.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        module.functions[0].blocks.push(dead);
        let site = unfaithful_assert_site(&module.functions[0]).expect("the dead Assert is found");
        assert_eq!((site.block, site.index), (BlockId::new(7), 1));
        assert_implicit_panic_refusal(
            lower_module_to_lir(&module, FuncId::new(0)),
            "block 7, node 1",
        );
    }

    /// Trust (trust-ir v54): an `AssertInvoke` is the same check as a sited `Assert` whose
    /// failure enters an in-frame landing pad, so the syntactic unfaithful-panic predicate finds
    /// it exactly as it finds an `Assert`.
    #[test]
    fn an_assert_invoke_is_an_unfaithful_assert_site() {
        let mut module = module_with_body(
            "assert_invoke",
            vec![Ty::I32],
            vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] })],
        );
        let mut checked = Block::new(BlockId::new(3));
        checked.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(ValueId::new(5)),
        );
        checked.body.push(InstrNode::new(Inst::AssertInvoke {
            cond: ValueId::new(5),
            kind: trust_ir::AssertKind::DivByZero,
            site: trust_ir::PanicSite {
                entry: FuncId::new(0),
                location: trust_ir::PanicLocation::Value(ValueId::new(0)),
            },
            normal_dest: BlockId::new(0),
            normal_args: vec![],
            unwind_dest: BlockId::new(0),
        }));
        module.functions[0].blocks.push(checked);
        let site = unfaithful_assert_site(&module.functions[0]).expect("the AssertInvoke is found");
        assert_eq!((site.block, site.index), (BlockId::new(3), 1));
    }

    /// Trust (trust-ir v52/v54): the splicers admit a SITELESS assert, whatever its kind, and
    /// never a sited one (its failure calls the site's entry, which a trap is not); a kind's
    /// operands and a site's run-time location count as reads in the fresh-id scan.
    #[test]
    fn a_sited_assert_is_not_inlinable_and_its_operands_are_reads() {
        let kinded = Inst::Assert {
            cond: ValueId::new(1),
            kind: trust_ir::AssertKind::BoundsCheck {
                index: ValueId::new(2),
                len: ValueId::new(3),
            },
            site: None,
        };
        assert!(is_multiblock_inlinable_value(&kinded));
        assert_eq!(
            inst_value_operands(&kinded),
            vec![ValueId::new(1), ValueId::new(2), ValueId::new(3)]
        );
        let sited = Inst::Assert {
            cond: ValueId::new(1),
            kind: trust_ir::AssertKind::Unspecified,
            site: Some(trust_ir::PanicSite {
                entry: FuncId::new(0),
                location: trust_ir::PanicLocation::Value(ValueId::new(4)),
            }),
        };
        assert!(!is_multiblock_inlinable_value(&sited));
        assert!(inst_value_operands(&sited).contains(&ValueId::new(4)));
    }

    #[test]
    fn unbound_box_operand_at_max_id_refuses_before_call_preprocessing_can_wrap() {
        use trust_ir::box_validity::{
            BoxDerefSite, BoxFactSession, BoxPointee, BoxValidityFact, PremiseRoot,
        };
        let mut module = caller_calls_add_module();
        module.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::BoxDeref {
                ptr_ty: Ty::Ptr,
                pointee: BoxPointee::Sized { ty: Ty::I32 },
                operand: ValueId::new(u32::MAX),
                fact: Box::new(BoxValidityFact::premise(
                    BoxDerefSite { item: [8; 16], ordinal: 0 },
                    BoxFactSession::PROOF_SNAPSHOT,
                    PremiseRoot::ParamByValue,
                )),
            })
            .with_result(ValueId::new(5)),
        );
        // Intentionally malformed unbound input: it must produce a structured
        // refusal, never panic or wrap before the ordinary BoxDeref barrier.
        let error = lower_module_to_lir(&module, FuncId::new(0))
            .expect_err("the unbound maximum operand must refuse before allocation");
        assert!(matches!(&error, ModuleLirError::FreshIdExhausted { space: "value", .. }));
        assert_eq!(error.class_name(), "FreshIdExhausted");
    }

    #[test]
    fn inliner_value_reservations_refuse_exhaustion_and_preserve_sparse_id_control() {
        for (highest, exhausted) in [(u32::MAX - 2, true), (u32::MAX - 3, false)] {
            let mut module = caller_calls_add_module();
            let result = ValueId::new(highest);
            module.functions[0].blocks[0].body = vec![
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![ValueId::new(0), ValueId::new(1)],
                })
                .with_result(result),
                InstrNode::new(Inst::Return { values: vec![result] }),
            ];
            // Two genuine pure-leaf results require two fresh IDs. At MAX-2
            // the first reservation succeeds and the second must refuse.
            module.functions[1].blocks[0].body.insert(
                0,
                InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(1) })
                    .with_result(ValueId::new(13)),
            );
            let lowered = lower_module_to_lir(&module, FuncId::new(0));
            if exhausted {
                assert!(matches!(
                    lowered,
                    Err(ModuleLirError::FreshIdExhausted { space: "value", .. })
                ));
            } else {
                assert!(lowered.is_ok(), "two available fresh IDs must still lower: {lowered:?}");
            }
        }
    }

    #[test]
    fn recursive_flattening_preserves_typed_id_exhaustion() {
        let mut module = caller_calls_add_module();
        let mut leaf = module.functions[1].clone();
        leaf.id = FuncId::new(2);
        leaf.name = "deep_add".into();
        leaf.blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(1) })
                .with_result(ValueId::new(13)),
        );
        let result = ValueId::new(u32::MAX - 2);
        module.functions[1].blocks[0].body = vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(2),
                args: vec![ValueId::new(10), ValueId::new(11)],
            })
            .with_result(result),
            InstrNode::new(Inst::Return { values: vec![result] }),
        ];
        module.functions.push(leaf);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::FreshIdExhausted { space: "value", .. })
        ));
    }

    #[test]
    fn maximum_source_block_id_refuses_in_call_preprocessing() {
        let mut module = caller_calls_add_module();
        module.functions[0].entry = BlockId::new(u32::MAX);
        module.functions[0].blocks[0].id = BlockId::new(u32::MAX);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::FreshIdExhausted { space: "block", .. })
        ));
    }

    #[test]
    fn multiblock_inline_reservations_refuse_exhaustion_and_keep_the_control() {
        for (highest, exhausted) in [(u32::MAX - 2, true), (u32::MAX - 4, false)] {
            let mut module = caller_calls_add_module();
            module.functions[0].entry = BlockId::new(highest);
            module.functions[0].blocks[0].id = BlockId::new(highest);
            // A real two-block pure callee needs the continuation and both
            // cloned block IDs; entry args flow into the exit's actual param.
            module.functions[1].blocks[0].body = vec![InstrNode::new(Inst::Br {
                target: BlockId::new(1),
                args: vec![ValueId::new(10)],
            })];
            let mut exit = Block::new(BlockId::new(1));
            exit.params.push((ValueId::new(12), Ty::I32));
            exit.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(12)] }));
            module.functions[1].blocks.push(exit);
            let lowered = lower_module_to_lir(&module, FuncId::new(0));
            if exhausted {
                assert!(matches!(
                    lowered,
                    Err(ModuleLirError::FreshIdExhausted { space: "block", .. })
                ));
            } else {
                assert!(
                    lowered.is_ok(),
                    "three available fresh blocks must still lower: {lowered:?}"
                );
            }
        }
    }

    #[test]
    fn edge_split_block_reservations_refuse_without_an_inlining_call() {
        for (highest, exhausted) in [(u32::MAX - 1, true), (u32::MAX - 4, false)] {
            let mut module = module_with_body("edge_ids", vec![Ty::I32], Vec::new());
            module.functions[0].entry = BlockId::new(highest);
            let entry = &mut module.functions[0].blocks[0];
            entry.id = BlockId::new(highest);
            entry.body = vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I32,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(0),
                    then_args: vec![ValueId::new(0)],
                    else_target: BlockId::new(1),
                    else_args: vec![ValueId::new(1)],
                }),
            ];
            for (id, value) in [(0, 3), (1, 4)] {
                let mut exit = Block::new(BlockId::new(id));
                exit.params.push((ValueId::new(value), Ty::I32));
                exit.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(value)] }));
                module.functions[0].blocks.push(exit);
            }
            let lowered = lower_module_to_lir(&module, FuncId::new(0));
            if exhausted {
                assert!(matches!(
                    lowered,
                    Err(ModuleLirError::FreshIdExhausted { space: "block", .. })
                ));
            } else {
                assert!(lowered.is_ok(), "two available edge blocks must still lower: {lowered:?}");
            }
        }
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

    /// The trust-ratio `span_width` shape: `caller(lo,hi) = f2(f1(lo,hi), hi)`.
    /// The direct THIR producer emits BOTH calls in ONE caller block, and both
    /// callees are MULTI-BLOCK diamonds, so the first splice leaves the second
    /// call sitting in the freshly created continuation block — only the
    /// fixpoint driver re-running the pass reaches it.
    fn two_calls_one_block_module() -> Module {
        let mut module = Module::new("fix");
        // ty 0: (i32,i32)->i32 for all three functions.
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        });

        // A 4-block diamond callee: f(a,b) = if a <op> b { a } else { b }.
        let diamond = |id: u32, name: &str, op: ICmpOp| {
            let mut f = IrFunction::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
            let a = ValueId::new(20);
            let b = ValueId::new(21);
            let c = ValueId::new(22);
            let p = ValueId::new(23);
            let mut b0 = Block::new(BlockId::new(0));
            b0.params.push((a, Ty::I32));
            b0.params.push((b, Ty::I32));
            b0.body.push(
                InstrNode::new(Inst::ICmp { op, ty: Ty::I32, lhs: a, rhs: b }).with_result(c),
            );
            b0.body.push(InstrNode::new(Inst::CondBr {
                cond: c,
                then_target: BlockId::new(1),
                then_args: vec![],
                else_target: BlockId::new(2),
                else_args: vec![],
            }));
            let mut b1 = Block::new(BlockId::new(1));
            b1.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![a] }));
            let mut b2 = Block::new(BlockId::new(2));
            b2.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![b] }));
            let mut b3 = Block::new(BlockId::new(3));
            b3.params.push((p, Ty::I32));
            b3.body.push(InstrNode::new(Inst::Return { values: vec![p] }));
            f.blocks.extend([b0, b1, b2, b3]);
            f
        };

        // caller(lo,hi): %2 = call f1(lo,hi); %3 = call f2(%2,hi); ret %3 —
        // TWO calls in ONE block.
        let mut caller =
            IrFunction::new(FuncId::new(0), "caller", FuncTyId::new(0), BlockId::new(0));
        let lo = ValueId::new(0);
        let hi = ValueId::new(1);
        let r1 = ValueId::new(2);
        let r2 = ValueId::new(3);
        let mut cb = Block::new(BlockId::new(0));
        cb.params.push((lo, Ty::I32));
        cb.params.push((hi, Ty::I32));
        cb.body.push(
            InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![lo, hi] })
                .with_result(r1),
        );
        cb.body.push(
            InstrNode::new(Inst::Call { callee: FuncId::new(2), args: vec![r1, hi] })
                .with_result(r2),
        );
        cb.body.push(InstrNode::new(Inst::Return { values: vec![r2] }));
        caller.blocks.push(cb);

        module.functions.push(caller);
        module.functions.push(diamond(1, "rawish", ICmpOp::Ult));
        module.functions.push(diamond(2, "clampish", ICmpOp::Ugt));
        module
    }

    #[test]
    fn fixpoint_inlines_two_calls_in_one_block() {
        let module = two_calls_one_block_module();
        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("both nested calls inline via the fixpoint");
        for (id, block) in &lir.blocks {
            for inst in &block.instructions {
                assert!(
                    !matches!(inst.opcode, Opcode::Call { .. } | Opcode::CallIndirect),
                    "a call opcode survived fixpoint inlining in {id:?}: {:?}",
                    inst.opcode
                );
            }
        }
    }

    #[test]
    fn inlines_callee_with_unop() {
        // The trust-align `raw_up_from_mask` blocker: a local pure leaf whose
        // body carries a bare `UnOp` (`not`). UnOp is converter-supported, so
        // excluding it from the inlinable sets was a pure omission — pin both
        // the single-block path (all-single-result body) and, via the caller's
        // second call, the multiblock path (diamond containing the UnOp).
        let mut module = two_calls_one_block_module();
        // Rewrite callee 1 (single-block admissible shape): mask(a,b) = !a & b.
        {
            let f = module.function_by_id_mut(FuncId::new(1)).expect("callee 1");
            let a = ValueId::new(20);
            let b = ValueId::new(21);
            let n = ValueId::new(22);
            let r = ValueId::new(23);
            let mut b0 = Block::new(BlockId::new(0));
            b0.params.push((a, Ty::I32));
            b0.params.push((b, Ty::I32));
            b0.body.push(
                InstrNode::new(Inst::UnOp { op: UnOp::Not, ty: Ty::I32, operand: a })
                    .with_result(n),
            );
            b0.body.push(
                InstrNode::new(Inst::BinOp { op: BinOp::And, ty: Ty::I32, lhs: n, rhs: b })
                    .with_result(r),
            );
            b0.body.push(InstrNode::new(Inst::Return { values: vec![r] }));
            f.blocks = vec![b0];
        }
        // Inject a UnOp into callee 2's diamond (multiblock path).
        {
            let f = module.function_by_id_mut(FuncId::new(2)).expect("callee 2");
            let a = f.blocks[0].params[0].0;
            let inv = ValueId::new(30);
            f.blocks[1].body.insert(
                0,
                InstrNode::new(Inst::UnOp { op: UnOp::Not, ty: Ty::I32, operand: a })
                    .with_result(inv),
            );
            let Inst::Br { args, .. } = &mut f.blocks[1].body.last_mut().unwrap().inst else {
                unreachable!("diamond then-arm ends in Br");
            };
            args[0] = inv;
        }
        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("UnOp-bearing callees inline on both splice paths");
        for (id, block) in &lir.blocks {
            for inst in &block.instructions {
                assert!(
                    !matches!(inst.opcode, Opcode::Call { .. } | Opcode::CallIndirect),
                    "a call opcode survived UnOp inlining in {id:?}: {:?}",
                    inst.opcode
                );
            }
        }
    }

    /// caller -> mid -> leaf call chain: `mid` is a local NON-LEAF callee (its
    /// body calls `leaf`), so plain splice admission rejects it; the recursive
    /// flatten must first inline `leaf` into a copy of `mid` and then splice
    /// that call-free copy into `caller`.
    #[test]
    fn flattens_local_nonleaf_callee_chain() {
        let mut module = Module::new("chain");
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        });

        // leaf(x,y) = x + y  (FuncId 2).
        let mut leaf = IrFunction::new(FuncId::new(2), "leaf", FuncTyId::new(0), BlockId::new(0));
        {
            let x = ValueId::new(40);
            let y = ValueId::new(41);
            let s = ValueId::new(42);
            let mut b0 = Block::new(BlockId::new(0));
            b0.params.push((x, Ty::I32));
            b0.params.push((y, Ty::I32));
            b0.body.push(
                InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: x, rhs: y })
                    .with_result(s),
            );
            b0.body.push(InstrNode::new(Inst::Return { values: vec![s] }));
            leaf.blocks.push(b0);
        }

        // mid(a,b) = leaf(a,b) & b  (FuncId 1, NON-LEAF).
        let mut mid = IrFunction::new(FuncId::new(1), "mid", FuncTyId::new(0), BlockId::new(0));
        {
            let a = ValueId::new(20);
            let b = ValueId::new(21);
            let c = ValueId::new(22);
            let r = ValueId::new(23);
            let mut b0 = Block::new(BlockId::new(0));
            b0.params.push((a, Ty::I32));
            b0.params.push((b, Ty::I32));
            b0.body.push(
                InstrNode::new(Inst::Call { callee: FuncId::new(2), args: vec![a, b] })
                    .with_result(c),
            );
            b0.body.push(
                InstrNode::new(Inst::BinOp { op: BinOp::And, ty: Ty::I32, lhs: c, rhs: b })
                    .with_result(r),
            );
            b0.body.push(InstrNode::new(Inst::Return { values: vec![r] }));
            mid.blocks.push(b0);
        }

        // caller(a,b) = mid(a,b)  (FuncId 0).
        let mut caller =
            IrFunction::new(FuncId::new(0), "caller", FuncTyId::new(0), BlockId::new(0));
        {
            let a = ValueId::new(0);
            let b = ValueId::new(1);
            let r = ValueId::new(2);
            let mut b0 = Block::new(BlockId::new(0));
            b0.params.push((a, Ty::I32));
            b0.params.push((b, Ty::I32));
            b0.body.push(
                InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![a, b] })
                    .with_result(r),
            );
            b0.body.push(InstrNode::new(Inst::Return { values: vec![r] }));
            caller.blocks.push(b0);
        }

        module.functions.push(caller);
        module.functions.push(mid);
        module.functions.push(leaf);

        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("non-leaf callee flattens recursively and splices");
        for (id, block) in &lir.blocks {
            for inst in &block.instructions {
                assert!(
                    !matches!(inst.opcode, Opcode::Call { .. } | Opcode::CallIndirect),
                    "a call opcode survived recursive flattening in {id:?}: {:?}",
                    inst.opcode
                );
            }
        }
    }

    /// Mutual recursion (f -> g -> f) must neither hang the flatten nor be
    /// mis-inlined: the flatten stack breaks the cycle and the converter
    /// fail-closes on the surviving call.
    #[test]
    fn mutual_recursion_fail_closes_without_hanging() {
        let mut module = Module::new("mutrec");
        module.func_types.push(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        });
        for (id, other, name) in [(0u32, 1u32, "f"), (1, 0, "g")] {
            let mut f = IrFunction::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
            let a = ValueId::new(0);
            let b = ValueId::new(1);
            let r = ValueId::new(2);
            let mut b0 = Block::new(BlockId::new(0));
            b0.params.push((a, Ty::I32));
            b0.params.push((b, Ty::I32));
            b0.body.push(
                InstrNode::new(Inst::Call { callee: FuncId::new(other), args: vec![a, b] })
                    .with_result(r),
            );
            b0.body.push(InstrNode::new(Inst::Return { values: vec![r] }));
            f.blocks.push(b0);
            module.functions.push(f);
        }
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedInst { inst: "Call", .. })
        ));
    }

    /// A UNIT (`()`) formal occupies NO LIR parameter slot — the captureless
    /// closure's `bb0(%0: ())` environment formal, measured in trust-ts-strip's
    /// `lexer::lex::{closure#0}` family. The unit ValueId stays UNBOUND, so a
    /// body that actually READS the unit value fails closed as undefined.
    /// `fn requested(p: &S) -> usize` over a struct with a RUSTC-RECORDED
    /// layout — the measured `EntropyError::requested` shape: a
    /// WHOLE-AGGREGATE load through an incoming `Ty::Ptr` param (a read-only
    /// root), then a field extract. Lowers to per-field Ldr at the RECORDED
    /// `ptr + offset` (repr(Rust) reorders, so a canonical guess would read
    /// the wrong bytes — the recorded offsets deliberately swap the fields
    /// here to prove the recorded ones are used); a STORE through the same
    /// root stays fail-closed, and so is a Tuple-typed incoming load (no
    /// recorded offsets exist for tuples).
    #[test]
    fn incoming_ptr_aggregate_load_decomposes_per_field() {
        let agg_ty = Ty::Struct(trust_ir::value::StructId::new(0));
        let build = |store_back: bool| {
            let mut module = Module::new("t");
            module.structs.push(trust_ir::StructDef {
                id: trust_ir::value::StructId::new(0),
                name: "S".to_string(),
                fields: vec![
                    trust_ir::ty::FieldDef {
                        name: "requested".to_string(),
                        ty: Ty::Usize,
                        // rustc put the u32 FIRST: usize lives at offset 8.
                        offset: Some(8),
                    },
                    trust_ir::ty::FieldDef {
                        name: "kind".to_string(),
                        ty: Ty::U32,
                        offset: Some(0),
                    },
                ],
                size: Some(16),
                align: Some(8),
                repr: Default::default(),
                origin: None,
            });
            module.func_types.push(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::Usize],
                is_vararg: false,
                abi: None,
            });
            let mut f = IrFunction::new(FuncId::new(0), "r", FuncTyId::new(0), BlockId::new(0));
            let mut b0 = Block::new(BlockId::new(0));
            b0.params.push((ValueId::new(0), Ty::Ptr));
            b0.body.push(
                InstrNode::new(Inst::Load {
                    ty: agg_ty.clone(),
                    ptr: ValueId::new(0),
                    volatile: false,
                    align: None,
                })
                .with_result(ValueId::new(1)),
            );
            if store_back {
                b0.body.push(InstrNode::new(Inst::Store {
                    ty: agg_ty.clone(),
                    ptr: ValueId::new(0),
                    value: ValueId::new(1),
                    volatile: false,
                    align: None,
                }));
            }
            b0.body.push(
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::Usize,
                    aggregate: ValueId::new(1),
                    field: 0,
                })
                .with_result(ValueId::new(2)),
            );
            b0.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }));
            f.blocks.push(b0);
            module.functions.push(f);
            module
        };

        let lir = lower_module_to_lir(&build(false), FuncId::new(0))
            .expect("incoming-root aggregate load must lower");
        let block = lir.blocks.get(&Block(0)).expect("entry");
        let loads =
            block.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Load { .. })).count();
        assert_eq!(loads, 2, "one Ldr per scalar field");
        assert!(
            block.instructions.iter().any(|i| matches!(i.opcode, Opcode::Copy)),
            "the field extract is a Copy of the loaded field"
        );

        // The RECORDED offsets are the ones used: the usize field was
        // recorded at offset 8, so exactly one address computation adds 8.
        let gep_offsets: Vec<i64> = block
            .instructions
            .iter()
            .filter_map(|i| match i.opcode {
                Opcode::Iconst { imm, .. } => Some(imm),
                _ => None,
            })
            .collect();
        assert!(
            gep_offsets.contains(&8),
            "the usize field loads at its RECORDED offset 8, got consts {gep_offsets:?}"
        );

        // Writing the aggregate back through the incoming pointer is refused:
        // the root is read-only and never a slot.
        assert!(lower_module_to_lir(&build(true), FuncId::new(0)).is_err());
    }

    /// Keep the unsupported aggregate-memory shape from the superseded DST
    /// read-lane proposal refused. The landed bridge's `address_of_dst_field`
    /// carries the incoming container length and advances its data address by
    /// the declared field offset; it does not load the tail as a fat-pointer cell.
    ///
    /// This fixture instead loads a struct containing a `FatPtr(Slice)` field
    /// through an incoming pointer. Interpreting an inline DST tail that way
    /// would read its content bytes as a (ptr, len) pair and fabricate metadata.
    /// `scalar_field_size_align` currently refuses fat fields in aggregate loads.
    /// Supporting actual in-memory fat-pointer fields in the future must keep
    /// them distinct from inline unsized tails; this test pins the present fence.
    #[test]
    fn incoming_ptr_aggregate_load_with_fat_field_is_refused() {
        let agg_ty = Ty::Struct(trust_ir::value::StructId::new(0));
        let mut module = Module::new("t");
        module.types.push(Ty::U8);
        let tail_ty = Ty::FatPtr(trust_ir::ty::FatPtrKind::Slice(trust_ir::value::TyId::new(0)));
        module.structs.push(trust_ir::StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "OsSlice".to_string(),
            fields: vec![trust_ir::ty::FieldDef {
                name: "inner".to_string(),
                ty: tail_ty.clone(),
                offset: Some(0),
            }],
            size: Some(16),
            align: Some(8),
            repr: Default::default(),
            origin: None,
        });
        // No fat RETURN (that is refused earlier, as `UnsupportedType { function
        // return }`); the value is extracted and dropped so the refusal under test
        // is the aggregate-memory slice's own.
        module.func_types.push(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "tail", FuncTyId::new(0), BlockId::new(0));
        let mut b0 = Block::new(BlockId::new(0));
        b0.params.push((ValueId::new(0), Ty::Ptr));
        b0.body.push(
            InstrNode::new(Inst::Load {
                ty: agg_ty.clone(),
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
        );
        b0.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: tail_ty.clone(),
                aggregate: ValueId::new(1),
                field: 0,
            })
            .with_result(ValueId::new(2)),
        );
        b0.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(b0);
        module.functions.push(f);

        let err = lower_module_to_lir(&module, FuncId::new(0))
            .expect_err("an incoming-root aggregate load with a FatPtr field must be refused");
        assert!(
            matches!(err, ModuleLirError::UnsupportedAggregate { .. }),
            "the refusal must be the aggregate-memory slice's own, got {err:?}"
        );
    }

    /// The PAIR-ENUM lane end to end, on the measured `Option<u64>` shape:
    /// `take(o: Option<u64>) -> u64` (pair param, tag switch via extract 0,
    /// payload extract 1) and `mk(x: u64) -> Option<u64>` (const-seed +
    /// insertfield construct, pair return). The enum def is the producer's
    /// exact spelling: `repr(u64) { None = 0, Some(u64) = 1 }` with a
    /// recorded Direct{0} descriptor.
    #[test]
    fn pair_enum_option_shapes_lower_as_register_pairs() {
        let option_def = || {
            let mut def = trust_ir::EnumDef::new(
                trust_ir::EnumId::new(0),
                "Option",
                vec![
                    trust_ir::EnumVariant {
                        name: "None".to_string(),
                        fields: vec![],
                        field_names: vec![],
                    },
                    trust_ir::EnumVariant {
                        name: "Some".to_string(),
                        fields: vec![Ty::U64],
                        field_names: vec![],
                    },
                ],
            );
            def.discriminants = vec![Some(0), Some(1)];
            def.repr = Some(EnumTagRepr::U64);
            def.layout = Some(trust_ir::EnumLayoutDescriptor {
                encoding: trust_ir::EnumTagEncoding::Direct { tag_offset: 0 },
                size: 16,
                align: 8,
                variant_field_offsets: vec![vec![], vec![8]],
            });
            def
        };
        let ety = Ty::Enum(trust_ir::EnumId::new(0));

        // mk(x) -> Option<u64>: const { 1, 0 }; insertfield 1, x; ret.
        let mut module = Module::new("t");
        module.enums.push(option_def());
        module.func_types.push(FuncTy {
            params: vec![Ty::U64],
            returns: vec![ety.clone()],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "mk", FuncTyId::new(0), BlockId::new(0));
        let mut b0 = Block::new(BlockId::new(0));
        b0.params.push((ValueId::new(0), Ty::U64));
        b0.body.push(
            InstrNode::new(Inst::Const {
                ty: ety.clone(),
                value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(0)]),
            })
            .with_result(ValueId::new(1)),
        );
        b0.body.push(
            InstrNode::new(Inst::InsertField {
                ty: ety.clone(),
                aggregate: ValueId::new(1),
                field: 1,
                value: ValueId::new(0),
            })
            .with_result(ValueId::new(2)),
        );
        b0.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }));
        f.blocks.push(b0);
        module.functions.push(f);
        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("the Option construct must lower as a register pair");
        assert_eq!(
            lir.signature.returns,
            vec![LirType::I64, LirType::I64],
            "the enum returns as (tag, payload)"
        );
        let block = lir.blocks.get(&Block(0)).expect("entry");
        let ret = block.instructions.last().expect("return");
        assert!(matches!(ret.opcode, Opcode::Return));
        assert_eq!(ret.args.len(), 2, "both lanes return");

        // take(o) -> u64: extract 0 (tag), switch, extract 1 (payload), join.
        let mut module = Module::new("t");
        module.enums.push(option_def());
        module.func_types.push(FuncTy {
            params: vec![ety.clone()],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "take", FuncTyId::new(0), BlockId::new(0));
        let mut b0 = Block::new(BlockId::new(0));
        b0.params.push((ValueId::new(0), ety.clone()));
        b0.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U64,
                aggregate: ValueId::new(0),
                field: 0,
            })
            .with_result(ValueId::new(2)),
        );
        b0.body.push(InstrNode::new(Inst::Switch {
            value: ValueId::new(2),
            default: BlockId::new(2),
            default_args: vec![],
            cases: vec![trust_ir::inst::SwitchCase {
                value: Constant::Int(1),
                target: BlockId::new(1),
                args: vec![],
            }],
            exhaustive_enum_unreachable: false,
        }));
        f.blocks.push(b0);
        let mut b1 = Block::new(BlockId::new(1));
        b1.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U64,
                aggregate: ValueId::new(0),
                field: 1,
            })
            .with_result(ValueId::new(3)),
        );
        b1.body.push(InstrNode::new(Inst::Br {
            target: BlockId::new(3),
            args: vec![ValueId::new(3)],
        }));
        f.blocks.push(b1);
        let mut b2 = Block::new(BlockId::new(2));
        b2.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(0) })
                .with_result(ValueId::new(4)),
        );
        b2.body.push(InstrNode::new(Inst::Br {
            target: BlockId::new(3),
            args: vec![ValueId::new(4)],
        }));
        f.blocks.push(b2);
        let mut b3 = Block::new(BlockId::new(3));
        b3.params.push((ValueId::new(1), Ty::U64));
        b3.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
        f.blocks.push(b3);
        module.functions.push(f);
        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("the Option match must lower from the register pair");
        assert_eq!(
            lir.signature.params,
            vec![LirType::I64, LirType::I64],
            "the enum formal splits into (tag, payload)"
        );
    }

    /// A BY-VALUE 2-scalar-field struct of 16 bytes or fewer rides rustc's
    /// PassMode::Pair: two register formals in LAYOUT order, with the
    /// declaration-order mapping absorbing a repr(Rust) reorder — the
    /// `Range<usize>` argument shape. Extracts are Copies of the mapped
    /// formal.
    #[test]
    fn by_value_pair_struct_param_maps_fields_to_register_formals() {
        // The recorded offsets REORDER the fields (decl 0 at offset 8): the
        // signature emits layout order, and extract-by-decl-index must still
        // reach the right formal.
        let mut module = Module::new("t");
        module.structs.push(trust_ir::StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "R".to_string(),
            fields: vec![
                trust_ir::ty::FieldDef {
                    name: "start".to_string(),
                    ty: Ty::Usize,
                    offset: Some(8),
                },
                trust_ir::ty::FieldDef { name: "end".to_string(), ty: Ty::Usize, offset: Some(0) },
            ],
            size: Some(16),
            align: Some(8),
            repr: Default::default(),
            origin: None,
        });
        let sty = Ty::Struct(trust_ir::value::StructId::new(0));
        module.func_types.push(FuncTy {
            params: vec![sty.clone()],
            returns: vec![Ty::Usize],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "r", FuncTyId::new(0), BlockId::new(0));
        let mut b0 = Block::new(BlockId::new(0));
        b0.params.push((ValueId::new(0), sty));
        // ret start - end  (uses BOTH fields so both Copies exist)
        b0.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Usize,
                aggregate: ValueId::new(0),
                field: 0,
            })
            .with_result(ValueId::new(1)),
        );
        b0.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Usize,
                aggregate: ValueId::new(0),
                field: 1,
            })
            .with_result(ValueId::new(2)),
        );
        b0.body.push(
            InstrNode::new(Inst::BinOp {
                op: trust_ir::inst::BinOp::Sub,
                ty: Ty::Usize,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
        );
        b0.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }));
        f.blocks.push(b0);
        module.functions.push(f);

        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("a 16-byte two-scalar struct formal must ride the register pair");
        assert_eq!(lir.signature.params, vec![LirType::I64, LirType::I64], "two register formals");
        let block = lir.blocks.get(&Block(0)).expect("entry");
        let copies: Vec<&Instruction> =
            block.instructions.iter().filter(|i| matches!(i.opcode, Opcode::Copy)).collect();
        assert_eq!(copies.len(), 2, "each field extract is a Copy of a formal");
        // Layout order put decl-field 1 ("end", offset 0) FIRST: the entry
        // block's params are [end, start], so decl-field 0's Copy must read
        // the SECOND formal.
        let entry_params: Vec<Value> = block.params.iter().map(|(v, _)| *v).collect();
        assert_eq!(entry_params.len(), 2);
        assert_eq!(
            copies[0].args[0], entry_params[1],
            "decl field 0 (offset 8) maps to the second (layout-later) formal"
        );
        assert_eq!(
            copies[1].args[0], entry_params[0],
            "decl field 1 (offset 0) maps to the first (layout-first) formal"
        );
    }

    /// A BY-VALUE struct larger than 16 bytes arrives INDIRECTLY (rustc's
    /// hidden pointer in one GPR): the formal binds one I64, and a field
    /// extract loads through it at the RECORDED offset — the measured
    /// `transform::is_kw(Token)` shape, minus Token's niche-encoded enum
    /// field (which stays refused with its own reason). A <=16-byte struct
    /// (Direct/Pair registers) refuses by name.
    #[test]
    fn by_value_indirect_struct_param_reads_fields_through_the_hidden_pointer() {
        let build = |size: u64| {
            let mut module = Module::new("t");
            module.structs.push(trust_ir::StructDef {
                id: trust_ir::value::StructId::new(0),
                name: "Token".to_string(),
                fields: vec![
                    trust_ir::ty::FieldDef {
                        name: "start".to_string(),
                        ty: Ty::Usize,
                        offset: Some(0),
                    },
                    trust_ir::ty::FieldDef {
                        name: "end".to_string(),
                        ty: Ty::Usize,
                        offset: Some(8),
                    },
                    trust_ir::ty::FieldDef {
                        name: "flag".to_string(),
                        ty: Ty::Bool,
                        offset: Some(16),
                    },
                ],
                size: Some(size),
                align: Some(8),
                repr: Default::default(),
                origin: None,
            });
            let sty = Ty::Struct(trust_ir::value::StructId::new(0));
            module.func_types.push(FuncTy {
                params: vec![sty.clone()],
                returns: vec![Ty::Usize],
                is_vararg: false,
                abi: None,
            });
            let mut f = IrFunction::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));
            let mut b0 = Block::new(BlockId::new(0));
            b0.params.push((ValueId::new(0), sty));
            b0.body.push(
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::Usize,
                    aggregate: ValueId::new(0),
                    field: 1,
                })
                .with_result(ValueId::new(1)),
            );
            b0.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
            f.blocks.push(b0);
            module.functions.push(f);
            module
        };

        let lir = lower_module_to_lir(&build(24), FuncId::new(0))
            .expect("a >16-byte recorded struct formal must ride the hidden pointer");
        assert_eq!(lir.signature.params, vec![LirType::I64], "the formal is ONE hidden pointer");
        let block = lir.blocks.get(&Block(0)).expect("entry");
        assert!(
            block.instructions.iter().any(|i| matches!(i.opcode, Opcode::Iconst { imm: 8, .. })),
            "field 1 loads at its recorded offset 8"
        );
        assert!(
            block.instructions.iter().any(|i| matches!(i.opcode, Opcode::Load { .. })),
            "the field read is a Load through the pointer"
        );

        // 16 bytes or fewer rides Direct/Pair registers — refused by name.
        assert!(matches!(
            lower_module_to_lir(&build(16), FuncId::new(0)),
            Err(ModuleLirError::UnsupportedSignature { .. })
        ));
    }

    /// A TUPLE-typed incoming aggregate load must refuse: tuples carry no
    /// recorded offsets and repr(Rust) reorders, so no sound layout exists.
    #[test]
    fn incoming_ptr_tuple_load_refuses_without_recorded_layout() {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Usize],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "r", FuncTyId::new(0), BlockId::new(0));
        let mut b0 = Block::new(BlockId::new(0));
        b0.params.push((ValueId::new(0), Ty::Ptr));
        b0.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::Tuple(vec![Ty::Usize, Ty::U32]),
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
        );
        b0.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Usize,
                aggregate: ValueId::new(1),
                field: 0,
            })
            .with_result(ValueId::new(2)),
        );
        b0.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }));
        f.blocks.push(b0);
        module.functions.push(f);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedAggregate { .. })
        ));
    }

    #[test]
    fn unit_param_occupies_no_lir_slot() {
        let build = |read_unit: bool| {
            let mut module = Module::new("t");
            module.func_types.push(FuncTy {
                params: vec![Ty::Unit, Ty::I32],
                returns: vec![Ty::I32],
                is_vararg: false,
                abi: None,
            });
            let mut f = IrFunction::new(FuncId::new(0), "c", FuncTyId::new(0), BlockId::new(0));
            let mut b0 = Block::new(BlockId::new(0));
            b0.params.push((ValueId::new(0), Ty::Unit));
            b0.params.push((ValueId::new(1), Ty::I32));
            let ret = if read_unit {
                // A (malformed) read of the unit value: pass it to Return.
                ValueId::new(0)
            } else {
                ValueId::new(1)
            };
            b0.body.push(InstrNode::new(Inst::Return { values: vec![ret] }));
            f.blocks.push(b0);
            module.functions.push(f);
            module
        };

        let lir = lower_module_to_lir(&build(false), FuncId::new(0))
            .expect("a unit formal must not refuse the function");
        assert_eq!(
            lir.signature.params,
            vec![LirType::I32],
            "the unit formal contracts away; only the scalar remains"
        );
        let entry = lir.blocks.get(&Block(0)).expect("entry block");
        assert_eq!(entry.params.len(), 1, "entry block params match the signature");

        // Reading the unbound unit value fails closed.
        assert!(lower_module_to_lir(&build(true), FuncId::new(0)).is_err());
    }

    /// The `&str` FORMAL lane: at the machine level a `&str` is `&[u8]` —
    /// the same (data, len) ScalarPair split, with BYTE loads through the
    /// data pointer. `fn f(s: &str) -> u64 { ptr_metadata }` must lower with
    /// the split; UTF-8 validity is a producer-side fact this lane never
    /// consults.
    #[test]
    fn str_param_splits_like_a_byte_slice() {
        use trust_ir::ty::FatPtrKind;
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![Ty::FatPtr(FatPtrKind::Str)],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "len", FuncTyId::new(0), BlockId::new(0));
        let mut b0 = Block::new(BlockId::new(0));
        b0.params.push((ValueId::new(0), Ty::FatPtr(FatPtrKind::Str)));
        b0.body.push(
            InstrNode::new(Inst::PtrMetadata {
                ptr_ty: Ty::FatPtr(FatPtrKind::Str),
                metadata_ty: Ty::U64,
                ptr: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
        );
        b0.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
        f.blocks.push(b0);
        module.functions.push(f);

        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("a &str formal must split like &[u8]");
        assert_eq!(
            lir.signature.params,
            vec![LirType::I64, LirType::I64],
            "&str splits into (data, len)"
        );
    }

    /// The `&[T]` FORMAL lane: `fn at(s: &[u8], i: usize) -> u8` as the
    /// producer emits it — `ptr_metadata` (len), `ptr_data` (base), `gep`,
    /// `load` — lowers with the fat param SPLIT into (data, len) I64 slots and
    /// the load riding the incoming read-only root. A STORE through the same
    /// root stays fail-closed (`&[T]` is shared).
    #[test]
    fn fat_slice_param_splits_and_loads() {
        use trust_ir::ty::FatPtrKind;
        use trust_ir::value::TyId;

        let mut module = Module::new("t");
        module.types.push(Ty::U8); // TyId(0) = slice element
        module.func_types.push(FuncTy {
            params: vec![Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))), Ty::Usize],
            returns: vec![Ty::U8],
            is_vararg: false,
            abi: None,
        });
        let mut f = IrFunction::new(FuncId::new(0), "at", FuncTyId::new(0), BlockId::new(0));
        let s = ValueId::new(0);
        let i = ValueId::new(1);
        let len = ValueId::new(2);
        let data = ValueId::new(3);
        let addr = ValueId::new(4);
        let byte = ValueId::new(5);
        let mut b0 = Block::new(BlockId::new(0));
        b0.params.push((s, Ty::FatPtr(FatPtrKind::Slice(TyId::new(0)))));
        b0.params.push((i, Ty::Usize));
        b0.body = vec![
            InstrNode::new(Inst::PtrMetadata {
                ptr_ty: Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
                metadata_ty: Ty::U64,
                ptr: s,
            })
            .with_result(len),
            InstrNode::new(Inst::PtrData {
                ptr_ty: Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
                ptr: s,
            })
            .with_result(data),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U8,
                base: data,
                indices: vec![i],
                inbounds: true,
            })
            .with_result(addr),
            InstrNode::new(Inst::Load { ty: Ty::U8, ptr: addr, volatile: false, align: None })
                .with_result(byte),
            InstrNode::new(Inst::Return { values: vec![byte] }),
        ];
        let _ = len; // metadata result is deliberately unused in this body
        f.blocks.push(b0);
        module.functions.push(f);

        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("fat slice param lane lowers at/gep/load");
        assert_eq!(
            lir.signature.params,
            vec![LirType::I64, LirType::I64, LirType::I64],
            "the fat param splits into (data, len) plus the index"
        );
        let loads = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|inst| matches!(inst.opcode, Opcode::Load { .. }))
            .count();
        assert_eq!(loads, 1, "exactly one element load");

        // Fail-closed twin: a STORE through the slice data pointer refuses.
        let g = module.function_by_id_mut(FuncId::new(0)).unwrap();
        let entry = &mut g.blocks[0];
        entry.body.remove(3); // drop the Load
        entry.body.insert(
            3,
            InstrNode::new(Inst::Store {
                ty: Ty::U8,
                ptr: addr,
                value: i,
                volatile: false,
                align: None,
            }),
        );
        // Return something type-correct so only the Store can be the refusal.
        let last = entry.body.len() - 1;
        entry.body[last] = InstrNode::new(Inst::Return { values: vec![i] });
        module.func_types[0].returns = vec![Ty::Usize];
        assert!(
            matches!(
                lower_module_to_lir(&module, FuncId::new(0)),
                Err(ModuleLirError::NonLocalPointer { .. })
            ),
            "a store through the incoming slice root must fail closed"
        );
    }

    #[test]
    fn fixpoint_terminates_and_fail_closes_on_inadmissible_second_call() {
        // First call admissible (local leaf diamond), second call retargeted to
        // a FuncId ABSENT from the module. The fixpoint must stop once no pass
        // makes progress, and the converter must fail-close on the residual
        // call — this test completing at all is the termination pin.
        let mut module = two_calls_one_block_module();
        let caller = &mut module.functions[0];
        let second = caller.blocks[0]
            .body
            .iter_mut()
            .filter(|n| matches!(n.inst, Inst::Call { .. }))
            .nth(1)
            .expect("caller has two calls");
        let Inst::Call { callee, .. } = &mut second.inst else { unreachable!() };
        *callee = FuncId::new(9);
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedInst { inst: "Call", .. })
        ));
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
            abi: None,
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
    fn fail_closed_on_non_leaf_callee_with_inadmissible_nested_call() {
        // HISTORY: this pin used to assert that ANY non-leaf callee fail-closes.
        // The recursive flatten retired that limitation (see
        // `flattens_local_nonleaf_callee_chain` for the success pin). What
        // SURVIVES is the boundary this test now pins: a non-leaf callee whose
        // OWN call cannot be flattened (here: a callee absent from the module)
        // is declined without mis-inlining, and the converter fail-closes on
        // the surviving Call in the caller.
        let mut module = Module::new("nonleaf");
        for _ in 0..3 {
            module.func_types.push(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                is_vararg: false,
                abi: None,
            });
        }
        // FuncId 2: a leaf that exists but is NOT what mid calls.
        let mut leaf = IrFunction::new(FuncId::new(2), "leaf", FuncTyId::new(2), BlockId::new(0));
        let mut lb = Block::new(BlockId::new(0));
        lb.params.push((ValueId::new(20), Ty::I32));
        lb.params.push((ValueId::new(21), Ty::I32));
        lb.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(20)] }));
        leaf.blocks.push(lb);

        // FuncId 1: the (non-leaf) callee whose nested call targets FuncId 9 —
        // absent from the module, so the flatten cannot remove it.
        let mut mid = IrFunction::new(FuncId::new(1), "mid", FuncTyId::new(1), BlockId::new(0));
        let mut mb = Block::new(BlockId::new(0));
        mb.params.push((ValueId::new(10), Ty::I32));
        mb.params.push((ValueId::new(11), Ty::I32));
        mb.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(9),
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
            abi: None,
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
            abi: None,
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
            abi: None,
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

    /// Build the LEGACY bridge checked-arith TUPLE idiom, the shape
    /// `trust_ir_bridge::lower_to_trust_ir` emitted on a `CheckedBinaryOp` VF
    /// before BMC-LANE-1 (2026-11-06; it now packs the pair with one
    /// `MakeAggregate`, which `bridge_checked_add_make_aggregate_module` builds
    /// from this fixture): an `Inst::Overflow -> [value, flag]`, a
    /// `Tuple([Int,Bool])` `Undef` seed, two `InsertField`s (field 0 = value,
    /// field 1 = flag), an `ExtractField`
    /// of the flag, an `ICmp Eq(flag, false)` = `ok`, then in a second block an
    /// `ExtractField` of the value and `return`. Two blocks so the tuple
    /// decompose is exercised CROSS-block (the value read is in bb1). The
    /// bridge's `assert ok` after the `ICmp` is OMITTED since 2026-09-30: a
    /// body carrying it is refused as an unfaithful implicit panic
    /// (`ModuleLirError::ImplicitPanicUnfaithful`), and this fixture is about
    /// the tuple decompose, which the guard never touched.
    fn bridge_checked_add_tuple_module(op: OverflowOp, ty: Ty) -> Module {
        let mut module = Module::new("t");
        module.func_types.push(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![ty.clone()],
            is_vararg: false,
            abi: None,
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

        // Exactly one CheckedSadd and one Icmp; no Brif and no Trap (no guard).
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
        assert_eq!(brif, 0, "no Brif: the unguarded tuple idiom has no assert");
        assert_eq!(trap, 0, "no Trap: an Assert-free body never reaches the trap block");
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

    /// The pair as the bridge spells it since BMC-LANE-1: ONE complete
    /// `MakeAggregate` over the `Overflow` results, in place of the poison seed
    /// and its two `InsertField`s (value ids otherwise unchanged).
    fn bridge_checked_add_make_aggregate_module(op: OverflowOp, ty: Ty) -> Module {
        let mut module = bridge_checked_add_tuple_module(op, ty.clone());
        let body = &mut module.functions[0].blocks[0].body;
        body.retain(|node| !matches!(node.inst, Inst::Undef { .. } | Inst::InsertField { .. }));
        body.insert(
            1,
            InstrNode::new(Inst::MakeAggregate {
                ty: Ty::Tuple(vec![ty, Ty::Bool]),
                variant: None,
                fields: vec![ValueId::new(4), ValueId::new(5)],
            })
            .with_result(ValueId::new(8)),
        );
        module
    }

    #[test]
    fn decomposes_bridge_checked_add_make_aggregate() {
        let module = bridge_checked_add_make_aggregate_module(OverflowOp::AddOverflow, Ty::I32);
        let lir = lower_module_to_lir(&module, FuncId::new(0))
            .expect("the complete constructor of the checked pair decomposes");
        assert!(lir.stack_slots.is_empty(), "the pair materializes no memory");
        let opcodes: Vec<_> =
            lir.blocks.values().flat_map(|b| &b.instructions).map(|i| &i.opcode).collect();
        assert_eq!(opcodes.iter().filter(|op| matches!(op, Opcode::CheckedSadd)).count(), 1);
        assert!(
            opcodes.iter().filter(|op| matches!(op, Opcode::Copy)).count() >= 2,
            "both ExtractFields resolve to the constructor's lanes"
        );
    }

    #[test]
    fn fail_closed_on_checked_pair_make_aggregate_escaping_to_memory() {
        // A pair claimed by the pure-SSA decomposition never reaches memory.
        let mut module = bridge_checked_add_make_aggregate_module(OverflowOp::AddOverflow, Ty::I32);
        let tuple_ty = Ty::Tuple(vec![Ty::I32, Ty::Bool]);
        let body = &mut module.functions[0].blocks[0].body;
        body.insert(
            2,
            InstrNode::new(Inst::Alloca { ty: tuple_ty.clone(), count: None, align: None })
                .with_result(ValueId::new(20)),
        );
        body.insert(
            3,
            InstrNode::new(Inst::Store {
                ty: tuple_ty,
                ptr: ValueId::new(20),
                value: ValueId::new(8),
                volatile: false,
                align: None,
            }),
        );
        assert!(matches!(
            lower_module_to_lir(&module, FuncId::new(0)),
            Err(ModuleLirError::UnsupportedAggregate { .. })
        ));
    }

    #[test]
    fn fail_closed_on_a_checked_pair_make_aggregate_built_from_a_tracked_pair() {
        // A second `(i32, bool)` constructor whose lane 0 is the first pair (8)
        // rather than a scalar: `%20 = make_aggregate (i32,bool) [%8, %5]`. Both
        // are checked-arith pairs by type, so PASS 1.6 claims both, and only its
        // own lane check refuses the second. PASS 1.6 runs before the
        // aggregate-memory analysis whatever the function allocates, so no
        // Alloca is needed to reach it. `%20` is never read: the refusal is at
        // the constructor itself. Without the check `%20` would be admitted with
        // the pair `%8` recorded as its scalar value field.
        let mut module = bridge_checked_add_make_aggregate_module(OverflowOp::AddOverflow, Ty::I32);
        let body = &mut module.functions[0].blocks[0].body;
        body.insert(
            2,
            InstrNode::new(Inst::MakeAggregate {
                ty: Ty::Tuple(vec![Ty::I32, Ty::Bool]),
                variant: None,
                fields: vec![ValueId::new(8), ValueId::new(5)],
            })
            .with_result(ValueId::new(20)),
        );
        match lower_module_to_lir(&module, FuncId::new(0)) {
            Err(ModuleLirError::UnsupportedAggregate { detail, .. }) => assert_eq!(
                detail, "checked-arith pair 20 is built from a tracked tuple value",
                "refused by PASS 1.6's lane check, not another arm"
            ),
            other => panic!("a pair built from a tracked pair must be refused: {other:?}"),
        }
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
            abi: None,
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

    // =====================================================================
    // FIELDLESS (C-like) ENUMS
    //
    // Two rules, tested through `lower_module_to_lir` rather than through the
    // helpers directly, because what ships is the converter's answer:
    //
    //  1. the LIR carrier of an enum-typed slot is the PRODUCER's tag width
    //     (`EnumLayoutDescriptor` + `canonical_tag_repr`), never a guess;
    //  2. an enum-typed `Inst::Const` is admitted ONLY at a DECLARED
    //     discriminant.
    //
    // Every test here pairs its fail-closed half with a POSITIVE CONTROL that
    // only passes once the carrier rule exists. Without the control a refusal
    // is consistent with "the converter refuses all enums", which is what HEAD
    // does and is not what is being asserted.
    // =====================================================================

    /// A fieldless enum def SHAPED EXACTLY AS THE PRODUCER WRITES IT.
    ///
    /// Not invented: every field here was READ BACK out of a real
    /// `-Ztrust-ir-lower --emit=trust-ir` module for the corresponding Rust
    /// source (`trust-ir convert --from bin --to json`). For
    /// `enum Three { X, Y, Z }` the producer writes explicit
    /// `discriminants: [0, 1, 2]`, `repr: null`, and
    /// `layout: { Direct { tag_offset: 0 }, size: 1, align: 1,
    /// variant_field_offsets: [[], [], []] }`. `repr` is only `Some` when
    /// `widen_enum_repr_to_rustc_tag_lane` had to move the lane onto rustc's tag
    /// — measured on `#[repr(u32)] enum Wide { A, B, C }`, which comes out
    /// `repr: U32, size: 4`.
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

    /// The three-variant `enum Three { X, Y, Z }` shape, verbatim from the
    /// producer: the default fixture for everything that is not about widths.
    fn three_variant_enum() -> trust_ir::EnumDef {
        fieldless_enum(&[0, 1, 2], None, 1)
    }

    /// `fn k() -> E { <disc> }` over `def` — the producer's canonical fieldless
    /// enum literal, whose `Inst::Const` is `(Ty::Enum, Aggregate([Int(disc)]))`
    /// with field 0 the DISCRIMINANT. Measured on a real compile of
    /// `pub fn three_z() -> Three { Three::Z }`, whose body is
    /// `%0 = const enum.0 { 2 } ; ret %0`.
    fn enum_const_module(def: trust_ir::EnumDef, disc: i128) -> Module {
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
        module
    }

    /// The carrier is the PRODUCER's tag width — and the immediate is the
    /// discriminant itself, because for a fieldless enum the value IS the tag.
    ///
    /// The four rows are the four real producer shapes measured above:
    /// `enum Three { X, Y, Z }` (u8), `#[repr(u32)] enum Wide { A, B, C }`
    /// (u32), `enum Big { P = 0, Q = 300 }` (u16, hint-less — the width comes
    /// from the VALUES), and `enum Neg { M = -1, N = 0 }` (i8, signed).
    ///
    /// No hardcoded carrier can pass this: any single fixed width fails at
    /// least two of the four rows.
    #[test]
    fn fieldless_enum_carrier_is_the_producers_tag_width() {
        for (name, discs, repr, size, tag, want) in [
            ("Three (u8)", &[0i128, 1, 2][..], None, 1u64, 2i64, LirType::I8),
            ("Wide (repr u32)", &[0, 1, 2][..], Some(EnumTagRepr::U32), 4, 2, LirType::I32),
            ("Big (u16 by value)", &[0, 300][..], None, 2, 300, LirType::I16),
            ("Neg (i8, signed)", &[-1, 0][..], None, 1, -1, LirType::I8),
        ] {
            let module = enum_const_module(fieldless_enum(discs, repr, size), i128::from(tag));
            let lir = lower_module_to_lir(&module, FuncId::new(0))
                .unwrap_or_else(|e| panic!("{name}: fieldless enum must lower, got {e:?}"));
            assert_eq!(lir.signature.params, Vec::<LirType>::new(), "{name}");
            assert_eq!(lir.signature.returns, vec![want], "{name}: carrier width");
            let block = lir.blocks.get(&Block(0)).expect("entry block");
            assert!(
                matches!(block.instructions[0].opcode, Opcode::Iconst { imm, .. } if imm == tag),
                "{name}: the immediate must be the DISCRIMINANT itself, got {:?}",
                block.instructions[0].opcode
            );
            assert!(matches!(block.instructions[1].opcode, Opcode::Return), "{name}");
        }
    }

    /// `fn f(e: E) -> u8 { extractfield u8 %e, 0 }` — the producer's tag read on
    /// a BY-VALUE fieldless-enum param (the `is_gt_fam`/`gt_cnt` switch-head
    /// shape, measured in trust-ts-strip). The extract is an identity at the
    /// machine level, so it lowers to a `Copy` of the carrier value; field
    /// indices other than 0 and a mistyped tag read stay refused.
    #[test]
    fn fieldless_enum_param_tag_extract_lowers_to_copy() {
        let build = |field: u32, field_ty: Ty| {
            let mut module = Module::new("t");
            module.enums.push(three_variant_enum());
            let ety = Ty::Enum(trust_ir::EnumId::new(0));
            module.func_types.push(FuncTy {
                params: vec![ety.clone()],
                returns: vec![Ty::U8],
                is_vararg: false,
                abi: None,
            });
            let mut f = IrFunction::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
            let mut block = Block::new(BlockId::new(0));
            block.params = vec![(ValueId::new(0), ety.clone())];
            block.body = vec![
                InstrNode::new(Inst::ExtractField {
                    ty: field_ty,
                    aggregate: ValueId::new(0),
                    field,
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }),
            ];
            f.blocks.push(block);
            module.functions.push(f);
            module
        };

        // The admitted identity read: field 0 typed at the tag repr (u8).
        let lir = lower_module_to_lir(&build(0, Ty::U8), FuncId::new(0))
            .expect("fieldless-enum tag extract must lower");
        assert_eq!(lir.signature.params, vec![LirType::I8], "param is the tag carrier");
        let block = lir.blocks.get(&Block(0)).expect("entry block");
        assert!(
            matches!(block.instructions[0].opcode, Opcode::Copy),
            "tag extract is an identity Copy, got {:?}",
            block.instructions[0].opcode
        );
        assert!(matches!(block.instructions[1].opcode, Opcode::Return));

        // A non-zero field index has nothing to read on a fieldless enum.
        assert!(matches!(
            lower_module_to_lir(&build(1, Ty::U8), FuncId::new(0)),
            Err(ModuleLirError::UnsupportedAggregate { .. })
        ));
        // A tag read typed wider than the admitted carrier is def drift.
        assert!(matches!(
            lower_module_to_lir(&build(0, Ty::U32), FuncId::new(0)),
            Err(ModuleLirError::UnsupportedAggregate { .. })
        ));
    }

    /// The carrier comes from the DESCRIPTOR, so a def the descriptor does not
    /// pin stays refused — even though its `canonical_tag_repr` alone would
    /// happily name a width.
    ///
    /// The `Direct { size 1, repr U8 }` control at the top is the row that only
    /// passes with the carrier rule in place; every row below it is a
    /// perturbation of exactly one field of that same def.
    #[test]
    fn fieldless_enum_carrier_fails_closed_without_a_pinning_descriptor() {
        let control = enum_const_module(three_variant_enum(), 2);
        lower_module_to_lir(&control, FuncId::new(0)).expect("control: pinned def must lower");

        // (a) No descriptor at all: nothing ties the tag width to rustc's.
        let mut def = three_variant_enum();
        def.layout = None;

        // (b) The descriptor's total size is not the tag's — that is what would
        // betray a payload or padding this rule does not model.
        let mut size_mismatch = three_variant_enum();
        size_mismatch.layout.as_mut().expect("layout").size = 4;

        // (c) A NICHE encoding: the value is not a plain tag there.
        let mut niche = three_variant_enum();
        niche.layout.as_mut().expect("layout").encoding = trust_ir::EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 2,
            niche_start: 1,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U8,
        };

        // (d) A tag at a non-zero offset is not the whole value.
        let mut offset_tag = three_variant_enum();
        offset_tag.layout.as_mut().expect("layout").encoding =
            trust_ir::EnumTagEncoding::Direct { tag_offset: 4 };

        // (e) A PAYLOAD-carrying variant: the value is not just the tag.
        let mut payload = three_variant_enum();
        payload.variants[1].fields.push(Ty::I32);

        // (f) Fewer than 2 variants: rustc gives a 1-variant enum
        // `PassMode::Ignore`, so it is not a register value at all.
        let single = fieldless_enum(&[0], None, 1);

        // (g) A `#[repr]` hint too narrow for the values has no canonical tag.
        let too_narrow = fieldless_enum(&[0, 300], Some(EnumTagRepr::U8), 2);

        // The payload-carrying row is RETIRED BY CAPABILITY: a Direct-tagged
        // single-payload enum now lowers through the PAIR-ENUM lane (its
        // constant becomes a (tag, payload) register pair — see the
        // pair_enum_* pins), so it is asserted to LOWER here rather than
        // refuse. Every row that remains has NO admitting lane.
        let m = enum_const_module(payload, 0);
        assert!(
            lower_module_to_lir(&m, FuncId::new(0)).is_ok(),
            "a Direct-tagged single-payload enum constant rides the pair-enum lane"
        );

        for (why, def) in [
            ("no layout descriptor", def),
            ("size 4 with a 1-byte tag", size_mismatch),
            ("niche encoding", niche),
            ("tag at offset 4", offset_tag),
            ("a single-variant enum", single),
            ("a repr hint narrower than the values", too_narrow),
        ] {
            let m = enum_const_module(def, 0);
            assert!(
                matches!(
                    lower_module_to_lir(&m, FuncId::new(0)),
                    Err(ModuleLirError::UnsupportedType { .. })
                ),
                "{why} must fail closed"
            );
        }
    }

    /// The VALUE-VALIDITY half. rustc marks a fieldless-enum slot `NoUndef`
    /// with a validity range, so materializing a tag the def does not DECLARE
    /// would be an invalid value of the type. Both halves are asserted in one
    /// test: the declared tags lower (this is the half that fails without the
    /// change), the undeclared ones do not.
    #[test]
    fn fieldless_enum_const_must_be_a_declared_discriminant() {
        // Declared: 0, 1, 2.
        for disc in [0i128, 1, 2] {
            let m = enum_const_module(three_variant_enum(), disc);
            let lir = lower_module_to_lir(&m, FuncId::new(0))
                .unwrap_or_else(|e| panic!("declared discriminant {disc} must lower: {e:?}"));
            let block = lir.blocks.get(&Block(0)).expect("entry block");
            let want = i64::try_from(disc).expect("fits");
            assert!(
                matches!(block.instructions[0].opcode, Opcode::Iconst { imm, .. } if imm == want),
                "declared discriminant {disc} must materialize as itself"
            );
        }
        // Not declared: past the last variant, elsewhere in the carrier's range,
        // its top value, and a negative.
        for disc in [3i128, 7, 255, -1] {
            let m = enum_const_module(three_variant_enum(), disc);
            assert!(
                matches!(
                    lower_module_to_lir(&m, FuncId::new(0)),
                    Err(ModuleLirError::UnsupportedConstant { .. })
                ),
                "tag {disc} is not a DECLARED discriminant and must fail closed"
            );
        }
        // "Declared" is read off the def, not assumed to be `0..variant_count`:
        // `enum E { A = 10, B = 20 }` admits 10 and 20 and refuses 0, 1 and 11.
        let def = fieldless_enum(&[10, 20], None, 1);
        for (disc, ok) in [(10i128, true), (20, true), (0, false), (1, false), (11, false)] {
            let m = enum_const_module(def.clone(), disc);
            let got = lower_module_to_lir(&m, FuncId::new(0));
            assert_eq!(
                got.is_ok(),
                ok,
                "explicit-discriminant def: tag {disc} should be {}, got {got:?}",
                if ok { "admitted" } else { "refused" }
            );
        }
    }

    /// The enum type is admitted at the FOUR sites the fragment allows and
    /// NOWHERE else: an enum-typed value never reaches arithmetic, a compare or
    /// a cast. The `Return`-only control lowers; the same module with one
    /// arithmetic node added does not.
    #[test]
    fn enum_typed_values_stay_out_of_arithmetic() {
        let ety = Ty::Enum(trust_ir::EnumId::new(0));

        // Control: signature + Const + Return is in the fragment.
        let control = enum_const_module(three_variant_enum(), 2);
        lower_module_to_lir(&control, FuncId::new(0)).expect("control must lower");

        // Same module, one `add` on the enum-typed value: refused.
        let mut m = enum_const_module(three_variant_enum(), 2);
        let block = &mut m.functions[0].blocks[0];
        block.body.insert(
            1,
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: ety.clone(),
                lhs: ValueId::new(0),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
        );
        let got = lower_module_to_lir(&m, FuncId::new(0));
        assert!(
            matches!(&got, Err(ModuleLirError::UnsupportedType { ty: Ty::Enum(_), .. })),
            "arithmetic on an enum-typed value must fail closed ON THE ENUM TYPE, not for \
             some unrelated reason; got {got:?}"
        );

        // ... and one `icmp`: refused.
        let mut m = enum_const_module(three_variant_enum(), 2);
        let block = &mut m.functions[0].blocks[0];
        block.body.insert(
            1,
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: ety,
                lhs: ValueId::new(0),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
        );
        let got = lower_module_to_lir(&m, FuncId::new(0));
        assert!(
            matches!(&got, Err(ModuleLirError::UnsupportedType { ty: Ty::Enum(_), .. })),
            "comparing enum-typed values must fail closed ON THE ENUM TYPE; got {got:?}"
        );
    }

    // ---- BMC-LANE-1 hostile review #19: PASS 1.7 admits an aggregate slot only
    // when every use of it is the POINTER of a whole-aggregate Store/Load at the
    // slot's own type. Each probe below was LOWERED before the guard (the reviewer
    // measured p1-p4 against the committed converter); each must now be refused
    // for the slot misuse itself, and p5, the whole round trip, must still lower.

    /// `%4 = make (i32,i32) [%0, %1]; %5 = alloca (i32,i32); store %4 -> *%5`,
    /// then `tail`.
    fn aggregate_slot_body(tail: Vec<InstrNode>) -> Vec<InstrNode> {
        let tup = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let mut body = vec![
            InstrNode::new(Inst::MakeAggregate {
                ty: tup.clone(),
                variant: None,
                fields: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Alloca { ty: tup.clone(), count: None, align: None })
                .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Store {
                ty: tup,
                ptr: ValueId::new(5),
                value: ValueId::new(4),
                volatile: false,
                align: None,
            }),
        ];
        body.extend(tail);
        body
    }

    /// Is the refusal the slot guard's, naming slot `slot` and the misusing `inst`?
    fn aggregate_slot_misuse_refusal(
        got: &Result<impl std::fmt::Debug, ModuleLirError>,
        slot: u32,
        inst: &str,
    ) -> Result<(), String> {
        let want = format!("aggregate slot {slot} is used by `{inst}` other than as the pointer");
        if matches!(got, Err(ModuleLirError::UnsupportedMemory { detail, .. })
            if detail.starts_with(&want))
        {
            Ok(())
        } else {
            Err(format!(
                "expected the aggregate-slot guard to refuse `{inst}` on slot {slot}; got {got:?}"
            ))
        }
    }

    /// The refusal is the slot guard's, naming slot `slot` and the misusing `inst`.
    fn assert_aggregate_slot_misuse(
        got: &Result<impl std::fmt::Debug, ModuleLirError>,
        slot: u32,
        inst: &str,
    ) {
        if let Err(why) = aggregate_slot_misuse_refusal(got, slot, inst) {
            panic!("{why}");
        }
    }

    /// p1: a scalar `load i32` through the `(i32,i32)` slot.
    #[test]
    fn a_scalar_load_through_an_aggregate_slot_is_refused() {
        let body = aggregate_slot_body(vec![
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: ValueId::new(5),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(6)] }),
        ]);
        let module = module_with_body("p1_scalar_load", vec![Ty::I32], body);
        assert_aggregate_slot_misuse(&lower_module_to_lir(&module, FuncId::new(0)), 5, "Load");
    }

    /// p2: a scalar `store i32` into the slot, then a whole load of it.
    #[test]
    fn a_scalar_store_into_an_aggregate_slot_is_refused() {
        let body = aggregate_slot_body(vec![
            InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: ValueId::new(5),
                value: ValueId::new(1),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Load {
                ty: Ty::Tuple(vec![Ty::I32, Ty::I32]),
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
            InstrNode::new(Inst::Return { values: vec![ValueId::new(7)] }),
        ]);
        let module = module_with_body("p2_scalar_store", vec![Ty::I32], body);
        assert_aggregate_slot_misuse(&lower_module_to_lir(&module, FuncId::new(0)), 5, "Store");
    }

    /// p3: `gep i32 %slot, 1` then a scalar load: the GEP arm would address the
    /// slot at `1 * size_of(i32)`, which only coincides with field 1's C offset.
    #[test]
    fn a_gep_off_an_aggregate_slot_is_refused() {
        let body = aggregate_slot_body(vec![
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(1) })
                .with_result(ValueId::new(6)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I32,
                base: ValueId::new(5),
                indices: vec![ValueId::new(6)],
                inbounds: false,
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: ValueId::new(7),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(8)] }),
        ]);
        let module = module_with_body("p3_gep", vec![Ty::I32], body);
        assert_aggregate_slot_misuse(&lower_module_to_lir(&module, FuncId::new(0)), 5, "GEP");
    }

    /// p4, the measured miscompile: `struct S { a: i32 @ 4, b: i32 @ 0 }` (a
    /// DECLARED, reordered layout, as the producer's `register_struct` fills from
    /// rustc), stored whole from `(a, b) = (7, 9)` and read back by a scalar
    /// `load i32` at the slot's base. The interpreter lays the slot out at the
    /// declared offsets and returns `b` = 9; the converter laid it out in
    /// declaration order and returned `a` = 7. It must be refused.
    #[test]
    fn a_scalar_load_of_a_declared_layout_struct_slot_is_refused_where_it_miscompiled() {
        use trust_ir::interpret::{InterpretValue, Interpreter};
        let sid = trust_ir::value::StructId::new(0);
        let sty = Ty::Struct(sid);
        let mut module = module_with_body(
            "p4_declared_layout",
            vec![Ty::I32],
            vec![
                InstrNode::new(Inst::MakeAggregate {
                    ty: sty.clone(),
                    variant: None,
                    fields: vec![ValueId::new(0), ValueId::new(1)],
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Alloca { ty: sty.clone(), count: None, align: None })
                    .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Store {
                    ty: sty,
                    ptr: ValueId::new(3),
                    value: ValueId::new(2),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: ValueId::new(3),
                    volatile: false,
                    align: None,
                })
                .with_result(ValueId::new(4)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(4)] }),
            ],
        );
        module.structs.push(trust_ir::StructDef {
            id: sid,
            name: "S".to_string(),
            fields: vec![
                trust_ir::ty::FieldDef { name: "a".to_string(), ty: Ty::I32, offset: Some(4) },
                trust_ir::ty::FieldDef { name: "b".to_string(), ty: Ty::I32, offset: Some(0) },
            ],
            size: Some(8),
            align: Some(4),
            repr: trust_ir::ty::StructRepr::Rust,
            origin: None,
        });
        let args = vec![
            InterpretValue::int(Ty::I32, 7).expect("fits"),
            InterpretValue::int(Ty::I32, 9).expect("fits"),
        ];
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), args)
            .expect("the module executes on the reference interpreter");
        let [returned] = outcome.returns.as_slice() else {
            panic!("one returned value, got {:?}", outcome.returns)
        };
        assert_eq!(
            returned,
            &InterpretValue::int(Ty::I32, 9).expect("fits"),
            "the interpreter reads the declared offset 0, field `b` = 9"
        );
        assert_aggregate_slot_misuse(&lower_module_to_lir(&module, FuncId::new(0)), 3, "Load");
    }

    // ---- CG-DECLARED-LAYOUT-1: an aggregate slot is laid out at the trust-ir
    // interpreter's own layout of its type. A struct that declares
    // size/align/`FieldDef::offset`, and a tuple with a `Module::tuple_layouts`
    // descriptor, are laid out at the DECLARED offsets (until 2026-11-10 both were
    // laid out in declaration order); a declaration the interpreter refuses is
    // refused. The byte-level gate (emitted bytes vs the interpreter's slot image)
    // is `tests/module_to_lir_struct_mem_proven_output.rs`.

    /// `(a, b) -> a - b` over `ty`: `make ty [a, b]; alloca ty; store; load;
    /// extract 0, 1; sub`. Executable on the reference interpreter.
    fn declared_round_trip_module(name: &str, ty: Ty) -> Module {
        module_with_body(
            name,
            vec![Ty::I32],
            vec![
                InstrNode::new(Inst::MakeAggregate {
                    ty: ty.clone(),
                    variant: None,
                    fields: vec![ValueId::new(0), ValueId::new(1)],
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Alloca { ty: ty.clone(), count: None, align: None })
                    .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Store {
                    ty: ty.clone(),
                    ptr: ValueId::new(3),
                    value: ValueId::new(2),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Load {
                    ty: ty.clone(),
                    ptr: ValueId::new(3),
                    volatile: false,
                    align: None,
                })
                .with_result(ValueId::new(4)),
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::I32,
                    aggregate: ValueId::new(4),
                    field: 0,
                })
                .with_result(ValueId::new(5)),
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::I32,
                    aggregate: ValueId::new(4),
                    field: 1,
                })
                .with_result(ValueId::new(6)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I32,
                    lhs: ValueId::new(5),
                    rhs: ValueId::new(6),
                })
                .with_result(ValueId::new(7)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(7)] }),
            ],
        )
    }

    /// The `i32` struct `S { a, b }` with the given declared triple.
    fn declared_struct(
        size: Option<u64>,
        align: Option<u64>,
        offsets: [Option<u64>; 2],
    ) -> trust_ir::StructDef {
        trust_ir::StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "S".to_string(),
            fields: vec![
                trust_ir::ty::FieldDef { name: "a".to_string(), ty: Ty::I32, offset: offsets[0] },
                trust_ir::ty::FieldDef { name: "b".to_string(), ty: Ty::I32, offset: offsets[1] },
            ],
            size,
            align,
            repr: trust_ir::ty::StructRepr::Rust,
            origin: None,
        }
    }

    fn declared_struct_module(def: trust_ir::StructDef) -> Module {
        let mut module = declared_round_trip_module(
            "declared_struct",
            Ty::Struct(trust_ir::value::StructId::new(0)),
        );
        module.structs.push(def);
        module
    }

    /// The target the producer stamps on a module whose tuples it describes
    /// (`tuple_layout_ledger`); the interpreter refuses a tuple descriptor on a
    /// module with none (`LayoutError::TupleLayoutTargetMissing`).
    fn producer_target() -> trust_ir::TargetInfo {
        trust_ir::TargetInfo {
            triple: "arm64-apple-macosx".to_string(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        }
    }

    /// `(i32, i32)` with a `Module::tuple_layouts` descriptor per `rows`, on the
    /// producer's target.
    fn described_tuple_module(rows: &[(u64, u64, Vec<u64>)]) -> Module {
        let tup = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let mut module = declared_round_trip_module("described_tuple", tup.clone());
        module.target_info = Some(producer_target());
        let tuple_type = module.add_type(tup).expect("Module::add_type: test fixture");
        for (size, align, field_offsets) in rows {
            module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
                tuple_type,
                size: *size,
                align: *align,
                field_offsets: field_offsets.clone(),
            });
        }
        module
    }

    /// The byte offset in its slot of every LIR `Store`, in emission order, with
    /// the stored value: the address is the slot's `StackAddr` (offset 0) or an
    /// `ArrayGep i8` off it by an `Iconst` (`emit_field_addr`'s two spellings).
    fn lir_store_offsets(lir: &LirFunction) -> Vec<(Value, u32, i64)> {
        let insts: Vec<&Instruction> = lir.blocks.values().flat_map(|b| &b.instructions).collect();
        let def = |v: Value| insts.iter().find(|i| i.results.contains(&v)).copied();
        insts
            .iter()
            .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
            .map(|store| {
                let addr = def(store.args[1]).expect("the store address is defined");
                match (&addr.opcode, addr.args.as_slice()) {
                    (Opcode::StackAddr { slot }, []) => (store.args[0], *slot, 0),
                    (Opcode::ArrayGep { elem_ty: LirType::I8 }, [base, idx]) => {
                        let Some(Opcode::StackAddr { slot }) = def(*base).map(|b| &b.opcode) else {
                            panic!("field address is not slot-relative: {addr:?}")
                        };
                        let Some(Opcode::Iconst { imm, .. }) = def(*idx).map(|i| &i.opcode) else {
                            panic!("field offset is not a constant: {addr:?}")
                        };
                        (store.args[0], *slot, *imm)
                    }
                    other => panic!("unexpected field address {other:?}"),
                }
            })
            .collect()
    }

    fn interpret_round_trip(module: &Module, a: i128, b: i128) -> Result<i128, String> {
        use trust_ir::interpret::{InterpretValue, Interpreter};
        let args = vec![
            InterpretValue::int(Ty::I32, a).expect("fits"),
            InterpretValue::int(Ty::I32, b).expect("fits"),
        ];
        let outcome = Interpreter::with_module(module)
            .execute_func(FuncId::new(0), args)
            .map_err(|e| format!("{e:?}"))?;
        Ok(outcome.returns[0].as_int().expect("integer return").as_signed())
    }

    /// `S { a@4, b@0 }`: the slot is the declared 8 bytes, `a` (param 0) is stored
    /// at 4 and `b` (param 1) at 0, and the value is the interpreter's.
    #[test]
    fn a_declared_struct_layout_places_each_field_at_its_declared_offset() {
        let module = declared_struct_module(declared_struct(Some(8), Some(4), [Some(4), Some(0)]));
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("declared layout lowers");
        assert_eq!(lir.stack_slots.len(), 1);
        assert_eq!((lir.stack_slots[0].size, lir.stack_slots[0].align), (8, 4));
        let a = Value(0);
        let b = Value(1);
        assert_eq!(
            lir_store_offsets(&lir),
            vec![(a, 0, 4), (b, 0, 0)],
            "field a (param 0) at its declared offset 4, field b (param 1) at 0"
        );
        assert_eq!(interpret_round_trip(&module, 7, 9), Ok(-2));
    }

    /// A declared size larger than the declaration-order one (rustc may pad)
    /// sizes the slot; the fields keep their declared offsets.
    #[test]
    fn a_declared_struct_size_and_alignment_size_the_slot() {
        let module = declared_struct_module(declared_struct(Some(16), Some(8), [Some(8), Some(0)]));
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("declared layout lowers");
        assert_eq!((lir.stack_slots[0].size, lir.stack_slots[0].align), (16, 8));
        assert_eq!(lir_store_offsets(&lir), vec![(Value(0), 0, 8), (Value(1), 0, 0)]);
        assert_eq!(interpret_round_trip(&module, 7, 9), Ok(-2));
    }

    /// `(i32, i32)` described at `[4, 0]`: laid out at the descriptor's offsets.
    #[test]
    fn a_described_tuple_places_each_element_at_its_descriptor_offset() {
        let module = described_tuple_module(&[(8, 4, vec![4, 0])]);
        let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("described tuple lowers");
        assert_eq!((lir.stack_slots[0].size, lir.stack_slots[0].align), (8, 4));
        assert_eq!(lir_store_offsets(&lir), vec![(Value(0), 0, 4), (Value(1), 0, 0)]);
        assert_eq!(interpret_round_trip(&module, 7, 9), Ok(-2));
    }

    /// A type that declares no layout keeps the declaration-order one (the
    /// interpreter's `aggregate_layout`), for a struct and a tuple alike, and a
    /// descriptor for ANOTHER tuple does not move it.
    #[test]
    fn an_undeclared_layout_stays_in_declaration_order() {
        let plain = declared_struct_module(declared_struct(None, None, [None, None]));
        let lir = lower_module_to_lir(&plain, FuncId::new(0)).expect("plain struct lowers");
        assert_eq!(lir_store_offsets(&lir), vec![(Value(0), 0, 0), (Value(1), 0, 4)]);

        let mut other =
            declared_round_trip_module("other_tuple", Ty::Tuple(vec![Ty::I32, Ty::I32]));
        other.target_info = Some(producer_target());
        let described = other
            .add_type(Ty::Tuple(vec![Ty::I64, Ty::I32]))
            .expect("Module::add_type: test fixture");
        other.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
            tuple_type: described,
            size: 16,
            align: 8,
            field_offsets: vec![8, 0],
        });
        let lir = lower_module_to_lir(&other, FuncId::new(0)).expect("undescribed tuple lowers");
        assert_eq!(lir_store_offsets(&lir), vec![(Value(0), 0, 0), (Value(1), 0, 4)]);
        assert_eq!(interpret_round_trip(&other, 7, 9), Ok(-2));
    }

    /// Every declaration the reference interpreter refuses is refused here too,
    /// by the declared-layout reader — never repaired into a layout of our own.
    /// Each row is executed on the interpreter first, which must refuse it.
    #[test]
    fn a_declared_layout_the_interpreter_refuses_is_refused() {
        let structs: [(&str, trust_ir::StructDef); 9] = [
            ("size without align", declared_struct(Some(8), None, [Some(4), Some(0)])),
            ("align without size", declared_struct(None, Some(4), [Some(4), Some(0)])),
            ("offset without size/align", declared_struct(None, None, [Some(4), None])),
            ("sized field with no offset", declared_struct(Some(8), Some(4), [Some(4), None])),
            ("misaligned offset", declared_struct(Some(12), Some(4), [Some(2), Some(8)])),
            ("overlapping fields", declared_struct(Some(8), Some(4), [Some(0), Some(0)])),
            ("field past the size", declared_struct(Some(8), Some(4), [Some(4), Some(8)])),
            ("size not a multiple of align", declared_struct(Some(6), Some(4), [Some(4), Some(0)])),
            ("over-aligned field", declared_struct(Some(8), Some(2), [Some(4), Some(0)])),
        ];
        for (why, def) in structs {
            let module = declared_struct_module(def);
            assert!(
                interpret_round_trip(&module, 7, 9).is_err(),
                "{why}: the interpreter must refuse this declaration"
            );
            let got = lower_module_to_lir(&module, FuncId::new(0));
            assert!(
                matches!(&got, Err(ModuleLirError::UnsupportedAggregate { .. })),
                "{why}: the converter must refuse it; got {got:?}"
            );
        }
        // `(size, align, field_offsets)` per descriptor row.
        type Descriptors = Vec<(u64, u64, Vec<u64>)>;
        let tuples: [(&str, Descriptors, bool); 4] = [
            ("overlapping elements", vec![(8, 4, vec![0, 0])], true),
            ("element past the size", vec![(8, 4, vec![4, 8])], true),
            ("two descriptors for one tuple", vec![(8, 4, vec![4, 0]), (8, 4, vec![0, 4])], true),
            ("a descriptor on a module with no target", vec![(8, 4, vec![4, 0])], false),
        ];
        for (why, rows, targeted) in tuples {
            let mut module = described_tuple_module(&rows);
            if !targeted {
                module.target_info = None;
            }
            assert!(
                interpret_round_trip(&module, 7, 9).is_err(),
                "{why}: the interpreter must refuse this descriptor"
            );
            let got = lower_module_to_lir(&module, FuncId::new(0));
            assert!(
                matches!(&got, Err(ModuleLirError::UnsupportedAggregate { .. })),
                "{why}: the converter must refuse it; got {got:?}"
            );
        }
    }

    /// A declared layout on a target this converter's 64-bit little-endian field
    /// table does not describe is refused; the same declaration on aarch64 lowers.
    #[test]
    fn a_declared_layout_on_another_target_layout_is_refused() {
        use trust_ir::Endianness::{Big, Little};
        let target = |triple: &str, pointer_size, endianness| trust_ir::TargetInfo {
            triple: triple.to_string(),
            pointer_size,
            endianness,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        };
        let declared = || declared_struct(Some(8), Some(4), [Some(4), Some(0)]);
        let mut on_aarch64 = declared_struct_module(declared());
        on_aarch64.target_info = Some(target("aarch64-apple-darwin", 8, Little));
        let lir = lower_module_to_lir(&on_aarch64, FuncId::new(0)).expect("aarch64 lowers");
        assert_eq!(lir_store_offsets(&lir), vec![(Value(0), 0, 4), (Value(1), 0, 0)]);
        assert_eq!(interpret_round_trip(&on_aarch64, 7, 9), Ok(-2));
        for (triple, pointer_size, endianness) in [
            ("wasm32-unknown-unknown", 4, Little),
            ("i686-unknown-linux-gnu", 4, Little),
            ("aarch64_be-unknown-linux-gnu", 8, Big),
        ] {
            let mut module = declared_struct_module(declared());
            module.target_info = Some(target(triple, pointer_size, endianness));
            let got = lower_module_to_lir(&module, FuncId::new(0));
            assert!(
                matches!(&got, Err(ModuleLirError::UnsupportedAggregate { detail, .. })
                    if detail.contains("canonical-scalar layout this converter")),
                "{triple}: a declared layout must be refused; got {got:?}"
            );
        }
    }

    /// An undeclared `S { a: i32, b: i32, n: usize }` round-tripped through its
    /// slot, returning `a - b`.
    fn pointer_width_field_module() -> Module {
        let s = Ty::Struct(trust_ir::value::StructId::new(0));
        let mut module = module_with_body(
            "pointer_width_field",
            vec![Ty::I32],
            vec![
                InstrNode::new(Inst::Const { ty: Ty::Usize, value: Constant::Int(3) })
                    .with_result(ValueId::new(2)),
                InstrNode::new(Inst::MakeAggregate {
                    ty: s.clone(),
                    variant: None,
                    fields: vec![ValueId::new(0), ValueId::new(1), ValueId::new(2)],
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Alloca { ty: s.clone(), count: None, align: None })
                    .with_result(ValueId::new(4)),
                InstrNode::new(Inst::Store {
                    ty: s.clone(),
                    ptr: ValueId::new(4),
                    value: ValueId::new(3),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::Load {
                    ty: s,
                    ptr: ValueId::new(4),
                    volatile: false,
                    align: None,
                })
                .with_result(ValueId::new(5)),
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::I32,
                    aggregate: ValueId::new(5),
                    field: 0,
                })
                .with_result(ValueId::new(6)),
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::I32,
                    aggregate: ValueId::new(5),
                    field: 1,
                })
                .with_result(ValueId::new(7)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I32,
                    lhs: ValueId::new(6),
                    rhs: ValueId::new(7),
                })
                .with_result(ValueId::new(8)),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(8)] }),
            ],
        );
        let field = |name: &str, ty: Ty| trust_ir::ty::FieldDef {
            name: name.to_string(),
            ty,
            offset: None,
        };
        module.structs.push(trust_ir::StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "S".to_string(),
            fields: vec![field("a", Ty::I32), field("b", Ty::I32), field("n", Ty::Usize)],
            size: None,
            align: None,
            repr: trust_ir::ty::StructRepr::Rust,
            origin: None,
        });
        module
    }

    /// A `usize` field is laid out at 8 bytes only where the interpreter sizes it
    /// at 8: a target-free module and a target with 8-byte pointers. On a 32-bit
    /// target the interpreter sizes it at 4, so the converter refuses instead of
    /// laying the slot out from its 64-bit field table.
    #[test]
    fn a_pointer_width_field_is_laid_out_only_at_an_8_byte_pointer_width() {
        let target = |triple: &str, pointer_size| trust_ir::TargetInfo {
            triple: triple.to_string(),
            pointer_size,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        };
        for target_info in [None, Some(target("aarch64-apple-darwin", 8))] {
            let mut module = pointer_width_field_module();
            module.target_info = target_info.clone();
            let lir = lower_module_to_lir(&module, FuncId::new(0))
                .unwrap_or_else(|e| panic!("{target_info:?}: the slot must lower; got {e:?}"));
            assert_eq!(lir.stack_slots.len(), 1);
            assert_eq!((lir.stack_slots[0].size, lir.stack_slots[0].align), (16, 8));
            let offsets: Vec<i64> =
                lir_store_offsets(&lir).iter().map(|&(_, _, offset)| offset).collect();
            assert_eq!(offsets, vec![0, 4, 8], "{target_info:?}: a@0, b@4, n@8");
            assert_eq!(interpret_round_trip(&module, 7, 9), Ok(-2), "{target_info:?}");
        }
        for (triple, pointer_size) in [("wasm32-unknown-unknown", 4), ("i686-unknown-linux-gnu", 4)]
        {
            let mut module = pointer_width_field_module();
            module.target_info = Some(target(triple, pointer_size));
            let got = lower_module_to_lir(&module, FuncId::new(0));
            assert!(
                matches!(&got, Err(ModuleLirError::UnsupportedAggregate { detail, .. })
                    if detail.contains("is pointer-width and the module's target has 4-byte pointers")),
                "{triple}: a pointer-width field must be refused; got {got:?}"
            );
        }
    }

    /// The slot returned as a pointer escapes.
    #[test]
    fn an_aggregate_slot_that_is_returned_is_refused() {
        let returned = aggregate_slot_body(vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(5)],
        })]);
        let module = module_with_body("slot_returned", vec![Ty::Ptr], returned);
        assert_aggregate_slot_misuse(&lower_module_to_lir(&module, FuncId::new(0)), 5, "Return");
    }

    /// The slot read whole at a type that is not the slot's (same arity, wider
    /// fields). Its own test, so a mutant of the guard is measured on it alone
    /// (BMC-LANE-1 hostile review 4, F6: it shared a test with the returned slot
    /// and never ran under the step-1b mutant).
    #[test]
    fn an_aggregate_slot_read_whole_at_another_type_is_refused() {
        let wider = aggregate_slot_body(vec![
            InstrNode::new(Inst::Load {
                ty: Ty::Tuple(vec![Ty::I64, Ty::I64]),
                ptr: ValueId::new(5),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I64,
                aggregate: ValueId::new(6),
                field: 1,
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(7)] }),
        ]);
        let module = module_with_body("slot_read_wider", vec![Ty::I64], wider);
        assert_aggregate_slot_misuse(&lower_module_to_lir(&module, FuncId::new(0)), 5, "Load");
    }

    /// The slot as other operands, each refused at the instruction that uses it
    /// (BMC-LANE-1 hostile reviews 4, F5, and 5, B-L1). A hand-written check over
    /// `Load`/`Store`/`GEP`/`Return` in place of trust-ir's operand visitor passes
    /// every probe above and fails here. The rows are a sample, not every position
    /// the visitor reaches (`CallIndirect`, `InsertField`'s value, the atomics, a
    /// `MakeAggregate` lane, `BinOp`, ... are not pinned one by one); the guard's
    /// walk is the exhaustive one. Three rows (`Call`, `Cast`, `Store` into itself)
    /// are also refused by later arms when step 1b is off, so for them the message
    /// check is what fails.
    #[test]
    fn an_aggregate_slot_as_any_other_operand_is_refused() {
        let slot = ValueId::new(5);
        let tup = Ty::Tuple(vec![Ty::I32, Ty::I32]);
        let cond = || {
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(6))
        };
        let ret = || InstrNode::new(Inst::Return { values: vec![] });
        let block_with_ptr_param = |id: u32, param: u32| {
            let mut block = Block::new(BlockId::new(id));
            block.params.push((ValueId::new(param), Ty::Ptr));
            block.body = vec![ret()];
            block
        };
        let one_block = |name: &str, tail: Vec<InstrNode>| {
            module_with_body(name, vec![], aggregate_slot_body(tail))
        };

        let mut cases: Vec<(&str, Module)> = Vec::new();

        let mut br = one_block(
            "slot_br_arg",
            vec![InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![slot] })],
        );
        br.functions[0].blocks.push(block_with_ptr_param(1, 6));
        cases.push(("Br", br));

        let mut cond_br = one_block(
            "slot_cond_br_arg",
            vec![
                cond(),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(6),
                    then_target: BlockId::new(1),
                    then_args: vec![slot],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        );
        cond_br.functions[0].blocks.push(block_with_ptr_param(1, 7));
        let mut else_block = Block::new(BlockId::new(2));
        else_block.body = vec![ret()];
        cond_br.functions[0].blocks.push(else_block);
        cases.push(("CondBr", cond_br));

        let mut call = one_block(
            "slot_call_arg",
            vec![InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![slot] }), ret()],
        );
        call.func_types.push(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
            abi: None,
        });
        let mut callee =
            IrFunction::new(FuncId::new(1), "takes_ptr", FuncTyId::new(1), BlockId::new(0));
        callee.blocks.push(block_with_ptr_param(0, 0));
        call.functions.push(callee);
        cases.push(("Call", call));

        cases.push((
            "Store",
            one_block(
                "slot_stored_as_value",
                vec![
                    InstrNode::new(Inst::Alloca { ty: Ty::Ptr, count: None, align: None })
                        .with_result(ValueId::new(6)),
                    InstrNode::new(Inst::Store {
                        ty: Ty::Ptr,
                        ptr: ValueId::new(6),
                        value: slot,
                        volatile: false,
                        align: None,
                    }),
                    ret(),
                ],
            ),
        ));
        // The slot stored into ITSELF at its own type: pins the guard's `value != ptr`.
        cases.push((
            "Store",
            one_block(
                "slot_stored_into_itself",
                vec![
                    InstrNode::new(Inst::Store {
                        ty: tup,
                        ptr: slot,
                        value: slot,
                        volatile: false,
                        align: None,
                    }),
                    ret(),
                ],
            ),
        ));
        // A `Switch` edge argument, default and case: the terminator other than
        // `Br`/`CondBr` that carries block arguments.
        for (name, default_args, case_args) in [
            ("slot_switch_default_arg", vec![slot], vec![]),
            ("slot_switch_case_arg", vec![], vec![slot]),
        ] {
            let (default_param, case_param) = (!default_args.is_empty(), !case_args.is_empty());
            let mut switch = one_block(
                name,
                vec![InstrNode::new(Inst::Switch {
                    value: ValueId::new(0),
                    default: BlockId::new(1),
                    default_args,
                    cases: vec![trust_ir::inst::SwitchCase {
                        value: Constant::Int(1),
                        target: BlockId::new(2),
                        args: case_args,
                    }],
                    exhaustive_enum_unreachable: false,
                })],
            );
            for (id, param, takes) in [(1, 6, default_param), (2, 7, case_param)] {
                let mut block = Block::new(BlockId::new(id));
                if takes {
                    block.params.push((ValueId::new(param), Ty::Ptr));
                }
                block.body = vec![ret()];
                switch.functions[0].blocks.push(block);
            }
            cases.push(("Switch", switch));
        }
        // A `GEP` INDEX: the slot used as an offset into another allocation, not as
        // the base.
        cases.push((
            "GEP",
            one_block(
                "slot_as_gep_index",
                vec![
                    InstrNode::new(Inst::Alloca { ty: Ty::I8, count: None, align: None })
                        .with_result(ValueId::new(6)),
                    InstrNode::new(Inst::GEP {
                        pointee_ty: Ty::I8,
                        base: ValueId::new(6),
                        indices: vec![slot],
                        inbounds: false,
                    })
                    .with_result(ValueId::new(7)),
                    ret(),
                ],
            ),
        ));
        cases.push((
            "Copy",
            one_block(
                "slot_copied",
                vec![
                    InstrNode::new(Inst::Copy { ty: Ty::Ptr, operand: slot })
                        .with_result(ValueId::new(6)),
                    ret(),
                ],
            ),
        ));
        cases.push((
            "Select",
            one_block(
                "slot_selected",
                vec![
                    cond(),
                    InstrNode::new(Inst::Select {
                        ty: Ty::Ptr,
                        cond: ValueId::new(6),
                        then_val: slot,
                        else_val: slot,
                    })
                    .with_result(ValueId::new(7)),
                    ret(),
                ],
            ),
        ));
        cases.push((
            "Cast",
            one_block(
                "slot_cast_to_int",
                vec![
                    InstrNode::new(Inst::Cast {
                        op: trust_ir::inst::CastOp::PtrToInt,
                        src_ty: Ty::Ptr,
                        dst_ty: Ty::I64,
                        operand: slot,
                    })
                    .with_result(ValueId::new(6)),
                    ret(),
                ],
            ),
        ));
        cases.push((
            "ICmp",
            one_block(
                "slot_compared",
                vec![
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::Ptr,
                        lhs: slot,
                        rhs: slot,
                    })
                    .with_result(ValueId::new(6)),
                    ret(),
                ],
            ),
        ));

        // Every case is checked before the verdict, so a mutant's log names each
        // route it reopens.
        let failures: Vec<String> = cases
            .iter()
            .filter_map(|(inst, module)| {
                aggregate_slot_misuse_refusal(&lower_module_to_lir(module, FuncId::new(0)), 5, inst)
                    .err()
                    .map(|why| format!("{}: {why}", module.functions[0].name))
            })
            .collect();
        assert!(
            failures.is_empty(),
            "{} of {} cases:\n{}",
            failures.len(),
            cases.len(),
            failures.join("\n")
        );
    }

    /// p5, the control: the whole round trip (whole store, whole load at the slot's
    /// own type, `ExtractField`) still lowers, so the guard refuses only the misuse.
    #[test]
    fn a_whole_round_trip_through_an_aggregate_slot_still_lowers() {
        let body = aggregate_slot_body(vec![
            InstrNode::new(Inst::Load {
                ty: Ty::Tuple(vec![Ty::I32, Ty::I32]),
                ptr: ValueId::new(5),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: ValueId::new(6),
                field: 1,
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(7)] }),
        ]);
        let module = module_with_body("p5_round_trip", vec![Ty::I32], body);
        let got = lower_module_to_lir(&module, FuncId::new(0));
        assert!(got.is_ok(), "a whole round trip must still lower; got {got:?}");
    }

    // ---- F1-FIELD-POINTER-AGREEMENT-1: step 1b admits one partial access, a
    // FIELD POINTER: `gep i8 %slot, %c` off a `Ty::Struct` slot, `%c` a
    // `const i64` that starts exactly one field of the slot's layout (the
    // interpreter's own, CG-DECLARED-LAYOUT-1), used only as the pointer of a
    // non-volatile Load/Store at that field's type. The F1 producer's
    // `lower_field_of_local_addr` spells `&s.f` / `s.f = v` this way. Everything
    // else stays refused; these tests pin both sides. The byte-level gate (ay over
    // the emitted bytes, the interpreter's slot image as the offset oracle) is
    // `tests/module_to_lir_struct_mem_proven_output.rs`, TESTS 18-21.

    /// `S` (`Module::structs[0]`) with `fields` as (type, declared offset) and an
    /// optional declared `(size, align)`.
    fn field_struct(
        fields: &[(Ty, Option<u64>)],
        declared: Option<(u64, u64)>,
    ) -> trust_ir::StructDef {
        trust_ir::StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "S".to_string(),
            fields: fields
                .iter()
                .enumerate()
                .map(|(i, (ty, offset))| trust_ir::ty::FieldDef {
                    name: format!("f{i}"),
                    ty: ty.clone(),
                    offset: *offset,
                })
                .collect(),
            size: declared.map(|(size, _)| size),
            align: declared.map(|(_, align)| align),
            repr: trust_ir::ty::StructRepr::Rust,
            origin: None,
        }
    }

    /// `%2 = alloca S` (`S` = `def`), then `tail`, in the entry block whose two
    /// `i32` params are `%0`, `%1`.
    fn field_pointer_module(
        name: &str,
        def: trust_ir::StructDef,
        returns: Vec<Ty>,
        tail: Vec<InstrNode>,
    ) -> Module {
        let sty = Ty::Struct(trust_ir::value::StructId::new(0));
        let mut body = vec![
            InstrNode::new(Inst::Alloca { ty: sty, count: None, align: None })
                .with_result(ValueId::new(2)),
        ];
        body.extend(tail);
        let mut module = module_with_body(name, returns, body);
        module.structs.push(def);
        module
    }

    /// `%off = const <ty> <offset>; %ptr = gep i8 %2, %off`.
    fn field_gep_typed(off: u32, ptr: u32, ty: Ty, offset: i128) -> [InstrNode; 2] {
        [
            InstrNode::new(Inst::Const { ty, value: Constant::Int(offset) })
                .with_result(ValueId::new(off)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base: ValueId::new(2),
                indices: vec![ValueId::new(off)],
                inbounds: true,
            })
            .with_result(ValueId::new(ptr)),
        ]
    }

    /// The producer's spelling: `%off = const i64 <offset>; %ptr = gep i8 %2, %off`.
    fn field_gep(off: u32, ptr: u32, offset: i128) -> [InstrNode; 2] {
        field_gep_typed(off, ptr, Ty::I64, offset)
    }

    fn field_store(ty: Ty, ptr: u32, value: u32) -> InstrNode {
        InstrNode::new(Inst::Store {
            ty,
            ptr: ValueId::new(ptr),
            value: ValueId::new(value),
            volatile: false,
            align: None,
        })
    }

    fn field_load(ty: Ty, ptr: u32, result: u32) -> InstrNode {
        InstrNode::new(Inst::Load { ty, ptr: ValueId::new(ptr), volatile: false, align: None })
            .with_result(ValueId::new(result))
    }

    /// `s.f0 = %0` through a field pointer at `offsets[0]`, `s.f1 = %1` at
    /// `offsets[1]`, then `s` read WHOLE and `f0 - f1` returned (`-`, so a
    /// lowering that swapped the two fields changes the result).
    fn fill_then_whole_load(offsets: [i128; 2]) -> Vec<InstrNode> {
        let sty = Ty::Struct(trust_ir::value::StructId::new(0));
        let [c0, g0] = field_gep(3, 4, offsets[0]);
        let [c1, g1] = field_gep(5, 6, offsets[1]);
        vec![
            c0,
            g0,
            field_store(Ty::I32, 4, 0),
            c1,
            g1,
            field_store(Ty::I32, 6, 1),
            field_load(sty, 2, 7),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: ValueId::new(7),
                field: 0,
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: ValueId::new(7),
                field: 1,
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I32,
                lhs: ValueId::new(8),
                rhs: ValueId::new(9),
            })
            .with_result(ValueId::new(10)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(10)] }),
        ]
    }

    /// The refusal is the field-pointer walk's, naming the pointer, its field and
    /// slot, and the misusing `inst`.
    fn field_pointer_misuse_refusal(
        got: &Result<impl std::fmt::Debug, ModuleLirError>,
        pointer: u32,
        field: usize,
        inst: &str,
    ) -> Result<(), String> {
        let want = format!(
            "field pointer {pointer} (field {field} of aggregate slot 2) is used by `{inst}` \
             other than as the pointer of a non-volatile Load/Store at the field's type"
        );
        if matches!(got, Err(ModuleLirError::UnsupportedMemory { detail, .. })
            if detail.starts_with(&want))
        {
            Ok(())
        } else {
            Err(format!(
                "expected the field-pointer guard to refuse `{inst}` on pointer {pointer}; got \
                 {got:?}"
            ))
        }
    }

    /// The two `i32` field layouts the admitted shapes are checked at: undeclared
    /// (declaration order, `f0 @ 0, f1 @ 4`), the producer's reordered
    /// `S { a @ 4, b @ 0 }`, and a padded `S { a @ 8, b @ 0 }` in 16 bytes.
    fn two_i32_field_layouts() -> Vec<(&'static str, trust_ir::StructDef, [u32; 2])> {
        vec![
            ("undeclared", field_struct(&[(Ty::I32, None), (Ty::I32, None)], None), [0, 4]),
            (
                "S { a @ 4, b @ 0 }",
                field_struct(&[(Ty::I32, Some(4)), (Ty::I32, Some(0))], Some((8, 4))),
                [4, 0],
            ),
            (
                "S { a @ 8, b @ 0 } in 16",
                field_struct(&[(Ty::I32, Some(8)), (Ty::I32, Some(0))], Some((16, 8))),
                [8, 0],
            ),
        ]
    }

    /// The admitted fill: field pointers at the slot layout's offsets, a Store of
    /// each param at its field's type, then a whole load. Each field pointer
    /// lowers to an `ArrayGep i8` off the slot's `StackAddr` by the field's layout
    /// offset, the param is stored there at 32 bits, and the reference
    /// interpreter computes `7 - 9` on the same module, the reordered and padded
    /// declarations included.
    #[test]
    fn a_field_pointer_fill_lowers_at_the_slot_layout_offsets() {
        for (label, def, offsets) in two_i32_field_layouts() {
            let module = field_pointer_module(
                "field_ptr_fill",
                def,
                vec![Ty::I32],
                fill_then_whole_load(offsets.map(i128::from)),
            );
            assert_eq!(interpret_round_trip(&module, 7, 9), Ok(-2), "{label}: the interpreter");
            let lir = lower_module_to_lir(&module, FuncId::new(0))
                .unwrap_or_else(|e| panic!("{label}: the field-pointer fill must lower: {e:?}"));
            assert_eq!(lir.stack_slots.len(), 1, "{label}: one aggregate slot");
            assert_eq!(
                lir_store_offsets(&lir),
                vec![(Value(0), 0, i64::from(offsets[0])), (Value(1), 0, i64::from(offsets[1]))],
                "{label}: param k is stored through field k's pointer at its layout offset"
            );
            let insts: Vec<&Instruction> =
                lir.blocks.values().flat_map(|b| &b.instructions).collect();
            assert_eq!(
                insts
                    .iter()
                    .filter(|i| i.opcode == Opcode::Store { ty: LirType::I32, align: None })
                    .count(),
                2,
                "{label}: one 32-bit store per field pointer"
            );
        }
    }

    /// A field read through a field pointer after a whole store reads that field.
    #[test]
    fn a_field_pointer_load_after_a_whole_store_reads_its_field() {
        for (label, def, offsets) in two_i32_field_layouts() {
            for (field, want) in [(0usize, 7i128), (1, 9)] {
                let sty = Ty::Struct(trust_ir::value::StructId::new(0));
                let [c, g] = field_gep(4, 5, i128::from(offsets[field]));
                let module = field_pointer_module(
                    "field_ptr_load",
                    def.clone(),
                    vec![Ty::I32],
                    vec![
                        InstrNode::new(Inst::MakeAggregate {
                            ty: sty.clone(),
                            variant: None,
                            fields: vec![ValueId::new(0), ValueId::new(1)],
                        })
                        .with_result(ValueId::new(3)),
                        field_store(sty, 2, 3),
                        c,
                        g,
                        field_load(Ty::I32, 5, 6),
                        InstrNode::new(Inst::Return { values: vec![ValueId::new(6)] }),
                    ],
                );
                assert_eq!(interpret_round_trip(&module, 7, 9), Ok(want), "{label} field {field}");
                let got = lower_module_to_lir(&module, FuncId::new(0));
                assert!(
                    got.is_ok(),
                    "{label} field {field}: a field-pointer load must lower; {got:?}"
                );
            }
        }
    }

    /// Offsets that start no field of the slot's layout: padding, inside a field,
    /// at and past the end, negative, and (on the producer's reordered
    /// `{ a: u8 @ 6, b: i16 @ 4, c: u32 @ 0 }`) field `b`'s DECLARATION-ORDER
    /// offset 2, which is inside `c` in the declared layout. Each GEP is refused as
    /// a slot misuse.
    #[test]
    fn a_field_pointer_at_an_offset_that_starts_no_field_is_refused() {
        let ret = || InstrNode::new(Inst::Return { values: vec![] });
        let one_store = |offset: i128| {
            let [c, g] = field_gep(3, 4, offset);
            vec![c, g, field_store(Ty::U8, 4, 0), ret()]
        };
        let u8_i32 = || field_struct(&[(Ty::U8, None), (Ty::I32, None)], None);
        let reordered = field_struct(
            &[(Ty::U8, Some(6)), (Ty::I16, Some(4)), (Ty::U32, Some(0))],
            Some((8, 4)),
        );
        let cases: Vec<(&str, trust_ir::StructDef, i128)> = vec![
            ("padding", u8_i32(), 1),
            ("inside a field", u8_i32(), 5),
            ("at the end", u8_i32(), 8),
            ("past the end", u8_i32(), 12),
            ("negative", u8_i32(), -4),
            ("a declaration-order offset inside a declared field", reordered, 2),
        ];
        let failures: Vec<String> = cases
            .into_iter()
            .filter_map(|(why, def, offset)| {
                let module =
                    field_pointer_module("field_ptr_offset", def, vec![], one_store(offset));
                aggregate_slot_misuse_refusal(
                    &lower_module_to_lir(&module, FuncId::new(0)),
                    2,
                    "GEP",
                )
                .err()
                .map(|e| format!("{why}: {e}"))
            })
            .collect();
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }

    /// A GEP off a struct slot that is not the producer's constant byte offset: a
    /// runtime offset, a constant of another type, a wider pointee
    /// (`idx * size_of(i32)`), two indices, an index or pointer with a second
    /// definition. And a byte GEP off a TUPLE slot at a field start: tuples get no
    /// field pointers.
    #[test]
    fn a_slot_gep_that_is_not_a_struct_field_pointer_is_refused() {
        let ret = || InstrNode::new(Inst::Return { values: vec![] });
        let gep = |pointee_ty: Ty, indices: Vec<u32>| {
            InstrNode::new(Inst::GEP {
                pointee_ty,
                base: ValueId::new(2),
                indices: indices.into_iter().map(ValueId::new).collect(),
                inbounds: true,
            })
            .with_result(ValueId::new(4))
        };
        let const_at = |ty: Ty, value: i128| {
            InstrNode::new(Inst::Const { ty, value: Constant::Int(value) })
                .with_result(ValueId::new(3))
        };
        let cases: Vec<(&str, Vec<InstrNode>)> = vec![
            ("runtime offset", vec![gep(Ty::I8, vec![0]), field_store(Ty::I32, 4, 1), ret()]),
            (
                "i32 constant",
                vec![const_at(Ty::I32, 4), gep(Ty::I8, vec![3]), field_store(Ty::I32, 4, 1), ret()],
            ),
            (
                "u64 constant",
                vec![const_at(Ty::U64, 4), gep(Ty::I8, vec![3]), field_store(Ty::I32, 4, 1), ret()],
            ),
            // `gep i32 %slot, 4` is byte 16 (past the end) to the interpreter, while
            // byte 4 starts field 1: only the pointee check refuses it.
            (
                "i32 pointee",
                vec![
                    const_at(Ty::I64, 4),
                    gep(Ty::I32, vec![3]),
                    field_store(Ty::I32, 4, 1),
                    ret(),
                ],
            ),
            (
                "two indices",
                vec![
                    const_at(Ty::I64, 4),
                    gep(Ty::I8, vec![3, 3]),
                    field_store(Ty::I32, 4, 1),
                    ret(),
                ],
            ),
            // Not SSA: the index or the pointer has a second definition, so the
            // interpreter's runtime index (or the pointer a use sees) need not be
            // the constant the address is lowered from.
            (
                "index defined twice",
                vec![
                    const_at(Ty::I64, 4),
                    const_at(Ty::I64, 0),
                    gep(Ty::I8, vec![3]),
                    field_store(Ty::I32, 4, 1),
                    ret(),
                ],
            ),
            (
                "pointer defined twice",
                vec![
                    const_at(Ty::I64, 4),
                    gep(Ty::I8, vec![3]),
                    gep(Ty::I8, vec![3]),
                    field_store(Ty::I32, 4, 1),
                    ret(),
                ],
            ),
        ];
        let mut failures: Vec<String> = cases
            .into_iter()
            .filter_map(|(why, tail)| {
                let module = field_pointer_module(
                    "struct_slot_gep",
                    field_struct(&[(Ty::I32, None), (Ty::I32, None)], None),
                    vec![],
                    tail,
                );
                aggregate_slot_misuse_refusal(
                    &lower_module_to_lir(&module, FuncId::new(0)),
                    2,
                    "GEP",
                )
                .err()
                .map(|e| format!("{why}: {e}"))
            })
            .collect();
        // The tuple slot `%5` of `aggregate_slot_body`, byte GEP at field 1's start.
        let tuple = module_with_body(
            "tuple_byte_gep",
            vec![Ty::I32],
            aggregate_slot_body(vec![
                InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(4) })
                    .with_result(ValueId::new(6)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I8,
                    base: ValueId::new(5),
                    indices: vec![ValueId::new(6)],
                    inbounds: true,
                })
                .with_result(ValueId::new(7)),
                field_load(Ty::I32, 7, 8),
                InstrNode::new(Inst::Return { values: vec![ValueId::new(8)] }),
            ]),
        );
        if let Err(e) =
            aggregate_slot_misuse_refusal(&lower_module_to_lir(&tuple, FuncId::new(0)), 5, "GEP")
        {
            failures.push(format!("tuple slot: {e}"));
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }

    /// A field pointer accessed at any type but its field's (another width, the
    /// same width and another type), volatile, or used as anything but the
    /// pointer of that access, including the p4 class through a field pointer:
    /// on `S { a: u8 @ 4, b: i32 @ 0 }`, offset 4 is `a`, and a 32-bit store
    /// there (where a declaration-order `b @ 4` would put it) is refused.
    #[test]
    fn a_field_pointer_used_other_than_at_its_field_type_is_refused() {
        let ret = || InstrNode::new(Inst::Return { values: vec![] });
        let ret5 = || InstrNode::new(Inst::Return { values: vec![ValueId::new(5)] });
        let i32_pair = || field_struct(&[(Ty::I32, None), (Ty::I32, None)], None);
        let volatile_load = InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: ValueId::new(4),
            volatile: true,
            align: None,
        })
        .with_result(ValueId::new(5));
        let volatile_store = InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: ValueId::new(4),
            value: ValueId::new(0),
            volatile: true,
            align: None,
        });
        let regep = InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I8,
            base: ValueId::new(4),
            indices: vec![ValueId::new(3)],
            inbounds: true,
        })
        .with_result(ValueId::new(5));
        let call_with_ptr = vec![
            InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(4)] }),
            ret(),
        ];
        // (inst, field index, struct, returns, tail after the field GEP at offset 4)
        type MisuseCase = (&'static str, usize, trust_ir::StructDef, Vec<Ty>, Vec<InstrNode>);
        let cases: Vec<MisuseCase> = vec![
            ("Load", 1, i32_pair(), vec![Ty::I64], vec![field_load(Ty::I64, 4, 5), ret5()]),
            ("Load", 1, i32_pair(), vec![Ty::I8], vec![field_load(Ty::I8, 4, 5), ret5()]),
            // Same width, other type: the walk compares types, not widths.
            ("Load", 1, i32_pair(), vec![Ty::U32], vec![field_load(Ty::U32, 4, 5), ret5()]),
            ("Store", 1, i32_pair(), vec![], vec![field_store(Ty::I64, 4, 0), ret()]),
            ("Store", 1, i32_pair(), vec![], vec![field_store(Ty::U32, 4, 0), ret()]),
            ("Load", 1, i32_pair(), vec![Ty::I32], vec![volatile_load, ret5()]),
            ("Store", 1, i32_pair(), vec![], vec![volatile_store, ret()]),
            // The pointer stored into its own field at the field's type.
            ("Store", 1, i32_pair(), vec![], vec![field_store(Ty::I32, 4, 4), ret()]),
            (
                "Return",
                1,
                i32_pair(),
                vec![Ty::Ptr],
                vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(4)] })],
            ),
            ("GEP", 1, i32_pair(), vec![], vec![regep, ret()]),
            (
                "Store",
                1,
                i32_pair(),
                vec![],
                vec![
                    InstrNode::new(Inst::Alloca { ty: Ty::Ptr, count: None, align: None })
                        .with_result(ValueId::new(5)),
                    field_store(Ty::Ptr, 5, 4),
                    ret(),
                ],
            ),
            (
                "Copy",
                1,
                i32_pair(),
                vec![],
                vec![
                    InstrNode::new(Inst::Copy { ty: Ty::Ptr, operand: ValueId::new(4) })
                        .with_result(ValueId::new(5)),
                    ret(),
                ],
            ),
            (
                "ICmp",
                1,
                i32_pair(),
                vec![],
                vec![
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::Ptr,
                        lhs: ValueId::new(4),
                        rhs: ValueId::new(4),
                    })
                    .with_result(ValueId::new(5)),
                    ret(),
                ],
            ),
            (
                "Cast",
                1,
                i32_pair(),
                vec![],
                vec![
                    InstrNode::new(Inst::Cast {
                        op: trust_ir::inst::CastOp::PtrToInt,
                        src_ty: Ty::Ptr,
                        dst_ty: Ty::I64,
                        operand: ValueId::new(4),
                    })
                    .with_result(ValueId::new(5)),
                    ret(),
                ],
            ),
            ("Call", 1, i32_pair(), vec![], call_with_ptr),
            (
                "Store",
                0,
                field_struct(&[(Ty::U8, Some(4)), (Ty::I32, Some(0))], Some((8, 4))),
                vec![],
                vec![field_store(Ty::I32, 4, 0), ret()],
            ),
        ];
        let failures: Vec<String> = cases
            .into_iter()
            .enumerate()
            .filter_map(|(row, (inst, field, def, returns, tail))| {
                let [c, g] = field_gep(3, 4, 4);
                let mut body = vec![c, g];
                body.extend(tail);
                let mut module = field_pointer_module("field_ptr_misuse", def, returns, body);
                if inst == "Call" {
                    module.func_types.push(FuncTy {
                        params: vec![Ty::Ptr],
                        returns: vec![],
                        is_vararg: false,
                        abi: None,
                    });
                    let mut callee = IrFunction::new(
                        FuncId::new(1),
                        "takes_ptr",
                        FuncTyId::new(1),
                        BlockId::new(0),
                    );
                    let mut block = Block::new(BlockId::new(0));
                    block.params.push((ValueId::new(0), Ty::Ptr));
                    block.body = vec![InstrNode::new(Inst::Return { values: vec![] })];
                    callee.blocks.push(block);
                    module.functions.push(callee);
                }
                field_pointer_misuse_refusal(
                    &lower_module_to_lir(&module, FuncId::new(0)),
                    4,
                    field,
                    inst,
                )
                .err()
                .map(|e| format!("row {row}: {e}"))
            })
            .collect();
        assert!(failures.is_empty(), "{} rows:\n{}", failures.len(), failures.join("\n"));
    }

    /// A field pointer passed along a CFG edge escapes the walk's reach: refused at
    /// the branch.
    #[test]
    fn a_field_pointer_passed_as_a_block_argument_is_refused() {
        let [c, g] = field_gep(3, 4, 4);
        let mut module = field_pointer_module(
            "field_ptr_br_arg",
            field_struct(&[(Ty::I32, None), (Ty::I32, None)], None),
            vec![],
            vec![
                c,
                g,
                InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![ValueId::new(4)] }),
            ],
        );
        let mut next = Block::new(BlockId::new(1));
        next.params.push((ValueId::new(5), Ty::Ptr));
        next.body =
            vec![field_store(Ty::I32, 5, 0), InstrNode::new(Inst::Return { values: vec![] })];
        module.functions[0].blocks.push(next);
        if let Err(e) =
            field_pointer_misuse_refusal(&lower_module_to_lir(&module, FuncId::new(0)), 4, 1, "Br")
        {
            panic!("{e}");
        }
    }
}
