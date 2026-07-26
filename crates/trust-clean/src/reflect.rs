// trust-clean/reflect.rs: the type-reflection functor R (scalar + product fragment).
//
// R lifts a Trust type into a Clean (Lean-style) dependent-type CIC `ProofTerm`
// (see docs/PLAN-clean-dependent-type-reflection.md). It replaces the lossy
// `_ => Sort::Int` collapse in `SortFromTy::from_ty`
// (crates/trust-types/src/formula/sort.rs:34) at the reflection boundary:
//
//   * S0 (scalars/pointers): `Bool`/`Int`/`BitVec`/`RawPtr`/`Bv` -> `Trust.Sort.*`
//     carrier constants.
//   * M2 (products/sequences): tuples and structs -> right-nested
//     `Trust.Sort.Prod` products terminated by `Trust.Sort.Unit`; fixed-size
//     arrays -> `Trust.Sort.Vec elem <len>` (length as a `Trust.Nat` index);
//     slices -> `Trust.Sort.Slice elem`. These cases recurse through `reflect_ty`,
//     so a composite containing a non-reflectable component (e.g. a struct with
//     a `float` field) FAILS CLOSED transitively with that component's error.
//   * Everything else (Ref/Closure/FnPtr/Dynamic/Coroutine/Never/Float/...) still
//     fails closed with a distinct `ReflectError` (refs/closures land in M5;
//     a real IEEE-754 float carrier lands in M6).
//
// `Trust.Sort.Prod` is a NON-dependent product, which is exactly right for Rust
// ADTs (a struct's field types do not depend on field values). Value-dependent
// Sigma is a separate concern for refinement/spec types (plan M3).
//
// IMPORTANT soundness note: `from_ty` maps `Ty::Float{width} -> Sort::BitVec`,
// aliasing IEEE-754 floats onto 2's-complement bitvectors. `reflect_ty` does NOT
// repeat this — it fails closed on `Ty::Float` until a real float carrier lands.
//
// The Clean kernel `KernelContext` starts empty and resolves `Const` names only
// against itself, so `carrier_context()` declares exactly the carriers R emits,
// making reflected `ProofTerm`s type-check under `infer_type`/`check_proof`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// EXPANDED TRUST TYPES — the `#[refine("φ")]` refinement-type IR (a
// `(variable, predicate)` pairing), reflected to the dependent SUBSET carrier.
use trust_types::{
    FnSig, Formula, FunctionSpec, Sort, Ty, TypeRefinementContract, VerifiableFunction,
};

use crate::kernel_check::{KernelContext, ProofTerm, shift};

// ---------------------------------------------------------------------------
// Carrier vocabulary
// ---------------------------------------------------------------------------

/// Carrier constant for `Bool`.
pub const CARRIER_BOOL: &str = "Trust.Sort.Bool";
/// Carrier constant for `Int` (and the intentional pointer-as-integer model).
pub const CARRIER_INT: &str = "Trust.Sort.Int";
/// Width-indexed carrier for `BitVec`: `Trust.Sort.BitVec : Trust.Nat -> Trust.SortTy`.
pub const CARRIER_BITVEC: &str = "Trust.Sort.BitVec";
/// Nullary carrier for the unit / empty product.
pub const CARRIER_UNIT: &str = "Trust.Sort.Unit";
/// Binary product carrier: `Trust.Sort.Prod : SortTy -> SortTy -> SortTy`.
pub const CARRIER_PROD: &str = "Trust.Sort.Prod";
/// Length-indexed vector carrier: `Trust.Sort.Vec : SortTy -> Nat -> SortTy`.
pub const CARRIER_VEC: &str = "Trust.Sort.Vec";
/// Slice carrier (dynamically sized): `Trust.Sort.Slice : SortTy -> SortTy`.
pub const CARRIER_SLICE: &str = "Trust.Sort.Slice";
/// Function-arrow carrier: `Trust.Sort.Fn : SortTy -> SortTy -> SortTy`. The
/// carriers form a Tarski-style universe of type *codes* (every carrier is a
/// term of `Trust.SortTy`), so a function type is the code `Fn dom cod`, not a
/// raw kernel `Pi`. The kernel `Pi` is reserved for genuine dependent binding
/// (carrier declarations, and M3 spec antecedents).
pub const CARRIER_FN: &str = "Trust.Sort.Fn";
/// COVERAGE-AGENDA #2 (raw pointers) — the SortTy *code* for a BARE raw pointer
/// (`*const T` / `*mut T`) that is NOT a transparent smart-pointer wrapper. It
/// decodes (`decode_el_code`) to the registered SHALLOW opaque-address inductive
/// [`PTR_INDUCTIVE`] (`Trust.Ptr`), a single-constructor `Trust.Ptr { addr : Int }`
/// — an abstract pointer ADDRESS with NO value model for the pointee. A bare-ptr
/// value/return inhabits by `Trust.Ptr.mk 0` (the null address), grounding the
/// dominant clone/Default/Debug contracts that never dereference. This is
/// DELIBERATELY a distinct carrier from `CARRIER_INT`: a raw pointer is no longer
/// silently identified with its address integer, so a dereference/offset that READS
/// THROUGH the pointer has no faithful integer value and stays FAIL-CLOSED (the
/// points-to model is deferred). Address arithmetic still works because MIR emits an
/// explicit `Cast(ptr → usize)` first, operating on the resulting `Int` local.
pub const CARRIER_PTR: &str = "Trust.Sort.Ptr";
/// The registered Clean inductive a bare raw pointer's [`CARRIER_PTR`] code decodes
/// to: a single-constructor struct `Trust.Ptr` with one `addr : Int` field (the
/// abstract address). Registered through the SAME modulo-3 `register_adt_carriers`
/// path as a non-generic struct (constructor `Trust.Ptr.mk : Int → Trust.Ptr`,
/// kernel-derived projection + recursor); the `Int` address field is axiom-free, so
/// NO 4th axiom is introduced. Inhabited by `Trust.Ptr.mk (Int.ofNat 0)`.
pub const PTR_INDUCTIVE: &str = "Trust.Ptr";
/// COVERAGE-AGENDA #4 (Formatter/Debug opaque-sink SHIM) — the SortTy *code* for an
/// abstract WRITER SINK: a `dyn`-trait field NESTED inside a struct/enum (the
/// canonical case being `core::fmt::Formatter`'s `buf : &mut dyn core::fmt::Write`,
/// but any nested trait-object field collapses here). It decodes (`decode_el_code`)
/// to the registered nullary opaque inductive [`SINK_INDUCTIVE`] (`Trust.Sink`).
///
/// WHY a CODE distinct from `Trust.Dyn.*`: a bare `dyn Trait` PARAMETER reflects to
/// the Pi-bound opaque type VARIABLE `Trust.Dyn.<trait>` (a `Sort 1` type abstracted
/// into an outer `Π(_ : Type)` binder) — the more-precise model, and unchanged. But
/// a `dyn` field INSIDE a struct cannot be Pi-bound as a struct type parameter (an
/// existential, not a generic), so today such a struct fails closed to the anonymous
/// `Prod`/whole-param-`Trust.Opaque` over-approximation, and the `dyn`-in-`Formatter`
/// plumbing POISONS the struct's grounding even though the writer sink is
/// faithfulness-NEUTRAL (a `Debug`/`Display::fmt` value contract says nothing about
/// the bytes emitted to the sink). Collapsing the nested `dyn` to the CONCRETE,
/// CLOSED `Trust.Sink` code lets the carrying struct (`core::fmt::Formatter`) register
/// as a REAL named inductive whose `buf` field is the opaque atom — so the dominant
/// 100%-boilerplate `fmt` functions GROUND instead of failing closed.
///
/// SOUNDNESS: `Trust.Sink` is INHABITED (a trait object always is — sound for
/// inhabitation) but STRUCTURELESS (a single nullary constructor, no value/integer
/// model), so an obligation that reads THROUGH the sink (the emitted bytes) has no
/// faithful value and stays FAIL-CLOSED, exactly like `Trust.Ptr`'s missing pointee
/// model. It is a CLOSED type (not a type variable), so no parametricity quantifier
/// is needed, yet an integer fact about a `Trust.Sink`-typed value is still
/// unprovable (it is not `Int`). The atom is axiom-free (a nullary inductive like
/// `Unit`), so the carrier passes the modulo-3 `axiom_deps` gate with NO 4th axiom.
pub const CARRIER_SINK: &str = "Trust.Sort.Sink";
/// The registered Clean inductive a nested-`dyn` writer-sink field's [`CARRIER_SINK`]
/// code decodes to: a single nullary-constructor opaque inductive `Trust.Sink`
/// (constructor `Trust.Sink.mk : Trust.Sink`, NO fields — a pure abstract atom, like
/// `Unit`). Registered through the SAME modulo-3 `register_adt_carriers` path as any
/// non-generic struct, introducing NO 4th axiom (a field-less inductive is
/// axiom-free). Inhabited by `Trust.Sink.mk` — the witness for a `Formatter` whose
/// `buf : dyn Write` is non-load-bearing.
pub const SINK_INDUCTIVE: &str = "Trust.Sink";
/// Prefix for a NAMED struct inductive carrier. A non-generic struct `Wrapper`
/// registers as the REAL single-constructor Clean inductive `Trust.Adt.Wrapper`
/// (ctor `Trust.Adt.Wrapper.mk`, kernel-derived projections + recursor), rather
/// than the anonymous right-nested `Trust.Sort.Prod` it falls back to. See
/// [`reflect_struct`] / [`AdtCarrier`].
pub const ADT_PREFIX: &str = "Trust.Adt.";

/// CLOSURE RECORD (M5) — prefix for the NAMED single-constructor Clean inductive
/// (a dependent RECORD) a closure `Ty::Closure { name, upvars, .. }` reflects to. A
/// closure named `c` registers as `Trust.Closure.<c>` — the closure as its captured
/// ENVIRONMENT paired with its CALL signature: a single-constructor inductive
///
/// ```text
///   Trust.Closure.<c> (A : Type) (B : Type) :=
///     mk (env : <captured-env carrier>) (call : A → B)
/// ```
///
/// parameterized over two `Type` variables `A`/`B` (the call's domain/codomain).
/// The `env` field is the right-nested `Trust.Sort.Prod` of the closure's upvar
/// carriers — the REAL captured environment. The `call` field is a GENUINE kernel
/// `Pi` `A → B` (a real dependent function type, rooted in the 3 — the kernel has
/// `Pi` natively), with `A`/`B` left as quantified `Type` parameters because the
/// extractor's `Ty::Closure` carries only `upvars`, NOT the call signature. This is
/// the "quantified Sigma over the call type" the plan asks for: the call's
/// domain/codomain are EXISTENTIALLY abstracted as the inductive's two `Type`
/// parameters (`Σ(A:Type)(B:Type). (A → B)`), realized as the parameterization
/// rather than a free const. It registers through the SAME modulo-3
/// `register_adt_carriers`/`add_inductive` path as a parameterized struct, so
/// `axiom_deps` stays EMPTY (NO 4th axiom — `Prod`/`Unit`/the upvar scalar carriers
/// and the kernel `Pi` are all axiom-free).
pub const CLOSURE_PREFIX: &str = "Trust.Closure.";

// ===========================================================================
// TYPE-ZOO CLOSE (additive) — six remaining Rust type families as REAL Clean
// dependent types, axiom_deps ⊆ {propext, Quot.sound, Classical.choice}. Each
// carrier registers through the SAME modulo-3 kernel paths the committed
// 48/49 base uses (`register_adt_carriers` / `register_dyn_carriers` / native
// `Pi`/`Type`), so NO 4th axiom is introduced. These are ADDITIVE: they leave
// `reflect_ty`'s existing cases (and mirsem / vc_refute) untouched, surfacing
// the new structure through dedicated reflection entry points + corpus probes.
// ===========================================================================

/// TYPE-ZOO #1 (CONST GENERICS) — the LENGTH-INDEXED vector inductive
/// `Trust.ArrayN (T : Type) : Trust.Nat → Type`. A fixed-size array `[T; N]`
/// reflects to `Trust.ArrayN (decode T) N` with `N` a REAL `Trust.Nat` value (the
/// const generic as a genuine dependent INDEX), NOT the length-erased `Slice`/
/// `List` model `reflect_ty` falls back to. It registers as a real inductive with
/// ONE `Type` PARAMETER (`T`) and ONE `Nat` INDEX (the length) — a genuine indexed
/// family, two constructors `nil : ArrayN T 0` and `cons : T → ArrayN T n →
/// ArrayN T (n+1)` (the standard length-indexed-vector shape) — so the length is a
/// first-class value the kernel tracks. Registered through the modulo-3
/// `register_arrayn_carrier` path (axiom_deps EMPTY — `Nat`/`Type`/the two
/// constructors are all axiom-free); NO 4th axiom.
pub const CARRIER_ARRAYN: &str = "Trust.ArrayN";
/// The `nil` constructor of [`CARRIER_ARRAYN`]: `nil : Π(T:Type). ArrayN T 0`.
pub const ARRAYN_NIL: &str = "Trust.ArrayN.nil";
/// The `cons` constructor of [`CARRIER_ARRAYN`]:
/// `cons : Π(T:Type)(n:Nat). T → ArrayN T n → ArrayN T (n+1)`.
pub const ARRAYN_CONS: &str = "Trust.ArrayN.cons";

/// TYPE-ZOO #4 (HRTBs) — the erased REGION/lifetime carrier `Trust.Region : Type`.
/// A lifetime `'a` carries no value content (it is erased at MIR), so it reflects
/// to this opaque-but-CLOSED `Type` atom (a single nullary-constructor inductive,
/// like `Trust.Sink`). A higher-ranked bound `for<'a> Fn(&'a T)` is the UNIVERSAL
/// quantifier over the region: `Π(r : Trust.Region) → (the fn arrow over r)` — a
/// genuine kernel `Pi` (rooted in the 3). Registered modulo 3 via the nullary
/// `register_adt_carriers` path (axiom-free; NO 4th axiom).
pub const CARRIER_REGION: &str = "Trust.Region";
/// The registered inductive a [`CARRIER_REGION`] decodes to: a single nullary
/// constructor `Trust.Region.mk : Trust.Region` (an erased lifetime atom, like
/// `Unit`). Axiom-free — NO 4th axiom.
pub const REGION_INDUCTIVE: &str = "Trust.Region";

/// NEVER (`!`) — the standalone bottom/never type reflects to the EMPTY INDUCTIVE
/// carrier `Trust.Never` (the Clean analogue of `False`/`Empty`): a `Type` with
/// ZERO constructors. Reflecting the TYPE is unconditional — a genuine Clean
/// dependent type rooted in EXACTLY the 3 foundational axioms (an empty inductive
/// is axiom-free, its auto-derived recursor `Trust.Never.rec` is the eliminator
/// `Π(motive : Never → Sort u)(t : Never). motive t`, the constructive
/// "ex falso quodlibet"). INHABITATION stays FAIL-CLOSED *by construction*: an
/// empty inductive has NO constructor, so `default_inhabitant_term` finds no `.mk`
/// and returns `None` — a never-returning `fn() -> !` cannot be inhabited, which is
/// correct. So the never TYPE is structural-modulo-3 (closing the last scalar gap —
/// the `!`/`never` corpus entry), while the VALUE stays unreachable.
///
/// `reflect_ty(Ty::Never)` itself stays `Err(NeverType)` — the conservative
/// COMPOSITION floor — so a `[!; N]` / `(bool, !)` / `!`-capturing closure /
/// refinement-over-`!` still fails its WITNESS-binding closed (those need an
/// inhabitant, and `!` has none). The standalone never TYPE is classified
/// structural through the dedicated [`crate::clean_ground::register_never_carrier`]
/// real-kernel gate, NOT through the composition carrier.
pub const CARRIER_NEVER: &str = "Trust.Sort.Never";
/// The EMPTY inductive a [`CARRIER_NEVER`] denotes: `Trust.Never : Type` with NO
/// constructors (the Clean analogue of `False`/`Empty`). Registered modulo 3 via
/// [`crate::clean_ground::register_never_carrier`] (inductive + auto-derived
/// recursor `axiom_deps` EMPTY — NO 4th axiom). Uninhabited by construction.
pub const NEVER_INDUCTIVE: &str = "Trust.Never";

/// TYPE-ZOO #2 (impl Trait, RPIT/TAIT) — prefix for an OPAQUE return type
/// `impl Trait`. Like `dyn Trait`, an `impl Trait` opaque return is an EXISTENTIAL
/// "∃ a concrete carrier `T : Type` together with the trait-method witness for `T`",
/// so it reflects to the SAME `Sigma (T:Type), Vtable_<trait> T` existential a `dyn`
/// does (`reflect_dyn` / `register_dyn_carriers`), under a distinct stable name so an
/// `impl Trait` and a `dyn Trait` over the same trait do not collide. The DIFFERENCE
/// from `dyn` is only erasure-site (return vs. dispatch); the dependent-type model is
/// identical (the existential), rooted in the 3.
pub const IMPL_TRAIT_PREFIX: &str = "Trust.Impl.";

// --- GOAL-ITEM #3: structured IEEE-754 float carriers -----------------------
//
// A `Ty::Float{width}` is NOT aliased onto a flat `BitVec width` (a bare bitvector
// is the bit pattern, not the IEEE-754 *structure*). Instead it reflects to a REAL
// single-constructor Clean inductive `Trust.Float32`/`Trust.Float64` that decomposes
// the IEEE-754 layout into NAMED, kernel-projectable fields:
//
//   f32 → Trust.Float32 { sign : Bool, exponent : BitVec 8,  mantissa : BitVec 23 }
//   f64 → Trust.Float64 { sign : Bool, exponent : BitVec 11, mantissa : BitVec 52 }
//
// These register through the SAME P1 `register_adt_carriers`/`add_inductive` path as
// any non-generic struct: a `Trust.FloatN.mk` constructor, kernel-derived named
// projections (`Trust.Float32.sign`, …) + recursor, all modulo exactly 3 axioms (the
// fields decode to `Bool`/`Int`, both axiom-free prelude inductives — NO 4th axiom, NO
// opaque declaration). A float value thus reflects with its real IEEE structure
// (sign/exponent/mantissa accessible), not an opaque placeholder and not a flat BitVec.
//
// PHASE 1 (this) is the STRUCTURED BIT MODEL + the IEEE-754 classification predicates
// (`isNaN`/`isInf`/`isZero`/`isSubnormal`, built as Clean defs over the structure; see
// `clean_ground`). The real-number VALUE interpretation (mantissa→rational, the value a
// float denotes) and rounding-correct arithmetic ops (round-to-nearest-even add/mul/div)
// are the DEFERRED Phase-2 refinement — they are NOT faked here: a float-VALUE-arithmetic
// safety/overflow VC that needs value semantics fails closed (sound). The TYPE, however,
// is now structural (0 opaque for floats), which is goal-item #3's core.

/// The Clean inductive name for an IEEE-754 float of `width` bits
/// (`Trust.Float32`/`Trust.Float64`). `None` for an unsupported width.
#[must_use]
pub fn float_inductive_name(width: u32) -> Option<&'static str> {
    match width {
        32 => Some("Trust.Float32"),
        64 => Some("Trust.Float64"),
        _ => None,
    }
}

/// The single constructor name for the float inductive of `width` bits
/// (`Trust.Float32.mk`/`Trust.Float64.mk`). `None` for an unsupported width.
#[must_use]
pub fn float_ctor_name(width: u32) -> Option<String> {
    float_inductive_name(width).map(|n| format!("{n}.mk"))
}

/// The IEEE-754 (exponent_bits, mantissa_bits) decomposition for a float of `width`
/// bits: f32 = (8, 23), f64 = (11, 52). The sign is always 1 bit (a `Bool`), so the
/// total is `1 + exponent_bits + mantissa_bits = width`. `None` for an unsupported
/// width (the caller then fails closed, never aliasing onto a flat BitVec).
#[must_use]
pub fn ieee754_layout(width: u32) -> Option<(u32, u32)> {
    match width {
        32 => Some((8, 23)),
        64 => Some((11, 52)),
        _ => None,
    }
}

/// GOAL-ITEM #3 (VALUE) — the IEEE-754 exponent BIAS for a float of `width` bits:
/// `2^(exponent_bits − 1) − 1` (127 for f32, 1023 for f64). The bias is what the
/// VALUE interpretation subtracts from the stored (biased) exponent field to recover
/// the true power-of-two scale of a normal float. `None` for an unsupported width
/// (the caller then fails closed). A WRONG bias here would make the value model
/// denote the wrong rational — the value-anchor tests pin the correct bias and a
/// wrong-bias claim must fail closed (`KernelRejected`).
#[must_use]
pub fn ieee754_bias(width: u32) -> Option<u64> {
    let (exp_bits, _mant_bits) = ieee754_layout(width)?;
    Some((1u64 << (exp_bits - 1)) - 1)
}

/// The carrier universe of reflected sorts.
pub const CARRIER_SORT_TY: &str = "Trust.SortTy";
/// The numeral universe (BitVec widths and Vec lengths).
pub const CARRIER_NAT: &str = "Trust.Nat";

/// The BitVec widths reflected scalars commonly use (all `<= MAX_DECLARED_NAT`,
/// so they are kernel-resolvable in `carrier_context()`).
pub const REFLECTED_BITVEC_WIDTHS: &[u32] = &[8, 16, 32, 64, 128];

/// Largest numeral `carrier_context()` declares. `reflect_bitvec`/array-length
/// reflection emit `Const("<n>")` for any `n`, but only numerals `<= this` are
/// declared; a larger width/length yields a structurally well-formed term whose
/// numeral the kernel will reject until the context is extended.
pub const MAX_DECLARED_NAT: u64 = 128;

// --- M3: predicate (proposition) vocabulary --------------------------------
//
// Propositions reflect into kernel `Prop` (`Sort(0)`). Integer-sorted operands
// reflect into a single `Trust.Int` term universe. These carriers are declared
// in `carrier_context()` so reflected predicates type-check to `Prop`.

/// The integer term universe (operands of comparisons / arithmetic).
pub const PROP_INT: &str = "Trust.Int";
/// Nullary `true` proposition (`: Prop`).
pub const PROP_TRUE: &str = "Trust.Prop.True";
/// Nullary `false` proposition (`: Prop`).
pub const PROP_FALSE: &str = "Trust.Prop.False";
/// Logical negation (`Prop -> Prop`).
pub const PROP_NOT: &str = "Trust.Prop.Not";
/// Conjunction (`Prop -> Prop -> Prop`).
pub const PROP_AND: &str = "Trust.Prop.And";
/// Disjunction (`Prop -> Prop -> Prop`).
pub const PROP_OR: &str = "Trust.Prop.Or";
/// Implication (`Prop -> Prop -> Prop`).
pub const PROP_IMPLIES: &str = "Trust.Prop.Implies";
/// Equality predicate (`Trust.Int -> Trust.Int -> Prop`).
pub const PROP_EQ: &str = "Trust.Prop.Eq";
/// A boolean result asserted true: `BoolTrue b` grounds to `@Eq Bool b Bool.true`.
/// Lets `#[ensures(|ret| ret)]`-style boolean-result postconditions ground over
/// the real `Bool` return type (not the integer `Eq`, which would type-mismatch).
pub const PROP_BOOL_TRUE: &str = "Trust.Prop.BoolTrue";
/// Prefix for a struct-field projection carrier: `Trust.Proj.<i> base` denotes the
/// `i`-th field of `base`, grounding to a structural `Prod` projection. Lets a
/// contract reference a parameter's field (`p.value`). Used when the parameter binds
/// at the ANONYMOUS `Prod` carrier (a struct that did NOT register as a named
/// inductive — the `Prod`/`Unit` floor).
pub const PROJ_PREFIX: &str = "Trust.Proj.";
/// Prefix for a NAMED struct-field projection carrier: `Trust.ProjN.<inductive>.<i>
/// base` denotes the `i`-th field of `base`, grounding to the kernel-native NAMED
/// projection of the registered inductive `<inductive>` (`Expr::proj(<inductive>, i,
/// base)`), NOT the anonymous `Prod` projection. Emitted by `reflect_contract` when a
/// parameter's type reflects to a REGISTERED named/parameterized inductive
/// (`Trust.Adt.<Name>` — the param binds at `<Name> T…`, so a `Prod` projection would
/// be a universe/structure mismatch). This keeps a contract's field reference
/// (`w.count`) in lockstep with the named binding (`w : Wrapper T`) so it type-checks.
pub const PROJN_PREFIX: &str = "Trust.ProjN.";
/// `<` predicate (`Trust.Int -> Trust.Int -> Prop`).
pub const PROP_LT: &str = "Trust.Prop.Lt";
/// `<=` predicate.
pub const PROP_LE: &str = "Trust.Prop.Le";
/// `>` predicate.
pub const PROP_GT: &str = "Trust.Prop.Gt";
/// `>=` predicate.
pub const PROP_GE: &str = "Trust.Prop.Ge";
/// Integer addition (`Trust.Int -> Trust.Int -> Trust.Int`).
pub const INT_ADD: &str = "Trust.Int.add";
/// Integer subtraction.
pub const INT_SUB: &str = "Trust.Int.sub";
/// Integer multiplication.
pub const INT_MUL: &str = "Trust.Int.mul";
/// Integer division.
pub const INT_DIV: &str = "Trust.Int.div";
/// Integer remainder.
pub const INT_REM: &str = "Trust.Int.rem";
/// Integer negation (`Trust.Int -> Trust.Int`).
pub const INT_NEG: &str = "Trust.Int.neg";
/// Dependent-pair (Sigma) carrier for postconditions:
/// `Trust.Sigma : Π(A : Type) → (A → Prop) → Type`. A function satisfying a
/// contract returns a `Trust.Sigma R(ρ) (λy. Q)` — a value paired with a proof
/// of the postcondition. (`ProofTerm` has no native Σ; this is the carrier.)
pub const CARRIER_SIGMA: &str = "Trust.Sigma";
/// Tarski decode `Trust.El : Trust.SortTy → Type`: turns a reflected type *code*
/// (a term of `SortTy`) into an actual kernel type, so a contract can bind a
/// parameter `x : El (R τ)` of any reflectable type. Integer-typed parameters
/// short-circuit to the `Trust.Int` term universe (so the integer predicate
/// vocabulary applies); other types decode opaquely through `El`.
pub const CARRIER_EL: &str = "Trust.El";

/// Integer literals `carrier_context()` declares (`Trust.Int.lit.<n>` : Trust.Int).
/// `reflect_int_term` emits `Const("Trust.Int.lit.<n>")` for any literal, but
/// only these are declared; other literals need the context extended (same
/// finite-context caveat as BitVec widths).
pub const DECLARED_INT_LITS: &[i128] = &[-1, 0, 1, 2, 3, 4, 5, 8, 10, 16, 32, 64, 100];

/// The carrier name for an integer literal `n` (`Trust.Int.lit.<n>`).
#[must_use]
pub fn int_lit_name(n: i128) -> String {
    format!("Trust.Int.lit.{n}")
}

// ---------------------------------------------------------------------------
// Opaque type variables: generic params (`TyKind::Param`) and trait objects
// (`Ty::Dynamic`)
// ---------------------------------------------------------------------------
//
// A generic parameter `T` in `fn f<T>(x: T) -> T` is NOT a placeholder scalar:
// reflecting it as `Int` would be UNSOUND (the kernel does not gate reflection
// faithfulness, so a VC asserting an integer fact over a `T`-typed value would
// falsely prove). Instead `T` reflects as a Pi-BOUND opaque type variable: the
// contract `fn f<T>(x: T) -> T` becomes `∀ (T : Type), Π(x : T) → … (T)`. The
// param binder's domain is the type universe `Type` (`Sort 1`) — `T : Type` — and
// `T` is genuinely opaque (no axiom about its structure), so a generic contract
// introduces NO new axiom and an integer fact about a `T`-typed value stays
// unprovable (parametricity).
//
// A TRAIT OBJECT `dyn Trait` (`Ty::Dynamic { trait_name }`) reflects through the
// SAME machinery as a fresh opaque type variable `Trust.Dyn.<trait_name>`. This is
// a SOUND over-approximation: a trait object is existential (`∃ D : Type with
// Trait, …`), but the reflected contract universally quantifies the opaque carrier
// (`∀ (D : Type), …`). Proving the (param-independent) integer safety VCs for ALL
// types `D` implies them for the specific `dyn Trait`, since the trait object never
// appears in the integer safety VCs and `∀` is STRONGER than the `∃` it covers.
// The carrier stays opaque (no axiom about `Trait`'s methods/structure), so
// modulo-3 is unchanged and integer facts about a `dyn`-typed value stay unprovable.
//
// The binder universe is `Type` (`Sort 1`, not `Prop`/`Sort 0`): a type variable
// IS a `Type`, and binding at `Sort 1` lets the variable serve directly as a
// `Trust.Sigma` return carrier (`Sigma : Π(A : Sort 1) → …`), which is what makes a
// generic/`dyn` RETURN type ground (the return carrier is the bound type var itself).

/// The `kind` string `trust-mir-extract` stamps on a generic type parameter
/// (`crates/trust-mir-extract/src/ty_convert.rs`: `TyKind::Param(param)` →
/// `unsupported_ty("TyKind::Param", …)`).
pub const PARAM_KIND: &str = "TyKind::Param";

/// Prefix for a reflected generic type-parameter binder. A param whose stable
/// identity is `id` (e.g. `T/#0`) reflects as the free const `Trust.Param.<id>`,
/// which `reflect_contract`/`reflect_function_spec` abstract into an outermost
/// `Π(<id> : Type)` binder. The full `name/#index` is the identity: distinct
/// params (even same-named) get distinct binders; the SAME param maps to the SAME
/// const everywhere in one function, so `Π(T) … Π(x : T)` binds correctly.
pub const PARAM_PREFIX: &str = "Trust.Param.";

/// Prefix for a reflected TRAIT-OBJECT (`dyn Trait`) opaque type variable. A
/// `Ty::Dynamic { trait_name }` reflects as the free const `Trust.Dyn.<trait_name>`,
/// collected + Pi-wrapped OUTERMOST as `Π(<dyn> : Type)` EXACTLY like a generic
/// param. This is SOUND as an over-approximation: the contract becomes
/// `∀ (D : Type), …` (a fresh opaque type variable per distinct trait), and proving
/// the param-independent integer safety VCs for ALL types `D` implies them for the
/// specific existential `dyn Trait`. The trait object never appears in the integer
/// safety VCs, and the universally-quantified contract is STRONGER than the
/// existential it over-approximates, so the verdict is conservative. The type var
/// stays genuinely opaque (no axiom, modulo-3 unchanged); an integer fact about a
/// `dyn`-typed value stays unprovable (parametricity), exactly as for a generic param.
pub const DYN_PREFIX: &str = "Trust.Dyn.";

/// Prefix for a SYNTHETIC opaque type variable standing in for a PARAMETER whose
/// type is a composite (tuple/struct/slice/array) that NESTS an opaque type variable
/// — e.g. `f : &mut core::fmt::Formatter` whose body holds a `&mut dyn Write` field,
/// or a `(T, u8)` tuple. There is no faithful `Trust.SortTy` carrier for such a type
/// (`Prod`/`Slice` cannot take a `Sort 1` element, and the nested var's `El`-decode
/// has no real-kernel grounding), so the WHOLE parameter binds at a fresh opaque
/// type variable `Trust.Opaque.<param>` (Pi-bound at `Type` like any other type
/// variable). This is the SAME sound over-approximation as a bare `dyn`: the contract
/// becomes `∀ (f_ty : Type), Π(f : f_ty) → …`, which is STRONGER than the specific
/// type it covers — proving the (param-independent) integer safety VCs for ALL `f_ty`
/// implies them for the real type. The carrier is genuinely opaque (no axiom about
/// the struct's fields), so modulo-3 is unchanged, and a contract that actually needs
/// the parameter's internal structure (e.g. projecting a field) fails closed — never
/// falsely proves. Keyed per-parameter so distinct composite params get distinct
/// binders; only used in PARAMETER position (a composite-with-var RETURN stays
/// fail-closed, since you cannot conjure a value of an opaque return type).
pub const OPAQUE_PREFIX: &str = "Trust.Opaque.";

/// Recover a generic type parameter's STABLE identity from the `detail` string
/// `trust-mir-extract` stamps: `"generic parameter <name>/#<index> needs
/// monomorphization"` (the `ParamTy` `Debug` is `{name}/#{index}`,
/// `compiler/rustc_middle/src/ty/structural_impls.rs`). Returns the `<name>/#<index>`
/// token (e.g. `T/#0`) — the full name+index, so two distinct params never alias.
/// Falls back to the whole `detail` if the surrounding text drifts (still stable
/// per-param, just less pretty).
#[must_use]
pub fn param_ident_from_detail(detail: &str) -> String {
    detail
        .strip_prefix("generic parameter ")
        .and_then(|rest| rest.strip_suffix(" needs monomorphization"))
        .unwrap_or(detail)
        .trim()
        .to_string()
}

/// The carrier const name for the generic type parameter whose stable identity is
/// `ident` (`Trust.Param.<ident>`).
#[must_use]
pub fn param_const_name(ident: &str) -> String {
    format!("{PARAM_PREFIX}{ident}")
}

/// Ident namespace (under [`PARAM_PREFIX`]) for an UNRESOLVED `Ty::Datatype`
/// by-name back-reference — the dump-compaction spelling `Ty::Datatype { name,
/// variants: [] }` `trust-mir-extract`'s `recursive_datatype_ref` emits when a
/// recursive ADT (`clean_kernel::Expr`, `Level`, …) is seen again at extraction
/// depth. When [`reflect_verifiable_function`]'s pre-resolution cannot recover the
/// full definition (no defining occurrence among the function's own locals — or
/// the reference is the datatype's own recursive occurrence inside its defining
/// variant list), the value reflects at the opaque, Pi-bound type variable
/// `Trust.Param.@datatype::<name>` — EXACTLY the generic-parameter treatment
/// (`Ty::Unsupported`/`PARAM_KIND`), the fail-closed convention this file already
/// audits:
///
///   * the contract universally quantifies it (`free_type_var_consts` collects the
///     `Trust.Param.*` const; `reflect_contract` Pi-binds it OUTERMOST at `Type`) —
///     a sound over-approximation, STRONGER than the concrete recursive type;
///   * NO structure is fabricated: the carrier has no fields, no constructors, no
///     axioms — an obligation needing the datatype's structure fails closed
///     (`carrier_mentions_param` keeps it out of registered inductives,
///     `code_mentions_type_var` routes a composite that nests it to the
///     `Trust.Opaque.<param>` whole-parameter over-approximation);
///   * a RETURN of the bare back-reference grounds as a `Sigma` over the bound
///     variable but can never be INHABITED by fiat (you cannot conjure a value of
///     an opaque type) — fail-closed, never a false certificate.
///
/// Keyed on the datatype's full extraction name, UNSANITIZED (like the `T/#0`
/// param idents): distinct datatypes NEVER alias one variable, and every
/// occurrence of the SAME datatype in one contract shares one binder. The `@`
/// sigil keeps the namespace disjoint from real generic-param idents (which are
/// `name/#index`-shaped) and from `Trust.Opaque.<param>` synthetic names.
pub const DATATYPE_BACKREF_IDENT_PREFIX: &str = "@datatype::";

/// The opaque type-variable const for an unresolved `Ty::Datatype` by-name
/// back-reference to `name` (`Trust.Param.@datatype::<name>`).
#[must_use]
pub fn datatype_backref_const_name(name: &str) -> String {
    param_const_name(&format!("{DATATYPE_BACKREF_IDENT_PREFIX}{name}"))
}

/// The carrier const name for the trait object over `trait_name` (`Trust.Dyn.<name>`).
///
/// A `dyn Trait` reflects to THIS const, which now names a REGISTERED Clean
/// **definition** — a genuine closed dependent type
/// `Trust.Dyn.<trait> := Sigma Type (Trust.Dyn.Vtable.<trait>)` — NOT a free opaque
/// type variable. The trait path is sanitized so the name is a stable, kernel-legal
/// `Name` (same mangling as [`adt_inductive_name`]); two `dyn Trait` occurrences of
/// the SAME trait share the const (and the registered existential).
#[must_use]
pub fn dyn_const_name(trait_name: &str) -> String {
    sanitize_dotted_segment(DYN_PREFIX, trait_name)
}

/// Sanitize `name` into a single dotted kernel-`Name` segment under `prefix`
/// (Rust path separators `::` and any non-identifier byte collapse to `_`, trailing
/// collapse underscores trimmed). The shared mangler behind [`adt_inductive_name`],
/// [`dyn_const_name`] and [`dyn_vtable_record_name`]: a const that the real kernel
/// REGISTERS (an inductive / definition) must be a legal `Name`, so `core::fmt::Write`
/// becomes `core_fmt_Write` rather than carrying raw `::` path separators the kernel
/// would mis-split.
#[must_use]
fn sanitize_dotted_segment(prefix: &str, name: &str) -> String {
    let mut s = String::with_capacity(prefix.len() + name.len());
    s.push_str(prefix);
    let mut prev_us = false;
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            s.push(ch);
            prev_us = false;
        } else if !prev_us {
            s.push('_');
            prev_us = true;
        }
    }
    while s.ends_with('_') {
        s.pop();
    }
    s
}

/// Prefix for the reflected VTABLE RECORD of a trait object — the single-constructor
/// Clean inductive `Trust.Dyn.Vtable.<trait>(T : Type)` whose fields are the trait's
/// method signatures over the (existentially-quantified) carrier `T`. The existential
/// `dyn Trait` reflects as `Sigma Type Trust.Dyn.Vtable.<trait>`: "there exists a
/// carrier `T : Type` together with the trait-method implementations for `T`".
pub const DYN_VTABLE_PREFIX: &str = "Trust.Dyn.Vtable.";

/// The vtable-record inductive name for the trait object over `trait_name`
/// (`Trust.Dyn.Vtable.<name>`), sanitized into a single kernel-legal `Name` segment.
#[must_use]
pub fn dyn_vtable_record_name(trait_name: &str) -> String {
    sanitize_dotted_segment(DYN_VTABLE_PREFIX, trait_name)
}

/// The constructor name of a vtable record (`<vtable>.mk`).
#[must_use]
pub fn dyn_vtable_ctor_name(vtable_name: &str) -> String {
    format!("{vtable_name}.mk")
}

/// A REAL trait-object reflection: the EXISTENTIAL `dyn Trait` as a genuine Clean
/// dependent type rooted in the 3 foundational axioms — **replacing** the opaque
/// free const `Trust.Dyn.<trait>` that the universal-binder over-approximation used.
///
/// A trait object `dyn Trait` is the existential "∃ a carrier type `T` together with
/// the trait-method implementations for `T`". This reflects as the dependent pair
///
/// ```text
///   Trust.Dyn.<trait>  :=  Sigma (T : Type), Trust.Dyn.Vtable.<trait> T
/// ```
///
/// where `Trust.Dyn.Vtable.<trait>` is a single-constructor (record) inductive
/// PARAMETERIZED over the carrier `T : Type`, with one field per trait method —
/// each method `m : (args) -> ret` reflecting to a field of the Pi type
/// `reflect(args) -> reflect(ret)`. `clean_ground::register_dyn_carriers` registers
/// the vtable record via `add_inductive` (auto-deriving its recursor) AND the
/// `Trust.Dyn.<trait>` definition over the prelude `Sigma`, asserting BOTH rest on
/// only the 3 foundational axioms (empty `axiom_deps`) — NO free const, NO 4th axiom.
///
/// This is a pure-data description (no `clean_kernel` dependency in `reflect.rs`),
/// mirroring [`AdtCarrier`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DynCarrier {
    /// The closed existential definition name (`Trust.Dyn.<trait>`).
    pub name: String,
    /// The vtable-record inductive name (`Trust.Dyn.Vtable.<trait>`).
    pub vtable_name: String,
    /// The vtable-record constructor name (`Trust.Dyn.Vtable.<trait>.mk`).
    pub vtable_ctor_name: String,
    /// The reflected method-signature fields of the vtable record, in trait
    /// declaration order: `(method_name, reflected method-type carrier)`. The carrier
    /// is the curried `reflect(args) -> reflect(ret)` Pi `ProofTerm` (over the bound
    /// carrier `T` where the method mentions `Self`). EMPTY when no method-signature
    /// info is available from the extractor (`Ty::Dynamic` carries only `trait_name`):
    /// the record is then the field-less single-ctor inductive (`Sigma Type Unit` — an
    /// existential over an opaque-but-QUANTIFIED carrier, rooted in the 3, NOT a free
    /// const). See [`reflect_dyn`].
    pub methods: Vec<(String, ProofTerm)>,
}

impl DynCarrier {
    /// Whether richer vtable-method modeling is present (≥1 reflected method
    /// signature). `false` for the best-sound minimal existential (`Sigma Type Unit`),
    /// which is all the current extractor (`Ty::Dynamic { trait_name }`, no method
    /// signatures) can supply.
    #[must_use]
    pub fn has_methods(&self) -> bool {
        !self.methods.is_empty()
    }
}

/// Reflect a trait object `dyn Trait` (named `trait_name`, with the optionally-known
/// method signatures `methods`) into a [`DynCarrier`] — the existential
/// `Sigma (T : Type), Vtable_<trait> T` and its vtable record.
///
/// Each method `(name, FnSig)` reflects to a vtable-record field whose carrier is the
/// curried arrow `reflect(args) -> reflect(ret)` ([`reflect_fn_sig`]); a method whose
/// signature does not reflect (a non-reflectable arg/ret) is DROPPED from the record
/// (fail-closed for that method, the existential is still sound — it just models fewer
/// methods). When `methods` is EMPTY — the only case the current `trust-mir-extract`
/// can produce, since `Ty::Dynamic` carries only the trait name — the record is
/// field-less, i.e. the BEST sound structural form `Sigma (T : Type) Unit`: an
/// existential over an opaque-but-QUANTIFIED carrier, which IS rooted in the 3 (unlike
/// a free const). Richer per-method modeling is deferred pending extractor support
/// (see the crate-level honesty note).
#[must_use]
pub fn reflect_dyn(trait_name: &str, methods: &[(String, FnSig)]) -> DynCarrier {
    let vtable_name = dyn_vtable_record_name(trait_name);
    let vtable_ctor_name = dyn_vtable_ctor_name(&vtable_name);
    let reflected_methods = methods
        .iter()
        .filter_map(|(m, sig)| reflect_fn_sig(sig).ok().map(|carrier| (m.clone(), carrier)))
        .collect();
    DynCarrier {
        name: dyn_const_name(trait_name),
        vtable_name,
        vtable_ctor_name,
        methods: reflected_methods,
    }
}

/// The type-universe an opaque type-variable binder (generic param OR trait object)
/// ranges over: `Type` (`Sort 1`). `T : Type` makes `Π(x : T)` well-formed
/// (`infer_sort_level(T) = 1`) AND lets `T` serve directly as a `Trust.Sigma` return
/// carrier (`Sigma : Π(A : Sort 1) → …`), while leaving `T` opaque. Centralized so
/// the binder domain stays consistent across reflection.
#[must_use]
pub fn reflect_param_sort() -> ProofTerm {
    ProofTerm::Sort(1)
}

/// If `ty` is a value of bare GENERIC-PARAMETER type — a generic param `T`, or a
/// transparent `&T`/`&mut T` reference whose referent is one — return the opaque
/// carrier's `Trust.Param.<id>` const name. References are transparent for type
/// reflection (`reflect_ty` reflects `&T` as its referent `reflect_ty(inner)`), so
/// `x : &T` binds at the same opaque type variable as `x : T`. Raw pointers are NOT
/// transparent here — `reflect_ty` models `*const T` as the integer address — so a
/// raw-pointer param keeps the pointer-as-integer binding and never routes here.
///
/// A trait object `dyn Trait` is DELIBERATELY NOT a type variable: it reflects to the
/// CLOSED existential dependent type `Trust.Dyn.<trait>` (`Sigma (T:Type), Vtable T`,
/// see [`reflect_dyn`] / [`dyn_object_const`]) — a real registered type rooted in the
/// 3 axioms, not a universally-abstracted opaque carrier.
fn bare_type_var(ty: &Ty) -> Option<String> {
    match ty {
        Ty::Unsupported { kind, detail } if kind == PARAM_KIND => {
            Some(param_const_name(&param_ident_from_detail(detail)))
        }
        // An UNRESOLVED `Ty::Datatype` by-name back-reference (dump compaction,
        // empty `variants`) is an opaque type variable keyed on the datatype name
        // ([`datatype_backref_const_name`]) — the generic-param treatment. This is
        // what makes a compacted recursive-ADT field a GENUINE dependent
        // constructor field (`reflect_struct`/`reflect_enum` add the ident to
        // `type_params`), a bare back-reference parameter bind at its own Pi-bound
        // variable, and a back-reference RETURN ground (but never inhabit by fiat).
        // A FULL definition (non-empty `variants`) is NOT a type variable — it
        // reflects structurally via `reflect_ty`'s `Ty::Datatype` arm.
        Ty::Datatype { name, variants } if variants.is_empty() => {
            Some(datatype_backref_const_name(name))
        }
        Ty::Ref { inner, .. } => bare_type_var(inner),
        _ => None,
    }
}

/// If `ty` is a value of TRAIT-OBJECT type — a bare `dyn Trait`, or one behind a
/// transparent `&dyn`/`&mut dyn` reference (the canonical `core::fmt::Formatter`
/// `buf : &mut dyn core::fmt::Write` shape) — return the CLOSED existential const
/// `Trust.Dyn.<trait>`. A `dyn` value binds DIRECTLY at this registered existential
/// dependent type (`Sigma (T:Type), Vtable_<trait> T`), NOT through `Trust.El` (the
/// existential is a `Type`, not a `Trust.SortTy` code that `El` decodes) and NOT as a
/// universally-abstracted opaque type variable. References are transparent exactly as
/// for [`bare_type_var`], so `&mut dyn Write` binds at the same `Trust.Dyn.<trait>`
/// existential as a bare `dyn Write`.
fn dyn_object_const(ty: &Ty) -> Option<String> {
    match ty {
        Ty::Dynamic { trait_name } => Some(dyn_const_name(trait_name)),
        Ty::Ref { inner, .. } => dyn_object_const(inner),
        _ => None,
    }
}

/// The synthetic opaque type-variable const for a composite-with-nested-var
/// PARAMETER named `pname` (`Trust.Opaque.<pname>`).
#[must_use]
fn opaque_const_name(pname: &str) -> String {
    format!("{OPAQUE_PREFIX}{pname}")
}

/// Whether a `Const` name is an opaque type-variable carrier — a generic param
/// (`Trust.Param.*`) or the synthetic composite-with-nested-var carrier
/// (`Trust.Opaque.*`). Centralizes the "this const is a universally-bound Sort-1 type
/// variable that binds OUTERMOST at `Π(_ : Type)` and stays opaque" predicate.
///
/// `Trust.Dyn.*` is DELIBERATELY EXCLUDED: a trait object is no longer a universal
/// opaque variable but a CLOSED existential dependent type (`Sigma (T:Type), Vtable T`,
/// [`reflect_dyn`]) — it binds at its registered type directly and is NEVER abstracted
/// into an outer `Π(D : Type)` binder (so `free_type_var_consts` does not collect it).
fn is_type_var_const(name: &str) -> bool {
    name.starts_with(PARAM_PREFIX) || name.starts_with(OPAQUE_PREFIX)
}

/// Whether a reflected `ProofTerm` *code* mentions any opaque type-variable const
/// (`Trust.Param.*`/`Trust.Dyn.*`) — the signal that a type variable leaked into a
/// `Trust.SortTy` composite (`Prod`/`Slice`/`Vec`) where it does not type-check.
fn code_mentions_type_var(term: &ProofTerm) -> bool {
    match term {
        ProofTerm::Const(n) => is_type_var_const(n),
        ProofTerm::App(f, a) => code_mentions_type_var(f) || code_mentions_type_var(a),
        ProofTerm::Lambda { binder_type, body, .. } => {
            code_mentions_type_var(binder_type) || code_mentions_type_var(body)
        }
        ProofTerm::Pi { domain, codomain, .. } => {
            code_mentions_type_var(domain) || code_mentions_type_var(codomain)
        }
        ProofTerm::Var(_) | ProofTerm::Sort(_) => false,
    }
}

/// The distinct opaque-type-variable carrier consts (`Trust.Param.*`/`Trust.Dyn.*`)
/// that occur free in `term`, in first-appearance (pre-order) order, WHOLE (the full
/// const name, e.g. `Trust.Param.T/#0` or `Trust.Dyn.core::fmt::Write`). Used to
/// decide which `Π(<var> : Type)` binders a contract wraps — exactly the type
/// variables the body references (whether bare, nested in a composite, or as a
/// return carrier).
fn free_type_var_consts(term: &ProofTerm) -> Vec<String> {
    let mut out = Vec::new();
    fn walk(term: &ProofTerm, out: &mut Vec<String>) {
        match term {
            ProofTerm::Const(n) => {
                if is_type_var_const(n) && !out.contains(n) {
                    out.push(n.clone());
                }
            }
            ProofTerm::App(f, a) => {
                walk(f, out);
                walk(a, out);
            }
            ProofTerm::Lambda { binder_type, body, .. } => {
                walk(binder_type, out);
                walk(body, out);
            }
            ProofTerm::Pi { domain, codomain, .. } => {
                walk(domain, out);
                walk(codomain, out);
            }
            ProofTerm::Var(_) | ProofTerm::Sort(_) => {}
        }
    }
    walk(term, &mut out);
    out
}

// ---------------------------------------------------------------------------
// Known std containers → structural Clean models (GOAL-ITEM #2)
// ---------------------------------------------------------------------------
//
// `trust-mir-extract` lowers a std container `TyKind::Adt` like a struct: it calls
// `adt_def.all_fields()` and recursively lowers each field's MONOMORPHIZED type
// (`crates/trust-mir-extract/src/ty_convert.rs`). So `Vec<T>` arrives as
// `Ty::Adt { name: "alloc::vec::Vec", fields: [(buf, RawVec…), (len, usize)], … }`
// — the type-ERASED internal layout, not a clean element. Reflecting that opaque
// internal product gives an anonymous `Prod` with no structural meaning. Instead a
// known-type table maps the COMMON containers to their REAL structural Clean model,
// keyed on the def-path `name` (the `safe_def_path_str` form: `alloc::vec::Vec`,
// `alloc::boxed::Box`, …), exactly mirroring `is_std_deep_clone_container`'s
// leaf+crate convention (`crates/trust-mir-extract/src/convert.rs`):
//
//   * SEQUENCE containers (`Vec<T>`, `VecDeque<T>`, `Box<[T]>`, `String`): a `Vec`
//     IS a growable slice. It reflects to the EXISTING slice carrier `Slice T`
//     (`CARRIER_SLICE` applied to `reflect_ty(T)`) — its safety obligations are
//     about its symbolic LENGTH (already handled by the slice machinery), and a
//     bare element `T` stays the Pi-bound `Trust.Param`. So a `Vec<T>` bounds VC
//     reconstructs STRUCTURALLY over `Slice T` instead of an opaque atom.
//   * SMART POINTERS (`Box<T>`, `Rc<T>`, `Arc<T>`): TRANSPARENT — they reflect to
//     `reflect_ty(inner)`, the pointer being invisible to the dependent-type
//     carrier, exactly like the existing `Ty::Ref` handling.
//   * `Option<T>` / `Result<T,E>`: these arrive as ENUMS (non-empty `variants`),
//     so they ALREADY route through the P4 multi-constructor inductive path
//     (`reflect_enum`). The container table deliberately does NOT touch enums; it
//     only intercepts struct-shaped (`variants` empty) containers, leaving the
//     parameterized-inductive `Option`/`Result` reflection unchanged.
//
// Everything is FAIL-CLOSED: an unknown container, or a known container whose
// element/inner type is not recoverable from the (type-erased) field tree, falls
// straight through to the existing opaque/`Prod` path — never an unsound mapping,
// never a 4th axiom (the slice carrier and the transparent inner reuse existing
// kernel declarations; no new inductive is introduced).

/// Whether a container def-path `name` denotes a SEQUENCE container that models
/// as a slice `Slice T` over its element `T` — `Vec`, `VecDeque`, `String`. Keyed
/// on the `safe_def_path_str` leaf (last `::` segment, stripped of any generic
/// args) gated on the `std`/`alloc`/`core` crate prefix, mirroring
/// `is_std_deep_clone_container` so the recognized set stays in lockstep with the
/// extractor. (`String` is morally `Vec<u8>`; its element is `u8`.)
#[must_use]
fn sequence_container_leaf(name: &str) -> Option<&'static str> {
    if !(name.starts_with("std::") || name.starts_with("alloc::") || name.starts_with("core::")) {
        return None;
    }
    let leaf = name.rsplit("::").next().unwrap_or(name);
    let leaf = leaf.split('<').next().unwrap_or(leaf);
    match leaf {
        "Vec" | "VecDeque" => Some("Vec"),
        "String" => Some("String"),
        _ => None,
    }
}

/// Whether a container def-path `name` denotes a TRANSPARENT smart-pointer
/// wrapper — a single-`T` pointer wrapper invisible to the dependent-type carrier,
/// reflected as its inner type `T` (exactly like `Ty::Ref`). COVERAGE-AGENDA #2
/// generalizes the original `Box`/`Rc`/`Arc` set to the full owning/non-null
/// pointer-wrapper family:
///   * `Box<T>` — unique owning heap pointer;
///   * `Rc<T>` / `Arc<T>` — shared-ownership pointers (shared ownership is
///     faithfulness-NEUTRAL for a value contract, so they stay transparent to `T`);
///   * `Unique<T>` — the owning-pointer newtype inside `Box`;
///   * `NonNull<T>` — the non-null `*mut T` newtype inside `Unique`/`Rc`/`Arc`.
/// Each grounds `-> Box<S>` / `-> NonNull<S>` etc. transparently to `S` whenever
/// `S` itself grounds + inhabits. Same leaf+crate keying as
/// [`sequence_container_leaf`]. NOTE: a transparent wrapper makes the pointer
/// invisible — it does NOT confer a value model on the pointee through a
/// dereference (that is the separate deferred points-to model); it only forwards
/// the value contract of the already-known inner `T`.
#[must_use]
fn smart_pointer_leaf(name: &str) -> bool {
    if !(name.starts_with("std::") || name.starts_with("alloc::") || name.starts_with("core::")) {
        return false;
    }
    let leaf = name.rsplit("::").next().unwrap_or(name);
    let leaf = leaf.split('<').next().unwrap_or(leaf);
    matches!(leaf, "Box" | "Rc" | "Arc" | "Unique" | "NonNull")
}

/// Recover the ELEMENT type of a sequence container from its (possibly
/// type-erased) lowered `Ty::Adt` field tree, or `None` to FAIL CLOSED.
///
/// The lowered shape varies: a clean dump may carry the element directly
/// (`Vec { elem: T }`-style single field, or a field that IS a `Slice`/`Array` of
/// the element); a fully-monomorphized dump type-erases it inside nested
/// `RawVec`/`Unique`/pointer structs. We recover it by these SOUND, fail-closed
/// rules, in order:
///   1. a field whose type is itself a `Slice { elem }` or `Array { elem }`
///      (e.g. a `Box<[T]>`-backed buffer) — the element is `elem`;
///   2. a single bare generic-parameter field (`value: T`) — the element is `T`;
///   3. a single reflectable non-`usize`/non-pointer field — the element is it;
/// recursing through `RawPtr`/`Ref`/nested container fields (the buffer pointer).
/// Anything ambiguous (no element found, or several incompatible candidates)
/// returns `None`, so the caller keeps the opaque path with NO regression.
fn sequence_element_ty(ty: &Ty) -> Option<Ty> {
    // The element is what the buffer POINTER points at: a `RawPtr`/`Ref` pointee is
    // taken DIRECTLY as the element (any reflectable type — scalar included), while
    // direct integer fields (`len`/`cap`) are length/capacity slots to skip. So we
    // only follow into pointer pointees, slice/array buffers, bare type vars, and
    // nested struct buffers (RawVec/Unique/NonNull/PhantomData); a bare integer
    // field is NOT an element candidate.
    fn search(ty: &Ty, depth: u32) -> Option<Ty> {
        if depth > 6 {
            return None; // bounded — never loop on a self-referential layout.
        }
        match ty {
            // A slice/array buffer field carries the element directly.
            Ty::Slice { elem } | Ty::Array { elem, .. } => Some((**elem).clone()),
            // A bare generic element `T` (`Unsupported{Param}`) — the surface form.
            Ty::Unsupported { kind, .. } if kind == PARAM_KIND => Some(ty.clone()),
            // The buffer pointer's POINTEE *is* the element (any reflectable type).
            Ty::RawPtr { pointee, .. } => Some((**pointee).clone()),
            Ty::Ref { inner, .. } => Some((**inner).clone()),
            // A nested container/struct (RawVec, Unique, NonNull, PhantomData …):
            // search its fields for the unique element candidate (accepting a
            // UNIQUE candidate, rejecting ambiguity). Integer/marker slots yield no
            // candidate of their own, so `len`/`cap` are naturally skipped.
            Ty::Adt { fields, variants, .. } if variants.is_empty() => {
                let mut found: Option<Ty> = None;
                for (_, fty) in fields {
                    if let Some(cand) = search(fty, depth + 1) {
                        match &found {
                            None => found = Some(cand),
                            Some(prev) if *prev == cand => {}
                            Some(_) => return None, // ambiguous — fail closed.
                        }
                    }
                }
                found
            }
            _ => None,
        }
    }
    let Ty::Adt { name, fields, variants, .. } = ty else {
        return None;
    };
    if variants.is_empty() {
        // `String` is `Vec<u8>`: its element is `u8` even though the `u8` is buried
        // in the type-erased buffer. Short-circuit to the known element.
        if sequence_container_leaf(name) == Some("String") {
            return Some(Ty::Int { width: 8, signed: false });
        }
    }
    // Search the field tree for the element candidate.
    for (_, fty) in fields {
        if let Some(elem) = search(fty, 0) {
            return Some(elem);
        }
    }
    None
}

/// Recover the INNER type a transparent smart pointer (`Box<T>`/`Rc<T>`/`Arc<T>`)
/// wraps, from its lowered field tree, or `None` to FAIL CLOSED.
///
/// A smart pointer is a single-`T` wrapper; its lowered fields bottom out in a
/// `Unique<T>`/`NonNull<T>` pointer to `T`. We recover `T` as the UNIQUE
/// non-trivial pointee/element reachable through the pointer/struct fields (same
/// bounded, ambiguity-rejecting search as [`sequence_element_ty`]).
fn smart_pointer_inner_ty(ty: &Ty) -> Option<Ty> {
    fn search(ty: &Ty, depth: u32) -> Option<Ty> {
        if depth > 6 {
            return None;
        }
        match ty {
            _ if bare_type_var(ty).is_some() && matches!(ty, Ty::Unsupported { .. }) => {
                Some(ty.clone())
            }
            Ty::RawPtr { pointee, .. } => search(pointee, depth + 1),
            Ty::Ref { inner, .. } => search(inner, depth + 1),
            Ty::Slice { .. } | Ty::Array { .. } => Some(ty.clone()),
            Ty::Adt { fields, variants, .. } if variants.is_empty() => {
                let mut found: Option<Ty> = None;
                for (_, fty) in fields {
                    if let Some(cand) = search(fty, depth + 1) {
                        match &found {
                            None => found = Some(cand),
                            Some(prev) if *prev == cand => {}
                            Some(_) => return None,
                        }
                    }
                }
                found
            }
            // A directly-carried scalar/concrete inner (a clean `Box { value: T }`
            // dump) is itself the inner.
            Ty::Int { .. } | Ty::Bool | Ty::Bv(_) | Ty::Float { .. } => Some(ty.clone()),
            _ => None,
        }
    }
    let Ty::Adt { fields, variants, .. } = ty else {
        return None;
    };
    if !variants.is_empty() {
        return None;
    }
    for (_, fty) in fields {
        if let Some(inner) = search(fty, 0) {
            return Some(inner);
        }
    }
    None
}

/// Reflect a KNOWN std container `Ty::Adt` to its REAL structural Clean carrier
/// *code*, or `None` to fall through to the existing opaque/`Prod` path.
///
/// - a sequence container (`Vec`/`VecDeque`/`String`/`Box<[T]>`) → `Slice T`
///   (`CARRIER_SLICE` applied to the reflected element);
/// - a transparent smart pointer (`Box<T>`/`Rc<T>`/`Arc<T>`) → `reflect_ty(inner)`.
///
/// Returns `None` (→ existing path, no regression) for: an enum-shaped container
/// (Option/Result — handled by `reflect_enum`), an unknown container, or a known
/// container whose element/inner type cannot be recovered or does not itself
/// reflect. Introduces NO axiom (slice carrier + transparent inner reuse existing
/// declarations).
fn reflect_known_container(ty: &Ty) -> Option<Result<ProofTerm, ReflectError>> {
    let Ty::Adt { name, variants, .. } = ty else {
        return None;
    };
    // Enums (Option/Result) are NOT containers here — they reflect via P4.
    if !variants.is_empty() {
        return None;
    }
    if sequence_container_leaf(name).is_some() {
        let elem = sequence_element_ty(ty)?;
        // `Slice (reflect_ty elem)` — fails closed transitively on a bad element.
        return Some(reflect_ty(&elem).map(|e| app(cst(CARRIER_SLICE), e)));
    }
    if smart_pointer_leaf(name) {
        let inner = smart_pointer_inner_ty(ty)?;
        // Transparent: the pointer is invisible — reflect the inner directly.
        return Some(reflect_ty(&inner));
    }
    None
}

/// GOAL-ITEM #2 — whether `ty` is a KNOWN std container that grounds to a REAL
/// structural model (a sequence container → `Slice T`, or a transparent smart
/// pointer → its inner), i.e. it is mapped by the known-type table and its
/// element/inner reflects. This is the DEPTH-METRIC predicate: a parameter of
/// such a type grounds STRUCTURALLY (over the existing slice carrier / inner),
/// not as an opaque internal-layout product. Returns `false` (fail-closed) for an
/// unknown container, an enum (Option/Result — counted as a structural ADT
/// instead), or a container whose element/inner is unrecoverable.
#[must_use]
pub fn is_structural_container(ty: &Ty) -> bool {
    matches!(reflect_known_container(ty), Some(Ok(_)))
}

/// RECURSIVE DEPENDENT CARRIER (goal bullet 2 tail) — the carriable ELEMENT/INNER
/// `Ty` a known std container reflects over: a sequence container's element
/// (`Vec<X>`/`VecDeque<X>`/`String`→`X`) or a transparent smart pointer's inner
/// (`Box<X>`/`Rc<X>`/`Arc<X>`→`X`). `None` for a non-container / unrecoverable
/// element. Lets `clean_ground` descend into a container's GENERIC element to register
/// a nested ADT (`Vec<Wrapper<T>>`) before the carrier that applies it.
#[must_use]
pub fn container_element_ty(ty: &Ty) -> Option<Ty> {
    let Ty::Adt { name, variants, .. } = ty else { return None };
    if !variants.is_empty() {
        return None;
    }
    if sequence_container_leaf(name).is_some() {
        return sequence_element_ty(ty);
    }
    if smart_pointer_leaf(name) {
        return smart_pointer_inner_ty(ty);
    }
    None
}

// ---------------------------------------------------------------------------
// COLLECTIONS (maps/sets) → association-list / element-list carriers (REAL-CODE
// COVERAGE — collections blocker). A `HashMap<K,V>`/`BTreeMap<K,V>` is morally a
// finite map, modeled as the ASSOCIATION-LIST carrier `Slice (Prod K V)` — a list
// of key-value PAIRS — reusing the existing axiom-free `Slice` + `Prod` carriers
// (NO new inductive, NO 4th axiom). A `HashSet<K>`/`BTreeSet<K>` is the
// element-list `Slice K` (a set IS a deduplicated list at the carrier level). This
// mirrors `sequence_container_leaf`/`reflect_known_container`: the table maps the
// COMMON map/set containers to their REAL structural Clean model keyed on the
// def-path leaf, and is FAIL-CLOSED — an unknown map, or a map whose `(K,V)` entry
// type is not recoverable from the (type-erased hashbrown / btree) field tree,
// falls straight through to the existing opaque/`Prod` path with NO regression.
// ---------------------------------------------------------------------------

/// Whether a container def-path `name` denotes an ASSOCIATIVE MAP container that
/// models as the association-list carrier `Slice (Prod K V)` — `HashMap`,
/// `BTreeMap`. Same leaf+crate keying as [`sequence_container_leaf`] (the
/// `std`/`alloc`/`core`/`hashbrown` crate prefix gate — `hashbrown` is the
/// in-`std` map backend whose `HashMap` is the same finite-map model).
#[must_use]
fn map_container_leaf(name: &str) -> bool {
    if !(name.starts_with("std::")
        || name.starts_with("alloc::")
        || name.starts_with("core::")
        || name.starts_with("hashbrown::"))
    {
        return false;
    }
    let leaf = name.rsplit("::").next().unwrap_or(name);
    let leaf = leaf.split('<').next().unwrap_or(leaf);
    matches!(leaf, "HashMap" | "BTreeMap")
}

/// Whether a container def-path `name` denotes a SET container that models as the
/// element-list carrier `Slice K` (a set is a deduplicated list at the carrier
/// level) — `HashSet`, `BTreeSet`. Same keying as [`map_container_leaf`].
#[must_use]
fn set_container_leaf(name: &str) -> bool {
    if !(name.starts_with("std::")
        || name.starts_with("alloc::")
        || name.starts_with("core::")
        || name.starts_with("hashbrown::"))
    {
        return false;
    }
    let leaf = name.rsplit("::").next().unwrap_or(name);
    let leaf = leaf.split('<').next().unwrap_or(leaf);
    matches!(leaf, "HashSet" | "BTreeSet")
}

/// Recover the `(K, V)` ENTRY type pair of a map container from its (type-erased)
/// lowered `Ty::Adt` field tree, or `None` to FAIL CLOSED.
///
/// The map's entries live behind a buffer pointer whose pointee is the entry
/// `(K, V)` TUPLE: in the monomorphized `hashbrown` layout the `Bucket`'s
/// `NonNull<*const (K, V)>` carries it; a cleaner dump may carry a `Slice`/`Array`
/// of `(K, V)`, or a direct `entries`/`pairs` field. We bounded-search the field
/// tree for the UNIQUE reachable `(K, V)` 2-tuple pointee/element (rejecting
/// ambiguity), exactly the same SOUND, fail-closed discipline as
/// [`sequence_element_ty`]. A fully-type-erased table (the `RawTable`-only
/// `HashMap` whose buckets are `*const u8`) exposes NO `(K, V)` tuple, so this
/// returns `None` and the map fails closed (NEVER an unsound mapping).
fn map_kv_tys(ty: &Ty) -> Option<(Ty, Ty)> {
    fn search(ty: &Ty, depth: u32) -> Option<(Ty, Ty)> {
        if depth > 12 {
            return None; // bounded — the btree/hashbrown layouts nest deeply.
        }
        match ty {
            // The entry pointee/element IS the `(K, V)` 2-tuple — the unique signal.
            Ty::Tuple(elems) if elems.len() == 2 => Some((elems[0].clone(), elems[1].clone())),
            // A slice/array of entries carries the `(K, V)` tuple as its element.
            Ty::Slice { elem } | Ty::Array { elem, .. } => search(elem, depth + 1),
            // Follow the buffer pointer / reference to the entry it points at.
            Ty::RawPtr { pointee, .. } => search(pointee, depth + 1),
            Ty::Ref { inner, .. } => search(inner, depth + 1),
            // Descend nested structs (RawTable / RawTableInner / NonNull / Bucket /
            // NodeRef / LeafNode …): accept a UNIQUE `(K, V)` candidate, reject
            // ambiguity (two incompatible entry shapes ⇒ fail closed).
            Ty::Adt { fields, variants, .. } => {
                let mut found: Option<(Ty, Ty)> = None;
                for (_, fty) in fields {
                    if let Some(cand) = search(fty, depth + 1) {
                        match &found {
                            None => found = Some(cand),
                            Some(prev) if *prev == cand => {}
                            Some(_) => return None,
                        }
                    }
                }
                for var in variants {
                    for (_, fty) in &var.fields {
                        if let Some(cand) = search(fty, depth + 1) {
                            match &found {
                                None => found = Some(cand),
                                Some(prev) if *prev == cand => {}
                                Some(_) => return None,
                            }
                        }
                    }
                }
                found
            }
            _ => None,
        }
    }
    let Ty::Adt { name, .. } = ty else { return None };
    if !map_container_leaf(name) {
        return None;
    }
    search(ty, 0)
}

/// Reflect a KNOWN map/set container `Ty::Adt` to its REAL structural Clean carrier
/// *code*, or `None` to fall through to the existing opaque/`Prod` path:
///
/// - a MAP (`HashMap<K,V>`/`BTreeMap<K,V>`) → the association-list carrier
///   `Slice (Prod (R K) (R V))` (a list of key-value pairs);
/// - a SET (`HashSet<K>`/`BTreeSet<K>`) → the element-list carrier `Slice (R K)`.
///
/// Reuses the axiom-free `Slice` + `Prod` carriers (NO new inductive, NO 4th
/// axiom). Returns `None` (→ existing path, no regression) for an unknown
/// container, a map whose `(K, V)` entry is not recoverable, a set whose element
/// is not recoverable, or a `(K, V)`/element that does not itself reflect.
fn reflect_known_map(ty: &Ty) -> Option<Result<ProofTerm, ReflectError>> {
    let Ty::Adt { name, variants, .. } = ty else {
        return None;
    };
    if !variants.is_empty() {
        return None; // an enum-shaped container is not a map/set struct.
    }
    if map_container_leaf(name) {
        let (k, v) = map_kv_tys(ty)?;
        // `Slice (Prod (R K) (R V))` — fails closed transitively on a bad K/V.
        return Some((|| {
            let kc = reflect_ty(&k)?;
            let vc = reflect_ty(&v)?;
            Ok(app(cst(CARRIER_SLICE), app(app(cst(CARRIER_PROD), kc), vc)))
        })());
    }
    if set_container_leaf(name) {
        // A set models as `Slice K` over its recovered element (same recovery as a
        // sequence container's element).
        let elem = sequence_element_ty(ty)?;
        return Some(reflect_ty(&elem).map(|e| app(cst(CARRIER_SLICE), e)));
    }
    None
}

/// REAL-CODE COVERAGE — whether `ty` is a KNOWN map/set container that grounds to a
/// REAL structural model (a map → `Slice (Prod K V)`, a set → `Slice K`). The
/// DEPTH-METRIC predicate for collections: a parameter of such a type grounds
/// STRUCTURALLY over the existing `Slice`/`Prod` carriers, not as an opaque
/// internal-layout product. Fail-closed for an unknown container or an
/// unrecoverable entry/element.
#[must_use]
pub fn is_structural_map(ty: &Ty) -> bool {
    matches!(reflect_known_map(ty), Some(Ok(_)))
}

/// REAL-CODE COVERAGE — the carriable `(K, V)` entry types a known map container
/// reflects over, or `None` for a non-map / unrecoverable entry. Lets
/// `clean_ground` descend into a map's generic K/V to register a nested ADT (a
/// `HashMap<String, Point>`) before the `Slice (Prod K V)` carrier that applies it.
#[must_use]
pub fn map_entry_tys(ty: &Ty) -> Option<(Ty, Ty)> {
    map_kv_tys(ty)
}

// ---------------------------------------------------------------------------
// ITERATOR ADAPTERS → REAL record carriers (REAL-CODE COVERAGE — iterator-
// combinator blocker; ~90% of real ADT nodes). A stdlib iterator adapter
// (`std::slice::Iter<T>`, `core::iter::{Map,Filter,Enumerate,Zip}`, `str::Chars`,
// `Copied`/`Cloned`, …) is a struct WRAPPING a SOURCE iterator (+ a closure for
// `Map`/`Filter`). The type-erased internal layout (`ptr`/`end_or_len`/`_marker`
// for `slice::Iter`) carries NO semantic meaning, so we DO NOT register that
// internal product. Instead each adapter reflects to a REAL single-constructor
// RECORD carrier `Trust.Adt.<Adapter>` over its RECOVERED, semantically-meaningful
// fields, reusing the SAME modulo-3 `register_adt_carriers` path as a non-generic
// struct (and the existing `Trust.Closure.*` record for the closure fields):
//
//   * `slice::Iter<T>` / `str::Chars`  → `{ source : Slice <elem> }`
//     (the remaining elements as a list; `Chars` is `Iter<u8>`'s `Slice (BitVec 8)`);
//   * `Map<I, F>`                       → `{ source : <reflect I>, f : <closure F> }`;
//   * `Filter<I, P>`                    → `{ source : <reflect I>, pred : <closure P> }`;
//   * `Enumerate<I>`                    → `{ source : <reflect I>, pos : BitVec 64 }`
//     (the running index `Nat`/usize);
//   * `Zip<A, B>`                       → `{ a : <reflect A>, b : <reflect B> }`;
//   * `Copied<I>` / `Cloned<I>`         → TRANSPARENT to their source `<reflect I>`
//     (no element transformation at the carrier level).
//
// FAIL-CLOSED: an unknown adapter, or one whose source/element/closure is not
// recoverable from the field tree, falls through to the existing opaque/`Prod`
// path. The closure fields reuse the already-modulo-3 `Trust.Closure.*` record —
// NO new axiom. axiom_deps EMPTY (the record's fields are `Slice`/`Prod`/`BitVec`/
// applied `Trust.Closure.*`/applied source records — all axiom-free).
// ---------------------------------------------------------------------------

/// Classification of a recognized stdlib iterator-adapter def-path leaf, naming the
/// (recovered) FIELDS the adapter's record carrier exposes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IterAdapterKind {
    /// `slice::Iter<T>` / `str::Chars` — `{ source : Slice <elem> }`.
    Source,
    /// `Map<I, F>` — `{ source : <I>, f : <closure F> }`.
    Map,
    /// `Filter<I, P>` — `{ source : <I>, pred : <closure P> }`.
    Filter,
    /// `Enumerate<I>` — `{ source : <I>, pos : usize }`.
    Enumerate,
    /// `Zip<A, B>` — `{ a : <A>, b : <B> }`.
    Zip,
    /// `Copied<I>` / `Cloned<I>` — TRANSPARENT to the source iterator `<I>`.
    Transparent,
    /// STRING-PATTERN SOURCE iterators that range over a string's remaining bytes
    /// with NO pattern/closure: `SplitWhitespace`, `Lines`, `CharIndices`,
    /// `LinesAny`. Modeled as `{ source : Slice (BitVec 8) }` — the remaining input
    /// as a byte list (the SAME `Chars`/`slice::Iter` source-record shape). The
    /// yielded element (a `&str` substring / `(usize, char)` pair) is a VIEW into
    /// this source, not a separately-modeled field.
    StringSource,
    /// STRING-PATTERN SPLITTER iterators that carry a SEARCH PATTERN over the input:
    /// `Split`, `SplitN`, `RSplit`, `RSplitN`, `SplitTerminator`, `SplitInclusive`,
    /// `Matches`, `MatchIndices`. Modeled as `{ source : Slice (BitVec 8), pattern :
    /// Slice (BitVec 8) }` — the remaining input plus the (string/char) needle, both
    /// as byte lists. A closure/`char`/`&str` pattern all collapse to the needle
    /// byte-slice; the `Searcher` state is a VIEW, not a separate field.
    StringSplit,
}

/// Whether a def-path `name` denotes a KNOWN stdlib ITERATOR ADAPTER, and which
/// [`IterAdapterKind`] it is. Keyed on the `safe_def_path_str` leaf gated on the
/// `std`/`core`/`alloc` crate prefix (the adapters live in `core::iter` / `std::
/// slice` / `std::str`). An unknown leaf returns `None` (fail closed — the ADT
/// keeps the ordinary struct/`Prod` path).
#[must_use]
fn iter_adapter_kind(name: &str) -> Option<IterAdapterKind> {
    if !(name.starts_with("std::") || name.starts_with("core::") || name.starts_with("alloc::")) {
        return None;
    }
    let leaf = name.rsplit("::").next().unwrap_or(name);
    let leaf = leaf.split('<').next().unwrap_or(leaf);
    match leaf {
        "Iter" | "IterMut" | "Chars" | "Bytes" => Some(IterAdapterKind::Source),
        "Map" => Some(IterAdapterKind::Map),
        "Filter" => Some(IterAdapterKind::Filter),
        "Enumerate" => Some(IterAdapterKind::Enumerate),
        "Zip" => Some(IterAdapterKind::Zip),
        "Copied" | "Cloned" => Some(IterAdapterKind::Transparent),
        // STRING-PATTERN source iterators (no needle) — `s.split_whitespace()`,
        // `s.lines()`, `s.char_indices()`. Model `{ source : Slice (BitVec 8) }`.
        "SplitWhitespace" | "SplitAsciiWhitespace" | "Lines" | "LinesAny" | "CharIndices" => {
            Some(IterAdapterKind::StringSource)
        }
        // STRING-PATTERN splitters (carry a needle) — `s.split(p)`, `s.splitn(n,p)`,
        // `s.matches(p)`, …. Model `{ source : Slice (BitVec 8), pattern : Slice
        // (BitVec 8) }`.
        "Split" | "SplitN" | "RSplit" | "RSplitN" | "SplitTerminator" | "RSplitTerminator"
        | "SplitInclusive" | "Matches" | "RMatches" | "MatchIndices" | "RMatchIndices" => {
            Some(IterAdapterKind::StringSplit)
        }
        _ => None,
    }
}

/// The mangled Clean inductive name for an iterator-adapter record. We key it on
/// the adapter's def-path `name` (sanitized like [`adt_inductive_name`]) so two
/// distinct adapters get distinct records (`Trust.Adt.std_slice_Iter`,
/// `Trust.Adt.std_iter_Map`, …) and the SAME adapter monomorphization maps to the
/// same record everywhere.
#[must_use]
fn iter_adapter_inductive_name(name: &str) -> String {
    adt_inductive_name(name)
}

/// Recover the SOURCE-iterator `Ty` (the wrapped inner iterator) of an adapter
/// whose first non-marker field is its source: `Map`/`Filter`/`Enumerate` carry it
/// as `iter`, `Chars` as `iter`, `Copied`/`Cloned`/`slice::Iter` directly. We take
/// the FIRST field whose type is an `Ty::Adt` (the wrapped iterator struct), or
/// `None` to fail closed.
fn iter_adapter_source_ty(ty: &Ty) -> Option<Ty> {
    let Ty::Adt { fields, .. } = ty else { return None };
    fields.iter().map(|(_, fty)| fty).find(|fty| matches!(fty, Ty::Adt { .. })).cloned()
}

/// Recover the CLOSURE `Ty` field of a `Map`/`Filter` adapter (the `f`/`predicate`
/// field), or `None` to fail closed. The closure may sit behind a transparent
/// reference.
fn iter_adapter_closure_ty(ty: &Ty) -> Option<Ty> {
    fn peel(t: &Ty) -> &Ty {
        match t {
            Ty::Ref { inner, .. } => peel(inner),
            other => other,
        }
    }
    let Ty::Adt { fields, .. } = ty else { return None };
    fields.iter().map(|(_, fty)| peel(fty)).find(|fty| matches!(fty, Ty::Closure { .. })).cloned()
}

/// Recover the ELEMENT `Ty` a `slice::Iter<T>` / `str::Chars` ranges over, from its
/// type-erased layout (`ptr : NonNull<*const T>`, `end_or_len : *const T`,
/// `_marker`), or `None` to fail closed. The element is the UNIQUE pointee reachable
/// through the `ptr`/`end_or_len` buffer pointers — the SAME bounded, ambiguity-
/// rejecting search [`sequence_element_ty`] uses (a `slice::Iter` IS the iterator
/// over a slice's backing buffer).
fn iter_source_element_ty(ty: &Ty) -> Option<Ty> {
    fn search(ty: &Ty, depth: u32) -> Option<Ty> {
        if depth > 6 {
            return None;
        }
        match ty {
            Ty::Slice { elem } | Ty::Array { elem, .. } => Some((**elem).clone()),
            Ty::RawPtr { pointee, .. } => Some((**pointee).clone()),
            Ty::Ref { inner, .. } => Some((**inner).clone()),
            Ty::Adt { fields, variants, .. } if variants.is_empty() => {
                let mut found: Option<Ty> = None;
                for (_, fty) in fields {
                    if let Some(cand) = search(fty, depth + 1) {
                        match &found {
                            None => found = Some(cand),
                            Some(prev) if *prev == cand => {}
                            Some(_) => return None,
                        }
                    }
                }
                found
            }
            _ => None,
        }
    }
    let Ty::Adt { fields, .. } = ty else { return None };
    for (_, fty) in fields {
        if let Some(elem) = search(fty, 0) {
            return Some(elem);
        }
    }
    None
}

/// ITERATOR ADAPTER RECORD — reflect a KNOWN stdlib iterator adapter `Ty::Adt` into
/// a REAL single-constructor Clean inductive carrier (a dependent RECORD over its
/// recovered, semantically-meaningful fields), or `None` to fall back to the opaque
/// internal-layout product (no regression).
///
/// The record's fields are the adapter's MODEL (source + closure / index / paired
/// source), NOT its private buffer layout — see [`IterAdapterKind`]. The closure
/// fields reuse the existing `Trust.Closure.*` record carrier (already modulo 3);
/// the element/source fields reuse the `Slice` carrier and the nested adapter
/// records (registered post-order by `collect_adt_carriers_recursive`). Registers
/// through the SAME modulo-3 `register_adt_carriers` path as a non-generic struct —
/// `axiom_deps` EMPTY (NO 4th axiom). A `Transparent` adapter (`Copied`/`Cloned`)
/// returns `None` HERE (its model is its source, handled by
/// [`reflect_known_iter_adapter`] reflecting the source directly), so it registers
/// NO spurious record.
///
/// Returns `None` (→ `Prod` floor, sound) for an unknown adapter or one whose
/// source/element/closure is not recoverable.
#[must_use]
pub fn reflect_iter_adapter_record(ty: &Ty) -> Option<AdtCarrier> {
    let Ty::Adt { name, variants, .. } = ty else { return None };
    if !variants.is_empty() {
        return None;
    }
    let kind = iter_adapter_kind(name)?;
    let inductive_name = iter_adapter_inductive_name(name);
    let ctor_name = adt_ctor_name(&inductive_name);
    let mk = |fields: Vec<(String, ProofTerm)>, type_params: Vec<String>| {
        Some(AdtCarrier {
            ctor_name: ctor_name.clone(),
            name: inductive_name.clone(),
            fields,
            type_params,
            constructors: Vec::new(),
        })
    };
    match kind {
        // `slice::Iter<T>` / `Chars` → `{ source : Slice <elem> }`.
        IterAdapterKind::Source => {
            let elem = iter_source_element_ty(ty)?;
            let elem_c = reflect_ty(&elem).ok()?;
            // A recovered element that still nests a type var has no concrete record
            // field carrier here — fail closed (deferred to the generic path).
            if carrier_mentions_param(&elem_c) {
                return None;
            }
            mk(vec![("source".to_string(), app(cst(CARRIER_SLICE), elem_c))], Vec::new())
        }
        // `Map<I, F>` → `{ source : <reflect I>, f : <closure F> }`;
        // `Filter<I, P>` → `{ source : <reflect I>, pred : <closure P> }`.
        //
        // The closure field carrier is the APPLIED closure record `Trust.Closure.<n>
        // (Param A) (Param B)` over the call signature's two `Type` variables. Those
        // are genuinely abstract (the extractor hands us only upvars, not the call
        // signature), so the adapter record is PARAMETERIZED over them too: its
        // `type_params` are the closure's call-param idents, threaded up so the closure
        // field's `Param A`/`Param B` args decode to the adapter record's bound
        // de-Bruijn `Type` variables (exactly how a struct field that is a generic inner
        // inductive contributes the inner's params to the outer's binder list).
        IterAdapterKind::Map | IterAdapterKind::Filter => {
            let source = iter_adapter_source_ty(ty)?;
            let source_c = reflect_ty(&source).ok()?;
            // The source itself may not mention a param (it is concrete), but the
            // closure field WILL — so we do NOT reject on the closure's params here.
            if carrier_mentions_param(&source_c) {
                return None;
            }
            let closure = iter_adapter_closure_ty(ty)?;
            let Ty::Closure { name: cname, upvars, .. } = &closure else { return None };
            // The closure record's own type_params are the abstraction handle.
            let crec = reflect_closure(cname, upvars)?;
            let closure_c = reflect_ty(&closure).ok()?;
            let fname = if kind == IterAdapterKind::Map { "f" } else { "pred" };
            mk(
                vec![("source".to_string(), source_c), (fname.to_string(), closure_c)],
                crec.type_params,
            )
        }
        // `Enumerate<I>` → `{ source : <reflect I>, pos : usize }`.
        IterAdapterKind::Enumerate => {
            let source = iter_adapter_source_ty(ty)?;
            let source_c = reflect_ty(&source).ok()?;
            if carrier_mentions_param(&source_c) {
                return None;
            }
            mk(
                vec![("source".to_string(), source_c), ("pos".to_string(), reflect_bitvec(64))],
                Vec::new(),
            )
        }
        // `Zip<A, B>` → `{ a : <reflect A>, b : <reflect B> }`.
        IterAdapterKind::Zip => {
            let Ty::Adt { fields, .. } = ty else { return None };
            let sources: Vec<&Ty> = fields
                .iter()
                .map(|(_, fty)| fty)
                .filter(|fty| matches!(fty, Ty::Adt { .. }))
                .collect();
            if sources.len() < 2 {
                return None;
            }
            let a_c = reflect_ty(sources[0]).ok()?;
            let b_c = reflect_ty(sources[1]).ok()?;
            if carrier_mentions_param(&a_c) || carrier_mentions_param(&b_c) {
                return None;
            }
            mk(vec![("a".to_string(), a_c), ("b".to_string(), b_c)], Vec::new())
        }
        // STRING-PATTERN SOURCE (`SplitWhitespace`/`Lines`/`CharIndices`) →
        // `{ source : Slice (BitVec 8) }` — the remaining input as a byte list, the
        // SAME source-record shape `Chars`/`slice::Iter` use. The byte element is a
        // concrete `BitVec 8`, so the record is non-generic and grounds modulo 3.
        IterAdapterKind::StringSource => {
            mk(vec![("source".to_string(), app(cst(CARRIER_SLICE), reflect_bitvec(8)))], Vec::new())
        }
        // STRING-PATTERN SPLITTER (`Split`/`SplitN`/`Matches`/…) →
        // `{ source : Slice (BitVec 8), pattern : Slice (BitVec 8) }` — the remaining
        // input plus the needle, both byte lists. A `char`/`&str`/closure pattern all
        // collapse to the needle byte-slice (the `Searcher` state is a VIEW into the
        // source, not a separate modeled field). Both fields concrete ⇒ modulo 3.
        IterAdapterKind::StringSplit => mk(
            vec![
                ("source".to_string(), app(cst(CARRIER_SLICE), reflect_bitvec(8))),
                ("pattern".to_string(), app(cst(CARRIER_SLICE), reflect_bitvec(8))),
            ],
            Vec::new(),
        ),
        // `Copied`/`Cloned` carry NO record of their own — they are transparent to
        // their source (handled by `reflect_known_iter_adapter`); register no record.
        IterAdapterKind::Transparent => None,
    }
}

/// ITERATOR ADAPTER — reflect a KNOWN stdlib iterator adapter `Ty::Adt` to its REAL
/// structural Clean carrier *code* (the record const `Trust.Adt.<Adapter>` that
/// [`reflect_iter_adapter_record`] registers, or — for a `Copied`/`Cloned` adapter
/// — TRANSPARENTLY its source's carrier), or `None` to fall through to the existing
/// opaque/`Prod` path (no regression).
///
/// The adapter records here are MONOMORPHIZED to concrete sources (a real
/// `.iter().map(..)` produces `Map<slice::Iter<i32>, {closure}>`), so the carrier
/// is the BARE record const `Trust.Adt.<Adapter>` (no type-param application). The
/// closure/source fields reflect concretely; a recovered field that nests a type
/// var fails the record closed (so the adapter keeps the opaque path). NO new
/// axiom (the record + the `Trust.Closure.*`/`Slice` fields are all axiom-free).
fn reflect_known_iter_adapter(ty: &Ty) -> Option<Result<ProofTerm, ReflectError>> {
    let Ty::Adt { name, variants, .. } = ty else {
        return None;
    };
    if !variants.is_empty() {
        return None;
    }
    let kind = iter_adapter_kind(name)?;
    // `Copied`/`Cloned` are TRANSPARENT to their source iterator's carrier.
    if kind == IterAdapterKind::Transparent {
        let source = iter_adapter_source_ty(ty)?;
        return Some(reflect_ty(&source));
    }
    // The other adapters reflect to their registered record const. We require the
    // record to be BUILDABLE (source/element/closure recoverable + concrete); else
    // fail closed to the opaque path. A PARAMETERIZED adapter record (a `Map`/`Filter`
    // over the closure's abstract call signature) is APPLIED to its type-param consts
    // (`Trust.Adt.std_iter_Map (Param A) (Param B)`), exactly like a generic struct
    // binding — so `reflect_contract` abstracts the call-sig `Type` vars into outer
    // `Π(A:Type)Π(B:Type)` binders. A non-generic adapter record (`Enumerate`/`Zip`/
    // `slice::Iter`) is the bare record const.
    let record = reflect_iter_adapter_record(ty)?;
    let mut applied = cst(&record.name);
    for id in &record.type_params {
        applied = app(applied, cst(&param_const_name(id)));
    }
    Some(Ok(applied))
}

/// REAL-CODE COVERAGE — whether `ty` is a KNOWN stdlib iterator adapter that grounds
/// to a REAL record model (the `Trust.Adt.<Adapter>` record const, or its source for
/// a transparent `Copied`/`Cloned`). The DEPTH-METRIC predicate for iterator
/// combinators: an adapter parameter/local grounds STRUCTURALLY over its recovered
/// source + closure record, not the opaque internal layout. Fail-closed for an
/// unknown adapter or an unrecoverable source/closure/element.
#[must_use]
pub fn is_structural_iter_adapter(ty: &Ty) -> bool {
    matches!(reflect_known_iter_adapter(ty), Some(Ok(_)))
}

// ---------------------------------------------------------------------------
// Fail-closed error
// ---------------------------------------------------------------------------

/// Why a Trust type/sort could not be reflected into a Clean carrier term.
///
/// Replaces the silent `_ => Sort::Int` collapse: every family R does not (yet)
/// reflect surfaces as a distinct, catchable error rather than a wrong scalar
/// carrier. Each variant carries a `&'static str` description.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ReflectError {
    /// `Sort::Array` (a map sort) reached `reflect_sort`, which cannot see the
    /// element structure needed to build a `Vec`/`Slice`. Use `reflect_ty`.
    ArrayType(&'static str),
    /// `Ty::Float` — no IEEE-754 carrier yet; deliberately NOT aliased to BitVec.
    FloatType(&'static str),
    /// `Ty::Ref` (`&T` / `&mut T`) — reflected in M5.
    RefType(&'static str),
    /// `Ty::Never`.
    NeverType(&'static str),
    /// `Ty::Closure` — reflected in M5.
    ClosureType(&'static str),
    /// `Ty::FnDef`.
    FnDefType(&'static str),
    /// `Ty::FnPtr`.
    FnPtrType(&'static str),
    /// `Ty::Dynamic` (trait object) — reflected in M5.
    DynamicType(&'static str),
    /// `Ty::Coroutine`.
    CoroutineType(&'static str),
    /// `Ty::Unsupported`, or an unknown `#[non_exhaustive]` variant.
    UnsupportedType(&'static str),
    /// A `Formula` variant outside the core predicate subset `reflect_formula`
    /// handles (bitvector theory, quantifiers, arrays, interned `SymVar`, …).
    PredicateUnsupported(&'static str),
    /// A source contract could not be parsed. The original parse failure is
    /// retained so reflection cannot turn a malformed clause into `true`.
    SpecParse(String),
}

impl ReflectError {
    /// The human-readable description carried by this error.
    #[must_use]
    pub fn message(&self) -> &str {
        match self {
            ReflectError::ArrayType(m)
            | ReflectError::FloatType(m)
            | ReflectError::RefType(m)
            | ReflectError::NeverType(m)
            | ReflectError::ClosureType(m)
            | ReflectError::FnDefType(m)
            | ReflectError::FnPtrType(m)
            | ReflectError::DynamicType(m)
            | ReflectError::CoroutineType(m)
            | ReflectError::UnsupportedType(m)
            | ReflectError::PredicateUnsupported(m) => m,
            ReflectError::SpecParse(m) => m,
        }
    }
}

impl std::fmt::Display for ReflectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "cannot reflect type into a Clean carrier: {}", self.message())
    }
}

impl std::error::Error for ReflectError {}

// ---------------------------------------------------------------------------
// Term builders
// ---------------------------------------------------------------------------

fn cst(name: &str) -> ProofTerm {
    ProofTerm::Const(name.to_string())
}

fn app(f: ProofTerm, a: ProofTerm) -> ProofTerm {
    ProofTerm::App(Box::new(f), Box::new(a))
}

/// A `Trust.Nat` numeral term `Const("<n>")`.
fn nat(n: u64) -> ProofTerm {
    ProofTerm::Const(n.to_string())
}

/// Build the width-indexed BitVec carrier term `Trust.Sort.BitVec <w>`.
///
/// `ProofTerm` has no numeric literal, so the width is the numeral constant
/// `Const("<w>")` (a `Trust.Nat`) applied to the BitVec carrier.
#[must_use]
pub fn reflect_bitvec(width: u32) -> ProofTerm {
    app(cst(CARRIER_BITVEC), nat(u64::from(width)))
}

/// Reflect a list of component types as a right-nested product terminated by
/// `Trust.Sort.Unit`: `[A, B] -> Prod A (Prod B Unit)`. Used for tuples and
/// struct field lists. Recurses through `reflect_ty`, so a non-reflectable
/// component fails the whole product closed.
fn reflect_product(elems: &[Ty]) -> Result<ProofTerm, ReflectError> {
    match elems.split_first() {
        None => Ok(cst(CARRIER_UNIT)),
        Some((head, tail)) => {
            let head_term = reflect_ty(head)?;
            let tail_term = reflect_product(tail)?;
            Ok(app(app(cst(CARRIER_PROD), head_term), tail_term))
        }
    }
}

/// COVERAGE-AGENDA #4 — reflect a struct's NAMED fields as a right-nested
/// `Trust.Sort.Prod` product, applying the opaque-sink SHIM per field: a NESTED
/// `dyn`-trait writer-sink field collapses to the concrete `Trust.Sort.Sink` code
/// (decoding to the opaque atom `Trust.Sink`), and every other field reflects via
/// the ordinary [`reflect_ty`]. This keeps the parameter-binding product
/// (`reflect_ty(Formatter)`) in lockstep with the named inductive
/// [`reflect_struct`] registers — the `buf : dyn Write` field is the SAME
/// `Trust.Sort.Sink` carrier in both, so the `Formatter` parameter binds at a real
/// `Trust.SortTy` code (`El (Prod … Sink …)`) instead of the whole-parameter opaque
/// over-approximation. Fails closed transitively on any non-reflectable non-`dyn`
/// component (unchanged from [`reflect_product`]).
fn reflect_struct_product(fields: &[(String, Ty)]) -> Result<ProofTerm, ReflectError> {
    match fields.split_first() {
        None => Ok(cst(CARRIER_UNIT)),
        Some(((_, head_ty), tail)) => {
            let head_term =
                if is_nested_dyn_field(head_ty) { cst(CARRIER_SINK) } else { reflect_ty(head_ty)? };
            let tail_term = reflect_struct_product(tail)?;
            Ok(app(app(cst(CARRIER_PROD), head_term), tail_term))
        }
    }
}

// ---------------------------------------------------------------------------
// Phase 1: named-struct inductives (NON-GENERIC structs)
// ---------------------------------------------------------------------------

/// The mangled Clean inductive name for a Trust struct named `name`
/// (`Trust.Adt.<name>`). The struct name is sanitized so it forms a single
/// dotted path segment (Rust path separators `::` and any non-identifier byte
/// collapse to `_`), keeping the inductive name a stable, kernel-legal `Name`.
#[must_use]
pub fn adt_inductive_name(name: &str) -> String {
    sanitize_dotted_segment(ADT_PREFIX, name)
}

/// The single-constructor name for a struct inductive (`<inductive>.mk`).
#[must_use]
pub fn adt_ctor_name(inductive_name: &str) -> String {
    format!("{inductive_name}.mk")
}

/// A REAL single-constructor Clean inductive reflected from a NON-GENERIC Trust
/// struct — the Phase 1 replacement for the anonymous right-nested
/// `Trust.Sort.Prod` over-approximation.
///
/// This is a pure-data description (no `clean_kernel` dependency in `reflect.rs`):
/// `clean_ground::register_adt_carriers` translates it into a real
/// `clean_kernel::InductiveDecl` and feeds it to `Environment::add_inductive`,
/// which auto-derives the recursor + projections. The reflected struct then
/// grounds STRUCTURALLY — `p.value` resolves to the NAMED projection of
/// `Trust.Adt.<Name>`, not `Prod.fst` of an anonymous product.
///
/// Built for any struct whose every field type is concrete-and-reflectable OR a
/// bare generic type parameter; see [`reflect_struct`]. Phase 1 covers the
/// non-generic case (`type_params` empty); Phase 2 covers a struct with a
/// generic field, which becomes a PARAMETERIZED inductive (`type_params`
/// non-empty). A struct with a float/`dyn`/composite-with-var field still yields
/// `None`, falling back to the `Prod` carrier with no regression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdtCarrier {
    /// The Clean inductive name (`Trust.Adt.<Name>`).
    pub name: String,
    /// The single constructor name (`Trust.Adt.<Name>.mk`). For an ENUM (see
    /// [`Self::constructors`]) this names the FIRST variant's constructor and is
    /// otherwise unused — each variant carries its own constructor name.
    pub ctor_name: String,
    /// The fields in MIR definition order: `(field_name, reflected field-type
    /// carrier)`. The carrier is the `ProofTerm` `reflect_ty` produces for the
    /// field type: a `Trust.Sort.*` code for a concrete field, or the bound
    /// type-variable const `Trust.Param.<id>` for a GENERIC field (Phase 2). It
    /// is used to build the constructor arrow `τ₁ → … → τₙ → (<Name> T…)` when
    /// grounding. For an ENUM this is the struct/union (all-variant-fields) view,
    /// retained for compatibility; the genuine per-constructor shape is in
    /// [`Self::constructors`].
    pub fields: Vec<(String, ProofTerm)>,
    /// PHASE 2 — the DISTINCT generic type parameters this struct/enum is
    /// parameterized over, in first-appearance (MIR field) order, by stable
    /// identity (e.g. `T/#0`). EMPTY for a non-generic (Phase 1) struct. Non-empty
    /// ⇒ the inductive is registered as a PARAMETERIZED Clean inductive
    /// `Trust.Adt.<Name>` over `type_params.len()` `Type`-sorted parameters, and a
    /// generic field's carrier is the bound param const `Trust.Param.<id>`. A
    /// generic ENUM (`Option<T>`) reuses this exact parameterized path.
    pub type_params: Vec<String>,
    /// PHASE 4 — for an ENUM, one [`EnumCtor`] per variant (MIR variant order),
    /// each with its discriminant tag and reflected field carriers. EMPTY for a
    /// STRUCT (the single anonymous constructor over [`Self::fields`] is used).
    /// Non-empty ⇒ `register_adt_carriers` builds a REAL multi-constructor Clean
    /// inductive (auto-derived recursor / casesOn / noConfusion), not the single
    /// `.mk` struct shape.
    pub constructors: Vec<EnumCtor>,
}

/// PHASE 4 — one constructor of a reflected ENUM inductive
/// (`Trust.Adt.<Enum>.<Variant>`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumCtor {
    /// The Clean constructor name, `Trust.Adt.<Enum>.<Variant>`.
    pub name: String,
    /// The variant's discriminant tag (the value a `SwitchInt` compares against),
    /// so the registered inductive's constructors line up with the enum's MIR
    /// tag set and an exhaustive match's `otherwise -> Unreachable` discharges.
    pub discriminant: i128,
    /// This variant's fields in MIR order: `(field_name, reflected field carrier)`.
    /// A field-less variant (`None`, `B`) is a NULLARY constructor (`fields: []`).
    /// A concrete field's carrier is a `Trust.Sort.*` code; a GENERIC field's is
    /// the bound type-param const `Trust.Param.<id>` (the same Phase-2 encoding as
    /// a generic struct field).
    pub fields: Vec<(String, ProofTerm)>,
}

impl AdtCarrier {
    /// The field index of a named projection, iff `field` is one of the
    /// struct's fields (MIR order).
    #[must_use]
    pub fn field_index(&self, field: &str) -> Option<usize> {
        self.fields.iter().position(|(n, _)| n == field)
    }

    /// PHASE 4 — whether this carrier is an ENUM (≥1 reflected constructor). A
    /// STRUCT (Phase 1/2) has `constructors: []` and returns `false`.
    #[must_use]
    pub fn is_enum(&self) -> bool {
        !self.constructors.is_empty()
    }

    /// PHASE 2 — whether this carrier is a PARAMETERIZED inductive (has ≥1 generic
    /// type parameter). `false` for a Phase-1 non-generic struct.
    #[must_use]
    pub fn is_parameterized(&self) -> bool {
        !self.type_params.is_empty()
    }

    /// PHASE 2 — if `carrier` is a generic field carrier (`Trust.Param.<id>`)
    /// whose `<id>` is one of this struct's [`Self::type_params`], return that
    /// param's INDEX in `type_params`. `None` for a concrete-field carrier (which
    /// decodes to a real kernel type) or a param not in this struct's binder list.
    /// This is what maps a generic field's type to its bound `Type`-parameter.
    #[must_use]
    pub fn field_param_index(&self, carrier: &ProofTerm) -> Option<usize> {
        let ProofTerm::Const(n) = carrier else { return None };
        let id = n.strip_prefix(PARAM_PREFIX)?;
        self.type_params.iter().position(|p| p == id)
    }
}

/// RECURSIVE DEPENDENT CARRIER (goal bullet 2 tail) — the GENERALIZATION that closes
/// the remaining opaque fallback: if `fty` is ANY composite that nests a generic
/// type variable at ANY depth, return BOTH a STRUCTURAL field carrier and the
/// distinct type-param idents it ranges over (first-appearance order). This is the
/// recursive superset of the three earlier shapes:
///   * a bare type var `T` → `Trust.Param.<id>` (`[id]`);
///   * a SEQUENCE `Vec<X>`/`&[X]`/`Box<[X]>` whose element `X` recursively carries →
///     `Slice <X-carrier>` (so `Vec<Vec<T>>` → `Slice (Slice (Param T))`,
///     `Vec<Wrapper<T>>` → `Slice (Trust.Adt.Wrapper (Param T))`);
///   * a FIXED ARRAY `[X; N]` whose element recursively carries → `Vec <X-carrier> <n>`;
///   * a nested generic STRUCT `Wrapper<…>` → `Trust.Adt.Wrapper <param-args…>`
///     (each arg recursively the carrier of the corresponding generic field's var);
///   * a nested generic ENUM `E<…>` → `Trust.Adt.E <param-args…>` (same applied shape);
///   * a TUPLE `(A, B, …)` that nests a type var → the right-nested
///     `Prod <A-carrier> (Prod <B-carrier> … Unit)` over the recursively-carried
///     components.
///
/// The carrier is a MIXED term: `Trust.SortTy` heads (`Slice`/`Vec`/`Prod`/`Unit`/
/// concrete `BitVec`/…) interleaved with the Pi-bound type-var consts
/// (`Trust.Param.<id>`) and APPLIED named inductives (`Trust.Adt.<I> …`). The
/// decoder `clean_ground::carrier_to_kernel_field_type` walks it symmetrically:
/// `Slice`/`Vec` → `List`, `Prod` → kernel `Prod`, `Trust.Param.<id>` → the bound
/// de-Bruijn `Type` variable, `Trust.Adt.<I> args` → the inner inductive applied.
/// NO new axiom — `List`/`Prod`/`Unit` are axiom-free prelude inductives, and a
/// nested named inductive is registered first (post-order) by
/// `collect_adt_carriers_recursive`.
///
/// Returns `None` (→ existing concrete-`El`/opaque fallback, no regression) iff the
/// composite contains NO type variable (a fully-concrete type stays on the concrete
/// `El`-code path), OR a genuinely non-carriable component is reached (a `dyn`
/// element/field, a float, a non-reflectable family) — fail-closed, never unsound.
/// References are transparent (peeled). The returned `type_params` are DISTINCT in
/// first-appearance order.
fn parameterized_composite_field(fty: &Ty) -> Option<(ProofTerm, Vec<String>)> {
    let mut ids: Vec<String> = Vec::new();
    let carrier = composite_carrier(fty, &mut ids)?;
    // Only a GENUINELY parameterized composite routes here; a fully-concrete type
    // keeps the ordinary concrete `El`-code path (so `Vec<u32>` is unchanged).
    if ids.is_empty() {
        return None;
    }
    Some((carrier, ids))
}

/// Build the RECURSIVE carrier *code* for `fty`, pushing each distinct generic-param
/// ident encountered into `ids` (first-appearance order, de-duplicated). Returns the
/// carrier `ProofTerm` (a mix of `Trust.SortTy` heads, `Trust.Param.*` type-var
/// consts, and applied named inductives), or `None` to fail closed on a
/// non-carriable component (`dyn`/float/never/unknown). A concrete leaf reflects
/// through `reflect_ty` (so a concrete element/field is its real `Trust.SortTy`
/// code, e.g. `[u8; 4]` element → `BitVec 8`).
fn composite_carrier(fty: &Ty, ids: &mut Vec<String>) -> Option<ProofTerm> {
    // References are transparent for type reflection — peel `&X`/`&mut X`.
    if let Ty::Ref { inner, .. } = fty {
        return composite_carrier(inner, ids);
    }
    // A bare generic type variable `T` is the recursion's base case: its carrier is
    // the Pi-bound type-var const, and its ident joins `ids`.
    if let Some(var) = bare_type_var(fty) {
        let id = var.strip_prefix(PARAM_PREFIX)?.to_string();
        if !ids.contains(&id) {
            ids.push(id);
        }
        return Some(cst(&var));
    }
    match fty {
        // A SLICE / known sequence container (`Vec<X>`/`&[X]`/`Box<[X]>`/…) — the
        // element `X` recursively carries; the head stays the `Slice` code so the
        // decoder maps it to `List <decode X>`.
        Ty::Slice { elem } => {
            let elem_carrier = composite_carrier(elem, ids)?;
            Some(app(cst(CARRIER_SLICE), elem_carrier))
        }
        // A FIXED ARRAY `[X; N]` — the element recursively carries; the head stays
        // the length-indexed `Vec` code (decoded to `List`, length a separate VC).
        Ty::Array { elem, len } => {
            let elem_carrier = composite_carrier(elem, ids)?;
            Some(app(app(cst(CARRIER_VEC), elem_carrier), nat(*len)))
        }
        // A TRAIT OBJECT `dyn Trait` nested as a COMPOSITE ELEMENT (e.g. a tuple
        // component of a `Vec` field) FAILS CLOSED here. The existential
        // `Trust.Dyn.<trait>` is a closed `Type 1`, which a value-level `Prod`/`Slice`
        // (whose elements live at `Type 0`) cannot host — and the existential is modeled
        // STRUCTURALLY only as a standalone type / direct struct field (via the Sink
        // shim), NOT as a deeply-nested composite element (richer nesting is deferred).
        // Declining here keeps the whole composite field on the sound `Prod` floor.
        Ty::Dynamic { .. } => None,
        // A TUPLE that nests a type var → the right-nested `Prod … Unit` over the
        // recursively-carried components (a concrete component is its concrete code).
        Ty::Tuple(elems) => composite_product_carrier(elems, ids),
        // An ADT: a known sequence container reflects as a `Slice` over its element
        // (the element recursively carries); a transparent smart pointer forwards to
        // its inner; a generic struct/enum reflects as the APPLIED named inductive.
        Ty::Adt { variants, name, .. } => {
            if !variants.is_empty() {
                // A generic ENUM `E<…>` → `Trust.Adt.E <param-args…>`.
                return applied_generic_adt_carrier(fty, ids);
            }
            // A known SEQUENCE container (`Vec<X>`/`VecDeque<X>`/`String`) carries as a
            // `Slice` over its recovered element (recursively carried), mirroring
            // `reflect_known_container` but recursing into a generic element.
            if sequence_container_leaf(name).is_some() {
                let elem = sequence_element_ty(fty)?;
                let elem_carrier = composite_carrier(&elem, ids)?;
                return Some(app(cst(CARRIER_SLICE), elem_carrier));
            }
            // A TRANSPARENT smart pointer (`Box<X>`/`Rc<X>`/`Arc<X>`) forwards to its
            // recursively-carried inner (the pointer is invisible to the carrier).
            if smart_pointer_leaf(name) {
                let inner = smart_pointer_inner_ty(fty)?;
                return composite_carrier(&inner, ids);
            }
            // A generic STRUCT `Wrapper<…>` → `Trust.Adt.Wrapper <param-args…>`.
            applied_generic_adt_carrier(fty, ids)
        }
        // A FULL `Ty::Datatype` definition (non-empty variants; an EMPTY-variant
        // back-reference was already handled by the `bare_type_var` base case
        // above) FAILS CLOSED as a composite element. Its `reflect_ty` carrier is
        // the datatype's inductive applied to `Trust.Param.@datatype::*` recursion
        // variables — params this composite walk does NOT track in `ids` (so the
        // registering struct would not Pi-bind them) and whose `Trust.Adt.*` head
        // `reachable_adt_carriers` does not register. Declining keeps the whole
        // composite field on the sound `Prod`-floor / whole-parameter-opaque path
        // (via the caller's `carrier_mentions_param`/`code_mentions_type_var`
        // gates) instead of minting a carrier with untracked free consts.
        Ty::Datatype { .. } => None,
        // A concrete (non-type-var) leaf reflects to its real `Trust.SortTy` code; a
        // non-reflectable family (`dyn`/float/never/…) fails closed here.
        _ => reflect_ty(fty).ok(),
    }
}

/// Build the right-nested `Prod <c₀> (Prod <c₁> … Unit)` carrier over a tuple's
/// component types, each recursively carried via [`composite_carrier`]. Fails closed
/// on any non-carriable component (transitive, like [`reflect_product`]).
fn composite_product_carrier(elems: &[Ty], ids: &mut Vec<String>) -> Option<ProofTerm> {
    match elems.split_first() {
        None => Some(cst(CARRIER_UNIT)),
        Some((head, tail)) => {
            let head_c = composite_carrier(head, ids)?;
            let tail_c = composite_product_carrier(tail, ids)?;
            Some(app(app(cst(CARRIER_PROD), head_c), tail_c))
        }
    }
}

/// Build the APPLIED named-inductive carrier `Trust.Adt.<Name> <arg₀> … <argₖ₋₁>`
/// for a generic struct/enum `fty`, where each `<argᵢ>` is the RECURSIVE carrier of
/// the type the i-th type parameter is instantiated with — recovered from the field
/// that introduced that param. Pushes each nested param ident into `ids`. Returns
/// `None` for a non-parameterized inner ADT (a concrete inner struct/enum keeps the
/// concrete `El`-code path), or one whose registration would be non-structural.
///
/// The inner inductive's OWN `type_params` are the abstraction handle: `reflect_struct
/// /reflect_enum` already build the inner carrier with `type_params` in
/// first-field-of-use order, and the per-param instantiation argument is exactly the
/// recursive carrier the inner field at that param position would produce. For the
/// common monomorphization shape the extractor hands us, the inner ADT's fields carry
/// the instantiated types directly, so the applied arguments are the recursive
/// carriers of the inner ADT's generic-field types in `type_params` order.
fn applied_generic_adt_carrier(fty: &Ty, ids: &mut Vec<String>) -> Option<ProofTerm> {
    let carrier = reflect_struct(fty)?;
    // Only a PARAMETERIZED inner ADT needs the dependent applied carrier; a concrete
    // (Phase-1) inner struct/enum reflects to a real `El`-code already, and a known
    // container was intercepted by the caller.
    if !carrier.is_parameterized() {
        return None;
    }
    // The inner ADT's instantiation arguments, in `type_params` (binder) order: the
    // recursive carrier of the type bound to each inner param. We recover them from
    // the inner ADT's field types — each generic field's type IS (an instance of) one
    // of the inner params, so the carrier of that field type is the applied argument.
    let arg_tys = inner_adt_param_arg_tys(fty, &carrier)?;
    let mut applied = cst(&carrier.name);
    for arg_ty in &arg_tys {
        let arg_carrier = composite_carrier(arg_ty, ids)?;
        applied = app(applied, arg_carrier);
    }
    Some(applied)
}

/// Recover, in the inner ADT's `type_params` (binder) order, the `Ty` bound to each
/// of its type parameters — read off the field that first introduced that param.
/// `reflect_struct`/`reflect_enum` collect `type_params` in first-field-of-use order,
/// so for each param ident we find the first (struct or variant) field whose
/// recursive carrier mentions that ident and take that field's `Ty` as the binding.
/// `None` if any param has no introducing field (should not happen — a param only
/// enters `type_params` via a field).
fn inner_adt_param_arg_tys(fty: &Ty, carrier: &AdtCarrier) -> Option<Vec<Ty>> {
    let Ty::Adt { fields, variants, .. } = fty else { return None };
    // The candidate fields, in MIR order: a struct's fields, else every variant's.
    let candidate_fields: Vec<&Ty> = if variants.is_empty() {
        fields.iter().map(|(_, t)| t).collect()
    } else {
        variants.iter().flat_map(|v| v.fields.iter().map(|(_, t)| t)).collect()
    };
    let mut out = Vec::with_capacity(carrier.type_params.len());
    for id in &carrier.type_params {
        // The first field whose type mentions this param ident — its `Ty` is the
        // binding for this inner param. For the common single-param shape this is the
        // bare-`T` field; for a multi-param inner ADT each param's field is distinct.
        let bound = candidate_fields.iter().copied().find(|t| ty_mentions_param_id(t, id))?;
        out.push(bound.clone());
    }
    Some(out)
}

/// Whether the `Ty` `t` (recursively, transparently through references/composites)
/// mentions the generic-param whose stable ident is `id`.
fn ty_mentions_param_id(t: &Ty, id: &str) -> bool {
    if let Some(var) = bare_type_var(t) {
        return var.strip_prefix(PARAM_PREFIX) == Some(id);
    }
    match t {
        Ty::Ref { inner, .. } => ty_mentions_param_id(inner, id),
        Ty::Slice { elem } | Ty::Array { elem, .. } => ty_mentions_param_id(elem, id),
        Ty::Tuple(elems) => elems.iter().any(|e| ty_mentions_param_id(e, id)),
        Ty::Adt { fields, variants, .. } => {
            fields.iter().any(|(_, f)| ty_mentions_param_id(f, id))
                || variants
                    .iter()
                    .any(|v| v.fields.iter().any(|(_, f)| ty_mentions_param_id(f, id)))
        }
        _ => false,
    }
}

/// Reflect a Trust struct (`Ty::Adt`) into a REAL named Clean inductive carrier
/// ([`AdtCarrier`]), or `None` to fall back to the anonymous `Trust.Sort.Prod`
/// product.
///
/// Returns `Some` iff:
/// - `ty` is a `Ty::Adt` (a struct — a single-constructor "struct" is exactly the
///   `Ty::Adt` shape Trust emits), AND
/// - every field type is either concrete-and-reflectable, OR a BARE generic type
///   parameter `T` (`Ty::Unsupported{PARAM_KIND}`, possibly behind a transparent
///   reference). A bare-generic field makes the struct a Phase-2 PARAMETERIZED
///   inductive: its `<id>` joins [`AdtCarrier::type_params`] and the field's
///   carrier is the param const `Trust.Param.<id>`.
///
/// Field order is MIR definition order (the order in `Ty::Adt::fields`), so the
/// constructor arrow and the named projections line up with the struct layout.
/// `type_params` collects the DISTINCT bare-generic params in first-field-of-use
/// order, reusing the same `param_ident_from_detail` ident scheme as
/// `reflect_ty`/`reflect_contract`, so the SAME param maps consistently to the
/// SAME `Type`-binder everywhere in one function.
///
/// A `dyn`-typed field, a float/never field, or a COMPOSITE field that NESTS a
/// generic param (`Vec<T>`-shaped, `(T, u8)`, …) still makes this return `None`
/// — there is no faithful single carrier for a type-var nested inside a
/// `Trust.SortTy` composite — so the caller keeps today's `reflect_product`
/// behavior, with NO regression and NO unsound inductive.
#[must_use]
pub fn reflect_struct(ty: &Ty) -> Option<AdtCarrier> {
    let Ty::Adt { name, fields, variants, .. } = ty else {
        return None;
    };
    // PHASE 4 — an ENUM (`variants` non-empty) reflects to a REAL multi-constructor
    // inductive via `reflect_enum`, NOT the single-`.mk` struct shape. Dispatch
    // here so every existing caller (`reachable_adt_carriers`, `vc_refute`,
    // `prove`) picks up enums with no change.
    if !variants.is_empty() {
        return reflect_enum(ty);
    }
    // GOAL-ITEM #2 — a KNOWN std container (`Vec`/`Box`/`Rc`/`Arc`/`String`/…) must
    // NOT register as a named struct inductive over its type-erased INTERNAL layout
    // (`buf`/`len`/`ptr`). Its real model is `reflect_ty`'s `Slice T` / transparent
    // inner, so return `None` here: `reachable_adt_carriers` then registers no
    // spurious internal-layout inductive, and a container parameter binds through
    // the `reflect_ty` carrier (`carrier_binding_type`'s `El`/opaque path), not an
    // anonymous product of its private fields.
    if reflect_known_container(ty).is_some() {
        return None;
    }
    // REAL-CODE COVERAGE (collections) — a KNOWN map/set container must NOT register
    // as a named struct inductive over its type-erased hashbrown/btree INTERNAL
    // layout: its real model is `reflect_ty`'s `Slice (Prod K V)` / `Slice K`, so
    // return `None` here (no spurious internal-layout inductive; the value binds
    // through the `reflect_ty` carrier).
    if reflect_known_map(ty).is_some() {
        return None;
    }
    // REAL-CODE COVERAGE (iterator combinators) — a KNOWN stdlib iterator adapter
    // registers as its REAL RECORD carrier (`Trust.Adt.<Adapter>` over the recovered
    // source + closure / index), NOT the opaque `ptr`/`end_or_len`/`_marker` internal
    // product. `reachable_adt_carriers` then registers the record modulo 3, and a
    // value of the adapter type binds at the registered record const. A `Copied`/
    // `Cloned` adapter (transparent to its source) builds NO record here (its
    // `reflect_iter_adapter_record` is `None`), so it falls through to the source's
    // own carrier with no spurious inductive.
    if let Some(record) = reflect_iter_adapter_record(ty) {
        return Some(record);
    }
    // A field-less struct (`struct Unit;`) has no Int content to reason about and
    // an empty constructor; keep it on the `Prod`/`Unit` floor (still sound).
    if fields.is_empty() {
        return None;
    }
    let inductive_name = adt_inductive_name(name);
    let mut reflected_fields = Vec::with_capacity(fields.len());
    let mut type_params: Vec<String> = Vec::new();
    for (fname, fty) in fields {
        // COVERAGE-AGENDA #4 — a NESTED `dyn`-trait WRITER-SINK field (the
        // `core::fmt::Formatter` `buf : &mut dyn core::fmt::Write` shape) collapses to
        // the CONCRETE `Trust.Sort.Sink` code (decoding to the opaque atom
        // `Trust.Sink`), so the carrying struct REGISTERS as a real named inductive
        // instead of failing closed to `Prod`. Sound: the sink is inhabited but
        // structureless (faithfulness-neutral — a fmt contract says nothing about the
        // emitted bytes), and an obligation reading through it stays fail-closed. This
        // is what makes the 100%-boilerplate `Debug`/`Display::fmt` functions GROUND.
        if is_nested_dyn_field(fty) {
            reflected_fields.push((fname.clone(), cst(CARRIER_SINK)));
            continue;
        }
        // PHASE 2 — a BARE generic type variable field `value: T` (possibly behind
        // a transparent `&T`). It contributes its stable param ident to the
        // inductive's `type_params` (de-duplicated, first-appearance order) and the
        // field carrier is the bound type-param const `Trust.Param.<id>`. This is a
        // GENUINE dependent constructor field, not a `Prod` fallback.
        if let Some(var) = bare_type_var(fty) {
            // A trait-object field is handled by the Sink shim above; any other
            // non-`Param` opaque carrier (none today) keeps the struct on the Prod
            // floor (sound; deferred).
            let Some(id) = var.strip_prefix(PARAM_PREFIX) else {
                return None;
            };
            let id = id.to_string();
            if !type_params.contains(&id) {
                type_params.push(id.clone());
            }
            reflected_fields.push((fname.clone(), cst(&param_const_name(&id))));
            continue;
        }
        // RECURSIVE DEPENDENT CARRIER (goal bullet 2 tail) — a field whose type is
        // ANY composite that nests a generic type variable at ANY depth — a nested
        // generic struct `inner : Wrapper<T>`, a sequence `items : Vec<T>` / `[T; N]`,
        // a DEEPLY-nested sequence `Vec<Vec<T>>` / `Vec<Wrapper<T>>`, a tuple `(T, u8)`,
        // or a nested generic enum — carries its `Sort 1` type-variable(s) in FIELD
        // position STRUCTURALLY via [`parameterized_composite_field`]: the carrier is a
        // mix of `Trust.SortTy` heads (`Slice`/`Vec`/`Prod`) and the Pi-bound type-var
        // consts / applied inner inductives. `ctor_field_type` decodes the whole carrier
        // to the real dependent kernel type (`List (List (BVar T))`, `Wrapper (BVar T)`,
        // `Prod (BVar T) (BitVec 8)`, …). The nested params join THIS struct's binder
        // list (de-duplicated, first-appearance order). NO anonymous `Prod` floor, NO
        // opaque fallback, NO new axiom (`List`/`Prod` are axiom-free; a nested named
        // inductive is registered first, post-order). This SUBSUMES the earlier
        // direct-only nested-struct / direct-sequence cases and recurses through them.
        if let Some((composite_carrier, nested_param_ids)) = parameterized_composite_field(fty) {
            for id in nested_param_ids {
                if !type_params.contains(&id) {
                    type_params.push(id);
                }
            }
            reflected_fields.push((fname.clone(), composite_carrier));
            continue;
        }
        // A concrete field type must be reflectable. `reflect_ty` fails closed on
        // non-reflectable families (float, never, dyn, …). A carrier that STILL nests
        // a param/dyn const after the recursive case declined (e.g. a `(dyn, T)` tuple
        // whose `dyn` component is non-carriable) has no faithful `Trust.SortTy`
        // carrier, so the whole struct falls back to Prod (sound, deferred).
        let carrier = reflect_ty(fty).ok()?;
        if carrier_mentions_param(&carrier) {
            return None;
        }
        reflected_fields.push((fname.clone(), carrier));
    }
    Some(AdtCarrier {
        ctor_name: adt_ctor_name(&inductive_name),
        name: inductive_name,
        fields: reflected_fields,
        type_params,
        // STRUCT: single anonymous `.mk` constructor (no per-variant ctors).
        constructors: Vec::new(),
    })
}

/// GOAL-ITEM #3 — reflect an IEEE-754 float type of `width` bits into a REAL
/// single-constructor Clean inductive carrier ([`AdtCarrier`]) decomposing the bit
/// layout into NAMED fields, or `None` for an unsupported width (the caller then
/// fails closed — NEVER aliases a float onto a flat BitVec).
///
/// - f32 → `Trust.Float32 { sign : Bool, exponent : BitVec 8,  mantissa : BitVec 23 }`
/// - f64 → `Trust.Float64 { sign : Bool, exponent : BitVec 11, mantissa : BitVec 52 }`
///
/// This is a NON-generic struct shape (`type_params`/`constructors` empty), so
/// [`super::clean_ground::register_adt_carriers`] registers it as a real
/// `Trust.FloatN` inductive (constructor `Trust.FloatN.mk`, kernel-derived named
/// projections + recursor), passing the modulo-3 axiom gate: the `sign` field's
/// `Bool` carrier and the `exponent`/`mantissa` `BitVec` carriers decode to the
/// prelude's axiom-free `Bool`/`Int` inductives — NO 4th axiom, NO opaque
/// declaration. A `Trust.Float32.sign` etc. projection then resolves to the kernel's
/// auto-derived named projection, exactly as for a P1 struct field.
/// The `Ty` decomposition of an IEEE-754 float of `width` bits, in MSB→LSB order:
/// `[Bool (sign), Int{exp,unsigned} (exponent), Int{mant,unsigned} (mantissa)]`.
/// `reflect_product` over this list yields exactly the same `Trust.Sort.Prod` code as
/// [`reflect_float`]'s field carriers, so `reflect_ty(Ty::Float)` and the named
/// inductive's fields agree. `None` for an unsupported width (fail closed).
#[must_use]
pub fn float_field_tys(width: u32) -> Option<Vec<Ty>> {
    let (exp_bits, mant_bits) = ieee754_layout(width)?;
    Some(vec![
        Ty::Bool,
        Ty::Int { width: exp_bits, signed: false },
        Ty::Int { width: mant_bits, signed: false },
    ])
}

#[must_use]
pub fn reflect_float(width: u32) -> Option<AdtCarrier> {
    let name = float_inductive_name(width)?.to_string();
    let (exp_bits, mant_bits) = ieee754_layout(width)?;
    let ctor_name = adt_ctor_name(&name);
    // IEEE-754 field order (MSB → LSB): sign (1 bit, a Bool), the biased exponent
    // (`exp_bits`-wide bitvector → Int), and the trailing significand / mantissa
    // (`mant_bits`-wide bitvector → Int). The carriers are exactly what `reflect_ty`
    // emits for a `Bool` / `Int{width=exp}` / `Int{width=mant}` scalar, so they
    // decode through the existing `decode_el_code`/`carrier_code_to_kernel_type`.
    let fields = vec![
        ("sign".to_string(), cst(CARRIER_BOOL)),
        ("exponent".to_string(), reflect_bitvec(exp_bits)),
        ("mantissa".to_string(), reflect_bitvec(mant_bits)),
    ];
    Some(AdtCarrier { ctor_name, name, fields, type_params: Vec::new(), constructors: Vec::new() })
}

// ---------------------------------------------------------------------------
// PTR-INTRINSIC MODEL (goal items 2+3) — pointer-producing
// `core::ptr::{offset,add,sub}` calls as a FIRST-CLASS reflected value: a (base
// slice, index) pointer into its pointee sequence. Read formulas are
// representational helpers only until a live caller authenticates their stricter
// safety obligation.
// ---------------------------------------------------------------------------
//
// The multi-crate coverage measurement found calls/ptr-intrinsics are the #1
// real-code exit (86% of functions; ptr-intrinsic 303 within calls). Slice
// indexing, iteration, and owned-collection access all lower to pointer
// ARITHMETIC — a `slice.as_ptr()` gives the base pointer at INDEX 0, `ptr::add(p,
// k)` advances the index by `k`, `ptr::sub(p, k)` retreats it, `ptr::offset(p, k)`
// is the signed advance, and `ptr::read(p)` reads the element AT that index.
//
// The bare-pointer carrier [`reflect_ptr`] (`Trust.Ptr { addr : Int }`) is the
// OPAQUE-address model with NO pointee value — it deliberately keeps a
// dereference fail-closed. This model is the COMPLEMENTARY one for the common
// case a pointer is derived FROM A KNOWN SLICE (`slice.as_ptr()` then arithmetic):
// there the pointer IS a slice-relative INDEX, so `ptr::add`/`sub`/`offset`
// reflect to INDEX ARITHMETIC over the SAME `Int`/`slice_len`/`idx_elem`
// vocabulary the array-index fragment already grounds — modulo 3, NO new axiom,
// NO new opaque constant. [`ptr_read_element`] can represent a prospective
// `ptr::read(p)` as `Select(slice, index)` (grounds to `idx_elem`, exactly like
// `s[i]`), but the live operand recognizer deliberately rejects call-defined read
// results today.
//
// FAIL-CLOSED IN-BOUNDS VC: an admitted offset must separately pass
// [`ptr_offset_bounds_vc`]. A read would instead have to pass the STRICT
// [`ptr_read_bounds_vc`] (`index < len`, never the offset's `index ≤ len`). No
// authenticated live read consumer is wired yet, so a one-past-end offset can
// never be smuggled into a modeled read result.

/// The recognized pointer-ARITHMETIC intrinsic a `Terminator::Call` invokes on a
/// `*const T` / `*mut T` derived from a slice. Each maps a `(pointer, count)` (or a
/// bare `pointer` for `Read`/`AsPtr`) call to an index transform on the pointer's
/// slice-relative INDEX.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PtrArith {
    /// `slice.as_ptr()` / `as_mut_ptr()` — the BASE pointer at INDEX 0 of its slice.
    AsPtr,
    /// `ptr::add(p, k)` — INDEX advances by `k` (unsigned). In-bounds: `i + k ≤ len`.
    Add,
    /// `ptr::sub(p, k)` — INDEX retreats by `k` (unsigned). In-bounds: `k ≤ i`.
    Sub,
    /// `ptr::offset(p, k)` — INDEX advances by the SIGNED `k`. In-bounds:
    /// `0 ≤ i + k ≤ len`.
    Offset,
    /// `ptr::read(p)` / `read_unaligned(p)` — the ELEMENT at the pointer's INDEX
    /// (`Select(slice, index)`). In-bounds: `i < len`.
    Read,
}

impl PtrArith {
    /// Classify a `Terminator::Call` callee path into the pointer-arithmetic family,
    /// or `None` (fail-closed) for any callee outside the modeled set. Matches the
    /// monomorphized `core::ptr::{const,mut}_ptr::<impl *…>::…` shapes the dumps
    /// carry (`as_ptr`, `add`, `sub`, `offset`, `read`/`read_unaligned`).
    #[must_use]
    pub fn classify(callee: &str) -> Option<Self> {
        // Def-path identity is authority here: a source crate can freely name a
        // module `slice`/`const_ptr` and a method `as_ptr`/`add`.  Substring or
        // tail-name matching would therefore let an arbitrary safe user function
        // masquerade as pointer arithmetic.  Accept only the canonical core/std
        // inherent-impl owners emitted by rustc.  The concrete type text inside
        // `<impl …>` is intentionally opaque (it may be monomorphized), but the
        // owner grammar around it is exact.
        let (owner, method) = callee.rsplit_once("::")?;
        let impl_owner = |prefix: &str, suffix: &str| {
            owner
                .strip_prefix(prefix)
                .and_then(|rest| rest.strip_suffix(suffix))
                .is_some_and(|inner| !inner.trim().is_empty())
        };
        let canonical_slice_owner =
            ["core", "std"].iter().any(|root| impl_owner(&format!("{root}::slice::<impl ["), "]>"));
        if canonical_slice_owner && matches!(method, "as_ptr" | "as_mut_ptr") {
            return Some(PtrArith::AsPtr);
        }

        // Arithmetic/read methods live on the exact raw-pointer inherent impls.
        match canonical_raw_ptr_method(callee)? {
            "add" => Some(PtrArith::Add),
            "sub" => Some(PtrArith::Sub),
            "offset" => Some(PtrArith::Offset),
            "read" | "read_unaligned" | "read_volatile" => Some(PtrArith::Read),
            _ => None,
        }
    }

    /// Whether this operation is a POINTER-PRODUCING offset (`AsPtr`/`Add`/`Sub`/
    /// `Offset`) — its dest is a new pointer whose slice-relative index is the
    /// transform of the input's. `Read` produces the ELEMENT, not a pointer.
    #[must_use]
    pub fn is_offset(self) -> bool {
        matches!(self, PtrArith::AsPtr | PtrArith::Add | PtrArith::Sub | PtrArith::Offset)
    }
}

/// Return the method tail only when `callee` names a canonical core/std raw-pointer
/// inherent impl.  This shared identity gate also protects the loop-counter lane,
/// whose allowlist includes `wrapping_add` but must not fall back to substring
/// matching for its owner.
pub(crate) fn canonical_raw_ptr_method(callee: &str) -> Option<&str> {
    let (owner, method) = callee.rsplit_once("::")?;
    let impl_owner = |prefix: &str, suffix: &str| {
        owner
            .strip_prefix(prefix)
            .and_then(|rest| rest.strip_suffix(suffix))
            .is_some_and(|inner| !inner.trim().is_empty())
    };
    ["core", "std"]
        .iter()
        .any(|root| {
            impl_owner(&format!("{root}::ptr::const_ptr::<impl *const "), ">")
                || impl_owner(&format!("{root}::ptr::mut_ptr::<impl *mut "), ">")
        })
        .then_some(method)
}

/// The slice-relative model of a `*const T` / `*mut T` derived from a known slice:
/// the `slice` base (a `Formula` naming the pointee sequence — a parameter slice or
/// a nested one) and the `index` into it (a `Formula` over `Int`). `slice.as_ptr()`
/// is `{ slice, index: 0 }`; `ptr::add(p, k)` advances `index` by `k`.
///
/// This is the value the pointer-arithmetic reflection resolves a pointer temp to
/// — the (base, index) pair the goal calls for. The bounds VC ([`ptr_offset_bounds_vc`])
/// is a SEPARATE, fail-closed obligation over the same `index`/`slice`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PtrModel {
    /// The pointee SEQUENCE the pointer walks — a `Formula` naming the base slice
    /// (typically `Formula::Var(slice_param)`), the `s` in `idx_elem`/`slice_len`.
    pub slice: Formula,
    /// The slice-relative INDEX the pointer currently addresses, a `Formula` over
    /// `Int` (`0` at `as_ptr`, `index + k` after `ptr::add(p, k)`).
    pub index: Formula,
    /// The PROVENANCE ROOT (which representation invariant licenses the in-bounds
    /// discharge). `SliceStart` for an `as_ptr`-rooted pointer; `IterCursor` for a
    /// slice-iterator cursor field (see [`PtrProvenance`]).
    pub provenance: PtrProvenance,
}

/// The PROVENANCE ROOT of a [`PtrModel`] — the fact that grounds its offset's
/// in-bounds obligation. The `(slice, index)` pair is the same in both; the
/// provenance selects the DISCHARGE DISCIPLINE
/// ([`crate::clean_ground::ptr_offset_bounds_open`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PtrProvenance {
    /// Rooted at `slice.as_ptr()`: `index` is measured from the slice START, and the
    /// upper bound `index ≤ slice_len(slice)` is a BODY-LOCAL fact discharged by the
    /// narrow syntactic decision procedure (`0 ≤ 0`, `len ≤ len`).
    SliceStart,
    /// P-ITER-CURSOR — rooted at a `&mut core::slice::iter::Iter<'_, T>` (non-ZST T)
    /// CURSOR field. `slice` names the REMAINING region `[cursor..end]`; `index` is
    /// measured from the CURRENT cursor (index 0 = the cursor). The `+k` bound
    /// `k ≤ len(region)` is NOT body-local: it rests on std's ENCAPSULATED
    /// representation invariant `start ≤ ptr ≤ end` (so `len(region) ≥ 0`) CONJOINED
    /// with a dominating `cursor != end` guard (so `len(region) ≥ 1`). Only
    /// `k ∈ {0, 1}` discharges (`k = 0` from the premise alone, `k = 1` from
    /// premise ∧ guard); `k ≥ 2` stays OPEN — the guard licenses exactly one step.
    IterCursor,
}

impl PtrModel {
    /// The BASE pointer `slice.as_ptr()`: index `0` into `slice`.
    #[must_use]
    pub fn base(slice: Formula) -> Self {
        PtrModel { slice, index: Formula::Int(0), provenance: PtrProvenance::SliceStart }
    }

    /// P-ITER-CURSOR base: the CURRENT cursor of a slice iterator at index `0` of its
    /// remaining region `region` (`[cursor..end]`). See [`PtrProvenance::IterCursor`].
    #[must_use]
    pub fn iter_cursor(region: Formula) -> Self {
        PtrModel { slice: region, index: Formula::Int(0), provenance: PtrProvenance::IterCursor }
    }

    /// The pointer-ARITHMETIC transform `ptr::<op>(self, k)` — a NEW `PtrModel` over
    /// the SAME slice whose index is the offset of `self.index` by `k`:
    ///   * `Add`    → `index + k`
    ///   * `Sub`    → `index - k`
    ///   * `Offset` → `index + k` (the signed `k` is already the delta)
    ///   * `AsPtr`  → unreachable here (no count operand; use [`PtrModel::base`])
    ///   * `Read`   → unreachable here (produces the element; see [`ptr_read_element`])
    ///
    /// Returns `None` (fail-closed) for the non-offset ops so a caller never
    /// mistakes a read for a pointer.
    #[must_use]
    pub fn offset_by(&self, op: PtrArith, k: &Formula) -> Option<Self> {
        let index = match op {
            PtrArith::Add | PtrArith::Offset => {
                Formula::Add(Box::new(self.index.clone()), Box::new(k.clone()))
            }
            PtrArith::Sub => Formula::Sub(Box::new(self.index.clone()), Box::new(k.clone())),
            PtrArith::AsPtr | PtrArith::Read => return None,
        };
        // The offset preserves the base pointer's PROVENANCE — advancing an `as_ptr`
        // pointer keeps `SliceStart`; advancing an iterator cursor keeps `IterCursor`.
        Some(PtrModel { slice: self.slice.clone(), index, provenance: self.provenance })
    }
}

/// The abstract REMAINING-REGION sequence of a slice iterator whose cursor is
/// `param`-derived: `Trust.MirSem.iter_region(param)` — the `[cursor..end]` sequence
/// whose `slice_len` is the count of not-yet-yielded elements. Deliberately a `Pred`
/// (never a bare `Formula::Var`), so the ptr-spine-arg lane — which admits only a
/// bare-PARAMETER `slice` — never mistakes an iterator cursor for a slice argument,
/// and no `slice.as_ptr()` model can alias it.
#[must_use]
pub fn iter_region_formula(param: Formula) -> Formula {
    Formula::Pred(trust_types::Symbol::intern("Trust.MirSem.iter_region"), vec![param])
}

/// Represent the ELEMENT a prospective `ptr::read(p)` would read as
/// `Select(slice, index)` — the SAME array-read shape a safe `s[i]` reflects to,
/// which [`clean_ground::ground_int`] grounds to the uninterpreted total
/// `idx_elem (g slice) (g index)`. This helper does not authenticate a MIR read:
/// a live caller must first discharge [`ptr_read_bounds_vc`], and no such caller is
/// currently wired.
#[must_use]
pub fn ptr_read_element(model: &PtrModel) -> Formula {
    Formula::Select(Box::new(model.slice.clone()), Box::new(model.index.clone()))
}

/// The slice LENGTH `slice_len(slice)` — the `Formula::Pred` keyed by the canonical
/// `Trust.MirSem.slice_len` name the array-length fragment grounds (see
/// `mirsem::SemOperand::Len::to_formula`). The `b` operand of the in-bounds bound.
#[must_use]
pub fn slice_len_formula(slice: &Formula) -> Formula {
    Formula::Pred(trust_types::Symbol::intern("Trust.MirSem.slice_len"), vec![slice.clone()])
}

/// The FAIL-CLOSED IN-BOUNDS VC for a pointer OFFSET `ptr::<op>(p, k)` producing a
/// pointer at `new_index` into `slice`: the offset must stay within the sequence,
/// `0 ≤ new_index ∧ new_index ≤ len(slice)` (the one-past-the-end pointer at
/// `len` is legal for an offset that is never read). Grounds via
/// [`clean_ground::ground_prop`] over the SAME `Int.le`/`slice_len` vocabulary.
///
/// SOUNDNESS: this is emitted as a SEPARATE obligation and left OPEN when it cannot
/// be discharged — an unbounded/out-of-bounds offset (e.g. `ptr::add(p, huge)`)
/// leaves it unprovable, so the function is grounded-NOT-faithful and NEVER falsely
/// certified. `slice.as_ptr()` at index 0 has the trivially-true `0 ≤ 0 ∧ 0 ≤ len`;
/// `ptr::add(as_ptr(s), len(s))` has `len ≤ len` (the exact `count`-shaped case),
/// also provable.
#[must_use]
pub fn ptr_offset_bounds_vc(model: &PtrModel) -> Formula {
    let zero = Formula::Int(0);
    let lower = Formula::Le(Box::new(zero), Box::new(model.index.clone()));
    let upper =
        Formula::Le(Box::new(model.index.clone()), Box::new(slice_len_formula(&model.slice)));
    Formula::And(vec![lower, upper])
}

/// The FAIL-CLOSED IN-BOUNDS VC for a pointer READ `ptr::read(p)` at `model.index`:
/// a read requires a STRICTLY in-bounds index (there is no one-past-the-end READ),
/// `0 ≤ index ∧ index < len(slice)`. Grounds via [`clean_ground::ground_prop`].
/// Left OPEN (fail-closed) when unprovable, exactly like the offset bound.
#[must_use]
pub fn ptr_read_bounds_vc(model: &PtrModel) -> Formula {
    let zero = Formula::Int(0);
    let lower = Formula::Le(Box::new(zero), Box::new(model.index.clone()));
    let upper =
        Formula::Lt(Box::new(model.index.clone()), Box::new(slice_len_formula(&model.slice)));
    Formula::And(vec![lower, upper])
}

/// COVERAGE-AGENDA #2 — reflect the SHALLOW opaque-address model of a BARE raw
/// pointer into the [`PTR_INDUCTIVE`] (`Trust.Ptr`) carrier: a NON-generic
/// single-constructor struct `Trust.Ptr { addr : Int }` whose sole field is the
/// abstract pointer ADDRESS (an axiom-free `Int`). It registers through the SAME
/// modulo-3 `register_adt_carriers` path as any non-generic struct/float carrier
/// (constructor `Trust.Ptr.mk : Int → Trust.Ptr`, a kernel-derived `addr`
/// projection + recursor), introducing NO 4th axiom: the `Int` address field
/// decodes to the prelude's axiom-free `Int`. The inhabitant
/// `Trust.Ptr.mk (Int.ofNat 0)` (the null address) is what `default_inhabitant`
/// synthesizes for a bare-pointer return, grounding the dominant clone/Default/
/// Debug contracts that never dereference. The `addr` field is DELIBERATELY the
/// only structure: the pointer has an address but NO pointee value (the points-to
/// model is deferred), so a dereference reading through it stays fail-closed.
#[must_use]
pub fn reflect_ptr() -> AdtCarrier {
    let name = PTR_INDUCTIVE.to_string();
    let ctor_name = adt_ctor_name(&name);
    // The single field is the abstract ADDRESS, modeled as `Int` (the same carrier
    // `reflect_ty` emits for an integer scalar), so it decodes through the existing
    // `carrier_code_to_kernel_type` and inhabits via `Int = 0`.
    let fields = vec![("addr".to_string(), cst(CARRIER_INT))];
    AdtCarrier { ctor_name, name, fields, type_params: Vec::new(), constructors: Vec::new() }
}

/// COVERAGE-AGENDA #4 — reflect the abstract WRITER-SINK model of a nested `dyn`
/// trait-object field into the [`SINK_INDUCTIVE`] (`Trust.Sink`) carrier: a
/// NON-generic, FIELD-LESS single-constructor inductive `Trust.Sink` (constructor
/// `Trust.Sink.mk : Trust.Sink`) — a pure abstract atom with NO structure, exactly
/// like the kernel `Unit`.
///
/// It registers through the SAME modulo-3 `register_adt_carriers` path as any
/// non-generic struct/float/ptr carrier and introduces NO 4th axiom (a field-less
/// inductive is axiom-free — its constructor and recursor rest on only the 3
/// foundational axioms). The inhabitant `Trust.Sink.mk` is what `default_inhabitant`
/// synthesizes for a `Formatter`-shaped struct's `buf : dyn Write` field, grounding
/// the dominant `Debug`/`Display::fmt` contracts (which never read the sink's bytes).
/// The atom is DELIBERATELY structureless: a `dyn Write` value carries no faithful
/// integer/value model in the dependent-type carrier, so an obligation reading
/// through the sink stays fail-closed (sound), and an integer fact about a
/// `Trust.Sink`-typed value is unprovable (it is not `Int`).
#[must_use]
pub fn reflect_sink() -> AdtCarrier {
    let name = SINK_INDUCTIVE.to_string();
    let ctor_name = adt_ctor_name(&name);
    // NO fields — the writer sink is a pure abstract atom (single nullary ctor).
    AdtCarrier {
        ctor_name,
        name,
        fields: Vec::new(),
        type_params: Vec::new(),
        constructors: Vec::new(),
    }
}

/// TYPE-ZOO #4 (HRTBs) — reflect the erased lifetime/REGION carrier `Trust.Region`:
/// a NON-generic, FIELD-LESS single-constructor inductive (`Trust.Region.mk :
/// Trust.Region`) — a pure abstract atom with NO structure, exactly like `Trust.Sink`
/// / the kernel `Unit`. A lifetime is value-erased at MIR, so its carrier is a closed
/// atom; the higher-ranked quantifier `for<'a> …` is modeled as a real kernel `Pi`
/// over this `Type` (see [`reflect_hrtb_fn`]). Registers through the SAME modulo-3
/// nullary `register_adt_carriers` path (axiom-free — NO 4th axiom). Inhabited by
/// `Trust.Region.mk`.
#[must_use]
pub fn reflect_region() -> AdtCarrier {
    let name = REGION_INDUCTIVE.to_string();
    let ctor_name = adt_ctor_name(&name);
    AdtCarrier {
        ctor_name,
        name,
        fields: Vec::new(),
        type_params: Vec::new(),
        constructors: Vec::new(),
    }
}

/// TYPE-ZOO #4 (HRTBs) — reflect a HIGHER-RANKED bound `for<'a> Fn(args… over 'a) ->
/// ret` into a GENUINE kernel `Pi` quantifying the erased region:
///
/// ```text
///   Π(r : Trust.Region) → (El R(arg₀) → … → El R(argₙ) → El R(ret))
/// ```
///
/// — the universal quantifier `for<'a>` is the outer `Π(r : Trust.Region)`, and the
/// inner arrow is the function signature reflected via [`reflect_fn_sig_pi`] (so a
/// non-`El`-decodable / opaque-type-variable parameter or return fails the whole HRTB
/// closed, exactly like a plain fn pointer). The kernel has `Pi`/`Type` primitively
/// (rooted in the 3), and `Trust.Region` is the axiom-free atom from [`reflect_region`]
/// — so the whole HRTB type rests on ⊆ the 3, NO 4th axiom. Multiple `for<'a, 'b>`
/// regions nest as additional outer `Π(r : Trust.Region)` binders (one per lifetime).
///
/// # Errors
///
/// Returns the [`ReflectError`] naming the first non-reflectable / opaque-type-variable
/// parameter or return (fails closed transitively, like [`reflect_fn_sig_pi`]).
pub fn reflect_hrtb_fn(num_regions: usize, sig: &FnSig) -> Result<ProofTerm, ReflectError> {
    // The inner fn arrow `El R(arg) → … → El R(ret)`.
    let inner = reflect_fn_sig_pi(sig)?;
    // Wrap in one `Π(r : Trust.Region)` per higher-ranked lifetime (`for<'a, 'b, …>`).
    Ok((0..num_regions).fold(inner, |acc, _| ProofTerm::Pi {
        binder_name: "_region".to_string(),
        domain: Box::new(cst(CARRIER_REGION)),
        codomain: Box::new(acc),
    }))
}

/// TYPE-ZOO #1 (CONST GENERICS) — reflect a fixed-size array `[T; N]` into the
/// APPLIED length-indexed carrier `Trust.ArrayN (decode T) N`, where `N` is a REAL
/// `Trust.Nat` value (the const generic as a genuine dependent INDEX), NOT the
/// length-erased `Slice`/`List` model. The element `T` reflects via [`reflect_ty`]
/// (so a non-reflectable element fails the whole array closed); the length is the
/// `Nat` numeral `Const("<n>")`. `clean_ground::register_arrayn_carrier` registers the
/// `Trust.ArrayN` inductive (one `Type` param + one `Nat` index) modulo 3, and the
/// decoder grounds this carrier to the kernel `ArrayN (decode T) (Nat.lit n)`.
///
/// # Errors
///
/// Returns the [`ReflectError`] naming the non-reflectable element type.
pub fn reflect_array_indexed(elem: &Ty, len: u64) -> Result<ProofTerm, ReflectError> {
    let elem_code = reflect_ty(elem)?;
    // `Trust.ArrayN (El-decodable elem) <n>` — the length is a real Nat numeral, so
    // `ArrayN T 4` and `ArrayN T 8` are DISTINCT dependent types (length-indexed).
    Ok(app(app(cst(CARRIER_ARRAYN), elem_code), nat(len)))
}

/// TYPE-ZOO #2 (impl Trait, RPIT/TAIT) — the stable existential const name for an
/// `impl Trait` opaque type over `trait_name` (`Trust.Impl.<trait>`), the
/// `impl Trait` analogue of [`dyn_const_name`]. Distinct prefix so an `impl Trait`
/// and a `dyn Trait` over the same trait register as separate existentials.
#[must_use]
pub fn impl_trait_const_name(trait_name: &str) -> String {
    sanitize_dotted_segment(IMPL_TRAIT_PREFIX, trait_name)
}

/// TYPE-ZOO #2 (impl Trait) — the vtable-record inductive name for an `impl Trait`
/// existential over `trait_name` (`Trust.Impl.Vtable.<trait>`).
#[must_use]
pub fn impl_trait_vtable_record_name(trait_name: &str) -> String {
    sanitize_dotted_segment("Trust.Impl.Vtable.", trait_name)
}

/// TYPE-ZOO #2 (impl Trait, RPIT/TAIT) — reflect an OPAQUE return type `impl Trait`
/// into the EXISTENTIAL `Sigma (T:Type), Vtable_<trait> T` — the SAME dependent-pair
/// model a `dyn Trait` uses ([`reflect_dyn`]), under the distinct `Trust.Impl.<trait>`
/// name. An `impl Trait` is "∃ a concrete carrier `T` with the trait witness"; the
/// only difference from `dyn` is the erasure site (a return-position opaque vs. a
/// dispatch object), and the dependent-type is identical — so this reuses the
/// `DynCarrier` machinery wholesale (registered modulo 3 by
/// `register_dyn_carriers`, axiom_deps EMPTY, NO free const, NO 4th axiom). With no
/// method signatures available from the extractor the record is the best-sound
/// `Sigma (T:Type) Unit` (an existential over an opaque-but-QUANTIFIED carrier).
#[must_use]
pub fn reflect_impl_trait(trait_name: &str, methods: &[(String, FnSig)]) -> DynCarrier {
    let vtable_name = impl_trait_vtable_record_name(trait_name);
    let vtable_ctor_name = dyn_vtable_ctor_name(&vtable_name);
    let reflected_methods = methods
        .iter()
        .filter_map(|(m, sig)| reflect_fn_sig(sig).ok().map(|carrier| (m.clone(), carrier)))
        .collect();
    DynCarrier {
        name: impl_trait_const_name(trait_name),
        vtable_name,
        vtable_ctor_name,
        methods: reflected_methods,
    }
}

/// TYPE-ZOO #3 (MULTI-BOUND trait objects, `dyn A + B + Send`) — split a `+`-joined
/// multi-bound trait-object name into its component trait paths, in source order. A
/// single-bound `dyn Trait` returns `["Trait"]`. Whitespace around each `+` is
/// trimmed. Used by [`reflect_multi_dyn`] to build the CONJOINED vtable record.
#[must_use]
pub fn split_multi_bound(trait_name: &str) -> Vec<String> {
    trait_name
        .split('+')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(ToString::to_string)
        .collect()
}

/// TYPE-ZOO #3 (MULTI-BOUND trait objects) — whether a trait-bound component is a
/// value-LESS MARKER trait (`Send`/`Sync`/`Sized`/`Unpin`/`Copy`-shaped auto traits).
/// A marker contributes NO vtable methods (an EMPTY obligation), so it adds nothing to
/// the conjoined record — exactly the goal's "marker traits contribute an empty/unit
/// obligation". Keyed on the leaf name (last `::` segment).
#[must_use]
pub fn is_marker_trait(trait_name: &str) -> bool {
    let leaf = trait_name.rsplit("::").next().unwrap_or(trait_name).trim();
    matches!(leaf, "Send" | "Sync" | "Sized" | "Unpin" | "Copy" | "RefUnwindSafe" | "UnwindSafe")
}

/// TYPE-ZOO #3 (MULTI-BOUND trait objects, `dyn A + B + Send`) — reflect a multi-bound
/// trait object into the EXISTENTIAL `Sigma (T:Type), Vtable_<A+B…> T` whose vtable
/// record CONJOINS the methods of every non-marker component trait (`A` AND `B`),
/// while a MARKER trait (`Send`/`Sync`/…) contributes an EMPTY obligation (no field).
/// This extends [`reflect_dyn`] from a single trait to the conjunction: the record's
/// fields are the union of each component's reflected method signatures (`methods`
/// keyed per component trait), so the existential is "∃ a carrier `T` together with the
/// implementations of EVERY bound trait for `T`". With no method signatures from the
/// extractor (the common case) the conjoined record is the best-sound field-less
/// `Sigma (T:Type) Unit` — an existential over the opaque-but-QUANTIFIED carrier,
/// rooted in the 3. Registered modulo 3 by `register_dyn_carriers` (NO 4th axiom).
///
/// The existential's NAME is the sanitized whole multi-bound string (so `dyn A + B`
/// and `dyn A` are distinct existentials), and a marker-only adjustment is invisible
/// to soundness (it only drops empty obligations).
#[must_use]
pub fn reflect_multi_dyn(trait_name: &str, methods: &[(String, FnSig)]) -> DynCarrier {
    // The existential / vtable names key on the WHOLE multi-bound string (sanitized),
    // so `dyn A + B + Send` is one stable existential distinct from `dyn A`.
    let vtable_name = dyn_vtable_record_name(trait_name);
    let vtable_ctor_name = dyn_vtable_ctor_name(&vtable_name);
    // Drop any method that names a MARKER-trait component (markers contribute the
    // empty obligation); reflect the remaining methods' signatures into record fields.
    // (With today's extractor `methods` is empty, so the conjoined record is field-less
    // `Sigma Type Unit` — the sound minimal existential.)
    let reflected_methods = methods
        .iter()
        .filter(|(m, _)| !is_marker_trait(m))
        .filter_map(|(m, sig)| reflect_fn_sig(sig).ok().map(|carrier| (m.clone(), carrier)))
        .collect();
    DynCarrier {
        name: dyn_const_name(trait_name),
        vtable_name,
        vtable_ctor_name,
        methods: reflected_methods,
    }
}

/// TYPE-ZOO #6 (COROUTINE / async state-machines) — prefix for the NAMED record
/// inductive a coroutine `Ty::Coroutine { name, upvars }` reflects to
/// (`Trust.Coroutine.<name>`). DISTINCT from a closure's `Trust.Closure.<name>`: a
/// coroutine carries a SUSPEND-POINT STATE that a plain closure does not.
pub const COROUTINE_PREFIX: &str = "Trust.Coroutine.";

/// TYPE-ZOO #6 — the mangled Clean inductive name for a coroutine named `name`
/// (`Trust.Coroutine.<name>`), sanitized exactly like [`closure_inductive_name`].
#[must_use]
pub fn coroutine_inductive_name(name: &str) -> String {
    let sanitized = adt_inductive_name(name);
    let seg = sanitized.strip_prefix(ADT_PREFIX).unwrap_or(&sanitized);
    format!("{COROUTINE_PREFIX}{seg}")
}

/// TYPE-ZOO #6 (COROUTINE / async state-machines) — reflect a coroutine
/// `Ty::Coroutine { name, upvars }` into a REAL single-constructor record inductive
/// (a dependent RECORD over the existential STATE type), or `None` if the captured
/// environment does not reflect.
///
/// A coroutine IS a suspendable state machine: an enum of suspend points (the STATE),
/// the captured environment, and a RESUME step. The extractor's `Ty::Coroutine`
/// carries only `upvars` (NOT the suspend-point enum structure), so — exactly as the
/// goal allows — we model the state as an EXISTENTIAL over the state `Type` (the
/// coroutine's first `Type` parameter `S`) PLUS a resume STEP, realized as the record
///
/// ```text
///   Trust.Coroutine.<name> (S : Type) (Y : Type) :=
///     mk (env : <captured-env carrier>) (resume : S → Y)
/// ```
///
/// where `S` is the suspend-point STATE (existentially abstracted as a `Type` param,
/// rooted in the 3 — NOT a free const) and `Y` is the yield/return carrier; `resume :
/// S → Y` is a genuine kernel `Pi` (the step function). The `env` field is the upvar
/// product (the captured environment). Registers through the SAME modulo-3
/// `register_adt_carriers` path as a parameterized closure record (`axiom_deps` EMPTY
/// — NO 4th axiom). A non-reflectable upvar fails the whole coroutine closed.
#[must_use]
pub fn reflect_coroutine(name: &str, upvars: &[Ty]) -> Option<AdtCarrier> {
    let inductive_name = coroutine_inductive_name(name);
    let ctor_name = adt_ctor_name(&inductive_name);
    // The captured ENVIRONMENT carrier (fails closed transitively on a bad upvar).
    let env_carrier = reflect_product(upvars).ok()?;
    // The two synthetic `Type` params: the suspend-point STATE `S` and the yield `Y`.
    let [s_id, y_id] = closure_call_param_idents(&inductive_name);
    // The RESUME field is a genuine kernel `Pi` `S → Y` (the step function): the
    // domain is the state param const, the codomain the yield param const.
    let resume_carrier = ProofTerm::Pi {
        binder_name: "_state".to_string(),
        domain: Box::new(cst(&param_const_name(&s_id))),
        codomain: Box::new(cst(&param_const_name(&y_id))),
    };
    Some(AdtCarrier {
        ctor_name,
        name: inductive_name,
        fields: vec![("env".to_string(), env_carrier), ("resume".to_string(), resume_carrier)],
        // PARAMETERIZED over the STATE / yield `Type` variables, in order.
        type_params: vec![s_id, y_id],
        constructors: Vec::new(),
    })
}

/// TYPE-ZOO #6 — the contract BINDING carrier for a coroutine value: the registered
/// record inductive `Trust.Coroutine.<name>` applied to its two `Type` params (the
/// existential STATE `S` and the yield `Y`), exactly like [`closure_binding`] applies
/// a closure record. Returns `None` (→ upvar `Prod` fallback) iff the captured
/// environment does not reflect.
#[must_use]
fn coroutine_binding(name: &str, upvars: &[Ty]) -> Option<ProofTerm> {
    let carrier = reflect_coroutine(name, upvars)?;
    let mut applied = cst(&carrier.name);
    for id in &carrier.type_params {
        applied = app(applied, cst(&param_const_name(id)));
    }
    Some(applied)
}

/// TYPE-ZOO #5 (GATs / associated-type projections) — prefix for a GENERIC
/// ASSOCIATED-TYPE FAMILY: a type-level function `Trust.Gat.<Trait>.<Out>`. A GAT
/// `trait Trait { type Out<P>; }` projected as `<T as Trait>::Out<P>` is a
/// PARAMETERIZED type-level function (a `Π(args) → Type` family), modeled as a
/// registered inductive with one `Type` parameter per GAT parameter — i.e. a field of
/// the trait's vtable record indexed by the GAT params.
pub const GAT_PREFIX: &str = "Trust.Gat.";

/// TYPE-ZOO #5 (GATs) — the mangled inductive name for a GAT family `<Trait>::<Out>`
/// (`Trust.Gat.<Trait>_<Out>`), sanitized into a single kernel-legal `Name` segment.
#[must_use]
pub fn gat_family_name(trait_name: &str, assoc: &str) -> String {
    sanitize_dotted_segment(GAT_PREFIX, &format!("{trait_name}::{assoc}"))
}

/// TYPE-ZOO #5 (GATs / generic associated types) — reflect a GENERIC ASSOCIATED-TYPE
/// family `<Trait>::<Out><P₀, …, Pₖ₋₁>` into a PARAMETERIZED named inductive (a
/// type-level FUNCTION): `Trust.Gat.<Trait>_<Out> (P₀ : Type) … (Pₖ₋₁ : Type) :
/// Type`, a single opaque constructor `.mk` over the GAT parameters. This is the
/// type-level-function / vtable-field view the goal asks for: the associated type is a
/// FAMILY indexed by its GAT parameters, so `Iterator::Item<'a>` over a parameter `'a`
/// is the family `Trust.Gat.Iterator_Item` applied to its param. With `k` parameters
/// it is a `k`-`Type`-param inductive (the same parameterized shape a generic struct
/// uses), registered modulo 3 via `register_adt_carriers` (axiom_deps EMPTY — NO 4th
/// axiom). A bare (non-parameterized) associated-type projection stays the simple
/// `Trust.Param.*` type variable (unchanged); this models the PARAMETERIZED case.
///
/// `param_idents` are the stable idents of the GAT's `Type` parameters (e.g. the
/// lifetime/type generics of `Out<…>`), in binder order. An EMPTY `param_idents` is a
/// degenerate non-GAT associated type and yields `None` (use the `Trust.Param.*` path).
#[must_use]
pub fn reflect_gat_family(
    trait_name: &str,
    assoc: &str,
    param_idents: &[String],
) -> Option<AdtCarrier> {
    if param_idents.is_empty() {
        // Not a GENERIC associated type — a bare `<T as Trait>::Out` is the simple
        // `Trust.Param.*` type-variable case (handled elsewhere).
        return None;
    }
    let inductive_name = gat_family_name(trait_name, assoc);
    let ctor_name = adt_ctor_name(&inductive_name);
    // The family is OPAQUE in its output (the associated type's structure is unknown),
    // so the single constructor takes the GAT parameters and produces the family — a
    // field-LESS constructor over `k` `Type` params (`mk : Π(P₀:Type)…(Pₖ₋₁:Type).
    // Family P₀ … Pₖ₋₁`). The `type_params` ARE the GAT parameters; `fields` is empty,
    // so the constructor is the nullary `.mk` quantified over the params.
    Some(AdtCarrier {
        ctor_name,
        name: inductive_name,
        fields: Vec::new(),
        type_params: param_idents.to_vec(),
        constructors: Vec::new(),
    })
}

/// TYPE-ZOO #5 (GATs) — the extractor tag prefix marking a GENERIC ASSOCIATED-TYPE
/// FAMILY projection: an `Ty::Adt` named `@gat::<Trait>::<Assoc>` whose bare-type-var
/// fields are the GAT's `Type` parameters (in binder order). A non-`@gat::` `Ty::Adt` is
/// an ordinary struct/container and never reaches the GAT path.
pub const GAT_ADT_TAG: &str = "@gat::";

/// TYPE-ZOO #5 (GATs / generic associated types) — the contract BINDING carrier for a
/// value whose type is a `@gat::<Trait>::<Assoc>`-tagged GAT projection (an `Ty::Adt`
/// whose bare-type-var fields are the GAT parameters): the registered PARAMETERIZED
/// family inductive `Trust.Gat.<Trait>_<Assoc>` ([`reflect_gat_family`]) APPLIED to its
/// GAT param consts — exactly like [`coroutine_binding`] / [`closure_binding`] apply a
/// record to its `type_params`. Returns `None` (→ the ordinary `Ty::Adt` struct/container
/// path) iff the name is not `@gat::`-tagged OR carries no bare-type-var GAT parameter
/// (a degenerate / non-generic associated type stays the simple `Trust.Param.*` path).
#[must_use]
fn gat_family_binding(name: &str, fields: &[(String, Ty)]) -> Option<ProofTerm> {
    let path = name.strip_prefix(GAT_ADT_TAG)?;
    let (trait_name, assoc) = path.rsplit_once("::").unwrap_or((path, "Assoc"));
    // The GAT parameters are the bare-generic-param fields' idents (`P/#k`), in order.
    let params: Vec<String> = fields
        .iter()
        .filter_map(|(_, fty)| bare_type_var(fty))
        .filter_map(|v| v.strip_prefix(PARAM_PREFIX).map(ToString::to_string))
        .collect();
    let carrier = reflect_gat_family(trait_name, assoc, &params)?;
    // `Trust.Gat.<Trait>_<Assoc>` applied to each GAT param const (in binder order); the
    // contract abstracts each param const into an outer `Π(P : Type)` binder, and
    // `to_clean_expr` decodes this applied family inductive to the kernel family type.
    let mut applied = cst(&carrier.name);
    for id in &carrier.type_params {
        applied = app(applied, cst(&param_const_name(id)));
    }
    Some(applied)
}

/// CLOSURE RECORD (M5) — the mangled Clean inductive name for a closure named
/// `name` (`Trust.Closure.<name>`). Sanitized into a single dotted path segment
/// exactly like [`adt_inductive_name`] (Rust `::`/non-identifier bytes collapse to
/// `_`, trailing collapse underscores trimmed), so the inductive name is a stable,
/// kernel-legal `Name`.
#[must_use]
pub fn closure_inductive_name(name: &str) -> String {
    // Reuse the ADT sanitizer, then swap its `Trust.Adt.` prefix for `Trust.Closure.`.
    let sanitized = adt_inductive_name(name);
    let seg = sanitized.strip_prefix(ADT_PREFIX).unwrap_or(&sanitized);
    format!("{CLOSURE_PREFIX}{seg}")
}

/// The two synthetic `Type`-parameter idents a closure inductive is parameterized
/// over — the call's DOMAIN (`A`) and CODOMAIN (`B`). Keyed by the (sanitized)
/// closure inductive name so two distinct closures get distinct binders and the
/// SAME closure maps to the same pair everywhere. Returned in binder order `[A, B]`.
#[must_use]
fn closure_call_param_idents(inductive_name: &str) -> [String; 2] {
    // The `!` separator never occurs in a sanitized inductive name, so these idents
    // can never collide with a real generic param's `name/#index` identity.
    [format!("{inductive_name}!callA"), format!("{inductive_name}!callB")]
}

/// CLOSURE RECORD (M5) — reflect a closure/coroutine `Ty::Closure { name, upvars, .. }`
/// into a REAL single-constructor Clean inductive carrier (a dependent RECORD), or
/// `None` to fall back to the upvar `Trust.Sort.Prod` product (no regression).
///
/// The closure becomes `Trust.Closure.<name> (A : Type) (B : Type) :=
/// mk (env : <upvar-product>) (call : A → B)` — its captured ENVIRONMENT (the
/// right-nested product of the upvar carriers) PLUS its CALL signature (a genuine
/// kernel `Pi` `A → B`, rooted in the 3). The call's domain/codomain are abstracted
/// as the inductive's two `Type` parameters because the extractor hands us only the
/// upvars, not the call signature — the quantified-Sigma-over-call-type form. The
/// `env` field's upvar carriers reflect via [`reflect_ty`], so a non-reflectable
/// upvar (e.g. a `Ty::Never` capture) FAILS the whole closure carrier closed
/// (`None` → upvar `Prod` floor, unchanged behavior). A closure with NO upvars
/// still gets an `env : Unit` field (the empty captured environment).
///
/// Registers through the SAME modulo-3 `register_adt_carriers`/`add_inductive` path
/// as a PARAMETERIZED struct (`type_params = [A, B]`): the `env` field decodes to
/// the kernel product, and the `call` field decodes to the kernel `Pi` over the two
/// bound `Type` params — all axiom-free, so `axiom_deps` stays EMPTY (NO 4th axiom).
#[must_use]
pub fn reflect_closure(name: &str, upvars: &[Ty]) -> Option<AdtCarrier> {
    let inductive_name = closure_inductive_name(name);
    let ctor_name = adt_ctor_name(&inductive_name);
    // The captured ENVIRONMENT carrier: the right-nested product of the upvar
    // carriers (fails closed transitively on a non-reflectable upvar).
    let env_carrier = reflect_product(upvars).ok()?;
    // The two synthetic `Type` params (call domain / codomain) and their carriers.
    let [a_id, b_id] = closure_call_param_idents(&inductive_name);
    // The CALL field is a genuine kernel `Pi` `A → B`: domain/codomain are the bound
    // type-param consts; `ctor_field_type` decodes this to `Expr::pi` over the two
    // `Type` parameters of the inductive. The codomain's de-Bruijn reference accounts
    // for the Pi's own binder during grounding (see `carrier_to_kernel_field_type`).
    let call_carrier = ProofTerm::Pi {
        binder_name: "_arg".to_string(),
        domain: Box::new(cst(&param_const_name(&a_id))),
        codomain: Box::new(cst(&param_const_name(&b_id))),
    };
    Some(AdtCarrier {
        ctor_name,
        name: inductive_name,
        fields: vec![("env".to_string(), env_carrier), ("call".to_string(), call_carrier)],
        // PARAMETERIZED over the call's domain/codomain `Type` variables, in order.
        type_params: vec![a_id, b_id],
        constructors: Vec::new(),
    })
}

/// COVERAGE-AGENDA #4 — whether `fty` is a NESTED `dyn`-trait writer-sink field that
/// the opaque-sink SHIM collapses to the [`CARRIER_SINK`] code: a bare trait object
/// `dyn Trait`, or one behind a transparent `&`/`&mut` reference (the canonical
/// `core::fmt::Formatter` `buf : &mut dyn core::fmt::Write` shape). Returns `false`
/// for a NON-`dyn` field (a generic param `T`, a concrete scalar/struct, …) so the
/// SHIM only ever absorbs an existential trait-object field, never a value-bearing
/// one. Centralizes the predicate used by [`reflect_struct`] / [`reflect_enum`] and
/// the `Trust.Sink` registration driver in `clean_ground`.
#[must_use]
pub fn is_nested_dyn_field(fty: &Ty) -> bool {
    dyn_object_const(fty).is_some()
}

/// PHASE 4 — the Clean constructor name for a variant `variant` of enum
/// inductive `inductive_name` (`<inductive>.<variant>`, the variant name
/// sanitized into a single dotted path segment exactly like the enum name).
#[must_use]
pub fn adt_variant_ctor_name(inductive_name: &str, variant: &str) -> String {
    // Reuse `adt_inductive_name`'s sanitizer on the variant, then splice its
    // segment after the inductive name's dot. `adt_inductive_name` prepends the
    // `Trust.Adt.` prefix; strip it so we get just the sanitized segment.
    let sanitized = adt_inductive_name(variant);
    let seg = sanitized.strip_prefix(ADT_PREFIX).unwrap_or(&sanitized);
    format!("{inductive_name}.{seg}")
}

/// PHASE 4 — reflect a Trust ENUM (`Ty::Adt` with non-empty `variants`) into a
/// REAL multi-constructor Clean inductive carrier ([`AdtCarrier`] with
/// `constructors` populated), or `None` to fall back to the anonymous
/// `Trust.Sort.Prod` product (no regression).
///
/// Each variant becomes a constructor `Trust.Adt.<Enum>.<Variant> : τ₁ → … → τₙ
/// → <Enum>` (a NULLARY constructor for a field-less variant). A GENERIC enum
/// (`Option<T>`) reuses the Phase-2 parameterized path: a bare-generic variant
/// field contributes its stable ident to [`AdtCarrier::type_params`] and its
/// carrier is `Trust.Param.<id>`; `register_adt_carriers` then registers
/// `Trust.Adt.<Enum>` as a parameterized inductive whose every constructor is
/// quantified over the type params.
///
/// Returns `None` (→ `Prod` fallback, sound) iff ANY variant field is
/// non-reflectable (float/never/`dyn`), or is a COMPOSITE that nests a generic
/// param (`Vec<T>`-shaped, `(T, u8)`), or is a trait-object field — exactly the
/// same fail-closed conditions as [`reflect_struct`], applied per variant field.
/// This never yields an unsound inductive and never adds a 4th axiom.
#[must_use]
pub fn reflect_enum(ty: &Ty) -> Option<AdtCarrier> {
    let Ty::Adt { name, variants, .. } = ty else {
        return None;
    };
    if variants.is_empty() {
        return None; // not an enum — caller handles the struct path.
    }
    let inductive_name = adt_inductive_name(name);
    let mut type_params: Vec<String> = Vec::new();
    let mut constructors: Vec<EnumCtor> = Vec::with_capacity(variants.len());

    for variant in variants {
        let mut reflected_fields = Vec::with_capacity(variant.fields.len());
        for (fname, fty) in &variant.fields {
            // COVERAGE-AGENDA #4 — a NESTED `dyn`-trait writer-sink variant field
            // collapses to the concrete `Trust.Sort.Sink` opaque-atom code (same
            // SHIM as `reflect_struct`), so an enum carrying a trait object in a
            // variant still registers as a real multi-constructor inductive. Sound:
            // the sink is structureless (faithfulness-neutral), reading through it
            // fails closed.
            if is_nested_dyn_field(fty) {
                reflected_fields.push((fname.clone(), cst(CARRIER_SINK)));
                continue;
            }
            // PHASE 2 reuse — a BARE generic type-variable field `T` (possibly
            // behind a transparent reference) is a genuine dependent constructor
            // field carried by the bound type-param const. A trait-object field is
            // handled by the Sink shim above; any other non-`Param` opaque carrier
            // falls back to Prod for the whole enum (sound; deferred).
            if let Some(var) = bare_type_var(fty) {
                let Some(id) = var.strip_prefix(PARAM_PREFIX) else {
                    return None;
                };
                let id = id.to_string();
                if !type_params.contains(&id) {
                    type_params.push(id.clone());
                }
                reflected_fields.push((fname.clone(), cst(&param_const_name(&id))));
                continue;
            }
            // RECURSIVE DEPENDENT CARRIER (goal bullet 2 tail) — a variant field that
            // is ANY composite nesting a generic type variable at ANY depth — a
            // sequence `V(Vec<T>)` / `[T; N]`, a deeply-nested `Vec<Vec<T>>` /
            // `Vec<Wrapper<T>>`, a nested generic struct `V(Wrapper<T>)`, a tuple
            // `V((T, u8))`, or a nested generic enum — is carried STRUCTURALLY via
            // [`parameterized_composite_field`] (the same recursive carrier
            // `reflect_struct` uses), decoded to the real dependent kernel type. The
            // nested params join this enum's binder list. NO anonymous `Prod` floor,
            // NO new axiom.
            if let Some((composite_carrier, nested_param_ids)) = parameterized_composite_field(fty)
            {
                for id in nested_param_ids {
                    if !type_params.contains(&id) {
                        type_params.push(id);
                    }
                }
                reflected_fields.push((fname.clone(), composite_carrier));
                continue;
            }
            // A concrete field must be reflectable and must NOT still nest a type var
            // after the recursive case declined (a non-carriable `dyn`/float component)
            // — same fail-closed rule as `reflect_struct`. Any failure falls the WHOLE
            // enum back to Prod.
            let carrier = reflect_ty(fty).ok()?;
            if carrier_mentions_param(&carrier) {
                return None;
            }
            reflected_fields.push((fname.clone(), carrier));
        }
        constructors.push(EnumCtor {
            name: adt_variant_ctor_name(&inductive_name, &variant.name),
            discriminant: variant.discriminant,
            fields: reflected_fields,
        });
    }

    Some(AdtCarrier {
        // For an enum, `fields`/`ctor_name` are the legacy struct view; the real
        // structure is `constructors`. Use the first variant's ctor name as a
        // stable placeholder and the union-of-fields as the compat `fields`.
        ctor_name: constructors
            .first()
            .map_or_else(|| adt_ctor_name(&inductive_name), |c| c.name.clone()),
        name: inductive_name,
        fields: enum_union_fields(&constructors),
        type_params,
        constructors,
    })
}

/// FAITHFULNESS FIX (enum sum types) — the FAITHFUL, INJECTIVE TYPE-LEVEL carrier
/// `ProofTerm` for an ENUM `Ty::Adt`, the term `reflect_ty` returns for it. This is
/// the registered multi-constructor inductive `Trust.Adt.<Enum>` (a distinct named
/// `Type` const per enum), applied to its `Type` params for a GENERIC enum
/// (`Trust.Adt.Option (Trust.Param.<T>)`) exactly as [`generic_struct_binding`]
/// builds it.
///
/// Why this is INJECTIVE (the audit's hole): the carrier is the enum's nominal
/// inductive NAME, NOT the `reflect_struct_product` over the UNION of variant fields.
/// A 2-variant `Option<i32>` → `Trust.Adt.core::option::Option`, which is DISTINCT
/// from `struct Wrap(i32)`'s `Prod (BitVec 32) Unit`; a fieldless 5-variant
/// `IntErrorKind` → `Trust.Adt.core::num::IntErrorKind`, DISTINCT from `Unit` and from
/// any 1-variant enum's own name; `Shape { Circle(u32), Rect{w,h} }` →
/// `Trust.Adt.Shape`, DISTINCT from a plain 3-field struct's `Prod`-of-3. The
/// SUM/discriminant structure (`Some` ≠ `None`, `Circle` ≠ `Rect`) is carried by the
/// `AdtCarrier::constructors` the registration turns into distinct kernel constructors.
///
/// Returns `None` (→ the caller's sound `Prod`-over-union floor) iff `reflect_enum`
/// declines (a non-reflectable variant field) — never an unsound carrier.
#[must_use]
fn reflect_enum_type_carrier(ty: &Ty) -> Option<ProofTerm> {
    let carrier = reflect_enum(ty)?;
    // The inductive `Trust.Adt.<Enum>` applied to each of its `Type` params (in
    // binder order) for a GENERIC enum; the bare named const for a CONCRETE enum
    // (`type_params` empty ⇒ no applications). A generic enum's `Trust.Param.*` args
    // are abstracted into the outer `Π(T : Type)` by `reflect_contract`, exactly as a
    // generic struct's applied carrier is.
    let mut applied = cst(&carrier.name);
    for id in &carrier.type_params {
        applied = app(applied, cst(&param_const_name(id)));
    }
    Some(applied)
}

/// FAITHFULNESS FIX (enum sum types) — whether `ty` is a CONCRETE (non-generic) enum
/// whose value binds DIRECTLY at the registered inductive `Trust.Adt.<Enum>` (a
/// `Type` const), NOT through `Trust.El` (the inductive is itself a `Type`, not a
/// `Trust.SortTy` *code* that `El` decodes) and NOT as a universally-abstracted opaque
/// variable (the enum is a CLOSED named inductive, registered modulo 3 by
/// `register_adt_carriers`). Returns the binding carrier const iff `ty` reflects to a
/// concrete enum carrier; `None` for a struct, a GENERIC enum (handled by
/// `generic_struct_binding`, which builds the parameterized applied carrier), or a
/// non-reflectable enum (the `Prod` floor). Mirrors `dyn_object_const`'s role for
/// trait objects.
#[must_use]
fn concrete_enum_binding(ty: &Ty) -> Option<ProofTerm> {
    let carrier = reflect_enum(ty)?;
    // Only a CONCRETE enum binds at the bare named const here; a generic enum's
    // applied/parameterized carrier is produced by `generic_struct_binding`, which
    // takes priority in `carrier_binding_type`.
    if carrier.is_parameterized() {
        return None;
    }
    Some(cst(&carrier.name))
}

/// PHASE 4 — the deduplicated union of all constructors' fields (first
/// occurrence wins), the struct/union compat view stored in
/// [`AdtCarrier::fields`] for an enum.
fn enum_union_fields(constructors: &[EnumCtor]) -> Vec<(String, ProofTerm)> {
    let mut out: Vec<(String, ProofTerm)> = Vec::new();
    for ctor in constructors {
        for (fname, carrier) in &ctor.fields {
            if !out.iter().any(|(n, _)| n == fname) {
                out.push((fname.clone(), carrier.clone()));
            }
        }
    }
    out
}

/// Whether a reflected type carrier mentions a generic-param / trait-object
/// opaque const (`Trust.Param.*` / `Trust.Dyn.*`) anywhere — i.e. the type is
/// generic and must not register as a NON-generic struct inductive.
fn carrier_mentions_param(term: &ProofTerm) -> bool {
    match term {
        ProofTerm::Const(n) => n.starts_with(PARAM_PREFIX) || n.starts_with(DYN_PREFIX),
        ProofTerm::App(f, a) => carrier_mentions_param(f) || carrier_mentions_param(a),
        ProofTerm::Lambda { binder_type, body, .. } => {
            carrier_mentions_param(binder_type) || carrier_mentions_param(body)
        }
        ProofTerm::Pi { domain, codomain, .. } => {
            carrier_mentions_param(domain) || carrier_mentions_param(codomain)
        }
        ProofTerm::Var(_) | ProofTerm::Sort(_) => false,
    }
}

/// PHASE 2 — the contract BINDING type for a value of a generic-struct parameter
/// type `ty`: the parameterized inductive applied to its type-parameter consts,
/// `Trust.Adt.<Name> (Trust.Param.<T₁>) … (Trust.Param.<Tₖ>)`. `reflect_contract`
/// abstracts those param consts into the outermost `Π(Tᵢ : Type)` binders, so a
/// generic-struct parameter binds as `Π(p : Wrapper T)` under `Π(T : Type)` —
/// the genuine dependent structure, not the anonymous `Prod` over-approximation.
/// Returns `None` for a non-parameterized struct or a `Ty` that is not a generic
/// struct (the caller then keeps the existing concrete/opaque path).
#[must_use]
fn generic_struct_binding(ty: &Ty) -> Option<ProofTerm> {
    let carrier = reflect_struct(ty)?;
    if !carrier.is_parameterized() {
        return None;
    }
    // `Trust.Adt.<Name>` applied to each type param const (in binder order).
    let mut applied = cst(&carrier.name);
    for id in &carrier.type_params {
        applied = app(applied, cst(&param_const_name(id)));
    }
    Some(applied)
}

/// RECURSIVE DEPENDENT CARRIER (goal bullet 2 tail) — the contract BINDING carrier
/// for a value whose type is ANY composite that nests a generic type variable at ANY
/// depth (NOT a bare generic struct, which `generic_struct_binding` handles): a
/// sequence `Vec<T>`/`&[T]`/`[T; N]`, a DEEPLY-nested `Vec<Vec<T>>` /
/// `Vec<Wrapper<T>>` / `[Wrapper<T>; N]`, a tuple `(T, u8)`, or a nested generic enum.
/// The carrier is the recursive [`parameterized_composite_field`] term (a mix of
/// `Slice`/`Vec`/`Prod` heads and the Pi-bound type-var consts / applied inner
/// inductives). `reflect_contract` abstracts the element/component param consts into
/// the outer `Π(T : Type)` binder(s), and `clean_ground`'s `to_clean_expr` decodes
/// the carrier to the real dependent kernel type (`List (List (BVar T))`,
/// `List (Wrapper (BVar T))`, `Prod (BVar T) Int`, …) — so the parameter binds
/// `Π(v : <decoded>)` under the outer type binders, and a value RETURN binds at the
/// decoded type (inhabited by the corresponding empty-list / pair witness). This is
/// the `Vec<T> → List T` family over the prelude's axiom-free `List`/`Prod`; NO new
/// axiom, NO opaque fallback. Returns `None` (→ existing concrete/opaque path) for a
/// fully-concrete composite or a non-carriable one (those route through `El`/the
/// deferred opaque fallback unchanged). References are transparent.
#[must_use]
fn parameterized_composite_binding(ty: &Ty) -> Option<ProofTerm> {
    parameterized_composite_field(ty).map(|(carrier, _)| carrier)
}

// ---------------------------------------------------------------------------
// Reflection
// ---------------------------------------------------------------------------

/// Reflect a (post-collapse) SMT `Sort` into a Clean carrier `ProofTerm`.
///
/// Scalars (`Bool`, `Int`, `BitVec`) map to carriers; `Array` (a map sort) fails
/// closed — element structure is not recoverable from `Sort` alone (use
/// `reflect_ty`, which sees `Ty::Array`/`Ty::Slice`).
///
/// # Errors
///
/// Returns [`ReflectError::ArrayType`] for `Sort::Array`, or
/// [`ReflectError::UnsupportedType`] for any future non-scalar `Sort` variant.
pub fn reflect_sort(sort: &Sort) -> Result<ProofTerm, ReflectError> {
    match sort {
        Sort::Bool => Ok(cst(CARRIER_BOOL)),
        Sort::Int => Ok(cst(CARRIER_INT)),
        Sort::BitVec(w) => Ok(reflect_bitvec(*w)),
        Sort::Array(..) => Err(ReflectError::ArrayType(
            "array/map sort is non-scalar and carries no element-structure for a Vec; \
             reflect the Ty instead",
        )),
        _ => Err(ReflectError::UnsupportedType("unknown non_exhaustive Sort variant")),
    }
}

/// Reflect a Trust MIR `Ty` into a Clean carrier `ProofTerm`.
///
/// Scalars and pointers map to `Trust.Sort.*` carriers; tuples/structs map to
/// `Trust.Sort.Prod` products; fixed arrays to `Trust.Sort.Vec`; slices to
/// `Trust.Sort.Slice`. Every other family fails closed with its dedicated
/// [`ReflectError`]. Composite cases recurse, so a non-reflectable component
/// fails the whole type closed.
///
/// # Errors
///
/// Returns the [`ReflectError`] naming the non-reflectable family (possibly a
/// component of a composite).
pub fn reflect_ty(ty: &Ty) -> Result<ProofTerm, ReflectError> {
    match ty {
        // --- S0: scalar carriers ---
        Ty::Bool => Ok(cst(CARRIER_BOOL)),
        Ty::Int { width, .. } => Ok(reflect_bitvec(*width)),
        // COVERAGE-AGENDA #2 — a BARE raw pointer (`*const T`/`*mut T`) reflects to
        // the SHALLOW opaque-address carrier `Trust.Sort.Ptr` (NOT `CARRIER_INT`),
        // which decodes to the registered `Trust.Ptr { addr : Int }` inductive
        // ([`PTR_INDUCTIVE`]). A bare-pointer value/return is then inhabitable by
        // `Trust.Ptr.mk 0` — grounding the dominant clone/Default/Debug contracts
        // that never dereference. Modeling the pointer as a distinct address ADT
        // (rather than identifying it with its address integer) is what keeps a
        // dereference/offset READING THROUGH the pointer fail-closed: `*p` has no
        // faithful integer value at `Trust.Ptr`, so a contract over the pointee value
        // stays undischarged (the points-to model is deferred). Address arithmetic
        // still grounds because MIR casts the pointer to `usize` first.
        Ty::RawPtr { .. } => Ok(cst(CARRIER_PTR)),
        // Machine bitvector (pre-type-recovery) is a genuine scalar bitvector.
        Ty::Bv(w) => Ok(reflect_bitvec(*w)),

        // --- M2: products and sequences (recursive) ---
        Ty::Unit => Ok(cst(CARRIER_UNIT)),
        Ty::Tuple(elems) => reflect_product(elems),
        Ty::Adt { name, fields, .. } => {
            // TYPE-ZOO #5 (GATs) — PRODUCTION-WIRED: a `@gat::<Trait>::<Assoc>`-tagged
            // `Ty::Adt` (a GENERIC ASSOCIATED-TYPE family projection whose fields are the
            // GAT's `Type` parameters) reflects to the PARAMETERIZED type-level-function
            // family `Trust.Gat.<Trait>_<Assoc>` APPLIED to its GAT param consts
            // ([`gat_family_binding`] / [`reflect_gat_family`]) — the SAME carrier the
            // `gat_family` corpus probe grounds. `register_adt_carriers` registers the family
            // modulo 3 (axiom_deps EMPTY — NO 4th axiom). A non-`@gat::` `Ty::Adt`, or a
            // `@gat::` Adt with no bare-type-var GAT parameter, falls through to the ordinary
            // container/struct path below (NO change to any concrete struct/container).
            if let Some(gat) = gat_family_binding(name, fields) {
                return Ok(gat);
            }
            // GOAL-ITEM #2 — a KNOWN std container (`Vec<T>`→`Slice T`,
            // `Box<T>`/`Rc<T>`/`Arc<T>`→transparent inner) reflects to its REAL
            // structural model instead of the opaque internal-layout product.
            // Fails closed to the `Prod` floor for any unknown container or an
            // unrecoverable element/inner. (Option/Result are enums → `reflect_enum`.)
            if let Some(container) = reflect_known_container(ty) {
                return container;
            }
            // REAL-CODE COVERAGE (collections) — a KNOWN map/set container
            // (`HashMap<K,V>`/`BTreeMap<K,V>`→`Slice (Prod K V)`,
            // `HashSet<K>`/`BTreeSet<K>`→`Slice K`) reflects to its REAL association-
            // list / element-list model over the existing `Slice`/`Prod` carriers,
            // instead of the type-erased hashbrown/btree internal product. Fails
            // closed (→ the `reflect_struct_product` floor) for an unrecoverable
            // `(K,V)`/element.
            if let Some(map) = reflect_known_map(ty) {
                return map;
            }
            // REAL-CODE COVERAGE (iterator combinators) — a KNOWN stdlib iterator
            // adapter (`slice::Iter`/`Map`/`Filter`/`Enumerate`/`Zip`/`Chars`/
            // `Copied`/`Cloned`) reflects to its REAL record model (the
            // `Trust.Adt.<Adapter>` record const, or its source for a transparent
            // `Copied`/`Cloned`), instead of the opaque `ptr`/`end_or_len`/`_marker`
            // internal layout. Fails closed for an unrecoverable source/closure/elem.
            if let Some(adapter) = reflect_known_iter_adapter(ty) {
                return adapter;
            }
            // FAITHFULNESS FIX (enum sum types) — an ENUM (`variants` non-empty)
            // reflects to its FAITHFUL, DISCRIMINANT-AWARE, INJECTIVE sum carrier, NOT
            // the NON-INJECTIVE `reflect_struct_product` over the UNION of variant
            // fields (which DISCARDED the sum structure: it conflated `Option<i32>`
            // with `struct Wrap(i32)`, a fieldless `IntErrorKind` with `Unit`, and a
            // multi-variant `Shape` with a plain 3-field struct). The carrier is the
            // registered multi-constructor inductive `Trust.Adt.<Enum>` ([`reflect_enum`]
            // + `clean_ground::register_adt_carriers`'s per-variant constructor gate, the
            // SAME path generics use), applied to its `Type` params for a generic enum.
            // INJECTIVE by inductive NAME (a 2-variant `Option` carrier
            // `Trust.Adt.core::option::Option` is DISTINCT from a 1-field struct's
            // anonymous `Prod`; `IntErrorKind`'s carrier is DISTINCT from any other
            // enum's name), and the per-variant constructors keep `Some`/`None` and
            // `Circle`/`Rect` DISTINCT constructors of the inductive. Falls back to the
            // sound `Prod` floor ONLY if a variant field is non-reflectable (the SAME
            // fail-closed condition `reflect_enum` already enforces) — never an unsound
            // inductive, never a 4th axiom (the inductive + recursor `axiom_deps` are
            // EMPTY). The named inductive is registered for grounding/binding by the
            // existing `reachable_adt_carriers` → `register_adt_carriers` pipeline (which
            // already dispatches enums via `reflect_struct` → `reflect_enum`), and a
            // value of the type binds at this const directly via `carrier_binding_type`'s
            // concrete-enum arm (NOT `El`-wrapped — the inductive is a `Type`, not a
            // `Trust.SortTy` code), with `to_clean_expr` passing the registered
            // `Trust.Adt.*` const through to the kernel.
            if ty.is_enum_adt() {
                if let Some(enum_carrier) = reflect_enum_type_carrier(ty) {
                    return Ok(enum_carrier);
                }
                // A non-reflectable variant field declined `reflect_enum` — fall back to
                // the sound (but length-erased / non-injective) `Prod`-over-union floor,
                // exactly as before this fix. No regression for the deferred shapes.
                return reflect_struct_product(fields);
            }
            // COVERAGE-AGENDA #4 — build the struct's product with the opaque-sink
            // SHIM applied per field, so a NESTED `dyn`-trait writer-sink field (the
            // `core::fmt::Formatter` `buf : &mut dyn Write` shape) collapses to the
            // concrete `Trust.Sort.Sink` code rather than the `Trust.Dyn.*` type
            // variable. This keeps `reflect_ty(Formatter)` CONSISTENT with the named
            // inductive `reflect_struct(Formatter)` registers — so the parameter binds
            // at `El (Prod … Sink …)` (a genuine `Trust.SortTy` code that grounds),
            // instead of `code_mentions_type_var` forcing the whole-parameter opaque
            // over-approximation. A non-`dyn` composite-nested type var (a `(T,u8)`
            // field) is UNCHANGED (it stays a type var, fail-closed at the carrier).
            reflect_struct_product(fields)
        }
        // DUMP COMPACTION (M6 census gap #1) — a RECURSIVE ADT `Ty::Datatype`, the
        // lowering `trust-mir-extract`'s `ty_convert` emits for a recursive
        // enum/struct family (`clean_kernel::Expr`, `Level`, …) that the flat
        // `Ty::Adt` encoding cannot represent. Two spellings (see the variant's own
        // doc in `trust-types/src/model.rs`):
        //
        //   * FULL DEFINITION (non-empty `variants`) — reflects EXACTLY like the
        //     equivalent `Ty::Adt` enum ([`datatype_equivalent_adt`]), through the
        //     SAME arm above: the named injective carrier `Trust.Adt.<name>`
        //     (applied to its `Type` params — including the `@datatype::` recursion
        //     variables its own back-reference fields introduce via
        //     `bare_type_var`), or the sound `Prod`-over-union floor when a variant
        //     field declines. One level of REAL structure (constructors/fields,
        //     straight from the dump — nothing fabricated), with the recursive
        //     occurrences abstracted as opaque Pi-bound type variables (the
        //     one-level-unrolled functor view: `∀ R, ExprShape R` is a sound,
        //     STRONGER over-approximation of the recursive fixpoint).
        //   * BY-NAME BACK-REFERENCE (empty `variants`) — the compacted spelling for
        //     "a reference to the datatype named `name`, defined elsewhere".
        //     [`reflect_verifiable_function`] PRE-RESOLVES these against the
        //     function's own locals (the defining occurrence always carries the
        //     full variant list) before reflection; one that still reaches here is
        //     UNRESOLVABLE and fails closed to the opaque-but-grounded type
        //     variable `Trust.Param.@datatype::<name>`
        //     ([`datatype_backref_const_name`]) — the generic-param convention:
        //     Pi-bound at `Type`, structureless, never inhabitable by fiat.
        Ty::Datatype { name, variants } => {
            if variants.is_empty() {
                Ok(cst(&datatype_backref_const_name(name)))
            } else {
                reflect_ty(&datatype_equivalent_adt(name, variants))
            }
        }
        // TYPE-ZOO #1 (CONST GENERICS) — PRODUCTION-WIRED: a fixed-size array `[T; N]`
        // reflects to the LENGTH-INDEXED carrier `Trust.ArrayN (decode T) N`
        // ([`reflect_array_indexed`]) — `N` is a REAL `Nat` INDEX (the const generic as a
        // genuine dependent value), NOT the length-erased `Slice`/`List` model. This is the
        // SAME carrier the dedicated entry point + the `const_generic_indexed` corpus probe
        // ground, now emitted by the MAIN grounding pipeline mirsem/§6/the prover consume.
        // The production decode path grounds it: `decode_el_code` (param position) maps
        // `Trust.ArrayN` → the registered `Trust.ArrayN (decode T) (Nat.lit n)`
        // (`decode_arrayn_code`); the binding-position and struct-field decoders
        // (`carrier_binding_to_kernel_type` / `carrier_to_kernel_field_type`) erase the
        // length to `List <decode elem>` for a generic/nested element (the SAME
        // length-erased model `Trust.Sort.Vec` had), so an array FIELD / generic-element
        // array keeps its prior `List`-based grounding — NO regression. `clean_ground::
        // register_arrayn_carrier` registers the inductive modulo 3 (axiom_deps EMPTY — NO
        // 4th axiom). A non-reflectable element fails the whole array closed (transitive).
        Ty::Array { elem, len } => reflect_array_indexed(elem, *len),
        Ty::Slice { elem } => Ok(app(cst(CARRIER_SLICE), reflect_ty(elem)?)),

        // GOAL-ITEM #3 — a float reflects to its STRUCTURED IEEE-754 carrier, the
        // right-nested product of its named fields `sign : Bool`, `exponent : BitVec
        // <exp>`, `mantissa : BitVec <mant>` — NOT a flat `BitVec <width>` (which would
        // be the bit pattern, not the IEEE *structure*) and NOT an opaque placeholder.
        // This `Trust.Sort.Prod` code is what a float-typed value reflects to as a
        // `Trust.SortTy` carrier (so a struct/tuple with a float field is now
        // reflectable, and `El (Prod …)` binds a float parameter at its real
        // decomposition). The matching NAMED inductive `Trust.FloatN` (with
        // kernel-projectable `Trust.FloatN.sign`/… projections) registers separately
        // via `register_adt_carriers` ([`reflect_float`]) and drives the structural
        // depth metric — exactly mirroring how a non-generic struct reflects to a
        // `Prod` code here while its fields ground over the registered `Trust.Adt.<S>`
        // inductive. An unsupported float width fails closed (NEVER aliases onto BitVec).
        Ty::Float { width } => match float_field_tys(*width) {
            Some(field_tys) => reflect_product(&field_tys),
            None => Err(ReflectError::FloatType(
                "unsupported IEEE-754 float width (only f32/f64 are structurally modeled); \
                 not aliased onto a flat BitVec",
            )),
        },
        // Trust: M5 — a reference `&T`/`&mut T` reflects as its referent's carrier
        // (references are transparent for type reflection; the borrow structure is
        // tracked by trust-vc, not the dependent-type carrier).
        Ty::Ref { inner, .. } => reflect_ty(inner),
        Ty::Never => Err(ReflectError::NeverType("never type is non-scalar")),
        // CLOSURE RECORD (M5) — a closure/coroutine reflects to its REAL dependent
        // RECORD: the registered single-constructor inductive `Trust.Closure.<name>`
        // (its captured ENVIRONMENT product `env` PLUS its CALL signature `call : A →
        // B`, a genuine kernel `Pi`), bound here as the APPLIED carrier
        // `Trust.Closure.<name> (Param A) (Param B)` over the two opaque call-signature
        // `Type` variables — the SAME applied-inductive binding a generic struct
        // `Wrapper<T>` gets (`generic_struct_binding`). `reflect_contract` abstracts the
        // call params into outer `Π(A:Type)Π(B:Type)` binders and `to_clean_expr`
        // decodes this to the kernel type `Closure A B`. The record registers
        // separately via `reflect_closure` + `register_adt_carriers` (modulo 3,
        // `axiom_deps` EMPTY — NO 4th axiom), exactly as a struct's `Prod`-code
        // `reflect_ty` is paired with `reflect_struct`'s named inductive. A
        // non-reflectable upvar (e.g. a `Ty::Never` capture) FAILS the closure carrier
        // closed (the `env` product fails transitively).
        Ty::Closure { name, upvars, .. } => closure_binding(name, upvars)
            .ok_or(ReflectError::ClosureType("a closure capture is non-reflectable")),
        // TYPE-ZOO #6 (COROUTINE / async state-machines) — PRODUCTION-WIRED: a coroutine
        // reflects to its OWN state-record carrier `Trust.Coroutine.<name>` ([`coroutine_binding`]
        // / [`reflect_coroutine`]) — env + `resume : S → Y` (the suspend-point STATE `S`
        // existentially abstracted as a `Type` param), DISTINCT from a closure's
        // `Trust.Closure.<name>` (a coroutine carries a suspend-point state a plain closure
        // does not). This is the SAME carrier the `coroutine` corpus probe grounds.
        // `register_adt_carriers` registers the record modulo 3 (axiom_deps EMPTY — NO 4th
        // axiom), exactly like a parameterized closure record. A non-reflectable upvar fails
        // the whole coroutine closed (the `env` product fails transitively).
        Ty::Coroutine { name, upvars } => coroutine_binding(name, upvars)
            .ok_or(ReflectError::CoroutineType("a coroutine capture is non-reflectable")),
        // FUNCTION POINTER (M5) — a function item / function pointer reflects to a
        // GENUINE kernel `Pi` (arrow) type `reflect(A) -> reflect(B)` (curried for
        // multi-arg), via `reflect_fn_sig_pi`. The type *is* the function type, so the
        // dependent-function skeleton is faithful, and `to_clean_expr` grounds the `Pi`
        // directly to the native `Expr::pi` — rooted in the 3 (the kernel has `Pi`
        // primitively), NOT the `Trust.Sort.Fn` *code* (which `reflect_fn_sig` still
        // builds for the carrier-composition callers). A non-reflectable / opaque-type-
        // variable parameter or return fails the fn-ptr closed (`reflect_fn_sig_pi`).
        Ty::FnDef { sig, .. } => reflect_fn_sig_pi(sig),
        // TYPE-ZOO #4 (HRTBs) — PRODUCTION-WIRED: a function pointer whose signature has a
        // REFERENCE parameter (`&'a …`) is the higher-ranked `for<'a> fn(&'a …) -> …`. The
        // universal lifetime quantifier becomes a GENUINE kernel `Pi` over the erased
        // `Trust.Region` atom, ONE `Π(r : Trust.Region)` per `&`-borrowed parameter, wrapped
        // around the ordinary fn arrow ([`reflect_hrtb_fn`]) — the SAME carrier the `hrtb_fn`
        // corpus probe grounds. `clean_ground::register_region_carrier` registers the
        // axiom-free `Trust.Region` atom and `to_clean_expr` binds the region directly at that
        // `Type` const (a real kernel Pi, ⊆ the 3, NO 4th axiom). A plain fn pointer with NO
        // reference parameter keeps the base `reflect_fn_sig_pi` arrow (the non-higher-ranked
        // case). A non-`El`-decodable / opaque-type-variable param or return fails closed
        // transitively, exactly like the base fn-ptr path.
        Ty::FnPtr { sig } => {
            let num_regions = sig.params.iter().filter(|p| matches!(p, Ty::Ref { .. })).count();
            if num_regions > 0 { reflect_hrtb_fn(num_regions, sig) } else { reflect_fn_sig_pi(sig) }
        }
        // Trust: a trait object `dyn Trait` reflects as the CLOSED EXISTENTIAL
        // dependent type const `Trust.Dyn.<trait_name>` (stable per-trait), which
        // `clean_ground::register_dyn_carriers` registers as the genuine dependent pair
        // `Sigma (T:Type), Trust.Dyn.Vtable.<trait> T` — "there exists a carrier `T`
        // together with the trait-method implementations for `T`". This is a REAL
        // dependent type rooted in the 3 foundational axioms (`add_inductive` over the
        // prelude `Sigma` + the vtable record, `axiom_deps` EMPTY), NOT a free opaque
        // const and NOT a universally-abstracted `∀ D` over-approximation. Reflecting
        // it as a scalar would be unsound; the existential is faithful and carries no
        // integer content, so an integer fact about a `dyn` value stays unprovable.
        // TYPE-ZOO #2/#3 + base dyn — PRODUCTION-WIRED trait-object dispatch by the
        // extractor's trait_name convention (the SAME tags the impl/multi corpus probes
        // carry):
        //   * `@impl::<trait>` (an RPIT/TAIT opaque return) → the `Trust.Impl.<trait>`
        //     existential const ([`reflect_impl_trait`] / [`impl_trait_const_name`]) — the
        //     `dyn` analogue under the DISTINCT `Trust.Impl.*` name, so an `impl Trait` and a
        //     `dyn Trait` over the same trait are separate existentials. `clean_ground::
        //     register_dyn_carriers` registers it as `Sigma (T:Type) Vtable_<trait> T`.
        //   * `<A> + <B> + …` (a MULTI-BOUND trait object) → the CONJOINED existential, whose
        //     const NAME is `dyn_const_name(trait_name)` keyed on the WHOLE `+`-joined string
        //     ([`reflect_multi_dyn`]) — so `dyn A + B` is a distinct existential from `dyn A`,
        //     and the conjoined vtable (methods of every non-marker bound) registers modulo 3.
        //   * a single-bound `dyn Trait` → the existing closed existential const
        //     `Trust.Dyn.<trait>` ([`dyn_const_name`]).
        // Every branch is an `El`-free `Type` const that `to_clean_expr` passes through as a
        // kernel const and `register_dyn_carriers` grounds to the registered `Sigma` Definition
        // (axiom_deps EMPTY — NO 4th axiom, NO free const). An env that did not register the
        // carrier fails closed at `infer_type` — sound, never a false proof.
        Ty::Dynamic { trait_name } => {
            if let Some(bare) = trait_name.strip_prefix("@impl::") {
                Ok(cst(&impl_trait_const_name(bare)))
            } else {
                // Single- AND multi-bound trait objects share the `dyn_const_name` keying
                // (multi keys on the whole `+`-joined string); the multi-bound vtable is the
                // conjoined record `reflect_multi_dyn` builds at registration time.
                Ok(cst(&dyn_const_name(trait_name)))
            }
        }
        // Trust: a generic type parameter `T` reflects as a FREE const
        // `Trust.Param.<id>` (stable per-param within a function). It is NOT a
        // scalar carrier of `Trust.SortTy` — it is a genuine type variable that a
        // contract abstracts into an outermost `Π(<id> : Type)` binder
        // (`reflect_contract`). Reflecting it as `Int` would be unsound; an opaque
        // bound `T` keeps integer facts about `T`-typed values unprovable.
        Ty::Unsupported { kind, detail } if kind == PARAM_KIND => {
            Ok(cst(&param_const_name(&param_ident_from_detail(detail))))
        }
        Ty::Unsupported { .. } => {
            Err(ReflectError::UnsupportedType("Ty::Unsupported is not reflectable"))
        }
        _ => Err(ReflectError::UnsupportedType("unknown non_exhaustive Ty variant")),
    }
}

/// The `Ty::Adt` ENUM equivalent of a FULL `Ty::Datatype` definition — the
/// bridge that lets a compacted recursive ADT reflect through the SAME
/// enum/struct machinery (`reflect_enum`/`reflect_struct_product`) an
/// uncompacted `Ty::Adt` uses, so the two spellings of one type reflect
/// IDENTICALLY by construction.
///
/// SOUNDNESS (nothing fabricated):
///   * constructors and fields are copied VERBATIM from the dump's variant list —
///     no structure is invented;
///   * `VariantDef::discriminant` is the constructor ORDINAL (SMT-LIB datatype
///     constructors carry no discriminant values). This is a labeling, not a
///     fact: `trust-clean` derives NO proof from `EnumCtor::discriminant`
///     (discriminant range/switch facts come from the MIR body and the
///     `disc_index_safe` flag), and
///   * `Ty::adt_enum` sets `disc_index_safe: false` — the conservative default —
///     so the native discriminant-range fact is NEVER synthesized for a
///     compacted type.
///
/// A single-constructor recursive struct arrives as a 1-variant enum and
/// reflects as a 1-constructor inductive — faithful to the SMT datatype view.
#[must_use]
pub fn datatype_equivalent_adt(name: &str, variants: &[(String, Vec<(String, Ty)>)]) -> Ty {
    let defs = variants
        .iter()
        .enumerate()
        .map(|(i, (vname, fields))| trust_types::VariantDef {
            name: vname.clone(),
            discriminant: i128::try_from(i).unwrap_or(i128::MAX),
            fields: fields.clone(),
        })
        .collect();
    Ty::adt_enum(name, defs)
}

/// Reflect a function signature into a Clean curried arrow *code*.
///
/// `fn(p1, p2) -> ret` becomes `Fn R(p1) (Fn R(p2) R(ret))`, a term of
/// `Trust.SortTy` built from the `Trust.Sort.Fn` carrier. A nullary `fn() -> ret`
/// reflects to `R(ret)` directly. This is the function-*type* skeleton; M3
/// attaches pre/post-condition predicates as dependent antecedents so the spec
/// becomes the type (Curry-Howard).
///
/// # Errors
///
/// Returns the [`ReflectError`] naming the first non-reflectable parameter or
/// return type (fails closed transitively).
pub fn reflect_fn_sig(sig: &FnSig) -> Result<ProofTerm, ReflectError> {
    let ret = reflect_ty(&sig.ret)?;
    sig.params.iter().rev().try_fold(ret, |acc, param| {
        let param_code = reflect_ty(param)?;
        Ok(app(app(cst(CARRIER_FN), param_code), acc))
    })
}

/// FUNCTION POINTER (M5) — reflect a function signature into a GENUINE Clean `Pi`
/// (dependent function / arrow) type, the real-kernel replacement for the
/// `Trust.Sort.Fn` *code* that [`reflect_fn_sig`] builds.
///
/// `fn(A, B) -> C` becomes the curried kernel arrow
/// `Π(_ : El R(A)) → Π(_ : El R(B)) → El R(C)` — `reflect(A) -> reflect(B) ->
/// reflect(C)`, a real `ProofTerm::Pi` chain that `clean_ground::to_clean_expr`
/// grounds DIRECTLY to the native kernel `Expr::pi` (the kernel has `Pi`
/// primitively, rooted in the 3 foundational axioms — NO new carrier, NO 4th
/// axiom). A nullary `fn() -> ret` reflects to `El R(ret)` directly.
///
/// Each parameter/return type reflects via [`reflect_ty`] and is wrapped in the
/// Tarski decode `Trust.El` so the `Pi` binder ranges over a real kernel TYPE
/// (`El (R τ)` decodes to `Int`/`Bool`/`List …`/… in `decode_el_code`). The arrow
/// is NON-dependent (a fn pointer's codomain does not mention the argument value),
/// so no de-Bruijn shifting is needed — the `El`-decoded domain/codomain are
/// closed kernel types.
///
/// # Errors
///
/// Returns the [`ReflectError`] naming the first non-reflectable parameter or
/// return type (fails closed transitively, exactly like [`reflect_fn_sig`]). In
/// particular a parameter/return that reflects to an opaque TYPE VARIABLE (a bare
/// `T`/`dyn`, whose `reflect_ty` is a `Sort 1` const, not an `El`-decodable code)
/// is rejected here so the Pi never wraps a non-`El` carrier in `El`; such a fn
/// pointer keeps the conservative fail-closed verdict.
pub fn reflect_fn_sig_pi(sig: &FnSig) -> Result<ProofTerm, ReflectError> {
    // The codomain (return) kernel type `El R(ret)`.
    let ret = fn_arrow_component_ty(&sig.ret)?;
    // Curry right-to-left: `Π(_ : El R(pₙ)) → … → El R(ret)`.
    sig.params.iter().rev().try_fold(ret, |acc, param| {
        let domain = fn_arrow_component_ty(param)?;
        Ok(ProofTerm::Pi {
            binder_name: "_".to_string(),
            domain: Box::new(domain),
            codomain: Box::new(acc),
        })
    })
}

/// The kernel TYPE a function-pointer arrow component (a parameter or the return)
/// binds at: `El (R τ)`, the Tarski decode of the reflected type code, so a real
/// kernel `Pi` can range over it. Fails closed (NOT wrapping in `El`) for a type
/// whose `reflect_ty` is an opaque TYPE VARIABLE const (`Trust.Param.*`/`Trust.Dyn.*`
/// — a `Sort 1` type, not an `El`-decodable `Trust.SortTy` code) so the Pi is never
/// built over a non-decodable carrier.
fn fn_arrow_component_ty(ty: &Ty) -> Result<ProofTerm, ReflectError> {
    let code = reflect_ty(ty)?;
    if is_type_var_const_term(&code) {
        return Err(ReflectError::UnsupportedType(
            "a function-pointer parameter/return whose type is an opaque type variable \
             has no El-decodable carrier for the kernel Pi; fails closed",
        ));
    }
    Ok(app(cst(CARRIER_EL), code))
}

/// Whether a reflected `ProofTerm` is exactly an opaque type-variable carrier const
/// (`Trust.Param.*`/`Trust.Dyn.*`/`Trust.Opaque.*`) — i.e. a `Sort 1` type, not a
/// `Trust.SortTy` *code* that `Trust.El` decodes.
fn is_type_var_const_term(term: &ProofTerm) -> bool {
    matches!(term, ProofTerm::Const(n) if is_type_var_const(n))
}

/// CLOSURE RECORD (M5) — the contract BINDING carrier for a value whose type is a
/// closure `Ty::Closure { name, upvars, .. }`: the registered record inductive
/// `Trust.Closure.<name>` applied to its two call-signature type params
/// `(Trust.Param.<A>) (Trust.Param.<B>)`, exactly like [`generic_struct_binding`]
/// applies a generic struct's inductive to its param consts. `reflect_contract`
/// abstracts the two param consts into outer `Π(A : Type) Π(B : Type)` binders, and
/// `clean_ground`'s `to_clean_expr` decodes the applied carrier to the real kernel
/// type `Closure A B` under those binders — so a closure PARAMETER binds at
/// `Π(c : Closure A B)`. Returns `None` (→ upvar `Prod` fallback) iff the closure's
/// upvar environment does not reflect (a non-reflectable capture).
#[must_use]
fn closure_binding(name: &str, upvars: &[Ty]) -> Option<ProofTerm> {
    let carrier = reflect_closure(name, upvars)?;
    // `Trust.Closure.<Name>` applied to each call-param const (in binder order).
    let mut applied = cst(&carrier.name);
    for id in &carrier.type_params {
        applied = app(applied, cst(&param_const_name(id)));
    }
    Some(applied)
}

// ---------------------------------------------------------------------------
// M3: predicate reflection (Formula -> Prop)
// ---------------------------------------------------------------------------

/// Reflect a Trust `Formula` (in proposition position) into a Clean term of
/// `Prop` (`Sort(0)`) — the spec-as-type proposition half of M3.
///
/// Handles the core predicate subset: boolean literals, boolean variables,
/// `Not`/`And`/`Or`/`Implies`, and the comparisons `Eq`/`Lt`/`Le`/`Gt`/`Ge`
/// (whose operands reflect via [`reflect_int_term`]). `And([])` is `True` and
/// `Or([])` is `False`. Free variables become `Const(name)` resolved against the
/// context (declared `: Prop` for bool vars). Everything outside the subset —
/// bitvector theory, quantifiers, arrays, `Ite`, interned `SymVar`, `Pred` —
/// fails closed with [`ReflectError::PredicateUnsupported`].
///
/// # Errors
///
/// Returns [`ReflectError::PredicateUnsupported`] for an out-of-subset variant
/// (possibly within a sub-formula).
pub fn reflect_formula(formula: &Formula) -> Result<ProofTerm, ReflectError> {
    use trust_types::Formula as F;
    match formula {
        F::Bool(true) => Ok(cst(PROP_TRUE)),
        F::Bool(false) => Ok(cst(PROP_FALSE)),
        // A bare variable used as a proposition is a boolean result asserted true:
        // `Var(b)` ⇒ `BoolTrue b`, which grounds to `@Eq Bool b Bool.true` over the
        // real `Bool` return type (M4 boolean-result reasoning).
        F::Var(name, _) => Ok(app(cst(PROP_BOOL_TRUE), cst(name))),
        F::Not(p) => Ok(app(cst(PROP_NOT), reflect_formula(p)?)),
        F::And(children) => reflect_connective(children, PROP_AND, PROP_TRUE),
        F::Or(children) => reflect_connective(children, PROP_OR, PROP_FALSE),
        F::Implies(a, b) => {
            Ok(app(app(cst(PROP_IMPLIES), reflect_formula(a)?), reflect_formula(b)?))
        }
        F::Eq(a, b) => reflect_cmp(PROP_EQ, a, b),
        F::Lt(a, b) => reflect_cmp(PROP_LT, a, b),
        F::Le(a, b) => reflect_cmp(PROP_LE, a, b),
        F::Gt(a, b) => reflect_cmp(PROP_GT, a, b),
        F::Ge(a, b) => reflect_cmp(PROP_GE, a, b),
        _ => Err(ReflectError::PredicateUnsupported(
            "Formula variant outside the core predicate subset (bitvector theory, \
             quantifiers, arrays, Ite, SymVar, or uninterpreted Pred)",
        )),
    }
}

/// Reflect an integer-sorted `Formula` (operand position) into a `Trust.Int`
/// term: literals, integer variables, and `+`/`-`/`*`/`/`/`%`/unary-`-`.
///
/// # Errors
///
/// Returns [`ReflectError::PredicateUnsupported`] for a non-integer-term variant.
pub fn reflect_int_term(formula: &Formula) -> Result<ProofTerm, ReflectError> {
    use trust_types::Formula as F;
    match formula {
        F::Int(n) => Ok(ProofTerm::Const(int_lit_name(*n))),
        // Unsigned literals are non-negative integers in the math-integer model.
        F::UInt(n) => Ok(ProofTerm::Const(int_lit_name(i128::try_from(*n).map_err(|_| {
            ReflectError::PredicateUnsupported("u128 literal exceeds i128 integer model")
        })?))),
        F::Var(name, _) => Ok(cst(name)),
        F::Add(a, b) => reflect_int_binop(INT_ADD, a, b),
        F::Sub(a, b) => reflect_int_binop(INT_SUB, a, b),
        F::Mul(a, b) => reflect_int_binop(INT_MUL, a, b),
        F::Div(a, b) => reflect_int_binop(INT_DIV, a, b),
        F::Rem(a, b) => reflect_int_binop(INT_REM, a, b),
        F::Neg(a) => Ok(app(cst(INT_NEG), reflect_int_term(a)?)),
        _ => Err(ReflectError::PredicateUnsupported(
            "Formula variant is not an integer-sorted term (bitvector op, bool, \
             comparison, or quantifier in operand position)",
        )),
    }
}

/// Reflect an n-ary connective (`And`/`Or`) as a right-nested binary application
/// terminated by its unit (`True`/`False`).
fn reflect_connective(
    children: &[Formula],
    op: &str,
    unit: &str,
) -> Result<ProofTerm, ReflectError> {
    match children.split_first() {
        None => Ok(cst(unit)),
        Some((head, tail)) => {
            let head_term = reflect_formula(head)?;
            if tail.is_empty() {
                return Ok(head_term);
            }
            let tail_term = reflect_connective(tail, op, unit)?;
            Ok(app(app(cst(op), head_term), tail_term))
        }
    }
}

/// Reflect a binary comparison `op a b` over integer operands.
fn reflect_cmp(op: &str, a: &Formula, b: &Formula) -> Result<ProofTerm, ReflectError> {
    Ok(app(app(cst(op), reflect_int_term(a)?), reflect_int_term(b)?))
}

/// Reflect a binary integer operation `op a b`.
fn reflect_int_binop(op: &str, a: &Formula, b: &Formula) -> Result<ProofTerm, ReflectError> {
    Ok(app(app(cst(op), reflect_int_term(a)?), reflect_int_term(b)?))
}

// ---------------------------------------------------------------------------
// M3 step 2: dependent contract types (the Curry-Howard close)
// ---------------------------------------------------------------------------

/// Bind a free `Const(name)` into a de-Bruijn variable at index `k`,
/// shifting existing free variables (`>= k`) up by one to make room.
///
/// This is the locally-nameless → de-Bruijn abstraction used to place a reflected
/// predicate (which names its variables `Const(name)`) under a kernel binder.
/// Replace each `Const(name)` that is a key of `rewrites` with its mapped term
/// (used to turn a struct-field reference `Const("p.value")` into a projection
/// carrier `Trust.Proj.0 (Const "p")` before parameter abstraction binds `p`).
fn rewrite_field_consts(
    term: &ProofTerm,
    rewrites: &std::collections::HashMap<String, ProofTerm>,
) -> ProofTerm {
    match term {
        ProofTerm::Const(n) => {
            rewrites.get(n).cloned().unwrap_or_else(|| ProofTerm::Const(n.clone()))
        }
        ProofTerm::App(f, a) => ProofTerm::App(
            Box::new(rewrite_field_consts(f, rewrites)),
            Box::new(rewrite_field_consts(a, rewrites)),
        ),
        ProofTerm::Lambda { binder_name, binder_type, body } => ProofTerm::Lambda {
            binder_name: binder_name.clone(),
            binder_type: Box::new(rewrite_field_consts(binder_type, rewrites)),
            body: Box::new(rewrite_field_consts(body, rewrites)),
        },
        ProofTerm::Pi { binder_name, domain, codomain } => ProofTerm::Pi {
            binder_name: binder_name.clone(),
            domain: Box::new(rewrite_field_consts(domain, rewrites)),
            codomain: Box::new(rewrite_field_consts(codomain, rewrites)),
        },
        other => other.clone(),
    }
}

fn abstract_const(term: &ProofTerm, name: &str, k: usize) -> ProofTerm {
    match term {
        ProofTerm::Const(n) if n == name => ProofTerm::Var(k),
        ProofTerm::Const(n) => ProofTerm::Const(n.clone()),
        ProofTerm::Var(i) => ProofTerm::Var(if *i >= k { i + 1 } else { *i }),
        ProofTerm::Sort(u) => ProofTerm::Sort(*u),
        ProofTerm::App(f, a) => ProofTerm::App(
            Box::new(abstract_const(f, name, k)),
            Box::new(abstract_const(a, name, k)),
        ),
        ProofTerm::Lambda { binder_name, binder_type, body } => ProofTerm::Lambda {
            binder_name: binder_name.clone(),
            binder_type: Box::new(abstract_const(binder_type, name, k)),
            body: Box::new(abstract_const(body, name, k + 1)),
        },
        ProofTerm::Pi { binder_name, domain, codomain } => ProofTerm::Pi {
            binder_name: binder_name.clone(),
            domain: Box::new(abstract_const(domain, name, k)),
            codomain: Box::new(abstract_const(codomain, name, k + 1)),
        },
    }
}

/// The kernel type a contract binds a value of type `ty` at. Integer types
/// short-circuit to the `Trust.Int` term universe (so the integer predicate
/// vocabulary — comparisons, arithmetic — applies to the bound value); every
/// other reflectable type decodes opaquely through `Trust.El` (`El (R ty)`).
/// Non-reflectable types fail closed via [`reflect_ty`].
/// `opaque_param`: when binding a PARAMETER, its name — enabling the
/// composite-with-nested-type-var over-approximation (the whole parameter binds at a
/// fresh `Trust.Opaque.<name>` type variable). `None` in RETURN position, where the
/// over-approximation is unsound (you cannot conjure a value of an opaque return) and
/// such a return stays fail-closed.
fn carrier_binding_type(ty: &Ty, opaque_param: Option<&str>) -> Result<ProofTerm, ReflectError> {
    match ty {
        Ty::Int { .. } | Ty::Bv(_) => Ok(cst(PROP_INT)),
        // A value whose type IS a bare generic param `T` (or a transparent `&T`/`&mut
        // T`) binds DIRECTLY at the type variable, not through `Trust.El`: the carrier
        // const (`Trust.Param.<id>`) is itself a type (`Sort 1`), not a `Trust.SortTy`
        // *code* that `El` decodes. After `reflect_contract` abstracts it, this becomes
        // `Π(x : Var<T>)` under the outer `Π(T : Type)`. Opaque `T` is sound — nothing
        // about its structure is assumed.
        _ if bare_type_var(ty).is_some() => reflect_ty(ty),
        // A value whose type is a TRAIT OBJECT `dyn Trait` (bare, or behind a
        // transparent `&dyn`/`&mut dyn`) binds DIRECTLY at the CLOSED existential
        // dependent type `Trust.Dyn.<trait>` (`Sigma (T:Type), Vtable_<trait> T`,
        // registered modulo 3 by `clean_ground::register_dyn_carriers`). NOT through
        // `Trust.El` (the existential is a `Type`, not a `Trust.SortTy` code) and NOT
        // as a universally-abstracted opaque variable — `Trust.Dyn.*` is no longer
        // collected by `free_type_var_consts`, so it gets NO outer `Π(D:Type)` binder.
        // `Π(w : Trust.Dyn.<trait>)` is a faithful existential binding; an integer fact
        // about a `dyn`-typed value stays unprovable (the existential carries no Int
        // content), failing closed not falsely.
        _ if dyn_object_const(ty).is_some() => reflect_ty(ty),
        // PHASE 2 — a GENERIC struct parameter `p : Wrapper<T>` binds at the
        // PARAMETERIZED inductive applied to its type params,
        // `Trust.Adt.Wrapper (Trust.Param.T)`. `reflect_contract` then abstracts the
        // param const into the outer `Π(T : Type)`, giving `Π(p : Wrapper T)` under
        // it — genuine dependent structure. The concrete fields project structurally;
        // a generic field stays opaque (parametricity). Takes priority over the
        // composite-with-type-var opaque fallback below (which a generic struct's
        // anonymous `Prod` code would otherwise hit).
        _ if generic_struct_binding(ty).is_some() => {
            Ok(generic_struct_binding(ty).expect("checked Some"))
        }
        // FAITHFULNESS FIX (enum sum types) — a CONCRETE enum value `p : Option<i32>`
        // binds DIRECTLY at its registered multi-constructor inductive `Trust.Adt.<Enum>`
        // (a closed named `Type`, registered modulo 3 by `register_adt_carriers` via the
        // existing `reachable_adt_carriers` pipeline), NOT through `Trust.El` (the
        // inductive is a `Type`, not a `Trust.SortTy` code) and NOT as the `El`-wrapped
        // `Prod`-over-union floor the pre-fix `reflect_ty` produced. `Π(p : Trust.Adt.
        // core::option::Option)` is the faithful sum-type binding — DISTINCT from a
        // 1-field struct's `Prod`, with `Some`/`None` distinct constructors. A generic
        // enum was already handled by `generic_struct_binding` above (its parameterized
        // applied carrier); this arm fires for a NON-generic enum only. Takes priority
        // over the `_` fallback, which would otherwise `El`-wrap the bare `Trust.Adt.*`
        // const (a const `decode_el_code` cannot decode).
        _ if concrete_enum_binding(ty).is_some() => {
            Ok(concrete_enum_binding(ty).expect("checked Some"))
        }
        // RECURSIVE DEPENDENT CARRIER (goal bullet 2 tail) — ANY composite that nests
        // a type variable at ANY depth (a sequence `Vec<T>`/`&[T]`/`[T; N]`, a
        // deeply-nested `Vec<Vec<T>>` / `Vec<Wrapper<T>>`, a tuple `(T, u8)`, a nested
        // generic enum) binds at the recursive [`parameterized_composite_binding`]
        // carrier — a mix of `Slice`/`Vec`/`Prod` heads and Pi-bound type-var consts /
        // applied inner inductives, which `to_clean_expr` decodes to the real dependent
        // kernel type under the outer `Π(T : Type)`. So a `Vec<Vec<T>>` PARAMETER binds
        // as `Π(v : List (List T))`, a `(T, u8)` PARAMETER as `Π(v : Prod T Int)`, and
        // a value RETURN at the decoded type (inhabited by the corresponding witness) —
        // STRUCTURAL, not the opaque `Trust.Opaque.<p>` fallback (parameter) or
        // fail-closed (return) below. Takes priority over the composite-with-type-var
        // opaque fallback, which the carrier would otherwise hit via
        // `code_mentions_type_var`.
        _ if parameterized_composite_binding(ty).is_some() => {
            Ok(parameterized_composite_binding(ty).expect("checked Some"))
        }
        _ => {
            let code = reflect_ty(ty)?;
            // A composite SortTy code that NESTS an opaque type variable (e.g.
            // `(T, u8)` → `Prod (Param T) …`, `&mut Formatter{… dyn Write …}` →
            // `El (Prod … (Dyn Write) …)`) is a universe error: the type variable is
            // a `Type` (`Sort 1`), not a `Trust.SortTy` code that `Prod`/`Slice`/`El`
            // accept, and its `El`-decode has no real-kernel grounding.
            if code_mentions_type_var(&code) {
                // PARAMETER position: bind the WHOLE parameter at a fresh opaque type
                // variable `Trust.Opaque.<name>` (Pi-bound at `Type` like any other
                // type variable). Sound over-approximation — the contract becomes
                // `∀ (p_ty : Type), Π(p : p_ty) → …`, STRONGER than the real type, and
                // the opaque carrier never appears in the integer safety VCs. A
                // contract that needs the parameter's internal structure fails closed.
                if let Some(pname) = opaque_param {
                    return Ok(cst(&opaque_const_name(pname)));
                }
                // RETURN position: fail closed (clean NotGrounded/UnsupportedType) —
                // an opaque return type cannot be inhabited (you cannot conjure a
                // value of an unknown type), so this is the sound verdict.
                return Err(ReflectError::UnsupportedType(
                    "an opaque type variable nested inside a composite RETURN type is \
                     not inhabitable (no faithful carrier, cannot conjure a value); \
                     fails closed",
                ));
            }
            Ok(app(cst(CARRIER_EL), code))
        }
    }
}

/// Reflect a function contract into a genuine **dependent type** — the spec-as-type
/// close of M3. For `fn(p₁, …, pₙ) requires P ensures Q -> ρ`, builds:
///
/// ```text
///   Π(p₁ : Int) … Π(pₙ : Int) → Π(_ : ⟦P⟧) → Trust.Sigma Int (λ ret. ⟦Q⟧)
/// ```
///
/// using the kernel's real `Pi` so the predicates `P`/`Q` are bound over the
/// parameters and the return value (via de-Bruijn abstraction). A function
/// inhabiting this type *is* a proof of the contract. `infer_type` accepting the
/// result as a well-formed `Type` validates the whole construction.
///
/// Parameters and return bind at [`carrier_binding_type`] (integers at
/// `Trust.Int`, other reflectable types at `El (R τ)`); `pre`/`post` must be in
/// the [`reflect_formula`] subset. A predicate that uses a non-integer parameter
/// as an integer operand builds a term the kernel rejects (caught by
/// `infer_type`) — i.e. it fails closed at the kernel boundary.
///
/// # Errors
///
/// Returns [`ReflectError`] if a parameter/return type is non-reflectable, or if
/// a predicate is outside the reflectable subset.
/// Parse a flattened enum MIR field name into `(variant_idx, field_idx_in_variant)`.
/// The MIR extractor flattens an enum local's fields as the discriminant `__tag`
/// followed by one `__v{v}_{field_name}` per variant field (`ty_convert::lower_enum_adt`).
/// Maps `__v{v}_{name}` to its variant index `v` and the position of `{name}` within
/// THAT variant's reflected constructor fields. `None` (skipped — not a per-variant
/// field, or an unparsed shape) for `__tag`, a malformed name, an out-of-range variant,
/// or a field name absent from the variant's reflected fields.
fn enum_flat_field_indices(fname: &str, carrier: &AdtCarrier) -> Option<(usize, usize)> {
    let rest = fname.strip_prefix("__v")?;
    let underscore = rest.find('_')?;
    let v: usize = rest[..underscore].parse().ok()?;
    let field_name = &rest[underscore + 1..];
    let ctor = carrier.constructors.get(v)?;
    let f = ctor.fields.iter().position(|(n, _)| n == field_name)?;
    Some((v, f))
}

/// FAITHFULNESS (enum sum types) — build the field-rewrite carrier for a CONCRETE
/// enum parameter's flattened field reference `p.__v{v}_{name}`: a RECURSOR-based
/// accessor `ProofTerm`, NOT a struct `Trust.Proj`. A concrete enum binds at its
/// multi-constructor inductive `Trust.Adt.<E>`, which the kernel rejects a struct
/// projection on (`InvalidProjNotStruct`). The field must instead be read by the
/// inductive's auto-derived RECURSOR (case-split on the variant, project the matched
/// constructor's field):
///
/// ```text
///   <E>.rec (motive := λ_:<E>. El <field_carrier>) minor₀ … minor_{m-1} (Const p)
/// ```
///
/// with one minor per constructor (MIR order): the TARGET variant's minor
/// `λ(x₀:El τ₀)…(x_{n-1}:El τ_{n-1}). x_target` projects the matched constructor's
/// `target_field_idx`-th argument (so on the active variant the recursor ι-reduces to
/// exactly the field), and every other variant's minor returns the field type's
/// fail-closed scalar default. The recursor `<E>.rec`'s `.{1}` (eliminate into `Type`)
/// level is supplied by `clean_ground::to_clean_expr`'s `.rec` decode; binder types are
/// `El`-wrapped carrier codes that decode to the kernel field types. `Const(p)` is the
/// bound parameter, abstracted by `reflect_contract`'s param Π-wrap exactly as the
/// `Trust.Proj`/`Trust.ProjN` carriers' base is.
///
/// Returns `None` (caller leaves the field unbound — fail-closed, never an unsound
/// proj) for a PARAMETERIZED enum (variant-field types would need the enum's `Type`
/// params in scope — deferred), an out-of-range variant / field, or a variant field
/// whose type is not a defaultable scalar (so an inactive-variant minor cannot be
/// totalized).
fn enum_field_recursor_carrier(
    pname: &str,
    carrier: &AdtCarrier,
    target_variant: usize,
    target_field_idx: usize,
) -> Option<ProofTerm> {
    if carrier.is_parameterized() {
        return None; // deferred — fail closed (no unsound proj).
    }
    let target = carrier.constructors.get(target_variant)?;
    let (_, target_field_code) = target.fields.get(target_field_idx)?;
    // The field's fail-closed scalar default (for the inactive-variant minors); also
    // gates that the TARGET field is a defaultable scalar.
    let field_default = scalar_field_default(target_field_code)?;

    // `<E>.rec` head. Its `.{1}` (eliminate into `Type`) level is supplied by
    // `to_clean_expr`'s `.rec` decode; the major premise (the bound parameter) is
    // appended last.
    let mut head = cst(&format!("{}.rec", carrier.name));

    // motive `λ_:<E>. El <target_field_carrier>` — non-dependent elimination into the
    // field's `Type` (the bound enum value is unused).
    head = app(
        head,
        ProofTerm::Lambda {
            binder_name: "_".to_string(),
            binder_type: Box::new(cst(&carrier.name)),
            body: Box::new(app(cst(CARRIER_EL), target_field_code.clone())),
        },
    );

    // One minor per constructor (MIR order): the TARGET minor projects the matched
    // constructor's field (a de-Bruijn `Var` under that minor's field binders); every
    // other minor returns the scalar default. Each minor abstracts its constructor's
    // fields as `λ(x : El τ)` (innermost field first).
    for (v_idx, ctor) in carrier.constructors.iter().enumerate() {
        let n = ctor.fields.len();
        let body = if v_idx == target_variant {
            // Under `n` field binders (0 = innermost), the j-th field (outermost-first)
            // is `Var(n-1-j)`.
            ProofTerm::Var(n.checked_sub(1 + target_field_idx)?)
        } else {
            field_default.clone()
        };
        let mut minor = body;
        for (_, fcode) in ctor.fields.iter().rev() {
            // Every minor binder's field must be a defaultable scalar so the recursor
            // binds only `El`-decodable kernel types — fail closed otherwise.
            scalar_field_default(fcode)?;
            minor = ProofTerm::Lambda {
                binder_name: "x".to_string(),
                binder_type: Box::new(app(cst(CARRIER_EL), fcode.clone())),
                body: Box::new(minor),
            };
        }
        head = app(head, minor);
    }

    // The major premise: the bound parameter `Const(p)` (abstracted by
    // `reflect_contract`'s param Π-wrap, exactly as the `Trust.Proj`/`Trust.ProjN`
    // carriers' base is).
    Some(app(head, cst(pname)))
}

/// A closed (context-free) `ProofTerm` canonical inhabitant of a CONCRETE scalar field
/// carrier code — the value an INACTIVE enum variant's minor premise returns. Defined
/// only for the scalar carriers a concrete variant field reflects to (`Trust.Sort.Int`,
/// a `Trust.Sort.BitVec w` machine integer → `Int` 0; `Trust.Sort.Bool` → `Bool.false`;
/// `Trust.Sort.Unit` → `Unit.unit`). `None` for any other carrier (the caller then
/// fails closed — NEVER a fabricated default for a non-scalar field).
fn scalar_field_default(code: &ProofTerm) -> Option<ProofTerm> {
    match code {
        // A machine integer `Trust.Sort.BitVec w` → 0 (decodes to `Int`).
        ProofTerm::App(f, _) if matches!(&**f, ProofTerm::Const(n) if n == CARRIER_BITVEC) => {
            Some(cst("Trust.Int.lit.0"))
        }
        ProofTerm::Const(n) if n == CARRIER_INT => Some(cst("Trust.Int.lit.0")),
        ProofTerm::Const(n) if n == CARRIER_BOOL => Some(cst("Bool.false")),
        ProofTerm::Const(n) if n == CARRIER_UNIT => Some(cst("Unit.unit")),
        _ => None,
    }
}

pub fn reflect_contract(
    params: &[(&str, &Ty)],
    pre: &Formula,
    ret_name: &str,
    ret_ty: &Ty,
    post: &Formula,
) -> Result<ProofTerm, ReflectError> {
    // A generic-parameter / trait-object RETURN type is now SUPPORTED: with the
    // opaque type variable bound at `Type` (`Sort 1`), the carrier const
    // (`Trust.Param.<id>`/`Trust.Dyn.<name>`) is itself a valid `Trust.Sigma`
    // return carrier (`Sigma : Π(A : Sort 1) → …`). So `fn id<T>(x: T) -> T` becomes
    // `Π(T : Type) → Π(x : T) → Π(_:P) → Sigma T (λ ret. Q)`. The contract TYPE
    // kernel-checks; inhabitation is still sound (a trivial postcondition over an
    // opaque return only inhabits if a value of `T` is in scope — e.g. the
    // identity returns its `T`-typed param — and an integer postcondition over the
    // opaque return stays unprovable by parametricity, failing closed not falsely).
    // RETURN position passes `None`: a composite-with-nested-var return stays
    // fail-closed (an opaque return is uninhabitable).
    let ret_carrier = carrier_binding_type(ret_ty, None)?;

    // Map each Adt parameter's field reference `p.field` to a projection carrier of
    // the bound parameter, so a contract referencing a struct field grounds as a
    // structural projection (rather than an unbound free constant). The carrier MUST
    // match how the parameter BINDS:
    //   * a param that reflects to a REGISTERED named/parameterized inductive
    //     (`Wrapper<T>` → binds at `Wrapper T`) uses the NAMED projection carrier
    //     `Trust.ProjN.<inductive>.<idx> p` — the kernel-native projection of that
    //     inductive — so `w.count` projects `Wrapper` (NOT an anonymous `Prod` of a
    //     `Wrapper`-typed value, which is a structure mismatch the kernel rejects);
    //   * any other Adt param (a struct on the anonymous `Prod`/`Unit` floor) uses the
    //     anonymous `Trust.Proj.<idx> p` Prod projection, exactly as before.
    let mut field_rewrites: std::collections::HashMap<String, ProofTerm> =
        std::collections::HashMap::new();
    for (pname, ty) in params {
        if let Ty::Adt { fields, .. } = ty {
            // FAITHFULNESS (enum sum types) — a CONCRETE ENUM param binds at its
            // multi-constructor inductive `Trust.Adt.<E>`, which the kernel rejects a
            // struct `Proj` on (`InvalidProjNotStruct`). Its flattened MIR fields
            // (`__tag`, `__v{v}_{name}`) are read via the inductive's auto-derived
            // RECURSOR (`enum_field_recursor_carrier`). The discriminant `__tag` and any
            // field the recursor carrier cannot faithfully build are LEFT UNBOUND
            // (fail-closed: a contract reading them then fails to ground rather than
            // grounding through an unsound projection).
            if let Some(enum_carrier) = reflect_struct(ty).filter(AdtCarrier::is_enum) {
                for (fname, _) in fields {
                    if let Some((v, f)) = enum_flat_field_indices(fname, &enum_carrier) {
                        if let Some(acc) = enum_field_recursor_carrier(pname, &enum_carrier, v, f) {
                            field_rewrites.insert(format!("{pname}.{fname}"), acc);
                        }
                    }
                }
                continue;
            }
            // A param that binds at a real PARAMETERIZED named inductive (`w :
            // Wrapper T`, via `generic_struct_binding`) uses the NAMED projection
            // (keyed by the inductive name + field index). A NON-generic (Phase-1)
            // struct param binds at the ANONYMOUS `El (Prod …)` carrier instead
            // (`carrier_binding_type`'s `El` path), so it KEEPS the anonymous `Prod`
            // projection — matching its binding.
            let named = reflect_struct(ty).filter(|c| c.is_parameterized() && !c.is_enum());
            for (idx, (fname, _)) in fields.iter().enumerate() {
                let proj_carrier = match &named {
                    Some(carrier) => {
                        app(cst(&format!("{PROJN_PREFIX}{}.{idx}", carrier.name)), cst(pname))
                    }
                    None => app(cst(&format!("{PROJ_PREFIX}{idx}")), cst(pname)),
                };
                field_rewrites.insert(format!("{pname}.{fname}"), proj_carrier);
            }
        }
    }

    // Σ(ret : R(ρ)) × ⟦Q⟧  =  Trust.Sigma R(ρ) (λ ret : R(ρ). ⟦Q⟧[ret := Var0])
    let post_term = rewrite_field_consts(&reflect_formula(post)?, &field_rewrites);
    let post_lam = ProofTerm::Lambda {
        binder_name: ret_name.to_string(),
        binder_type: Box::new(ret_carrier.clone()),
        body: Box::new(abstract_const(&post_term, ret_name, 0)),
    };
    let sigma = app(app(cst(CARRIER_SIGMA), ret_carrier), post_lam);

    // Π(_ : ⟦P⟧) → Σ…   (the precondition as an anonymous proof binder; shift the
    // body up by one for the new binder it does not reference).
    let pre_term = rewrite_field_consts(&reflect_formula(pre)?, &field_rewrites);
    let mut acc = ProofTerm::Pi {
        binder_name: "_".to_string(),
        domain: Box::new(pre_term),
        codomain: Box::new(shift(&sigma, 0, 1)),
    };

    // Wrap each parameter in Π(p : R(τ)), abstracting its name through the body.
    // An opaque-type-variable param's domain is the free type-var const
    // `Trust.Param.<id>`/`Trust.Dyn.<name>`, or — for a composite that nests a type
    // var — the synthetic `Trust.Opaque.<p>` (passing the param name enables that
    // over-approximation); concrete types bind at `El`/`Int`. Those free consts are
    // abstracted by the outermost type-Pi binders added below.
    for (name, ty) in params.iter().rev() {
        let domain = carrier_binding_type(ty, Some(name))?;
        acc = ProofTerm::Pi {
            binder_name: (*name).to_string(),
            domain: Box::new(domain),
            codomain: Box::new(abstract_const(&acc, name, 0)),
        };
    }

    // Pi-wrap each DISTINCT opaque type variable (generic param OR trait object)
    // that ACTUALLY occurs in the built contract OUTERMOST: `Π(T : Type) → …`.
    // Collecting the free `Trust.Param.*`/`Trust.Dyn.*` consts straight from the term
    // (rather than re-walking the `Ty`s) binds EXACTLY the type variables present —
    // no unused binders for one that appears only inside a pointer/composite that
    // reflected to a concrete carrier, and a shared binder for a param/`dyn Trait`
    // that recurs. `abstract_const` turns each free const into the bound type
    // variable, so the outer `Π(T : Type)` binds the `T` an inner `Π(x : T)` (or the
    // `Sigma T …` return carrier) mentions. Outer-binding order matches first
    // appearance walking the term.
    let var_consts = free_type_var_consts(&acc);
    for var_const in var_consts.iter().rev() {
        acc = ProofTerm::Pi {
            binder_name: var_const.clone(),
            domain: Box::new(reflect_param_sort()),
            codomain: Box::new(abstract_const(&acc, var_const, 0)),
        };
    }
    Ok(acc)
}

/// Bridge the compiler's spec data model to a dependent contract type: turn a
/// [`FnSig`] + [`FunctionSpec`] (`#[requires]`/`#[ensures]`, as flowed from the
/// frontend) into the kernel-checked dependent type via [`reflect_contract`].
///
/// This is the wiring point between the verification pipeline and the reflection
/// engine: a real Trust function's contract becomes a Clean dependent type. The
/// caller supplies `param_names` (matching the variable names the spec
/// expressions use). The return value is bound under the spec parser's canonical
/// `result` name (`_0`), so `#[ensures(result > x)]` resolves correctly.
/// Multiple `requires`/`ensures` clauses are conjoined; invariants are ignored
/// here (they are loop obligations, not the function contract).
///
/// # Errors
///
/// Returns [`ReflectError`] if `param_names` does not match the signature arity,
/// a type is non-reflectable, or a parsed clause is outside the predicate subset.
pub fn reflect_function_spec(
    sig: &FnSig,
    param_names: &[&str],
    spec: &FunctionSpec,
) -> Result<ProofTerm, ReflectError> {
    if param_names.len() != sig.params.len() {
        return Err(ReflectError::PredicateUnsupported(
            "param_names length must match the signature's parameter count",
        ));
    }
    let params: Vec<(&str, &Ty)> = param_names.iter().copied().zip(sig.params.iter()).collect();
    let pre = conjoin(
        spec.parse_requires()
            .map_err(|error| ReflectError::SpecParse(format!("requires clause: {error}")))?,
    );
    let post = conjoin(
        spec.parse_ensures()
            .map_err(|error| ReflectError::SpecParse(format!("ensures clause: {error}")))?,
    );
    // The spec parser canonicalizes `result` to `_0` (spec_parse.rs).
    reflect_contract(&params, &pre, SPEC_RESULT_VAR, &sig.ret, &post)
}

/// The spec parser's canonical name for the `result` (return) value.
const SPEC_RESULT_VAR: &str = "_0";

/// Reflect a [`VerifiableFunction`] — the pipeline's currency (MIR →
/// trust-mir-extract → `VerifiableFunction`) — directly into its dependent
/// contract type. This is the integration point a downstream verification stage
/// (or the MIR pass) calls to obtain the kernel-checkable spec type for a
/// function: it reads the already-parsed `preconditions`/`postconditions`
/// `Formula`s and the parameter/return types from the body (MIR convention:
/// local 0 is the return slot, locals `1..=arg_count` are the parameters,
/// preferring each local's source `name`).
///
/// # Errors
///
/// Returns [`ReflectError`] if a parameter/return type is non-reflectable or a
/// spec predicate is outside the reflectable subset.
pub fn reflect_verifiable_function(func: &VerifiableFunction) -> Result<ProofTerm, ReflectError> {
    let body = &func.body;
    // DUMP COMPACTION (M6 census gap #1) — PRE-RESOLVE `Ty::Datatype` by-name
    // back-references against the dump's own recursive-type map before reflecting.
    // `trust-mir-extract`'s compaction emits the full variant list at a recursive
    // datatype's DEFINING occurrence (a local's own declared type) and an empty
    // `variants: []` by-name reference everywhere it recurs, so the function's own
    // locals ARE the resolution map: collect every full definition reachable from
    // any local (name → variants, dropped on conflict — fail-closed), then rewrite
    // each parameter/return type with the definitions substituted (occurs-checked,
    // so a datatype's own recursive occurrences stay opaque back-references — the
    // one-level-unrolled view `reflect_ty`'s `Ty::Datatype` arm reflects). A
    // back-reference whose definition appears NOWHERE in the function stays as-is
    // and fails closed to the opaque `Trust.Param.@datatype::<name>` carrier.
    let datatype_defs = collect_datatype_defs(body);
    // ARITY-CONSISTENCY (M6 rung-5 successor item 1, "PI-ARITY") — a named
    // struct/enum whose OWN structural shape (hence `AdtCarrier::type_params`
    // arity) DIFFERS across different occurrences reachable from this
    // function's locals must never bind at its named inductive here: the
    // contract's Π domain would then apply a DIFFERENT number of type
    // arguments than whichever occurrence `clean_ground::reachable_adt_carriers`
    // happens to register in the kernel — an arity mismatch the real kernel's
    // `check_type` rejects (`NotAFunction`). Collapse every occurrence of such
    // an ambiguous name to the SAME opaque back-reference treatment an
    // unresolvable `Ty::Datatype` back-reference already gets (sound, strictly
    // weaker; never a false certificate) — see `ambiguous_adt_names` /
    // `collapse_ambiguous_tys`.
    let ambiguous = ambiguous_adt_names(func);
    // Trust: structural-fold rung E — run the same compaction pre-pass used by
    // ambiguity detection and kernel registration. SF-2 deliberately refuses
    // to enrich an identity-erased empty Datatype leaf from a merely same-name
    // Adt: such spellings remain incomparable and are collapsed opaquely by
    // `ambiguous_adt_names`. Full Datatype definition/back-reference resolution
    // below remains a separate, occurs-checked lane.
    let adt_defs = collect_adt_compaction_defs(body);
    let mut params: Vec<(String, Ty)> = Vec::with_capacity(body.arg_count);
    for i in 1..=body.arg_count {
        let local = body.locals.get(i).ok_or(ReflectError::PredicateUnsupported(
            "argument local index out of range for arg_count",
        ))?;
        let name = local.name.clone().unwrap_or_else(|| format!("_{i}"));
        let resolved = resolve_datatype_backrefs(
            &resolve_adt_compaction(&local.ty, &adt_defs),
            &datatype_defs,
        );
        params.push((name, collapse_ambiguous_tys(&resolved, &ambiguous)));
    }
    let param_refs: Vec<(&str, &Ty)> = params.iter().map(|(n, t)| (n.as_str(), t)).collect();
    // Keep only preconditions whose free variables are all parameters. The
    // contract's Π binds the parameters and nothing else, so a precondition that
    // references an internal local (e.g. a discriminant constraint `_13 ∈ {0,1}`
    // that leaked into the spec) cannot be expressed in it. Dropping a hypothesis
    // only STRENGTHENS the contract (the postcondition must hold for more inputs),
    // so this is sound — a non-trivial postcondition that truly needs the dropped
    // hypothesis simply fails closed.
    // A variable is contract-expressible iff it is a parameter OR a field of one
    // (`p` or `p.field` — the latter grounds to a `Prod` projection of `p`). An
    // internal-local reference (`_13`) is neither and is dropped.
    let param_names: std::collections::HashSet<&str> =
        params.iter().map(|(n, _)| n.as_str()).collect();
    let is_param_or_field = |v: &str| {
        param_names.contains(v)
            || v.split_once('.').is_some_and(|(base, _)| param_names.contains(base))
    };
    let kept_pre: Vec<Formula> = func
        .preconditions
        .iter()
        .filter(|p| p.free_variables().iter().all(|v| is_param_or_field(v.as_str())))
        .cloned()
        .collect();
    let pre = conjoin(kept_pre);
    let post = conjoin(func.postconditions.clone());
    let ret_ty = collapse_ambiguous_tys(
        &resolve_datatype_backrefs(
            &resolve_adt_compaction(&body.return_ty, &adt_defs),
            &datatype_defs,
        ),
        &ambiguous,
    );
    reflect_contract(&param_refs, &pre, SPEC_RESULT_VAR, &ret_ty, &post)
}

/// The full variant lists of every recursive datatype DEFINED (non-empty
/// `variants`) anywhere in a function's locals or return type — the dump's own
/// recursive-type map, reconstructed from the invariant that compaction always
/// leaves the full definition at the defining occurrence. Two CONFLICTING full
/// definitions under one name (never produced by the extractor; would mean the
/// name is ambiguous) remove that name entirely — fail-closed: its
/// back-references then stay opaque rather than resolving against a definition
/// that might be the wrong one.
fn collect_datatype_defs(
    body: &trust_types::VerifiableBody,
) -> std::collections::HashMap<String, Vec<(String, Vec<(String, Ty)>)>> {
    fn walk(
        ty: &Ty,
        defs: &mut std::collections::HashMap<String, Vec<(String, Vec<(String, Ty)>)>>,
        conflicted: &mut std::collections::HashSet<String>,
    ) {
        match ty {
            Ty::Datatype { name, variants } => {
                if !variants.is_empty() {
                    match defs.get(name) {
                        Some(existing) if existing != variants => {
                            conflicted.insert(name.clone());
                        }
                        Some(_) => {}
                        None => {
                            defs.insert(name.clone(), variants.clone());
                        }
                    }
                }
                for (_, fields) in variants {
                    for (_, fty) in fields {
                        walk(fty, defs, conflicted);
                    }
                }
            }
            Ty::Ref { inner, .. } => walk(inner, defs, conflicted),
            Ty::RawPtr { pointee, .. } => walk(pointee, defs, conflicted),
            Ty::Slice { elem } | Ty::SymArray { elem, .. } | Ty::Array { elem, .. } => {
                walk(elem, defs, conflicted);
            }
            Ty::Tuple(elems) => {
                for e in elems {
                    walk(e, defs, conflicted);
                }
            }
            Ty::Adt { fields, variants, .. } => {
                for (_, fty) in fields {
                    walk(fty, defs, conflicted);
                }
                for v in variants {
                    for (_, fty) in &v.fields {
                        walk(fty, defs, conflicted);
                    }
                }
            }
            Ty::Closure { upvars, call, .. } => {
                for u in upvars {
                    walk(u, defs, conflicted);
                }
                if let Some(call) = call {
                    for param in &call.params {
                        walk(param, defs, conflicted);
                    }
                    if let Some(ret) = &call.ret {
                        walk(ret, defs, conflicted);
                    }
                }
            }
            Ty::Coroutine { upvars, .. } => {
                for u in upvars {
                    walk(u, defs, conflicted);
                }
            }
            Ty::FnDef { sig, .. } | Ty::FnPtr { sig } => {
                for p in &sig.params {
                    walk(p, defs, conflicted);
                }
                walk(&sig.ret, defs, conflicted);
            }
            // Scalars / leaves (and any future non_exhaustive variant — a variant
            // this walk does not know cannot DEFINE a datatype it would resolve).
            _ => {}
        }
    }
    let mut defs = std::collections::HashMap::new();
    let mut conflicted = std::collections::HashSet::new();
    for local in &body.locals {
        walk(&local.ty, &mut defs, &mut conflicted);
    }
    walk(&body.return_ty, &mut defs, &mut conflicted);
    for name in conflicted {
        defs.remove(&name);
    }
    defs
}

/// Rewrite `ty` with every RESOLVABLE `Ty::Datatype` by-name back-reference
/// (empty `variants`) replaced by its full definition from `defs` — the
/// pre-resolution step of [`reflect_verifiable_function`]. OCCURS-CHECKED for
/// termination and for the one-level-unrolled reflection view: while inside the
/// (substituted or defining) variant list of datatype `N`, a back-reference to
/// `N` — or to any datatype on the current expansion chain — is NOT expanded
/// again; it stays the opaque back-reference `reflect_ty` reflects as the
/// `Trust.Param.@datatype::<N>` recursion variable. Each expansion adds a
/// DISTINCT name to the chain, so recursion depth is bounded by the number of
/// distinct datatypes. An unresolvable reference is returned unchanged
/// (fail-closed downstream). Purely structural otherwise — no other `Ty` is
/// altered.
fn resolve_datatype_backrefs(
    ty: &Ty,
    defs: &std::collections::HashMap<String, Vec<(String, Vec<(String, Ty)>)>>,
) -> Ty {
    fn resolve_variants(
        name: &str,
        variants: &[(String, Vec<(String, Ty)>)],
        defs: &std::collections::HashMap<String, Vec<(String, Vec<(String, Ty)>)>>,
        chain: &mut Vec<String>,
    ) -> Ty {
        chain.push(name.to_string());
        let resolved = variants
            .iter()
            .map(|(vname, fields)| {
                (
                    vname.clone(),
                    fields
                        .iter()
                        .map(|(fname, fty)| (fname.clone(), go(fty, defs, chain)))
                        .collect(),
                )
            })
            .collect();
        chain.pop();
        Ty::Datatype { name: name.to_string(), variants: resolved }
    }
    fn go(
        ty: &Ty,
        defs: &std::collections::HashMap<String, Vec<(String, Vec<(String, Ty)>)>>,
        chain: &mut Vec<String>,
    ) -> Ty {
        match ty {
            Ty::Datatype { name, variants } => {
                if variants.is_empty() {
                    // A back-reference: substitute the full definition unless the
                    // name is already on the expansion chain (its own recursive
                    // occurrence — stays opaque) or has no definition in scope.
                    if !chain.iter().any(|n| n == name) {
                        if let Some(full) = defs.get(name) {
                            return resolve_variants(name, full, defs, chain);
                        }
                    }
                    ty.clone()
                } else {
                    // A defining occurrence: resolve inside its own fields, with
                    // its name on the chain (self-references stay opaque).
                    resolve_variants(name, variants, defs, chain)
                }
            }
            Ty::Ref { mutable, inner } => {
                Ty::Ref { mutable: *mutable, inner: Box::new(go(inner, defs, chain)) }
            }
            Ty::RawPtr { mutable, pointee } => {
                Ty::RawPtr { mutable: *mutable, pointee: Box::new(go(pointee, defs, chain)) }
            }
            Ty::Slice { elem } => Ty::Slice { elem: Box::new(go(elem, defs, chain)) },
            Ty::Array { elem, len } => {
                Ty::Array { elem: Box::new(go(elem, defs, chain)), len: *len }
            }
            Ty::SymArray { elem, len_sym } => {
                Ty::SymArray { elem: Box::new(go(elem, defs, chain)), len_sym: len_sym.clone() }
            }
            Ty::Tuple(elems) => Ty::Tuple(elems.iter().map(|e| go(e, defs, chain)).collect()),
            Ty::Adt { layout, name, fields, variants, disc_index_safe, faithful_enum_repr, enum_layout: _, adt_kind } => Ty::Adt {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(fname, fty)| (fname.clone(), go(fty, defs, chain)))
                    .collect(),
                variants: variants
                    .iter()
                    .map(|v| trust_types::VariantDef {
                        name: v.name.clone(),
                        discriminant: v.discriminant,
                        fields: v
                            .fields
                            .iter()
                            .map(|(fname, fty)| (fname.clone(), go(fty, defs, chain)))
                            .collect(),
                    })
                    .collect(),
                disc_index_safe: *disc_index_safe,
                faithful_enum_repr: *faithful_enum_repr,
                layout: layout.clone(), enum_layout: None,
                // Trust: W19 — these transforms rewrite field TYPES only; the ADT
                // kind (struct/union/enum) is a property of the DEF, carried through.
                adt_kind: *adt_kind,
            },
            Ty::Closure { name, upvars, call } => Ty::Closure {
                name: name.clone(),
                upvars: upvars.iter().map(|u| go(u, defs, chain)).collect(),
                call: call.as_ref().map(|c| {
                    Box::new(trust_types::ClosureCallSig {
                        kind: c.kind,
                        params: c.params.iter().map(|t| go(t, defs, chain)).collect(),
                        ret: c.ret.as_ref().map(|t| go(t, defs, chain)),
                    })
                }),
            },
            Ty::Coroutine { name, upvars } => Ty::Coroutine {
                name: name.clone(),
                upvars: upvars.iter().map(|u| go(u, defs, chain)).collect(),
            },
            Ty::FnDef { name, sig } => Ty::FnDef {
                name: name.clone(),
                sig: Box::new(FnSig {
                    params: sig.params.iter().map(|p| go(p, defs, chain)).collect(),
                    ret: Box::new(go(&sig.ret, defs, chain)),
                }),
            },
            Ty::FnPtr { sig } => Ty::FnPtr {
                sig: Box::new(FnSig {
                    params: sig.params.iter().map(|p| go(p, defs, chain)).collect(),
                    ret: Box::new(go(&sig.ret, defs, chain)),
                }),
            },
            // Scalars / leaves (and any future non_exhaustive variant) pass
            // through unchanged.
            _ => ty.clone(),
        }
    }
    let mut chain = Vec::new();
    go(ty, defs, &mut chain)
}

/// Trust: structural-fold rung E (Ty::Datatype grounding, attack-plan family
/// G's "3 not_grounded" item) — whether `poor` is a COMPACTED spelling of the
/// same type as `rich` under a CANONICAL-IDENTITY match (SF-2,
/// docs/design-notes/2026-07-13-adversarial-verify-findings.md): identical
/// everywhere except that some subtree of `poor` is a recursively poorer
/// spelling of the SAME canonical identity `rich` carries there. Anything
/// else — different field names/order/arity, different scalar types,
/// different variant structure — is NOT a compaction and compares
/// incomparable (fail-closed).
///
/// SF-2 FAIL-CLOSED IDENTITY RULE: the only identity a `trust-types` ADT node
/// carries is its `name` — `trust-mir-extract`'s `safe_def_path_str`, a def
/// path WITHOUT generic arguments (no def-id, no substs). Within one
/// monomorphized function the same name can therefore denote DISTINCT
/// concrete types (two instantiations of one generic ADT). A full spelling
/// pins its identity structurally (name + complete monomorphized shape), but
/// the empty-variant `Ty::Datatype` compaction leaf carries the bare name and
/// NOTHING else — the instantiation the extractor erased is unrecoverable
/// downstream, so a name-only leaf-vs-rich match would fabricate a shape the
/// occurrence never carried (the SF-2 soundness-risk channel: the kernel
/// registration/contract then describes the WRONG concrete type). Identity is
/// genuinely unavailable at the leaf, so the leaf matches NOTHING but an
/// identical leaf (the `poor == rich` fast path); occurrences that differ by
/// an erased subtree are INCOMPARABLE, drop out of the defs map, and keep the
/// pre-rung-E opaque back-reference treatment ([`ambiguous_adt_names`] /
/// [`collapse_ambiguous_tys`]). Consequence: until `trust-types` carries a
/// canonical identity that survives compaction (substs-qualified path or
/// def-id + shape digest on the back-reference), this relation coincides with
/// structural equality; the recursive arms below are retained as the intended
/// partial order so re-enabling richer matching is a leaf-arm-only change.
fn ty_is_compaction_of(poor: &Ty, rich: &Ty) -> bool {
    if poor == rich {
        return true;
    }
    match (poor, rich) {
        // SF-2: the compaction leaf (empty-variant by-name back-reference)
        // has NO canonical identity beyond a generics-erased def path —
        // FAIL CLOSED, never a name-only match (see the doc above). An
        // identical leaf on both sides is already handled by the
        // `poor == rich` fast path.
        (Ty::Datatype { variants, .. }, _) if variants.is_empty() => false,
        (
            Ty::Adt { name: pn, fields: pf, variants: pv, .. },
            Ty::Adt { name: rn, fields: rf, variants: rv, .. },
        ) => {
            pn == rn
                && pf.len() == rf.len()
                && pv.len() == rv.len()
                && pf
                    .iter()
                    .zip(rf)
                    .all(|((pfn, pft), (rfn, rft))| pfn == rfn && ty_is_compaction_of(pft, rft))
                && pv.iter().zip(rv).all(|(p, r)| {
                    p.name == r.name
                        && p.discriminant == r.discriminant
                        && p.fields.len() == r.fields.len()
                        && p.fields.iter().zip(&r.fields).all(|((pfn, pft), (rfn, rft))| {
                            pfn == rfn && ty_is_compaction_of(pft, rft)
                        })
                })
        }
        (Ty::Datatype { name: pn, variants: pv }, Ty::Datatype { name: rn, variants: rv }) => {
            pn == rn
                && pv.len() == rv.len()
                && pv.iter().zip(rv).all(|((pvn, pfs), (rvn, rfs))| {
                    pvn == rvn
                        && pfs.len() == rfs.len()
                        && pfs.iter().zip(rfs).all(|((pfn, pft), (rfn, rft))| {
                            pfn == rfn && ty_is_compaction_of(pft, rft)
                        })
                })
        }
        (Ty::Ref { mutable: pm, inner: pi }, Ty::Ref { mutable: rm, inner: ri }) => {
            pm == rm && ty_is_compaction_of(pi, ri)
        }
        (Ty::RawPtr { mutable: pm, pointee: pi }, Ty::RawPtr { mutable: rm, pointee: ri }) => {
            pm == rm && ty_is_compaction_of(pi, ri)
        }
        (Ty::Slice { elem: pe }, Ty::Slice { elem: re }) => ty_is_compaction_of(pe, re),
        (Ty::Array { elem: pe, len: pl }, Ty::Array { elem: re, len: rl }) => {
            pl == rl && ty_is_compaction_of(pe, re)
        }
        (Ty::SymArray { elem: pe, len_sym: pl }, Ty::SymArray { elem: re, len_sym: rl }) => {
            pl == rl && ty_is_compaction_of(pe, re)
        }
        (Ty::Tuple(pe), Ty::Tuple(re)) => {
            pe.len() == re.len() && pe.iter().zip(re).all(|(p, r)| ty_is_compaction_of(p, r))
        }
        (
            Ty::Closure { name: pn, upvars: pu, call: pc },
            Ty::Closure { name: rn, upvars: ru, call: rc },
        ) => {
            pn == rn
                && pu.len() == ru.len()
                && pu.iter().zip(ru).all(|(p, r)| ty_is_compaction_of(p, r))
                && match (pc, rc) {
                    (None, None) => true,
                    (Some(p), Some(r)) => {
                        p.kind == r.kind
                            && p.params.len() == r.params.len()
                            && p.params
                                .iter()
                                .zip(&r.params)
                                .all(|(p, r)| ty_is_compaction_of(p, r))
                            && match (&p.ret, &r.ret) {
                                (None, None) => true,
                                (Some(p), Some(r)) => ty_is_compaction_of(p, r),
                                _ => false,
                            }
                    }
                    _ => false,
                }
        }
        (Ty::Coroutine { name: pn, upvars: pu }, Ty::Coroutine { name: rn, upvars: ru }) => {
            pn == rn
                && pu.len() == ru.len()
                && pu.iter().zip(ru).all(|(p, r)| ty_is_compaction_of(p, r))
        }
        (Ty::FnDef { name: pn, sig: ps }, Ty::FnDef { name: rn, sig: rs }) => {
            pn == rn
                && ps.params.len() == rs.params.len()
                && ps.params.iter().zip(&rs.params).all(|(p, r)| ty_is_compaction_of(p, r))
                && ty_is_compaction_of(&ps.ret, &rs.ret)
        }
        (Ty::FnPtr { sig: ps }, Ty::FnPtr { sig: rs }) => {
            ps.params.len() == rs.params.len()
                && ps.params.iter().zip(&rs.params).all(|(p, r)| ty_is_compaction_of(p, r))
                && ty_is_compaction_of(&ps.ret, &rs.ret)
        }
        _ => false,
    }
}

/// Trust: structural-fold rung E — the RICHEST `Ty::Adt` spelling of each
/// named struct/enum reachable from a function's locals/return type, under
/// the compaction partial order ([`ty_is_compaction_of`]). The extractor's
/// depth-/size-bounded compaction renders the SAME rustc type with different
/// spellings at different occurrences (full at a shallow parameter, a field
/// compacted to a by-name back-reference deep inside another local's struct).
/// FAIL-CLOSED: two occurrences that are INCOMPARABLE under the compaction
/// order remove the name entirely — its occurrences then stay exactly as
/// dumped and [`ambiguous_adt_names`] handles them as before. SF-2: since the
/// compaction leaf carries no canonical identity, [`ty_is_compaction_of`]
/// currently coincides with structural equality, so compaction-differing
/// occurrences land in the fail-closed (conflicted → removed) path too — the
/// map keeps only names whose reachable spellings agree EXACTLY, and the
/// one-name-one-shape reconstruction resumes once the back-reference carries
/// identity (see [`ty_is_compaction_of`]'s SF-2 doc).
pub(crate) fn collect_adt_compaction_defs(
    body: &trust_types::VerifiableBody,
) -> std::collections::HashMap<String, Ty> {
    fn walk(
        ty: &Ty,
        defs: &mut std::collections::HashMap<String, Ty>,
        conflicted: &mut std::collections::HashSet<String>,
    ) {
        if let Ty::Adt { name, .. } = ty {
            match defs.get(name) {
                Some(best) if ty_is_compaction_of(ty, best) => {}
                Some(best) if ty_is_compaction_of(best, ty) => {
                    defs.insert(name.clone(), ty.clone());
                }
                Some(_) => {
                    conflicted.insert(name.clone());
                }
                None => {
                    defs.insert(name.clone(), ty.clone());
                }
            }
        }
        match ty {
            Ty::Adt { fields, variants, .. } => {
                for (_, fty) in fields {
                    walk(fty, defs, conflicted);
                }
                for v in variants {
                    for (_, fty) in &v.fields {
                        walk(fty, defs, conflicted);
                    }
                }
            }
            Ty::Datatype { variants, .. } => {
                for (_, fields) in variants {
                    for (_, fty) in fields {
                        walk(fty, defs, conflicted);
                    }
                }
            }
            Ty::Ref { inner, .. } => walk(inner, defs, conflicted),
            Ty::RawPtr { pointee, .. } => walk(pointee, defs, conflicted),
            Ty::Slice { elem } | Ty::SymArray { elem, .. } | Ty::Array { elem, .. } => {
                walk(elem, defs, conflicted);
            }
            Ty::Tuple(elems) => {
                for e in elems {
                    walk(e, defs, conflicted);
                }
            }
            Ty::Closure { upvars, call, .. } => {
                for u in upvars {
                    walk(u, defs, conflicted);
                }
                if let Some(call) = call {
                    for param in &call.params {
                        walk(param, defs, conflicted);
                    }
                    if let Some(ret) = &call.ret {
                        walk(ret, defs, conflicted);
                    }
                }
            }
            Ty::Coroutine { upvars, .. } => {
                for u in upvars {
                    walk(u, defs, conflicted);
                }
            }
            Ty::FnDef { sig, .. } | Ty::FnPtr { sig } => {
                for p in &sig.params {
                    walk(p, defs, conflicted);
                }
                walk(&sig.ret, defs, conflicted);
            }
            _ => {}
        }
    }
    let mut defs = std::collections::HashMap::new();
    let mut conflicted = std::collections::HashSet::new();
    for local in &body.locals {
        walk(&local.ty, &mut defs, &mut conflicted);
    }
    walk(&body.return_ty, &mut defs, &mut conflicted);
    for name in conflicted {
        defs.remove(&name);
    }
    defs
}

/// Trust: structural-fold rung E — recursively walk `ty` and rewrite a named
/// `Ty::Adt` only when [`ty_is_compaction_of`] proves it is a strictly poorer
/// spelling of the exact definition in `defs`. SF-2 deliberately makes that
/// relation coincide with structural equality until a canonical identity
/// survives compaction; together with the `ty != rich` check, no replacement
/// is currently authorized. The complete traversal and nominal-resolution
/// chain are retained as future-proof partial-order machinery: if an
/// identity-bearing leaf is introduced, nested replacements are recursively
/// normalized without cycling through mutually recursive definitions.
/// Empty-variant `Ty::Datatype` back-references are never rewritten here; full
/// `Ty::Datatype` definition/back-reference resolution remains the separate,
/// occurs-checked [`resolve_datatype_backrefs`] lane.
pub(crate) fn resolve_adt_compaction(ty: &Ty, defs: &std::collections::HashMap<String, Ty>) -> Ty {
    fn go(ty: &Ty, defs: &std::collections::HashMap<String, Ty>, chain: &mut Vec<String>) -> Ty {
        if let Ty::Adt { name, .. } = ty {
            if let Some(rich) = defs.get(name) {
                if ty != rich && !chain.contains(name) && ty_is_compaction_of(ty, rich) {
                    chain.push(name.clone());
                    let resolved = go(rich, defs, chain);
                    chain.pop();
                    return resolved;
                }
            }
        }
        match ty {
            Ty::Adt { layout, name, fields, variants, disc_index_safe, faithful_enum_repr, enum_layout: _, adt_kind } => Ty::Adt {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(fname, fty)| (fname.clone(), go(fty, defs, chain)))
                    .collect(),
                variants: variants
                    .iter()
                    .map(|v| trust_types::VariantDef {
                        name: v.name.clone(),
                        discriminant: v.discriminant,
                        fields: v
                            .fields
                            .iter()
                            .map(|(fname, fty)| (fname.clone(), go(fty, defs, chain)))
                            .collect(),
                    })
                    .collect(),
                disc_index_safe: *disc_index_safe,
                faithful_enum_repr: *faithful_enum_repr,
                layout: layout.clone(), enum_layout: None,
                // Trust: W19 — these transforms rewrite field TYPES only; the ADT
                // kind (struct/union/enum) is a property of the DEF, carried through.
                adt_kind: *adt_kind,
            },
            Ty::Ref { mutable, inner } => {
                Ty::Ref { mutable: *mutable, inner: Box::new(go(inner, defs, chain)) }
            }
            Ty::RawPtr { mutable, pointee } => {
                Ty::RawPtr { mutable: *mutable, pointee: Box::new(go(pointee, defs, chain)) }
            }
            Ty::Slice { elem } => Ty::Slice { elem: Box::new(go(elem, defs, chain)) },
            Ty::Array { elem, len } => {
                Ty::Array { elem: Box::new(go(elem, defs, chain)), len: *len }
            }
            Ty::SymArray { elem, len_sym } => {
                Ty::SymArray { elem: Box::new(go(elem, defs, chain)), len_sym: len_sym.clone() }
            }
            Ty::Tuple(elems) => Ty::Tuple(elems.iter().map(|e| go(e, defs, chain)).collect()),
            Ty::Datatype { name, variants } if !variants.is_empty() => Ty::Datatype {
                name: name.clone(),
                variants: variants
                    .iter()
                    .map(|(variant, fields)| {
                        (
                            variant.clone(),
                            fields
                                .iter()
                                .map(|(field, ty)| (field.clone(), go(ty, defs, chain)))
                                .collect(),
                        )
                    })
                    .collect(),
            },
            Ty::Closure { name, upvars, call } => Ty::Closure {
                name: name.clone(),
                upvars: upvars.iter().map(|ty| go(ty, defs, chain)).collect(),
                call: call.as_ref().map(|call| {
                    Box::new(trust_types::ClosureCallSig {
                        kind: call.kind,
                        params: call.params.iter().map(|ty| go(ty, defs, chain)).collect(),
                        ret: call.ret.as_ref().map(|ty| go(ty, defs, chain)),
                    })
                }),
            },
            Ty::Coroutine { name, upvars } => Ty::Coroutine {
                name: name.clone(),
                upvars: upvars.iter().map(|ty| go(ty, defs, chain)).collect(),
            },
            Ty::FnDef { name, sig } => Ty::FnDef {
                name: name.clone(),
                sig: Box::new(FnSig {
                    params: sig.params.iter().map(|ty| go(ty, defs, chain)).collect(),
                    ret: Box::new(go(&sig.ret, defs, chain)),
                }),
            },
            Ty::FnPtr { sig } => Ty::FnPtr {
                sig: Box::new(FnSig {
                    params: sig.params.iter().map(|ty| go(ty, defs, chain)).collect(),
                    ret: Box::new(go(&sig.ret, defs, chain)),
                }),
            },
            // Empty Datatype views are recursion variables and every scalar /
            // leaf passes through unchanged. Named ADT replacements are the
            // only authority-producing rewrite.
            _ => ty.clone(),
        }
    }

    go(ty, defs, &mut Vec::new())
}

/// Trust: structural-fold rung E — apply the shared, fail-closed compaction
/// pre-pass consulted by [`ambiguous_adt_names`],
/// [`reflect_verifiable_function`], and `clean_ground`. Under SF-2 this walks
/// every supported type position but leaves identity-erased compaction
/// mismatches unchanged so the ambiguity lane can collapse them opaquely.
#[must_use]
pub fn canonicalize_compacted_ty(ty: &Ty, body: &trust_types::VerifiableBody) -> Ty {
    resolve_adt_compaction(ty, &collect_adt_compaction_defs(body))
}

/// Named `Ty::Adt`/`Ty::Datatype` carriers whose STRUCTURAL SHAPE (the
/// [`AdtCarrier`] [`reflect_struct`]/[`reflect_enum`] compute) DISAGREES across
/// different occurrences reachable from one function's locals/return type —
/// i.e. a name for which the `AdtCarrier` is NOT a pure function of the name
/// within this function (M6 rung-5 successor item 1, "PI-ARITY").
///
/// This happens because `trust-mir-extract`'s recursive-type compaction
/// (`compact_oversized_field` / the generic recursive-struct back-edge, AND
/// the Lever-A name-gated `Level`/`Expr`/`ExprKind` datatype lowering) is
/// DEPTH- and SIZE-BOUNDED, not name-canonical: the SAME named struct/enum can
/// have SOME of its own descendant fields compacted to an opaque by-name
/// `Ty::Datatype` back-reference at one occurrence (reached deep inside an
/// already-recursing parent, or once a subtree exceeds the size cap) while the
/// SAME descendant is fully inlined at a SHALLOWER occurrence (e.g. a direct
/// parameter's own declared type). Two occurrences of "the same name" can
/// therefore reflect to `AdtCarrier`s with DIFFERENT `type_params` — different
/// arity, different order, or both.
///
/// `reflect_verifiable_function`'s contract construction and
/// `clean_ground::reachable_adt_carriers`'s kernel registration each compute
/// an `AdtCarrier` for a named type FROM WHICHEVER OCCURRENCE THEY HAPPEN TO
/// CONSULT — the CONTRACT from the specific parameter/return type, the
/// registration from a first-wins scan over ALL locals. When a name is
/// ambiguous, these two computations can disagree, so the CONTRACT applies a
/// DIFFERENT number of type arguments than the REGISTERED kernel inductive
/// declares — an arity mismatch the real kernel's `check_type` correctly
/// rejects (`NotAFunction`: applying a further argument to an
/// already-fully-applied `Trust.Adt.<name> : Type -> … -> Type`). Confirmed
/// against the real M6 census dumps (`FoldMemo::get`: `Trust.Adt.expr_Expr`
/// registers with ONE `type_params` entry from one local's shape but the
/// `expr` parameter's own occurrence computes FIVE) — see
/// `reports/m6-datatype-reflect-validate-2026-07-10.md`'s successor item 1.
/// `reflect_contract`'s Pi-binding order is (and remains) correct for any
/// number of DISTINCT, CONSISTENTLY-shaped type variables; the bug is this
/// occurrence-dependent shape INCONSISTENCY, not a binder-order defect.
///
/// [`collapse_ambiguous_tys`] routes every occurrence of an ambiguous name to
/// the SAME opaque, Pi-bound `Trust.Param.@datatype::<name>` treatment an
/// unresolvable `Ty::Datatype` back-reference already gets — sound (a
/// strictly WEAKER, structureless over-approximation, never a false
/// certificate), and it keeps BOTH the contract and the kernel registration
/// off the mismatched named-inductive path for that name, so they can no
/// longer disagree.
#[must_use]
pub fn ambiguous_adt_names(func: &VerifiableFunction) -> std::collections::HashSet<String> {
    // Compute the `AdtCarrier` for a `Ty::Adt` node (or the `Ty::Adt` VIEW of a
    // FULL, non-empty `Ty::Datatype` — [`datatype_equivalent_adt`] is the same
    // bridge `reflect_ty`'s own `Ty::Datatype` arm uses, so a full datatype
    // definition compares under the SAME sanitized inductive name
    // (`Trust.Adt.<name>`) a plain `Ty::Adt` of the same source name would),
    // and record a shape disagreement keyed by that name.
    fn record(
        carrier_ty: &Ty,
        seen: &mut std::collections::HashMap<String, AdtCarrier>,
        ambiguous: &mut std::collections::HashSet<String>,
    ) {
        if let Some(carrier) = reflect_struct(carrier_ty) {
            match seen.get(&carrier.name) {
                Some(existing) if existing != &carrier => {
                    ambiguous.insert(carrier.name.clone());
                }
                Some(_) => {}
                None => {
                    seen.insert(carrier.name.clone(), carrier);
                }
            }
        }
    }
    fn walk(
        ty: &Ty,
        seen: &mut std::collections::HashMap<String, AdtCarrier>,
        ambiguous: &mut std::collections::HashSet<String>,
    ) {
        match ty {
            Ty::Adt { fields, variants, .. } => {
                record(ty, seen, ambiguous);
                for (_, fty) in fields {
                    walk(fty, seen, ambiguous);
                }
                for v in variants {
                    for (_, fty) in &v.fields {
                        walk(fty, seen, ambiguous);
                    }
                }
            }
            Ty::Datatype { name, variants } => {
                if !variants.is_empty() {
                    record(&datatype_equivalent_adt(name, variants), seen, ambiguous);
                }
                for (_, fields) in variants {
                    for (_, fty) in fields {
                        walk(fty, seen, ambiguous);
                    }
                }
            }
            Ty::Ref { inner, .. } => walk(inner, seen, ambiguous),
            Ty::RawPtr { pointee, .. } => walk(pointee, seen, ambiguous),
            Ty::Slice { elem } | Ty::SymArray { elem, .. } | Ty::Array { elem, .. } => {
                walk(elem, seen, ambiguous);
            }
            Ty::Tuple(elems) => {
                for e in elems {
                    walk(e, seen, ambiguous);
                }
            }
            Ty::Closure { upvars, call, .. } => {
                for u in upvars {
                    walk(u, seen, ambiguous);
                }
                if let Some(call) = call {
                    for param in &call.params {
                        walk(param, seen, ambiguous);
                    }
                    if let Some(ret) = &call.ret {
                        walk(ret, seen, ambiguous);
                    }
                }
            }
            Ty::Coroutine { upvars, .. } => {
                for u in upvars {
                    walk(u, seen, ambiguous);
                }
            }
            Ty::FnDef { sig, .. } | Ty::FnPtr { sig } => {
                for p in &sig.params {
                    walk(p, seen, ambiguous);
                }
                walk(&sig.ret, seen, ambiguous);
            }
            // Scalars / leaves (and any future non_exhaustive variant) carry no
            // named ADT of their own.
            _ => {}
        }
    }
    let mut seen = std::collections::HashMap::new();
    let mut ambiguous = std::collections::HashSet::new();
    // Trust: structural-fold rung E — run the compaction pre-pass FIRST
    // ([`collect_adt_compaction_defs`]/[`resolve_adt_compaction`]). SF-2: an
    // empty compaction leaf carries no canonical identity, so it never
    // name-matches a fuller spelling. Such occurrences are incomparable,
    // keep no def, and land here like any genuine shape disagreement
    // (fail-closed collapse). Only exactly agreeing reachable spellings stay
    // on the named-inductive path.
    let defs = collect_adt_compaction_defs(&func.body);
    for local in &func.body.locals {
        walk(&resolve_adt_compaction(&local.ty, &defs), &mut seen, &mut ambiguous);
    }
    walk(&resolve_adt_compaction(&func.body.return_ty, &defs), &mut seen, &mut ambiguous);
    ambiguous
}

/// Rewrite every occurrence of an AMBIGUOUS (see [`ambiguous_adt_names`])
/// named `Ty::Adt`/`Ty::Datatype` node in `ty` to the opaque, empty-variant
/// by-name back-reference `Ty::Datatype { name, variants: [] }` — the SAME
/// spelling an unresolvable recursive-datatype back-reference already uses,
/// so it reflects at the existing opaque Pi-bound type variable
/// (`bare_type_var` / [`datatype_backref_const_name`]), never at a named
/// inductive whose arity might disagree between the contract and the kernel
/// registration. A non-ambiguous node's OWN structure is left completely
/// unchanged (only a node whose OWN name is ambiguous is rewritten; a
/// non-ambiguous parent that merely CONTAINS an ambiguous nested field keeps
/// its other fields exactly as before — the collapse is local to the
/// ambiguous subtree). Purely structural — no other `Ty` is altered.
#[must_use]
pub fn collapse_ambiguous_tys(ty: &Ty, ambiguous: &std::collections::HashSet<String>) -> Ty {
    match ty {
        // `ambiguous` is keyed by the SANITIZED Clean inductive name
        // (`Trust.Adt.<name>`, [`ambiguous_adt_names`]'s `AdtCarrier::name`),
        // not the raw Rust def-path `Ty::Adt`/`Ty::Datatype` carry — convert
        // before comparing ([`adt_inductive_name`] is the same sanitizer
        // `reflect_struct`/`datatype_equivalent_adt` use to name the carrier).
        Ty::Adt { name, .. } | Ty::Datatype { name, .. }
            if ambiguous.contains(&adt_inductive_name(name)) =>
        {
            Ty::Datatype { name: name.clone(), variants: Vec::new() }
        }
        Ty::Adt { layout, name, fields, variants, disc_index_safe, faithful_enum_repr, enum_layout: _, adt_kind } => Ty::Adt {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(fname, fty)| (fname.clone(), collapse_ambiguous_tys(fty, ambiguous)))
                .collect(),
            variants: variants
                .iter()
                .map(|v| trust_types::VariantDef {
                    name: v.name.clone(),
                    discriminant: v.discriminant,
                    fields: v
                        .fields
                        .iter()
                        .map(|(fname, fty)| (fname.clone(), collapse_ambiguous_tys(fty, ambiguous)))
                        .collect(),
                })
                .collect(),
            disc_index_safe: *disc_index_safe,
            faithful_enum_repr: *faithful_enum_repr,
                layout: layout.clone(), enum_layout: None,
                // Trust: W19 — field-type rewrite only; ADT kind carried through.
                adt_kind: *adt_kind,
        },
        Ty::Datatype { name, variants } => Ty::Datatype {
            name: name.clone(),
            variants: variants
                .iter()
                .map(|(vname, fields)| {
                    (
                        vname.clone(),
                        fields
                            .iter()
                            .map(|(fname, fty)| {
                                (fname.clone(), collapse_ambiguous_tys(fty, ambiguous))
                            })
                            .collect(),
                    )
                })
                .collect(),
        },
        Ty::Ref { mutable, inner } => {
            Ty::Ref { mutable: *mutable, inner: Box::new(collapse_ambiguous_tys(inner, ambiguous)) }
        }
        Ty::RawPtr { mutable, pointee } => Ty::RawPtr {
            mutable: *mutable,
            pointee: Box::new(collapse_ambiguous_tys(pointee, ambiguous)),
        },
        Ty::Slice { elem } => Ty::Slice { elem: Box::new(collapse_ambiguous_tys(elem, ambiguous)) },
        Ty::Array { elem, len } => {
            Ty::Array { elem: Box::new(collapse_ambiguous_tys(elem, ambiguous)), len: *len }
        }
        Ty::SymArray { elem, len_sym } => Ty::SymArray {
            elem: Box::new(collapse_ambiguous_tys(elem, ambiguous)),
            len_sym: len_sym.clone(),
        },
        Ty::Tuple(elems) => {
            Ty::Tuple(elems.iter().map(|e| collapse_ambiguous_tys(e, ambiguous)).collect())
        }
        Ty::Closure { name, upvars, call } => Ty::Closure {
            name: name.clone(),
            upvars: upvars.iter().map(|u| collapse_ambiguous_tys(u, ambiguous)).collect(),
            call: call.as_ref().map(|c| {
                Box::new(trust_types::ClosureCallSig {
                    kind: c.kind,
                    params: c.params.iter().map(|t| collapse_ambiguous_tys(t, ambiguous)).collect(),
                    ret: c.ret.as_ref().map(|t| collapse_ambiguous_tys(t, ambiguous)),
                })
            }),
        },
        Ty::Coroutine { name, upvars } => Ty::Coroutine {
            name: name.clone(),
            upvars: upvars.iter().map(|u| collapse_ambiguous_tys(u, ambiguous)).collect(),
        },
        Ty::FnDef { name, sig } => Ty::FnDef {
            name: name.clone(),
            sig: Box::new(FnSig {
                params: sig.params.iter().map(|p| collapse_ambiguous_tys(p, ambiguous)).collect(),
                ret: Box::new(collapse_ambiguous_tys(&sig.ret, ambiguous)),
            }),
        },
        Ty::FnPtr { sig } => Ty::FnPtr {
            sig: Box::new(FnSig {
                params: sig.params.iter().map(|p| collapse_ambiguous_tys(p, ambiguous)).collect(),
                ret: Box::new(collapse_ambiguous_tys(&sig.ret, ambiguous)),
            }),
        },
        // Scalars / leaves (and any future non_exhaustive variant) pass through
        // unchanged.
        _ => ty.clone(),
    }
}

/// Conjoin a clause list into one `Formula` (`[] -> true`, `[f] -> f`).
fn conjoin(mut clauses: Vec<Formula>) -> Formula {
    match clauses.len() {
        0 => Formula::Bool(true),
        1 => clauses.pop().expect("len checked"),
        _ => Formula::And(clauses),
    }
}

// ---------------------------------------------------------------------------
// EXPANDED TRUST TYPES — the verification types Trust adds BEYOND Rust, as
// genuine Clean DEPENDENT types modulo 3. These are NOT `trust_types::Ty`
// constructors (the Rust ADTs are already covered by `reflect_ty`); they are the
// dependent/refinement/spec types Trust layers onto the type system to carry a
// proof obligation IN the type:
//
//   * REFINEMENT (liquid) type `{v : T | φ}` — Trust's `#[refine("φ")]`
//     (`ContractKind::TypeRefinement`), whose IR is `TypeRefinementContract {
//     variable, predicate, expr }` (a value-constraining predicate bound to a
//     named variable). It reflects to the dependent SUBSET / Σ-with-proof
//     `Σ(v : R(T)), Proof(φ v)`. This is EXACTLY the prelude `Subtype (decode T)
//     (λ v. ⟦φ⟧)` the contract Sigma already grounds to (`to_clean_expr`'s
//     `CARRIER_SIGMA` arm) — a real dependent type rooted in the 3 (the prelude
//     `Subtype` structure rests on only the foundational axioms; `axiom_deps`
//     EMPTY — NO 4th axiom).
//   * SPEC'd dependent FUNCTION `fn(x:T) requires{pre(x)} -> {r:U | post(x,r)}` —
//     the dependent `Π(x : R(T)), Proof(pre x) → Σ(r : R(U)), Proof(post x r)`
//     that `reflect_contract` / `reflect_function_spec` already build (the
//     Curry-Howard close): a function inhabiting this type IS a proof of the
//     contract. `reflect_spec_function` is the named entry point that surfaces
//     this as a first-class VERIFICATION type from a base type + bound var + the
//     pre/post predicates.
//   * TYPE INVARIANT `#[invariant("φ")]` on a value — a value of `T` that ALWAYS
//     satisfies `φ` is, AS A TYPE, the refinement `{v : T | φ}`. So an
//     invariant-carrying type reflects through the SAME `reflect_refinement`
//     subset carrier (the invariant is the refinement predicate). The distinction
//     is provenance (`#[invariant]` vs `#[refine]`), not type structure.
// ---------------------------------------------------------------------------

/// REFINEMENT / LIQUID type `{v : T | φ}` → the dependent SUBSET / Σ-with-proof
/// `Σ(v : R(T)), Proof(⟦φ⟧ v)`, a REAL Clean dependent type modulo 3.
///
/// The carrier is `Trust.Sigma R(T) (λ v : R(T). ⟦φ⟧[v])` — the SAME
/// `CARRIER_SIGMA` the postcondition dependent pair uses, which
/// [`to_clean_expr`](crate::clean_ground::to_clean_expr) grounds to the prelude
/// `Subtype (decode T) (λ v. ⟦φ⟧)` (the dependent subset type `{v : T // φ v}`).
/// `Subtype` is a prelude `structure` resting on only the 3 foundational axioms,
/// so a refinement type's `axiom_deps` is EMPTY — NO 4th axiom. A value of the
/// refinement type IS a pair (a witness `v : T` together with a proof `φ v`).
///
/// The predicate `φ` is a [`Formula`] over the bound variable `var` (and any
/// outer free variables, which become free `Const`s). It is reflected via
/// [`reflect_formula`] and `var` is abstracted into the Σ binder via de-Bruijn
/// (`abstract_const`), exactly as `reflect_contract` abstracts the return var into
/// the postcondition Σ.
///
/// `var` binds at [`carrier_binding_type`] (integers at `Trust.Int` so the integer
/// predicate vocabulary applies; other reflectable types opaquely through
/// `Trust.El`). Passing `None` for the opaque-param over-approximation means a
/// composite-with-nested-type-var base FAILS CLOSED here — a refinement over an
/// uninhabitable opaque carrier is not a faithful subset (you cannot conjure the
/// witness `v`), so a quantified Σ over a real carrier beats an opaque free const.
///
/// # Errors
///
/// Returns [`ReflectError`] if the base type `T` is non-reflectable (or nests an
/// opaque type variable — fails closed, like a contract RETURN), or if the
/// predicate `φ` is outside the [`reflect_formula`] subset.
pub fn reflect_refinement(
    var: &str,
    base_ty: &Ty,
    predicate: &Formula,
) -> Result<ProofTerm, ReflectError> {
    // The witness carrier `R(T)` — the type the refinement's bound value ranges
    // over. RETURN-position binding (`None`): a composite that nests an opaque type
    // variable is uninhabitable as a subset witness, so it fails closed (a quantified
    // Σ over a real carrier beats an opaque free const).
    let base_carrier = carrier_binding_type(base_ty, None)?;
    // ⟦φ⟧ with `var` abstracted to de-Bruijn `Var 0` under the λ binder.
    let pred = reflect_formula(predicate)?;
    let pred_lam = ProofTerm::Lambda {
        binder_name: var.to_string(),
        binder_type: Box::new(base_carrier.clone()),
        body: Box::new(abstract_const(&pred, var, 0)),
    };
    // `Trust.Sigma R(T) (λ v. ⟦φ⟧)` — grounds to `Subtype (decode T) (λ v. φ)`.
    Ok(app(app(cst(CARRIER_SIGMA), base_carrier), pred_lam))
}

/// Reflect a Trust [`TypeRefinementContract`] (the `#[refine("φ")]` IR — a
/// `(variable, predicate)` pairing) over its declared base type `base_ty` into the
/// dependent refinement-subset carrier, via [`reflect_refinement`]. This is the
/// wiring point from the compiler's refinement-annotation IR to the Clean
/// dependent subset type: a `#[refine]`-annotated binding becomes the genuine
/// dependent type `{v : T | φ}`.
///
/// # Errors
///
/// As [`reflect_refinement`].
pub fn reflect_refinement_contract(
    base_ty: &Ty,
    contract: &TypeRefinementContract,
) -> Result<ProofTerm, ReflectError> {
    reflect_refinement(&contract.variable, base_ty, &contract.predicate)
}

/// A TYPE INVARIANT `#[invariant("φ")]` carried by a value of type `T` is, as a
/// TYPE, the refinement `{v : T | φ}` — the value always satisfies `φ`. So it
/// reflects through the SAME dependent SUBSET carrier as [`reflect_refinement`]
/// (the invariant predicate IS the refinement predicate). Distinct entry point so
/// the verification-types corpus can record the `#[invariant]` provenance, but the
/// carrier — and its modulo-3 grounding — is identical.
///
/// # Errors
///
/// As [`reflect_refinement`]: the base type must be reflectable and `φ` in the
/// predicate subset.
pub fn reflect_invariant_type(
    var: &str,
    base_ty: &Ty,
    invariant: &Formula,
) -> Result<ProofTerm, ReflectError> {
    reflect_refinement(var, base_ty, invariant)
}

/// A SPEC'd dependent FUNCTION `fn(x : T) requires{pre(x)} -> {r : U | post(x,r)}`
/// as a first-class VERIFICATION type — the dependent
/// `Π(x : R(T)), Proof(pre x) → Σ(r : R(U)), Proof(post x r)`. This is the
/// Curry-Howard close: a function inhabiting this type IS a proof of the contract.
///
/// A thin named surface over [`reflect_contract`] (the existing dependent-contract
/// builder): it takes the SINGLE bound argument `(arg_name, arg_ty)`, the
/// precondition `pre` over `arg_name`, and the refined RETURN `{ret_name : ret_ty |
/// post}` (its predicate `post` over `arg_name` and `ret_name`). The result is the
/// SAME `Π … → Σ …` carrier `reflect_contract` builds, which grounds modulo 3
/// (the kernel `Pi` is primitive; the return `Σ` is the prelude `Subtype`).
///
/// # Errors
///
/// Returns [`ReflectError`] if a type is non-reflectable or a predicate is outside
/// the [`reflect_formula`] subset.
pub fn reflect_spec_function(
    arg_name: &str,
    arg_ty: &Ty,
    pre: &Formula,
    ret_name: &str,
    ret_ty: &Ty,
    post: &Formula,
) -> Result<ProofTerm, ReflectError> {
    reflect_contract(&[(arg_name, arg_ty)], pre, ret_name, ret_ty, post)
}

// ---------------------------------------------------------------------------
// Kernel carrier context
// ---------------------------------------------------------------------------

/// Build a `KernelContext` pre-populated with exactly the carrier constants that
/// `reflect_sort`/`reflect_ty` can emit, so reflected terms resolve under
/// `infer_type` / `check_proof`.
///
/// Declares (all as axioms):
/// ```text
///   Trust.SortTy      : Sort 1
///   Trust.Nat         : Sort 1
///   Trust.Sort.Bool   : Trust.SortTy
///   Trust.Sort.Int    : Trust.SortTy
///   Trust.Sort.Unit   : Trust.SortTy
///   Trust.Sort.BitVec : Trust.Nat -> Trust.SortTy
///   Trust.Sort.Prod   : Trust.SortTy -> Trust.SortTy -> Trust.SortTy
///   Trust.Sort.Vec    : Trust.SortTy -> Trust.Nat -> Trust.SortTy
///   Trust.Sort.Slice  : Trust.SortTy -> Trust.SortTy
///   "0" .. "128"      : Trust.Nat
/// ```
///
/// # Panics
///
/// Panics only on a programmer error (a duplicate carrier name among the
/// compile-time-constant names), never on runtime input.
#[must_use]
pub fn carrier_context() -> KernelContext {
    let mut ctx = KernelContext::new();
    let sort_ty = || cst(CARRIER_SORT_TY);
    let nat_u = || cst(CARRIER_NAT);
    let arrow = |domain: ProofTerm, codomain: ProofTerm| ProofTerm::Pi {
        binder_name: "_".to_string(),
        domain: Box::new(domain),
        codomain: Box::new(codomain),
    };

    ctx.add_axiom(CARRIER_SORT_TY, ProofTerm::Sort(1)).expect("SortTy");
    ctx.add_axiom(CARRIER_NAT, ProofTerm::Sort(1)).expect("Nat");
    ctx.add_axiom(CARRIER_BOOL, sort_ty()).expect("Bool carrier");
    ctx.add_axiom(CARRIER_INT, sort_ty()).expect("Int carrier");
    // COVERAGE-AGENDA #2 — the bare-raw-pointer SortTy code (`Trust.Sort.Ptr`), a
    // nullary carrier like `Int`/`Bool`. It DECODES (`decode_el_code`) to the
    // registered `Trust.Ptr` inductive; here it is only declared as a `Trust.SortTy`
    // code so a reflected bare-pointer carrier type-checks against `carrier_context`.
    ctx.add_axiom(CARRIER_PTR, sort_ty()).expect("Ptr carrier");
    // COVERAGE-AGENDA #4 — the nested-`dyn` writer-sink SortTy code (`Trust.Sort.Sink`),
    // a nullary carrier like `Int`/`Bool`/`Ptr`. It DECODES (`decode_el_code`) to the
    // registered nullary opaque inductive `Trust.Sink`; here it is only declared as a
    // `Trust.SortTy` code so a reflected `Formatter`-with-`buf:dyn-Write` carrier
    // type-checks against `carrier_context` (the local predicative checker).
    ctx.add_axiom(CARRIER_SINK, sort_ty()).expect("Sink carrier");
    ctx.add_axiom(CARRIER_UNIT, sort_ty()).expect("Unit carrier");
    ctx.add_axiom(CARRIER_BITVEC, arrow(nat_u(), sort_ty())).expect("BitVec carrier");
    ctx.add_axiom(CARRIER_PROD, arrow(sort_ty(), arrow(sort_ty(), sort_ty())))
        .expect("Prod carrier");
    ctx.add_axiom(CARRIER_VEC, arrow(sort_ty(), arrow(nat_u(), sort_ty()))).expect("Vec carrier");
    ctx.add_axiom(CARRIER_SLICE, arrow(sort_ty(), sort_ty())).expect("Slice carrier");
    ctx.add_axiom(CARRIER_FN, arrow(sort_ty(), arrow(sort_ty(), sort_ty()))).expect("Fn carrier");
    for n in 0..=MAX_DECLARED_NAT {
        ctx.add_axiom(&n.to_string(), nat_u()).expect("nat numeral");
    }

    // M3 predicate vocabulary: propositions live in Prop = Sort(0); integer
    // operands live in the Trust.Int universe.
    let prop = || ProofTerm::Sort(0);
    let int_u = || cst(PROP_INT);
    ctx.add_axiom(PROP_INT, ProofTerm::Sort(1)).expect("Int universe");
    ctx.add_axiom(PROP_TRUE, prop()).expect("True");
    ctx.add_axiom(PROP_FALSE, prop()).expect("False");
    ctx.add_axiom(PROP_NOT, arrow(prop(), prop())).expect("Not");
    for connective in [PROP_AND, PROP_OR, PROP_IMPLIES] {
        ctx.add_axiom(connective, arrow(prop(), arrow(prop(), prop()))).expect("connective");
    }
    for cmp in [PROP_EQ, PROP_LT, PROP_LE, PROP_GT, PROP_GE] {
        ctx.add_axiom(cmp, arrow(int_u(), arrow(int_u(), prop()))).expect("comparison");
    }
    for binop in [INT_ADD, INT_SUB, INT_MUL, INT_DIV, INT_REM] {
        ctx.add_axiom(binop, arrow(int_u(), arrow(int_u(), int_u()))).expect("int binop");
    }
    ctx.add_axiom(INT_NEG, arrow(int_u(), int_u())).expect("int neg");
    for n in DECLARED_INT_LITS {
        ctx.add_axiom(&int_lit_name(*n), int_u()).expect("int literal");
    }

    // M3 generalization: Tarski decode  Trust.El : Trust.SortTy -> Type.
    ctx.add_axiom(CARRIER_EL, arrow(sort_ty(), ProofTerm::Sort(1))).expect("El decode");

    // M3 step 2: dependent-pair carrier  Trust.Sigma : Π(A:Type) → (A → Prop) → Type.
    ctx.add_axiom(
        CARRIER_SIGMA,
        ProofTerm::Pi {
            binder_name: "A".to_string(),
            domain: Box::new(ProofTerm::Sort(1)),
            codomain: Box::new(ProofTerm::Pi {
                binder_name: "_".to_string(),
                // A → Prop, where A is the outer binder (Var 0 at this depth).
                domain: Box::new(arrow(ProofTerm::Var(0), prop())),
                codomain: Box::new(ProofTerm::Sort(1)),
            }),
        },
    )
    .expect("Sigma carrier");
    ctx
}

// ===========================================================================
// GOAL-ITEM 3 — FAITHFUL DISPATCH (trait methods / generics / closures).
//
// The base type-reflection above lifts `dyn Trait` to a Sigma existential, a
// generic param to a Pi-bound opaque `Type` var, and a closure to a record
// `{ env, call }`. Those are faithful TYPES but the *behavior* stayed deferred:
// a trait-method CALL denoted an opaque witness, a generic instantiation kept
// the bare Pi opaque, and a closure's `call` was an abstract `A → B` never
// applied to its captured env.
//
// This section adds the BEHAVIORAL reflections as pure-data `ProofTerm`/carrier
// descriptions (no `clean_kernel` dependency — `clean_ground` grounds them in
// the real kernel and asserts modulo 3):
//
//   1. STATIC (monomorphized) trait dispatch: a call to a trait method at a
//      KNOWN concrete impl reflects to the concrete IMPL BODY — the call site's
//      denotation is DEFINITIONALLY that impl's body (a real Clean `def`), NOT
//      an opaque. A wrong impl (different body const) is not def-eq → rejected.
//   2. GENERIC monomorphization: substitute a generic body's `Trust.Param.<id>`
//      carrier with a concrete type's carrier, yielding the MONOMORPHIZED body
//      — not the Pi-bound opaque.
//   3. CLOSURE with its REAL env: the `call` applied to the captured `env`
//      record — `dispatch : Closure → A → B := λ c a. body (env c) a`.
//
// FAIL-CLOSED: an unresolved impl / a non-reflectable body / a param carrier
// absent from the body yields `None`; the caller then falls back to the sound
// opaque/modular path — never a wrong dispatch and never a 4th axiom.
// ===========================================================================

/// STATIC-DISPATCH prefix. A monomorphized trait-method call site
/// `<Concrete as Trait>::method` reflects to a real Clean definition
/// `Trust.Dispatch.<trait>#<method>#<concrete>` whose VALUE is the resolved
/// impl body's denotation. The call site is then DEFINITIONALLY that body.
pub const DISPATCH_PREFIX: &str = "Trust.Dispatch.";

/// A resolved STATIC trait-method dispatch: the call-site denotation as a real
/// Clean definition, PLUS the concrete impl body it resolves to. This is a
/// pure-data description (mirroring [`DynCarrier`]/[`AdtCarrier`]); the real
/// kernel `def` + the modulo-3 gate live in
/// [`crate::clean_ground::register_static_dispatch`].
///
/// A wrong impl body is not definitionally equal to the right one, so a
/// dispatch registered against the WRONG impl fails the equivalence check the
/// caller runs — genuine fail-closed dispatch (not an `Eq.refl` on equal terms).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StaticDispatch {
    /// The dispatch definition name (`Trust.Dispatch.<trait>#<method>#<concrete>`).
    pub name: String,
    /// The reflected impl-body denotation this call resolves to (the value of the
    /// definition). A closed `ProofTerm` — e.g. a `λ`-abstraction over the method's
    /// parameters whose body is the reflected impl return, or a `Const` naming an
    /// already-grounded impl body. The call site's result is DEFINITIONALLY this.
    pub body: ProofTerm,
    /// The reflected result TYPE the impl body inhabits (for the kernel to check
    /// the definition's declared type against). The dispatch is faithful iff the
    /// impl body infers this type.
    pub result_ty: ProofTerm,
}

/// The stable dispatch-definition name for a trait method resolved at a concrete
/// type: `Trust.Dispatch.<trait>#<method>#<concrete>` (each segment sanitized like
/// an ADT name so it is one kernel-legal `Name`). Two call sites of the SAME
/// (trait, method, concrete) share the definition; distinct impls get distinct
/// names, so a wrong impl never aliases onto the right one.
#[must_use]
pub fn dispatch_def_name(trait_name: &str, method: &str, concrete_ty: &str) -> String {
    let seg = |s: &str| {
        let sanitized = adt_inductive_name(s);
        sanitized.strip_prefix(ADT_PREFIX).unwrap_or(&sanitized).to_string()
    };
    format!("{DISPATCH_PREFIX}{}#{}#{}", seg(trait_name), seg(method), seg(concrete_ty))
}

/// Reflect a STATIC (monomorphized) trait-method dispatch: given the (trait,
/// method, concrete-type) resolution and the already-reflected impl BODY
/// (denotation) + its result type, produce a [`StaticDispatch`] whose definition
/// value is that body. FAITHFUL: the call-site denotation is definitionally the
/// impl body, not an opaque witness.
///
/// `body` is the impl's reflected denotation (e.g. from `extract_return_formula`
/// grounded, wrapped in the method's parameter λ's) — a REAL Clean term. This is
/// the concrete-impl RESOLUTION (`func: String` in `Terminator::Call` already
/// names the monomorphized impl path) made into a checkable definition.
#[must_use]
pub fn reflect_static_dispatch(
    trait_name: &str,
    method: &str,
    concrete_ty: &str,
    body: ProofTerm,
    result_ty: ProofTerm,
) -> StaticDispatch {
    StaticDispatch { name: dispatch_def_name(trait_name, method, concrete_ty), body, result_ty }
}

/// GENERIC MONOMORPHIZATION — substitute EVERY occurrence of a generic param
/// carrier `Trust.Param.<id>` in `body` with the concrete carrier `concrete`,
/// yielding the monomorphized body. This is capture-free at the `Const` level
/// (a `Const` is a global name, not a de-Bruijn binder), so a plain structural
/// replacement is sound.
///
/// Returns the substituted term. When `body` does not mention the param, the
/// result is `body` unchanged (the caller's equivalence check then still holds,
/// but the caller should verify the param WAS present to avoid a vacuous
/// "monomorphization").
#[must_use]
pub fn substitute_param(body: &ProofTerm, param_ident: &str, concrete: &ProofTerm) -> ProofTerm {
    substitute_const(body, &param_const_name(param_ident), concrete)
}

/// Structural replacement of every `Const(target)` in `term` with `replacement`.
/// `Const`s are global (not de-Bruijn), so no shifting is needed — this is a
/// sound whole-term substitution used by generic monomorphization.
#[must_use]
pub fn substitute_const(term: &ProofTerm, target: &str, replacement: &ProofTerm) -> ProofTerm {
    match term {
        ProofTerm::Const(n) if n == target => replacement.clone(),
        ProofTerm::Const(_) | ProofTerm::Var(_) | ProofTerm::Sort(_) => term.clone(),
        ProofTerm::App(f, a) => ProofTerm::App(
            Box::new(substitute_const(f, target, replacement)),
            Box::new(substitute_const(a, target, replacement)),
        ),
        ProofTerm::Lambda { binder_name, binder_type, body } => ProofTerm::Lambda {
            binder_name: binder_name.clone(),
            binder_type: Box::new(substitute_const(binder_type, target, replacement)),
            body: Box::new(substitute_const(body, target, replacement)),
        },
        ProofTerm::Pi { binder_name, domain, codomain } => ProofTerm::Pi {
            binder_name: binder_name.clone(),
            domain: Box::new(substitute_const(domain, target, replacement)),
            codomain: Box::new(substitute_const(codomain, target, replacement)),
        },
    }
}

/// Whether `term` mentions the generic-param carrier `Trust.Param.<id>` — the
/// signal that a monomorphization actually substitutes something (a body that
/// does NOT reference the param is not genuinely generic in it, and the caller
/// should decline rather than claim a vacuous monomorphization).
#[must_use]
pub fn body_mentions_param(term: &ProofTerm, param_ident: &str) -> bool {
    let target = param_const_name(param_ident);
    fn walk(term: &ProofTerm, target: &str) -> bool {
        match term {
            ProofTerm::Const(n) => n == target,
            ProofTerm::Var(_) | ProofTerm::Sort(_) => false,
            ProofTerm::App(f, a) => walk(f, target) || walk(a, target),
            ProofTerm::Lambda { binder_type, body, .. } => {
                walk(binder_type, target) || walk(body, target)
            }
            ProofTerm::Pi { domain, codomain, .. } => {
                walk(domain, target) || walk(codomain, target)
            }
        }
    }
    walk(term, &target)
}

/// CLOSURE-DISPATCH prefix. A closure's REAL invocation — its reflected body
/// applied to its captured environment — reflects to a definition
/// `Trust.ClosureCall.<name>` beyond the abstract `call : A → B` field of the
/// base closure record.
pub const CLOSURE_CALL_PREFIX: &str = "Trust.ClosureCall.";

/// A CLOSURE INVOKED with its captured environment: the definition
/// `Trust.ClosureCall.<name> : env_ty → A → B := λ (e : env_ty)(a : A). body e a`
/// — the reflected closure body APPLIED to the real captured env record and the
/// call argument, beyond the base record's abstract `call` field. Pure data;
/// [`crate::clean_ground::register_closure_dispatch`] grounds it modulo 3.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosureDispatch {
    /// The closure-call definition name (`Trust.ClosureCall.<name>`).
    pub name: String,
    /// The closure record inductive this dispatch belongs to (`Trust.Closure.<name>`).
    pub closure_name: String,
    /// The reflected captured-environment carrier (the upvar product) — the `env`
    /// the body is applied to.
    pub env_carrier: ProofTerm,
    /// The reflected closure BODY as a function of `(env, arg)`: a `ProofTerm`
    /// `λ (e : env)(a : A). <body>` whose `<body>` USES `e` (the captured env) —
    /// so the invocation genuinely consumes the captures, not an abstract arrow.
    pub body: ProofTerm,
    /// The reflected result type `B` the invocation produces.
    pub result_ty: ProofTerm,
}

/// The closure-invocation definition name for a closure named `name`
/// (`Trust.ClosureCall.<name>`), sanitized like the closure inductive name.
#[must_use]
pub fn closure_call_name(name: &str) -> String {
    let inductive = closure_inductive_name(name);
    let seg = inductive.strip_prefix(CLOSURE_PREFIX).unwrap_or(&inductive);
    format!("{CLOSURE_CALL_PREFIX}{seg}")
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::axioms::axiom_closure;
    use crate::kernel_check::infer_type;

    fn bv(w: u32) -> ProofTerm {
        app(cst(CARRIER_BITVEC), nat(u64::from(w)))
    }

    fn infers_sort_ty(term: &ProofTerm) {
        let ctx = carrier_context();
        let inferred = infer_type(term, &ctx, &[])
            .unwrap_or_else(|e| panic!("term {term:?} should resolve in carrier ctx: {e}"));
        assert_eq!(inferred, cst(CARRIER_SORT_TY), "{term:?} should inhabit Trust.SortTy");
    }

    // --- S0 scalars (unchanged) --------------------------------------------

    #[test]
    fn reflect_sort_scalars() {
        assert_eq!(reflect_sort(&Sort::Bool), Ok(cst(CARRIER_BOOL)));
        assert_eq!(reflect_sort(&Sort::Int), Ok(cst(CARRIER_INT)));
        for &w in REFLECTED_BITVEC_WIDTHS {
            assert_eq!(reflect_sort(&Sort::BitVec(w)), Ok(bv(w)));
        }
    }

    #[test]
    fn reflect_sort_array_fails_closed() {
        let arr = Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8)));
        assert!(matches!(reflect_sort(&arr), Err(ReflectError::ArrayType(_))));
    }

    #[test]
    fn reflect_ty_scalars_map_to_carriers() {
        assert_eq!(reflect_ty(&Ty::Bool), Ok(cst(CARRIER_BOOL)));
        assert_eq!(reflect_ty(&Ty::Int { width: 32, signed: true }), Ok(bv(32)));
        assert_eq!(reflect_ty(&Ty::Bv(64)), Ok(bv(64)));
        // COVERAGE-AGENDA #2 — a BARE raw pointer reflects to the dedicated
        // opaque-address carrier `Trust.Sort.Ptr` (decodes to the `Trust.Ptr`
        // inductive), NOT silently to `Trust.Sort.Int`. This is what keeps a
        // dereference reading through it fail-closed (a pointer is no longer
        // identified with its address integer).
        assert_eq!(
            reflect_ty(&Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Bool) }),
            Ok(cst(CARRIER_PTR))
        );
        // It is a distinct carrier from the integer carrier.
        assert_ne!(
            reflect_ty(&Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Bool) }),
            Ok(cst(CARRIER_INT))
        );
    }

    /// COVERAGE-AGENDA #2 — [`reflect_ptr`] builds the `Trust.Ptr { addr : Int }`
    /// shallow opaque-address carrier: a NON-generic single-`.mk` struct whose only
    /// field is the abstract `Int` address (axiom-free — no 4th axiom). The bare-ptr
    /// SortTy code (`reflect_ty(RawPtr)`) is the distinct `Trust.Sort.Ptr`.
    #[test]
    fn reflect_ptr_builds_opaque_address_carrier() {
        let c = reflect_ptr();
        assert_eq!(c.name, PTR_INDUCTIVE);
        assert_eq!(c.name, "Trust.Ptr");
        assert_eq!(c.ctor_name, "Trust.Ptr.mk");
        assert_eq!(c.fields, vec![("addr".to_string(), cst(CARRIER_INT))]);
        // A shallow struct: no type params, single anonymous constructor (not an enum).
        assert!(c.type_params.is_empty());
        assert!(!c.is_enum());
        assert!(!c.is_parameterized());
    }

    /// GOAL-ITEM #3 — a float reflects to its STRUCTURED IEEE-754 carrier (the
    /// right-nested product of its `sign`/`exponent`/`mantissa` field codes), NEVER a
    /// flat `BitVec width` (the bit pattern, not the structure) and NEVER an error.
    #[test]
    fn reflect_ty_float_is_structured_not_aliased_to_bitvec() {
        // f32 → Prod Bool (Prod (BitVec 8) (Prod (BitVec 23) Unit)).
        let r32 = reflect_ty(&Ty::Float { width: 32 }).expect("f32 reflects structurally");
        let expected32 = reflect_product(&[
            Ty::Bool,
            Ty::Int { width: 8, signed: false },
            Ty::Int { width: 23, signed: false },
        ])
        .expect("product builds");
        assert_eq!(r32, expected32, "f32 must reflect to its IEEE field product");
        assert_ne!(r32, bv(32), "f32 must NEVER alias onto a flat BitVec 32");
        // f64 → Prod Bool (Prod (BitVec 11) (Prod (BitVec 52) Unit)).
        let r64 = reflect_ty(&Ty::Float { width: 64 }).expect("f64 reflects structurally");
        assert_ne!(r64, bv(64), "f64 must NEVER alias onto a flat BitVec 64");
        // An unsupported width still fails closed (never a flat BitVec).
        let r16 = reflect_ty(&Ty::Float { width: 16 });
        assert!(matches!(r16, Err(ReflectError::FloatType(_))), "f16 fails closed, got {r16:?}");
        assert_ne!(r16, Ok(bv(16)), "an unsupported float width must NOT alias onto BitVec");
    }

    /// GOAL-ITEM #3 SOUNDNESS GATE — `reflect_float(32)` builds the STRUCTURED IEEE-754
    /// carrier: a single-constructor `Trust.Float32` with NAMED fields
    /// `sign : Bool`, `exponent : BitVec 8`, `mantissa : BitVec 23` (NOT a flat BitVec,
    /// NOT opaque). Same f64 with (11, 52). The field carriers match exactly what
    /// `reflect_ty` produces for the corresponding scalars.
    #[test]
    fn reflect_float_builds_structured_named_carrier() {
        let c32 = reflect_float(32).expect("f32 reflects to a structured carrier");
        assert_eq!(c32.name, "Trust.Float32");
        assert_eq!(c32.ctor_name, "Trust.Float32.mk");
        assert!(
            c32.type_params.is_empty() && c32.constructors.is_empty(),
            "non-generic struct shape"
        );
        let names: Vec<&str> = c32.fields.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, vec!["sign", "exponent", "mantissa"], "IEEE field order MSB→LSB");
        assert_eq!(c32.fields[0].1, cst(CARRIER_BOOL), "sign is a Bool");
        assert_eq!(c32.fields[1].1, reflect_bitvec(8), "f32 exponent is BitVec 8");
        assert_eq!(c32.fields[2].1, reflect_bitvec(23), "f32 mantissa is BitVec 23");
        let c64 = reflect_float(64).expect("f64 reflects");
        assert_eq!(c64.name, "Trust.Float64");
        assert_eq!(c64.fields[1].1, reflect_bitvec(11), "f64 exponent is BitVec 11");
        assert_eq!(c64.fields[2].1, reflect_bitvec(52), "f64 mantissa is BitVec 52");
        // An unsupported width is None (fail closed; never a flat BitVec).
        assert_eq!(reflect_float(16), None);
        assert_eq!(float_inductive_name(16), None);
        assert_eq!(ieee754_layout(32), Some((8, 23)));
        assert_eq!(ieee754_layout(64), Some((11, 52)));
    }

    #[test]
    fn reflect_closure_is_record_inductive_with_env_and_call() {
        // CLOSURE RECORD (M5) — a closure reflects to its REAL dependent RECORD: the
        // registered single-constructor inductive `Trust.Closure.<name>` with an `env`
        // (captured environment) field and a `call : A → B` field, parameterized over
        // the call signature's two `Type` variables. `reflect_ty` binds it as the
        // APPLIED carrier `Trust.Closure.<name> (Param A) (Param B)`.
        let upvars = vec![Ty::Int { width: 8, signed: false }, Ty::Bool];
        let carrier = reflect_closure("c", &upvars).expect("closure reflects to a record");
        assert_eq!(carrier.name, "Trust.Closure.c");
        assert_eq!(carrier.ctor_name, "Trust.Closure.c.mk");
        assert_eq!(carrier.type_params.len(), 2, "parameterized over call A/B");
        // Fields: env (the upvar product) + call (a genuine Pi over the call params).
        let field_names: Vec<&str> = carrier.fields.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(field_names, vec!["env", "call"]);
        assert_eq!(carrier.fields[0].1, reflect_product(&upvars).expect("env product"));
        // The `call` field is a REAL kernel Pi (arrow), NOT a `Trust.Sort.Fn` code.
        assert!(matches!(carrier.fields[1].1, ProofTerm::Pi { .. }), "call is a kernel Pi");
        // `reflect_ty` binds the closure as the applied record inductive.
        let cl = Ty::Closure { name: "c".into(), upvars: upvars.clone(), call: None };
        match reflect_ty(&cl).expect("closure reflects") {
            ProofTerm::App(f, _) => match &*f {
                ProofTerm::App(head, _) => assert!(
                    matches!(&**head, ProofTerm::Const(n) if n == "Trust.Closure.c"),
                    "closure binds as `Trust.Closure.c A B`, got head {head:?}"
                ),
                other => panic!("expected applied closure inductive, got {other:?}"),
            },
            other => panic!("expected App (applied closure inductive), got {other:?}"),
        }
        // A coroutine takes the SAME record path.
        let co = Ty::Coroutine { name: "g".into(), upvars: upvars.clone() };
        assert!(reflect_ty(&co).is_ok(), "coroutine reflects to a record too");
        // A non-reflectable upvar still fails the whole closure closed.
        let bad = Ty::Closure { name: "b".into(), upvars: vec![Ty::Never], call: None };
        assert!(reflect_ty(&bad).is_err(), "a never upvar fails the closure closed");
        assert!(reflect_closure("b", &[Ty::Never]).is_none(), "never upvar → no carrier");
    }

    // === TYPE-ZOO CLOSE — reflection-side carrier shape (the six families) ======

    /// TYPE-ZOO #1 — a fixed-size array `[T; N]` reflects to the APPLIED length-indexed
    /// carrier `Trust.ArrayN (decode T) N` with `N` a REAL `Trust.Nat` numeral value
    /// (the const generic as a dependent INDEX), NOT the length-erased `Slice`/`List`.
    #[test]
    fn reflect_array_indexed_carries_length_as_real_nat_index() {
        let r4 = reflect_array_indexed(&Ty::Int { width: 32, signed: true }, 4)
            .expect("[i32; 4] reflects to the length-indexed carrier");
        // `Trust.ArrayN (BitVec 32) 4` — head `Trust.ArrayN`, then the element code, then
        // the REAL Nat numeral `4`.
        let expected = app(app(cst(CARRIER_ARRAYN), reflect_bitvec(32)), nat(4));
        assert_eq!(r4, expected, "[i32;4] is `Trust.ArrayN (BitVec 32) 4`");
        // The length is a real value: `[i32; 4]` and `[i32; 8]` are DISTINCT carriers.
        let r8 = reflect_array_indexed(&Ty::Int { width: 32, signed: true }, 8).unwrap();
        assert_ne!(r4, r8, "the const generic N is a real Nat index — 4 ≠ 8");
        // A non-reflectable element fails the array closed.
        assert!(reflect_array_indexed(&Ty::Never, 4).is_err(), "never element fails closed");
    }

    /// TYPE-ZOO #2 — an `impl Trait` opaque return reflects to the existential
    /// `DynCarrier` (the `dyn` analogue) under the distinct `Trust.Impl.<trait>` name,
    /// so an `impl Trait` and a `dyn Trait` over the same trait do not collide.
    #[test]
    fn reflect_impl_trait_is_existential_under_distinct_name() {
        let c = reflect_impl_trait("core::iter::Iterator", &[]);
        assert!(c.name.starts_with(IMPL_TRAIT_PREFIX), "impl Trait uses the Trust.Impl.* name");
        assert_eq!(c.name, "Trust.Impl.core_iter_Iterator");
        assert!(c.vtable_name.starts_with("Trust.Impl.Vtable."));
        // Distinct from the `dyn` existential over the SAME trait.
        let d = reflect_dyn("core::iter::Iterator", &[]);
        assert_ne!(c.name, d.name, "impl Trait and dyn Trait are separate existentials");
        // No methods from the extractor → the best-sound `Sigma Type Unit` form.
        assert!(!c.has_methods(), "field-less existential (Sigma Type Unit)");
    }

    /// TYPE-ZOO #3 — a multi-bound trait object `dyn A + B + Send` reflects to the
    /// CONJOINED existential: the trait list splits on `+`, a MARKER (`Send`) is
    /// recognized as contributing the empty obligation, and the existential name keys on
    /// the whole multi-bound string (distinct from a single-bound `dyn A`).
    #[test]
    fn reflect_multi_dyn_conjoins_and_drops_markers() {
        let bounds = split_multi_bound("core::fmt::Debug + core::clone::Clone + Send");
        assert_eq!(bounds, vec!["core::fmt::Debug", "core::clone::Clone", "Send"]);
        assert!(is_marker_trait("Send") && is_marker_trait("core::marker::Sync"));
        assert!(!is_marker_trait("core::fmt::Debug"), "Debug is not a marker");
        let multi = reflect_multi_dyn("core::fmt::Debug + core::clone::Clone + Send", &[]);
        let single = reflect_multi_dyn("core::fmt::Debug", &[]);
        assert_ne!(multi.name, single.name, "the multi-bound existential is distinct");
        // A single-bound list is just `[Trait]`.
        assert_eq!(split_multi_bound("Trait"), vec!["Trait"]);
    }

    /// TYPE-ZOO #4 — an HRTB `for<'a> fn(&'a u8) -> bool` reflects to a real kernel `Pi`
    /// quantifying the erased region: `Π(r : Trust.Region) → (El R(u8) → El R(bool))`.
    #[test]
    fn reflect_hrtb_fn_quantifies_region_as_kernel_pi() {
        let sig = FnSig {
            params: vec![Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Int { width: 8, signed: false }),
            }],
            ret: Box::new(Ty::Bool),
        };
        let hrtb = reflect_hrtb_fn(1, &sig).expect("for<'a> fn reflects");
        // Outer Π binds the region at the `Trust.Region` carrier.
        match &hrtb {
            ProofTerm::Pi { domain, codomain, .. } => {
                assert_eq!(
                    **domain,
                    cst(CARRIER_REGION),
                    "the for<'a> binder is Π(r : Trust.Region)"
                );
                // The codomain is the fn arrow (a Pi over El-wrapped codes).
                assert!(matches!(&**codomain, ProofTerm::Pi { .. }), "inner is the fn arrow");
            }
            other => panic!("HRTB must be Π(region) → arrow, got {other:?}"),
        }
        // Two regions nest two outer Π(Region) binders.
        let h2 = reflect_hrtb_fn(2, &sig).expect("for<'a,'b> reflects");
        match &h2 {
            ProofTerm::Pi { domain, codomain, .. } => {
                assert_eq!(**domain, cst(CARRIER_REGION));
                assert!(
                    matches!(&**codomain, ProofTerm::Pi { domain: d2, .. } if **d2 == cst(CARRIER_REGION))
                );
            }
            other => panic!("expected nested Π(Region), got {other:?}"),
        }
        // The erased-region atom is a nullary single-ctor inductive (axiom-free).
        let reg = reflect_region();
        assert_eq!(reg.name, REGION_INDUCTIVE);
        assert!(reg.fields.is_empty() && reg.type_params.is_empty() && !reg.is_enum());
    }

    /// TYPE-ZOO #5 — a GAT `<T as Iterator>::Item<'a>` reflects to a PARAMETERIZED
    /// type-level-function inductive `Trust.Gat.<Trait>_<Out> (P:Type) : Type`, with one
    /// `Type` parameter per GAT parameter. A NON-parameterized assoc type yields `None`
    /// (the simple `Trust.Param.*` case).
    #[test]
    fn reflect_gat_family_is_parameterized_type_level_function() {
        let c = reflect_gat_family("core::iter::Iterator", "Item", &["P/#0".to_string()])
            .expect("a GAT reflects to a parameterized family");
        assert!(c.name.starts_with(GAT_PREFIX), "uses the Trust.Gat.* name");
        assert!(c.is_parameterized(), "a GAT is a TYPE-indexed family");
        assert_eq!(c.type_params, vec!["P/#0".to_string()], "one Type param per GAT param");
        assert!(
            c.fields.is_empty(),
            "the family's output is opaque (field-less ctor over the params)"
        );
        // A bare (non-generic) associated type is NOT a GAT family.
        assert!(reflect_gat_family("Trait", "Out", &[]).is_none());
    }

    /// TYPE-ZOO #6 — a coroutine reflects to its OWN state record `Trust.Coroutine.<name>`
    /// (env + resume : S → Y, the suspend-point STATE `S` abstracted as a `Type` param),
    /// DISTINCT from a closure's `Trust.Closure.<name>` record.
    #[test]
    fn reflect_coroutine_is_state_record_distinct_from_closure() {
        let upvars = vec![Ty::Int { width: 32, signed: true }];
        let c =
            reflect_coroutine("{coroutine#0}", &upvars).expect("coroutine reflects to a record");
        assert!(c.name.starts_with(COROUTINE_PREFIX), "uses Trust.Coroutine.*");
        assert_eq!(c.type_params.len(), 2, "parameterized over the STATE S and yield Y");
        let field_names: Vec<&str> = c.fields.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(field_names, vec!["env", "resume"], "env + resume step");
        // The `resume` field is a genuine kernel Pi `S → Y`.
        assert!(matches!(c.fields[1].1, ProofTerm::Pi { .. }), "resume is a kernel Pi (the step)");
        // It is NOT the closure record (distinct name prefix).
        let cl = reflect_closure("{coroutine#0}", &upvars).expect("closure record");
        assert_ne!(c.name, cl.name, "the coroutine record is distinct from the closure record");
        // A non-reflectable upvar fails it closed.
        assert!(reflect_coroutine("x", &[Ty::Never]).is_none());
    }

    #[test]
    fn reflect_fnptr_and_fndef_are_real_kernel_pi() {
        use trust_types::FnSig;
        // FUNCTION POINTER (M5) — a fn pointer reflects to a GENUINE kernel `Pi`
        // (arrow), `El R(A) → El R(B)`, NOT the `Trust.Sort.Fn` *code*.
        let sig =
            FnSig { params: vec![Ty::Int { width: 8, signed: false }], ret: Box::new(Ty::Bool) };
        let fp = Ty::FnPtr { sig: Box::new(sig.clone()) };
        let reflected = reflect_ty(&fp).expect("fn pointer reflects");
        assert_eq!(
            Ok(reflected.clone()),
            reflect_fn_sig_pi(&sig),
            "fn ptr reflects via the Pi path"
        );
        // It is a real `ProofTerm::Pi` over `El`-wrapped reflected codes (a dependent
        // function type rooted in the 3 — NOT the `Trust.Sort.Fn` carrier code).
        match &reflected {
            ProofTerm::Pi { domain, codomain, .. } => {
                assert_eq!(**domain, app(cst(CARRIER_EL), bv(8)), "domain is El R(u8)");
                assert_eq!(
                    **codomain,
                    app(cst(CARRIER_EL), cst(CARRIER_BOOL)),
                    "codomain is El R(bool)"
                );
            }
            other => panic!("fn ptr must reflect to a kernel Pi, got {other:?}"),
        }
        assert_ne!(Ok(reflected), reflect_fn_sig(&sig), "the Pi is NOT the Trust.Sort.Fn code");
        // A function ITEM (`fn` def) takes the same Pi path.
        let fd = Ty::FnDef { name: "f".into(), sig: Box::new(sig.clone()) };
        assert_eq!(reflect_ty(&fd), reflect_fn_sig_pi(&sig));
        // Multi-arg curries right-nested: `fn(u8, bool) -> i32` → `El u8 → (El bool → El i32)`.
        let sig2 = FnSig {
            params: vec![Ty::Int { width: 8, signed: false }, Ty::Bool],
            ret: Box::new(Ty::Int { width: 32, signed: true }),
        };
        match reflect_fn_sig_pi(&sig2).expect("two-arg fn ptr reflects") {
            ProofTerm::Pi { codomain, .. } => {
                assert!(
                    matches!(&*codomain, ProofTerm::Pi { .. }),
                    "curried: codomain is itself a Pi"
                );
            }
            other => panic!("expected curried Pi, got {other:?}"),
        }
        // A fn ptr over an opaque type variable parameter fails closed (no El carrier).
        // NOTE (dyn-Sigma + closure merge): `dyn Trait` is NO LONGER an opaque type
        // variable — it reflects to the El-decodable existential `Trust.Dyn.<trait>`
        // (the Σ(T:Type) Vtable front), so a `fn(dyn Tr)` fn-ptr now takes the Pi path
        // over `El (Trust.Dyn.Tr)`. The genuinely-opaque case is a bare generic param
        // `T` (`Trust.Param.*`, NOT El-decodable), which still fails the fn-ptr closed.
        let sig_tv = FnSig {
            params: vec![Ty::Unsupported {
                kind: PARAM_KIND.into(),
                detail: "generic parameter T/#0 needs monomorphization".into(),
            }],
            ret: Box::new(Ty::Bool),
        };
        assert!(
            reflect_fn_sig_pi(&sig_tv).is_err(),
            "an opaque generic-param fn-ptr parameter has no El carrier; fails closed"
        );
        // And the dyn-parameter fn-ptr now SUCCEEDS via the existential's El carrier —
        // the merged, more-faithful behavior (dyn is a real carrier, not a type var).
        let sig_dyn = FnSig {
            params: vec![Ty::Dynamic { trait_name: "Tr".into() }],
            ret: Box::new(Ty::Bool),
        };
        assert!(
            reflect_fn_sig_pi(&sig_dyn).is_ok(),
            "a `dyn Trait` fn-ptr parameter takes the Pi path over `El (Trust.Dyn.Tr)`"
        );
    }

    // --- M2: products ------------------------------------------------------

    #[test]
    fn reflect_unit_is_unit_carrier() {
        assert_eq!(reflect_ty(&Ty::Unit), Ok(cst(CARRIER_UNIT)));
        infers_sort_ty(&cst(CARRIER_UNIT));
    }

    #[test]
    fn reflect_tuple_is_right_nested_product() {
        // (bool, u32) -> Prod Bool (Prod (BitVec 32) Unit)
        let ty = Ty::Tuple(vec![Ty::Bool, Ty::Int { width: 32, signed: false }]);
        let expected = app(
            app(cst(CARRIER_PROD), cst(CARRIER_BOOL)),
            app(app(cst(CARRIER_PROD), bv(32)), cst(CARRIER_UNIT)),
        );
        assert_eq!(reflect_ty(&ty), Ok(expected.clone()));
        infers_sort_ty(&expected); // the product kernel-resolves to Trust.SortTy
    }

    #[test]
    fn reflect_struct_adt_is_product_of_field_types() {
        // struct Point { x: i32, y: i32 } -> Prod (BitVec 32) (Prod (BitVec 32) Unit)
        let ty = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Point".into(),
            fields: vec![
                ("x".into(), Ty::Int { width: 32, signed: true }),
                ("y".into(), Ty::Int { width: 32, signed: true }),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let reflected = reflect_ty(&ty).expect("struct of scalars should reflect");
        infers_sort_ty(&reflected);
        // It is a product headed by Trust.Sort.Prod.
        match &reflected {
            ProofTerm::App(f, _) => match &**f {
                ProofTerm::App(prod, _) => assert_eq!(**prod, cst(CARRIER_PROD)),
                other => panic!("expected Prod head, got {other:?}"),
            },
            other => panic!("expected App, got {other:?}"),
        }
    }

    /// PHASE 1 — a non-generic struct reflects to a NAMED inductive carrier
    /// (`Trust.Adt.<Name>`, ctor `<Name>.mk`) with field carriers in MIR order,
    /// while `reflect_ty` STILL returns the anonymous `Prod` (no regression — the
    /// two are separate entry points; structural grounding registers the carrier).
    #[test]
    fn reflect_struct_builds_named_inductive_carrier_non_generic() {
        let ty = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Wrapper".into(),
            fields: vec![("value".into(), Ty::Int { width: 32, signed: true })],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let carrier =
            reflect_struct(&ty).expect("non-generic struct reflects to a named inductive");
        assert_eq!(carrier.name, "Trust.Adt.Wrapper");
        assert_eq!(carrier.ctor_name, "Trust.Adt.Wrapper.mk");
        assert_eq!(carrier.fields.len(), 1);
        assert_eq!(carrier.fields[0].0, "value");
        assert_eq!(carrier.field_index("value"), Some(0));
        assert_eq!(carrier.field_index("nope"), None);
        // The field-type carrier is the i32 BitVec carrier (MIR order preserved).
        assert_eq!(carrier.fields[0].1, reflect_bitvec(32));
        // reflect_ty is UNCHANGED — it still yields the anonymous Prod floor.
        match reflect_ty(&ty) {
            Ok(ProofTerm::App(f, _)) => match &*f {
                ProofTerm::App(prod, _) => assert_eq!(**prod, cst(CARRIER_PROD)),
                other => panic!("expected Prod head, got {other:?}"),
            },
            other => panic!("expected Prod App, got {other:?}"),
        }
    }

    /// PHASE 1 — a multi-field struct preserves MIR field order in the carrier.
    #[test]
    fn reflect_struct_preserves_mir_field_order() {
        let ty = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "my_crate::Point".into(),
            fields: vec![
                ("x".into(), Ty::Int { width: 32, signed: true }),
                ("y".into(), Ty::Int { width: 64, signed: false }),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let carrier = reflect_struct(&ty).expect("struct of scalars reflects");
        // The mangled name collapses `::` to a single underscore.
        assert_eq!(carrier.name, "Trust.Adt.my_crate_Point");
        assert_eq!(
            carrier.fields.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
            vec!["x", "y"]
        );
        assert_eq!(carrier.field_index("x"), Some(0));
        assert_eq!(carrier.field_index("y"), Some(1));
    }

    /// A generic param field (possibly behind a transparent `&T`).
    fn param_field(detail: &str) -> Ty {
        Ty::Unsupported { kind: PARAM_KIND.into(), detail: detail.into() }
    }

    /// PHASE 2 — a generic struct `Wrapper<T>{value:T, count:u32}` reflects to a
    /// PARAMETERIZED carrier: `type_params == ["T/#0"]`, the generic `value` field's
    /// carrier is the bound param const `Trust.Param.T/#0` (mapping to type-param 0),
    /// and the concrete `count` field keeps its BitVec carrier. A NON-generic struct
    /// is unchanged (`type_params` empty).
    #[test]
    fn reflect_struct_generic_field_builds_parameterized_carrier() {
        let ty = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Wrapper".into(),
            fields: vec![
                ("value".into(), param_field("generic parameter T/#0 needs monomorphization")),
                ("count".into(), Ty::Int { width: 32, signed: false }),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let carrier = reflect_struct(&ty).expect("a generic struct reflects parameterized");
        assert_eq!(carrier.name, "Trust.Adt.Wrapper");
        assert!(carrier.is_parameterized());
        assert_eq!(carrier.type_params, vec!["T/#0".to_string()]);
        // The generic `value` field carrier is the bound param const, and it maps to
        // type-param index 0; the concrete `count` field is the i32 BitVec carrier.
        assert_eq!(carrier.fields[0].0, "value");
        assert_eq!(carrier.fields[0].1, cst(&param_const_name("T/#0")));
        assert_eq!(carrier.field_param_index(&carrier.fields[0].1), Some(0));
        assert_eq!(carrier.fields[1].0, "count");
        assert_eq!(carrier.fields[1].1, reflect_bitvec(32));
        assert_eq!(carrier.field_param_index(&carrier.fields[1].1), None);

        // A non-generic struct is unchanged — empty type_params, NOT parameterized.
        let plain = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Pt".into(),
            fields: vec![("x".into(), Ty::Int { width: 32, signed: true })],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let pc = reflect_struct(&plain).expect("plain struct reflects");
        assert!(!pc.is_parameterized());
        assert!(pc.type_params.is_empty());
    }

    /// PHASE 2 — DISTINCT generic params across fields are collected once each, in
    /// first-appearance order, and the SAME param shared by two fields maps to ONE
    /// binder. `Pair<A,B>{ a:A, b:B, also_a:A }` ⇒ `type_params == [A/#0, B/#1]`
    /// with `also_a` reusing `A`'s binder (param index 0).
    #[test]
    fn reflect_struct_collects_distinct_type_params_sharing_repeats() {
        let ty = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Pair".into(),
            fields: vec![
                ("a".into(), param_field("generic parameter A/#0 needs monomorphization")),
                ("b".into(), param_field("generic parameter B/#1 needs monomorphization")),
                ("also_a".into(), param_field("generic parameter A/#0 needs monomorphization")),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let carrier = reflect_struct(&ty).expect("multi-param generic struct reflects");
        assert_eq!(carrier.type_params, vec!["A/#0".to_string(), "B/#1".to_string()]);
        // `a` and `also_a` share param 0 (A); `b` is param 1 (B).
        assert_eq!(carrier.field_param_index(&carrier.fields[0].1), Some(0));
        assert_eq!(carrier.field_param_index(&carrier.fields[1].1), Some(1));
        assert_eq!(carrier.field_param_index(&carrier.fields[2].1), Some(0));
    }

    /// PHASE 2 — a generic-struct PARAMETER binds at the parameterized inductive
    /// applied to its type-param consts, `Trust.Adt.Wrapper (Trust.Param.T/#0)`,
    /// which `reflect_contract` abstracts into the outer `Π(T:Type)`. A bare generic
    /// param (non-struct) is UNCHANGED — it still Pi-binds directly as a type var.
    #[test]
    fn generic_struct_param_binds_at_applied_inductive() {
        let ty = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Wrapper".into(),
            fields: vec![
                ("value".into(), param_field("generic parameter T/#0 needs monomorphization")),
                ("count".into(), Ty::Int { width: 32, signed: false }),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let bound =
            generic_struct_binding(&ty).expect("generic struct param has an applied binding");
        // `Trust.Adt.Wrapper (Trust.Param.T/#0)`.
        let expected = app(cst("Trust.Adt.Wrapper"), cst(&param_const_name("T/#0")));
        assert_eq!(bound, expected);
        // A bare generic param is NOT a struct — no applied-inductive binding.
        assert!(
            generic_struct_binding(&param_field("generic parameter T/#0 needs monomorphization"))
                .is_none()
        );
        // A non-generic struct has no applied-inductive binding either (Phase 1 path).
        let plain = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Pt".into(),
            fields: vec![("x".into(), Ty::Int { width: 32, signed: true })],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        assert!(generic_struct_binding(&plain).is_none());
    }

    #[test]
    fn reflect_empty_struct_is_unit() {
        let ty = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Empty".into(),
            fields: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        assert_eq!(reflect_ty(&ty), Ok(cst(CARRIER_UNIT)));
    }

    #[test]
    fn reflect_nested_struct_in_tuple_resolves() {
        // (Point, bool) where Point is a 2-int struct.
        let point = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Point".into(),
            fields: vec![("x".into(), Ty::Int { width: 8, signed: false })],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let ty = Ty::Tuple(vec![point, Ty::Bool]);
        let reflected = reflect_ty(&ty).expect("nested composite of scalars should reflect");
        infers_sort_ty(&reflected);
    }

    #[test]
    fn reflect_composite_fails_closed_transitively_on_bad_component() {
        // A tuple containing a never must fail closed with the never's error.
        let ty = Ty::Tuple(vec![Ty::Bool, Ty::Never]);
        assert!(matches!(reflect_ty(&ty), Err(ReflectError::NeverType(_))));
        // A struct with a still-non-reflectable (never) field fails closed
        // transitively with that field's error.
        let s = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Holder".into(),
            fields: vec![("r".into(), Ty::Never)],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        assert!(matches!(reflect_ty(&s), Err(ReflectError::NeverType(_))));
        // GOAL-ITEM #3 — a composite with a FLOAT component now reflects structurally
        // (the float is a structured carrier, not a non-reflectable family).
        let tf = Ty::Tuple(vec![Ty::Bool, Ty::Float { width: 64 }]);
        assert!(reflect_ty(&tf).is_ok(), "a tuple with a float field now reflects structurally");
        let sf = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Holder2".into(),
            fields: vec![("r".into(), Ty::Float { width: 32 })],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        assert!(reflect_ty(&sf).is_ok(), "a struct with a float field now reflects structurally");
    }

    // --- M2: sequences -----------------------------------------------------

    #[test]
    fn reflect_array_is_length_indexed_arrayn() {
        // TYPE-ZOO #1 — PRODUCTION-WIRED: `[bool; 4]` → the LENGTH-INDEXED carrier
        // `Trust.ArrayN Bool 4` (the const generic `N=4` as a REAL `Nat` INDEX), NOT the
        // length-erased `Trust.Sort.Vec`. The MAIN `reflect_ty` arm now emits the same
        // carrier the dedicated `reflect_array_indexed` entry point + the
        // `const_generic_indexed` corpus probe ground.
        let ty = Ty::Array { elem: Box::new(Ty::Bool), len: 4 };
        let expected = app(app(cst(CARRIER_ARRAYN), cst(CARRIER_BOOL)), nat(4));
        assert_eq!(reflect_ty(&ty), Ok(expected.clone()));
        // The production arm and the dedicated entry point agree EXACTLY.
        assert_eq!(reflect_ty(&ty), reflect_array_indexed(&Ty::Bool, 4));
        // The carrier is the El-decodable head of the registered `Trust.ArrayN` inductive.
        match &expected {
            ProofTerm::App(inner, len) => {
                assert_eq!(**len, nat(4), "length is a real Nat numeral index");
                match &**inner {
                    ProofTerm::App(head, _) => {
                        assert_eq!(**head, cst(CARRIER_ARRAYN), "head is Trust.ArrayN");
                    }
                    other => panic!("expected ArrayN application, got {other:?}"),
                }
            }
            other => panic!("expected ArrayN T n, got {other:?}"),
        }
    }

    #[test]
    fn reflect_slice_is_slice_carrier() {
        // [u32] -> Slice (BitVec 32)
        let ty = Ty::Slice { elem: Box::new(Ty::Int { width: 32, signed: false }) };
        let expected = app(cst(CARRIER_SLICE), bv(32));
        assert_eq!(reflect_ty(&ty), Ok(expected.clone()));
        infers_sort_ty(&expected);
    }

    #[test]
    fn reflect_array_of_non_reflectable_fails_closed() {
        let ty = Ty::Array { elem: Box::new(Ty::Never), len: 8 };
        assert!(matches!(reflect_ty(&ty), Err(ReflectError::NeverType(_))));
        // GOAL-ITEM #3 — an array of floats now reflects structurally (length-indexed
        // `Trust.ArrayN` over the float's structured carrier).
        let tf = Ty::Array { elem: Box::new(Ty::Float { width: 32 }), len: 8 };
        assert!(reflect_ty(&tf).is_ok(), "an array of floats now reflects structurally");
    }

    // --- still fail-closed families ----------------------------------------

    #[test]
    fn remaining_families_fail_closed_with_their_variant() {
        // (Ty::Ref reflects transparently to its referent — M5; Closure/Coroutine
        // reflect as their upvar product and FnDef/FnPtr via the Fn carrier — see
        // reflect_closure_and_coroutine_are_upvar_product / reflect_fnptr_and_fndef_*;
        // Ty::Dynamic reflects as an opaque type-variable const — see
        // reflect_ty_dynamic_is_opaque_type_var_const.)
        // These families are still fail-closed (no faithful carrier yet). NOTE: f32/f64
        // now reflect STRUCTURALLY (GOAL-ITEM #3) and are NOT in this set; only an
        // UNSUPPORTED float width (e.g. f16) still fails closed via `FloatType`.
        let cases: Vec<(Ty, fn(&ReflectError) -> bool)> = vec![
            (Ty::Float { width: 16 }, |e| matches!(e, ReflectError::FloatType(_))),
            (Ty::Never, |e| matches!(e, ReflectError::NeverType(_))),
            (Ty::Unsupported { kind: "k".into(), detail: "d".into() }, |e| {
                matches!(e, ReflectError::UnsupportedType(_))
            }),
        ];
        for (ty, is_expected) in cases {
            match reflect_ty(&ty) {
                Ok(t) => panic!("{ty:?} must fail closed, but reflected to {t:?}"),
                Err(e) => assert!(is_expected(&e), "wrong error variant for {ty:?}: {e:?}"),
            }
        }
    }

    // --- M3 groundwork: function-signature reflection ----------------------

    #[test]
    fn reflect_fn_sig_curries_into_arrow_codes() {
        // fn(u8, bool) -> u32  ->  Fn (BitVec 8) (Fn Bool (BitVec 32))
        let sig = FnSig {
            params: vec![Ty::Int { width: 8, signed: false }, Ty::Bool],
            ret: Box::new(Ty::Int { width: 32, signed: false }),
        };
        let expected =
            app(app(cst(CARRIER_FN), bv(8)), app(app(cst(CARRIER_FN), cst(CARRIER_BOOL)), bv(32)));
        assert_eq!(reflect_fn_sig(&sig), Ok(expected.clone()));
        infers_sort_ty(&expected);
    }

    #[test]
    fn reflect_fn_sig_nullary_is_just_return_code() {
        let sig = FnSig { params: vec![], ret: Box::new(Ty::Bool) };
        assert_eq!(reflect_fn_sig(&sig), Ok(cst(CARRIER_BOOL)));
    }

    #[test]
    fn reflect_fn_sig_fails_closed_on_bad_param_or_ret() {
        let bad_param = FnSig { params: vec![Ty::Never], ret: Box::new(Ty::Bool) };
        assert!(matches!(reflect_fn_sig(&bad_param), Err(ReflectError::NeverType(_))));
        let bad_ret = FnSig { params: vec![Ty::Bool], ret: Box::new(Ty::Never) };
        assert!(matches!(reflect_fn_sig(&bad_ret), Err(ReflectError::NeverType(_))));
        // GOAL-ITEM #3 — a float param/ret now reflects structurally (via the Fn carrier).
        let float_param = FnSig { params: vec![Ty::Float { width: 32 }], ret: Box::new(Ty::Bool) };
        assert!(reflect_fn_sig(&float_param).is_ok(), "a float param now reflects structurally");
    }

    // --- M3: predicate reflection ------------------------------------------

    fn ivar(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    /// A carrier context extended with the given integer variables (`: Trust.Int`).
    fn predicate_context(int_vars: &[&str]) -> KernelContext {
        let mut ctx = carrier_context();
        for v in int_vars {
            ctx.add_axiom(v, cst(PROP_INT)).expect("int var");
        }
        ctx
    }

    fn infers_prop(term: &ProofTerm, ctx: &KernelContext) {
        let inferred = infer_type(term, ctx, &[])
            .unwrap_or_else(|e| panic!("predicate {term:?} should be a Prop: {e}"));
        assert_eq!(inferred, ProofTerm::Sort(0), "{term:?} should inhabit Prop");
    }

    #[test]
    fn reflect_formula_bool_literals() {
        assert_eq!(reflect_formula(&Formula::Bool(true)), Ok(cst(PROP_TRUE)));
        assert_eq!(reflect_formula(&Formula::Bool(false)), Ok(cst(PROP_FALSE)));
    }

    #[test]
    fn reflect_formula_comparison_typechecks_to_prop() {
        // x > 0
        let f = Formula::Gt(Box::new(ivar("x")), Box::new(Formula::Int(0)));
        let term = reflect_formula(&f).expect("x > 0 should reflect");
        assert_eq!(term, app(app(cst(PROP_GT), cst("x")), cst(&int_lit_name(0))));
        infers_prop(&term, &predicate_context(&["x"]));
    }

    #[test]
    fn reflect_formula_compound_predicate_typechecks() {
        // x > 0 && x < 10
        let f = Formula::And(vec![
            Formula::Gt(Box::new(ivar("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(ivar("x")), Box::new(Formula::Int(10))),
        ]);
        let term = reflect_formula(&f).expect("conjunction should reflect");
        infers_prop(&term, &predicate_context(&["x"]));
    }

    #[test]
    fn reflect_formula_implication_with_arithmetic() {
        // x >= 1 -> x + (-1) >= 0
        let f = Formula::Implies(
            Box::new(Formula::Ge(Box::new(ivar("x")), Box::new(Formula::Int(1)))),
            Box::new(Formula::Ge(
                Box::new(Formula::Add(Box::new(ivar("x")), Box::new(Formula::Int(-1)))),
                Box::new(Formula::Int(0)),
            )),
        );
        let term = reflect_formula(&f).expect("implication should reflect");
        infers_prop(&term, &predicate_context(&["x"]));
    }

    #[test]
    fn reflect_formula_empty_connectives_are_units() {
        assert_eq!(reflect_formula(&Formula::And(vec![])), Ok(cst(PROP_TRUE)));
        assert_eq!(reflect_formula(&Formula::Or(vec![])), Ok(cst(PROP_FALSE)));
    }

    #[test]
    fn reflect_formula_bool_var_is_atomic_prop() {
        // A bare boolean variable reflects to `BoolTrue p` (grounds to `Eq Bool p true`).
        let f = Formula::Var("p".into(), Sort::Bool);
        assert_eq!(reflect_formula(&f), Ok(app(cst(PROP_BOOL_TRUE), cst("p"))));
    }

    #[test]
    fn reflect_formula_fails_closed_on_bitvector_and_quantifiers() {
        let bv = Formula::BvAdd(Box::new(ivar("x")), Box::new(ivar("y")), 32);
        assert!(matches!(reflect_formula(&bv), Err(ReflectError::PredicateUnsupported(_))));
        // A comparison whose operand is a bitvector op fails closed transitively.
        let cmp = Formula::Lt(Box::new(bv), Box::new(Formula::Int(0)));
        assert!(matches!(reflect_formula(&cmp), Err(ReflectError::PredicateUnsupported(_))));
    }

    #[test]
    fn reflect_predicate_has_no_unresolved_constants() {
        let f = Formula::And(vec![
            Formula::Gt(Box::new(ivar("x")), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(ivar("x")), Box::new(Formula::Int(100))),
        ]);
        let term = reflect_formula(&f).unwrap();
        let ctx = predicate_context(&["x"]);
        let report = axiom_closure(&term, &ctx);
        assert!(report.unresolved.is_empty(), "dangling: {:?}", report.unresolved);
        assert!(report.axioms.contains(PROP_AND));
        assert!(report.axioms.contains(PROP_GT));
    }

    // --- M3 step 2: dependent contract types -------------------------------

    fn i32() -> Ty {
        Ty::Int { width: 32, signed: true }
    }

    /// A reflected contract type is a well-formed kernel type when checked against
    /// the carrier context — this validates the de-Bruijn binding. Its sort is
    /// `Sort 1` for a fully-concrete contract, but `Sort 2` once it binds an opaque
    /// type variable (generic param / trait object) at `Type` (`Sort 1`), since
    /// `Π(T : Sort 1) → …` lands one universe up. Either way it must infer to *some*
    /// `Sort` of level ≥ 1 (a genuine type/kind, never a `Prop`).
    fn contract_is_a_type(term: &ProofTerm) {
        let ctx = carrier_context();
        let inferred = infer_type(term, &ctx, &[])
            .unwrap_or_else(|e| panic!("contract type should kernel-check: {e}\nterm: {term:?}"));
        assert!(
            matches!(inferred, ProofTerm::Sort(level) if level >= 1),
            "a contract is a type (Sort ≥ 1), got {inferred:?}"
        );
    }

    #[test]
    fn reflect_contract_single_param_is_a_dependent_type() {
        // fn(x: i32) requires x > 0 ensures ret > x -> i32
        let pre = Formula::Gt(Box::new(ivar("x")), Box::new(Formula::Int(0)));
        let post = Formula::Gt(Box::new(ivar("ret")), Box::new(ivar("x")));
        let contract =
            reflect_contract(&[("x", &i32())], &pre, "ret", &i32(), &post).expect("contract");
        // Π(x:Int) → Π(_ : Gt x 0) → Sigma Int (λ ret. Gt ret x)
        contract_is_a_type(&contract);
    }

    #[test]
    fn reflect_contract_two_params_binds_both() {
        // fn(a: i32, b: i32) requires a < b ensures ret > a -> i32
        let pre = Formula::Lt(Box::new(ivar("a")), Box::new(ivar("b")));
        let post = Formula::Gt(Box::new(ivar("ret")), Box::new(ivar("a")));
        let contract =
            reflect_contract(&[("a", &i32()), ("b", &i32())], &pre, "ret", &i32(), &post)
                .expect("two-param contract");
        contract_is_a_type(&contract);
    }

    #[test]
    fn reflect_contract_trivial_pre_post() {
        // fn(x: i32) requires true ensures true -> i32
        let contract = reflect_contract(
            &[("x", &i32())],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("trivial contract");
        contract_is_a_type(&contract);
    }

    // --- generic type parameters (TyKind::Param) ---------------------------

    /// A `Ty::Unsupported` modeling a generic type parameter `name/#index`.
    fn param_ty(name_idx: &str) -> Ty {
        Ty::Unsupported {
            kind: PARAM_KIND.into(),
            detail: format!("generic parameter {name_idx} needs monomorphization"),
        }
    }

    #[test]
    fn param_ident_parses_the_mir_extract_detail_format() {
        // `ParamTy` Debug is `{name}/#{index}` (rustc structural_impls.rs).
        assert_eq!(
            param_ident_from_detail("generic parameter T/#0 needs monomorphization"),
            "T/#0"
        );
        assert_eq!(
            param_ident_from_detail("generic parameter __H/#2 needs monomorphization"),
            "__H/#2"
        );
        // A drifted detail still yields a stable (if uglier) identity.
        assert_eq!(param_ident_from_detail("weird"), "weird");
    }

    #[test]
    fn reflect_ty_generic_param_is_a_stable_free_const() {
        // The same param maps to the same const; distinct params differ.
        assert_eq!(reflect_ty(&param_ty("T/#0")), Ok(cst("Trust.Param.T/#0")));
        assert_eq!(reflect_ty(&param_ty("T/#0")), reflect_ty(&param_ty("T/#0")));
        assert_ne!(reflect_ty(&param_ty("T/#0")), reflect_ty(&param_ty("U/#1")));
        // A non-Param Unsupported still fails closed.
        let other = Ty::Unsupported { kind: "TyKind::Bound".into(), detail: "d".into() };
        assert!(matches!(reflect_ty(&other), Err(ReflectError::UnsupportedType(_))));
    }

    #[test]
    fn reflect_contract_pi_binds_type_param_at_type_universe_and_kernel_checks() {
        // fn f<T>(x: T) requires true ensures true -> i32
        // becomes Π(T : Type) → Π(x : T) → Π(_:True) → Sigma Int (λ.True). The type
        // variable binds at `Type` (Sort 1), not `Prop` (Sort 0), so the same `T`
        // can serve as a `Sigma` return carrier when a function returns `T`.
        let t = param_ty("T/#0");
        let contract = reflect_contract(
            &[("x", &t)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("a generic-param value parameter reflects");
        // Outermost binder is the type variable, domain `Type` (Sort 1).
        match &contract {
            ProofTerm::Pi { domain, codomain, .. } => {
                assert_eq!(**domain, ProofTerm::Sort(1), "type-param binder is Type (Sort 1)");
                // The inner value-param binder's domain references the type var (Var 0).
                match &**codomain {
                    ProofTerm::Pi { domain: vdom, .. } => {
                        assert_eq!(**vdom, ProofTerm::Var(0), "x binds at the bound type var T");
                    }
                    other => panic!("expected inner Π(x : T), got {other:?}"),
                }
            }
            other => panic!("expected outer Π(T : Type), got {other:?}"),
        }
        // De-Bruijn correctness is validated by the real kernel: the whole contract
        // is a well-formed Type (`Sort 1`).
        contract_is_a_type(&contract);
    }

    #[test]
    fn reflect_contract_distinct_params_get_distinct_binders() {
        // fn g<T, U>(x: T, y: U) -> i32 : Π(T:Sort0) Π(U:Sort0) Π(x:T) Π(y:U) → Σ…
        let t = param_ty("T/#0");
        let u = param_ty("U/#1");
        let contract = reflect_contract(
            &[("x", &t), ("y", &u)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("two distinct generic params reflect");
        contract_is_a_type(&contract);
        // Exactly two outer Type (Sort 1) binders.
        let mut depth = 0;
        let mut cur = &contract;
        while let ProofTerm::Pi { domain, codomain, .. } = cur {
            if **domain == ProofTerm::Sort(1) {
                depth += 1;
                cur = codomain;
            } else {
                break;
            }
        }
        assert_eq!(depth, 2, "two distinct params ⇒ two Π(_:Type) binders");
    }

    #[test]
    fn reflect_contract_reference_to_generic_param_binds_at_type_var() {
        // fn h<T>(x: &T) -> i32 : a reference to a generic param is transparent, so
        // `x : &T` binds at the same opaque type variable `T`. Kernel-checks.
        let reft = Ty::Ref { mutable: false, inner: Box::new(param_ty("T/#0")) };
        let contract = reflect_contract(
            &[("x", &reft)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("&T param reflects at the opaque type var");
        contract_is_a_type(&contract);
    }

    #[test]
    fn reflect_contract_generic_return_grounds_with_type_var_sigma_carrier() {
        // fn id<T>(x: T) -> T : a generic RETURN now GROUNDS — the type variable `T`
        // is bound at `Type` (Sort 1), so it is itself a valid `Trust.Sigma` return
        // carrier. Builds `Π(T : Type) → Π(x : T) → Π(_:True) → Sigma T (λ.True)` and
        // kernel-checks. The SAME `T` binder is shared by the param `x` and the
        // return Sigma carrier (exactly one outer type binder).
        let t = param_ty("T/#0");
        let contract =
            reflect_contract(&[("x", &t)], &Formula::Bool(true), "ret", &t, &Formula::Bool(true))
                .expect("a generic-return contract now reflects (type-var Sigma carrier)");
        contract_is_a_type(&contract);
        // Exactly one outer Type binder is shared between the param and the return.
        let mut depth = 0;
        let mut cur = &contract;
        while let ProofTerm::Pi { domain, codomain, .. } = cur {
            if **domain == ProofTerm::Sort(1) {
                depth += 1;
                cur = codomain;
            } else {
                break;
            }
        }
        assert_eq!(depth, 1, "one shared `Π(T : Type)` for both the param and the return");
    }

    // --- dump compaction: Ty::Datatype (M6 census gap #1) --------------------

    /// A by-name back-reference to `demo::Tree` (the compacted spelling —
    /// `variants: []`).
    fn tree_backref() -> Ty {
        Ty::Datatype { name: "demo::Tree".into(), variants: vec![] }
    }

    /// The full defining variant list of the recursive `demo::Tree`:
    /// `enum Tree { Leaf(u32), Node(Tree, Tree) }` with the recursive fields as
    /// by-name back-references — exactly the shape `trust-mir-extract`'s
    /// compaction emits at a defining occurrence.
    fn tree_variants() -> Vec<(String, Vec<(String, Ty)>)> {
        vec![
            ("Leaf".into(), vec![("v".into(), Ty::Int { width: 32, signed: false })]),
            (
                "Node".into(),
                vec![("left".into(), tree_backref()), ("right".into(), tree_backref())],
            ),
        ]
    }

    fn tree_full() -> Ty {
        Ty::Datatype { name: "demo::Tree".into(), variants: tree_variants() }
    }

    #[test]
    fn reflect_ty_datatype_backref_is_the_opaque_datatype_type_variable() {
        // The compacted by-name reference (unresolved here) reflects to the
        // Pi-bindable opaque type variable keyed on the datatype name — a BARE
        // const: no applied structure, no fields, nothing fabricated.
        assert_eq!(reflect_ty(&tree_backref()), Ok(cst("Trust.Param.@datatype::demo::Tree")));
        // Same datatype → same variable; distinct datatypes NEVER alias.
        assert_eq!(reflect_ty(&tree_backref()), reflect_ty(&tree_backref()));
        let other = Ty::Datatype { name: "demo::Other".into(), variants: vec![] };
        assert_ne!(reflect_ty(&other), reflect_ty(&tree_backref()));
        // It is recognized by the type-variable machinery (Pi-bound outermost,
        // caught by the composite/registration fail-closed gates).
        assert!(is_type_var_const(&datatype_backref_const_name("demo::Tree")));
    }

    #[test]
    fn reflect_ty_datatype_full_definition_reflects_identically_to_equivalent_adt_enum() {
        // The full definition reflects EXACTLY like the equivalent `Ty::Adt` enum
        // (constructed independently here, pinning the conversion).
        let equivalent_adt = Ty::adt_enum(
            "demo::Tree",
            vec![
                VariantDef {
                    name: "Leaf".into(),
                    discriminant: 0,
                    fields: vec![("v".into(), Ty::Int { width: 32, signed: false })],
                },
                VariantDef {
                    name: "Node".into(),
                    discriminant: 1,
                    fields: vec![("left".into(), tree_backref()), ("right".into(), tree_backref())],
                },
            ],
        );
        assert_eq!(reflect_ty(&tree_full()), reflect_ty(&equivalent_adt));
        // The carrier is the ONE-LEVEL-UNROLLED functor view: the named injective
        // inductive applied to the datatype's own recursion variable — real
        // constructors/fields from the dump, recursion abstracted opaque.
        assert_eq!(
            reflect_ty(&tree_full()),
            Ok(app(cst("Trust.Adt.demo_Tree"), cst("Trust.Param.@datatype::demo::Tree")))
        );
        // The enum carrier is PARAMETERIZED over exactly the recursion variable —
        // the recursive fields are genuine dependent constructor fields, so no
        // registered inductive ever embeds an untracked free const.
        let carrier = reflect_enum(&equivalent_adt).expect("the converted enum reflects");
        assert!(carrier.is_enum() && carrier.is_parameterized());
        assert_eq!(carrier.type_params, vec!["@datatype::demo::Tree".to_string()]);
        assert_eq!(carrier.constructors.len(), 2);
        assert_eq!(
            carrier.constructors[1].fields[0].1,
            cst("Trust.Param.@datatype::demo::Tree"),
            "a recursive field is carried by the bound recursion variable"
        );
    }

    #[test]
    fn reflect_ty_non_recursive_datatype_full_definition_is_the_concrete_enum_carrier() {
        // A datatype whose full definition has no back-references (its recursion
        // was through a sibling the compactor resolved away) is just a concrete
        // enum: the bare named inductive const, exactly as the `Ty::Adt` arm gives.
        let dt = Ty::Datatype {
            name: "demo::Flat".into(),
            variants: vec![
                ("A".into(), vec![("v".into(), Ty::Int { width: 32, signed: false })]),
                ("B".into(), vec![]),
            ],
        };
        assert_eq!(reflect_ty(&dt), Ok(cst("Trust.Adt.demo_Flat")));
    }

    #[test]
    fn reflect_contract_datatype_backref_binds_like_a_generic_param_and_grounds() {
        // fn f(x: &Tree⟲) -> Tree⟲ (both compacted, unresolvable): binds/returns at
        // ONE shared Pi-bound opaque type variable, exactly like `fn id<T>(x:T)->T`.
        // The contract type kernel-checks (GROUNDED); inhabitation of the opaque
        // return stays impossible by parametricity (fail-closed, never by fiat).
        let reft = Ty::Ref { mutable: false, inner: Box::new(tree_backref()) };
        let contract = reflect_contract(
            &[("x", &reft)],
            &Formula::Bool(true),
            "ret",
            &tree_backref(),
            &Formula::Bool(true),
        )
        .expect("a bare datatype back-reference binds at its opaque type variable");
        contract_is_a_type(&contract);
        // Exactly one outer Π(_ : Type) binder, shared by the param and the return.
        let mut depth = 0;
        let mut cur = &contract;
        while let ProofTerm::Pi { domain, codomain, .. } = cur {
            if **domain == ProofTerm::Sort(1) {
                depth += 1;
                cur = codomain;
            } else {
                break;
            }
        }
        assert_eq!(depth, 1, "one shared `Π(R : Type)` for the back-referenced datatype");
    }

    #[test]
    fn datatype_nested_in_composite_param_grounds_opaque_and_return_fails_closed() {
        // The census shape (`&Abstractor`/`&FoldMemo`): a STRUCT nesting both a full
        // datatype definition and a back-reference. PARAMETER position binds the
        // whole value at the fresh `Trust.Opaque.<p>` variable (sound
        // over-approximation — the contract GROUNDS); RETURN position fails closed
        // (an opaque return cannot be conjured — never inhabited by fiat).
        let holder = Ty::adt(
            "demo::Holder",
            vec![("memo".into(), tree_full()), ("r".into(), tree_backref())],
        );
        let contract = reflect_contract(
            &[("x", &holder)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("a datatype-nesting composite PARAM grounds via the opaque carrier");
        contract_is_a_type(&contract);
        assert!(
            matches!(
                reflect_contract(
                    &[("x", &i32())],
                    &Formula::Bool(true),
                    "ret",
                    &holder,
                    &Formula::Bool(true),
                ),
                Err(ReflectError::UnsupportedType(_))
            ),
            "a datatype-nesting composite RETURN fails closed"
        );
    }

    #[test]
    fn reflect_verifiable_function_pre_resolves_backrefs_against_the_defining_local() {
        use trust_types::{LocalDecl, VerifiableBody, VerifiableFunction};
        // fn f(x: &Tree) -> bool, where `x`'s dumped type is the COMPACTED by-name
        // back-reference and the FULL definition appears only at another local's
        // own declared type (the defining occurrence) — the dump's recursive-type
        // map. Pre-resolution must make this reflect IDENTICALLY to the same
        // function with the full definition at the parameter directly.
        let with_param_ty = |param_inner: Ty, extra_local: Option<Ty>| {
            let mut locals = vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: Some("_0".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(param_inner) },
                    name: Some("x".into()),
                },
            ];
            if let Some(t) = extra_local {
                locals.push(LocalDecl { index: 2, ty: t, name: None });
            }
            VerifiableFunction {
                name: "f".into(),
                def_path: "crate::f".into(),
                span: Default::default(),
                body: VerifiableBody { locals, blocks: vec![], arg_count: 1, return_ty: Ty::Bool },
                contracts: vec![],
                preconditions: vec![],
                postconditions: vec![],
                spec: Default::default(),
            }
        };
        let compacted = with_param_ty(tree_backref(), Some(tree_full()));
        let uncompacted = with_param_ty(tree_full(), None);
        let resolved =
            reflect_verifiable_function(&compacted).expect("a resolvable back-reference reflects");
        assert_eq!(
            Ok(&resolved),
            reflect_verifiable_function(&uncompacted).as_ref(),
            "pre-resolution: back-reference + defining local ≡ full definition at the param"
        );
        // With NO defining occurrence anywhere, the back-reference stays opaque —
        // still Ok (grounded), but the DIFFERENT, structureless type-variable term.
        let unresolvable = with_param_ty(tree_backref(), None);
        let opaque = reflect_verifiable_function(&unresolvable)
            .expect("an unresolvable back-reference still reflects (opaque, fail-closed)");
        assert_ne!(opaque, resolved, "unresolvable ⇒ opaque variable, not the unrolled enum");
    }

    #[test]
    fn resolve_datatype_backrefs_terminates_on_mutual_recursion() {
        use trust_types::{LocalDecl, VerifiableBody, VerifiableFunction};
        // A ↔ B mutual recursion: A's definition references B by name and vice
        // versa. The occurs-checked substitution must terminate (chain-bounded)
        // and the whole function must reflect.
        let a_ref = Ty::Datatype { name: "demo::A".into(), variants: vec![] };
        let b_ref = Ty::Datatype { name: "demo::B".into(), variants: vec![] };
        let a_full = Ty::Datatype {
            name: "demo::A".into(),
            variants: vec![("MkA".into(), vec![("b".into(), b_ref.clone())])],
        };
        let b_full = Ty::Datatype {
            name: "demo::B".into(),
            variants: vec![
                ("MkB".into(), vec![("a".into(), a_ref.clone())]),
                ("End".into(), vec![]),
            ],
        };
        let func = VerifiableFunction {
            name: "g".into(),
            def_path: "crate::g".into(),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: Some("_0".into()) },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: false, inner: Box::new(a_ref) },
                        name: Some("x".into()),
                    },
                    LocalDecl { index: 2, ty: a_full, name: None },
                    LocalDecl { index: 3, ty: b_full, name: None },
                ],
                blocks: vec![],
                arg_count: 1,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        let contract = reflect_verifiable_function(&func)
            .expect("mutually-recursive datatypes resolve, unroll one level, and reflect");
        contract_is_a_type(&contract);
    }

    #[test]
    fn datatype_definition_in_closure_call_resolves_fnptr_backref() {
        use trust_types::{ClosureCallKind, ClosureCallSig};

        let backref = Ty::Datatype { name: "call_dt::Node".into(), variants: vec![] };
        let full = Ty::Datatype {
            name: "call_dt::Node".into(),
            variants: vec![(
                "Mk".into(),
                vec![("value".into(), Ty::Int { width: 8, signed: false })],
            )],
        };
        let closure = Ty::Closure {
            name: "call_dt::closure".into(),
            upvars: vec![],
            call: Some(Box::new(ClosureCallSig {
                kind: ClosureCallKind::Fn,
                params: vec![full.clone()],
                ret: None,
            })),
        };
        let fnptr = Ty::FnPtr { sig: Box::new(FnSig { params: vec![], ret: Box::new(backref) }) };
        let expected =
            Ty::FnPtr { sig: Box::new(FnSig { params: vec![], ret: Box::new(full.clone()) }) };
        let func = wrap_probe_function("call_datatype", closure, fnptr.clone());

        let defs = collect_datatype_defs(&func.body);
        assert_eq!(
            defs.get("call_dt::Node"),
            match &full {
                Ty::Datatype { variants, .. } => Some(variants),
                _ => unreachable!(),
            }
        );
        assert_eq!(
            resolve_datatype_backrefs(&fnptr, &defs),
            expected,
            "a definition reachable only through Closure.call must resolve a back-reference reachable only through FnPtr",
        );
    }

    #[test]
    fn conflicting_datatypes_in_call_signatures_remain_ambiguous() {
        use trust_types::{ClosureCallKind, ClosureCallSig};

        let datatype = |field_ty| Ty::Datatype {
            name: "call_dt::Conflict".into(),
            variants: vec![("Mk".into(), vec![("value".into(), field_ty)])],
        };
        let closure = Ty::Closure {
            name: "call_dt::conflict_closure".into(),
            upvars: vec![],
            call: Some(Box::new(ClosureCallSig {
                kind: ClosureCallKind::FnMut,
                params: vec![datatype(Ty::Bool)],
                ret: None,
            })),
        };
        let fnptr = Ty::FnPtr {
            sig: Box::new(FnSig {
                params: vec![datatype(Ty::Int { width: 8, signed: false })],
                ret: Box::new(Ty::Unit),
            }),
        };
        let func = wrap_probe_function("call_datatype_conflict", closure, fnptr);

        assert!(
            !collect_datatype_defs(&func.body).contains_key("call_dt::Conflict"),
            "conflicting full definitions reached through call signatures must be removed",
        );
        assert!(
            ambiguous_adt_names(&func).contains("Trust.Adt.call_dt_Conflict"),
            "the ambiguity scan must traverse Closure.call and function signatures",
        );
    }

    // --- ARITY-CONSISTENCY (M6 rung-5 successor item 1, "PI-ARITY") ----------

    /// PROBE (arity-consistency): a named struct whose STRUCTURAL SHAPE
    /// disagrees between two occurrences reachable from one function's own
    /// locals (`demo::Wrap`'s `x` field is a lone back-reference at one
    /// occurrence, but a SECOND field `y` joins it at another) is detected as
    /// AMBIGUOUS, and every occurrence collapses to the SAME opaque, Pi-bound
    /// `Trust.Param.@datatype::demo::Wrap` type variable — never a named
    /// inductive whose arity a caller (the contract vs.
    /// `clean_ground::reachable_adt_carriers`) could disagree about. This is
    /// the exact class of real-code bug the fix retires: the M6 census's
    /// `FoldMemo::get` registered `Trust.Adt.expr_Expr` with ONE `type_params`
    /// entry from one local's shape while the `expr` parameter's OWN
    /// occurrence computed FIVE, and the real kernel correctly rejected the
    /// resulting arity mismatch (`NotAFunction`) — see
    /// `reports/m6-datatype-reflect-validate-2026-07-10.md`'s successor item 1.
    #[test]
    fn ambiguous_adt_names_detects_shape_disagreement_across_locals() {
        let wrap_1param = Ty::adt(
            "demo::Wrap",
            vec![("x".into(), Ty::Datatype { name: "demo::Rec".into(), variants: vec![] })],
        );
        let wrap_2param = Ty::adt(
            "demo::Wrap",
            vec![
                ("x".into(), Ty::Datatype { name: "demo::Rec".into(), variants: vec![] }),
                ("y".into(), Ty::Datatype { name: "demo::Other".into(), variants: vec![] }),
            ],
        );
        let func = wrap_probe_function("f", wrap_1param.clone(), wrap_2param.clone());
        let ambiguous = ambiguous_adt_names(&func);
        assert!(
            ambiguous.contains("Trust.Adt.demo_Wrap"),
            "two differently-shaped occurrences of demo::Wrap must be flagged \
             ambiguous: {ambiguous:?}"
        );
        // Both occurrences collapse to the SAME opaque back-reference —
        // structurally IDENTICAL regardless of which occurrence is collapsed.
        let collapsed_1 = collapse_ambiguous_tys(&wrap_1param, &ambiguous);
        let collapsed_2 = collapse_ambiguous_tys(&wrap_2param, &ambiguous);
        assert_eq!(collapsed_1, collapsed_2);
        assert_eq!(collapsed_1, Ty::Datatype { name: "demo::Wrap".into(), variants: vec![] });
    }

    /// SF-2 regression (2026-07-13 adversarial-verify findings): the rung-E
    /// compaction order must match by CANONICAL IDENTITY, never by name
    /// alone. An empty-variant `Ty::Datatype` compaction leaf carries only a
    /// generics-erased def-path name — two DISTINCT concrete types can share
    /// it (two instantiations of one generic ADT) — so a leaf must NOT
    /// compact-match a fuller spelling of the same name (fail-closed), while
    /// an IDENTICAL leaf still matches itself (the equality fast path).
    #[test]
    fn sf2_compaction_leaf_never_name_matches_a_fuller_spelling() {
        let leaf = Ty::Datatype { name: "demo::P".into(), variants: vec![] };
        let rich_adt = Ty::adt("demo::P", vec![("v".into(), Ty::Int { width: 32, signed: false })]);
        let rich_datatype = Ty::Datatype {
            name: "demo::P".into(),
            variants: vec![(
                "MkP".into(),
                vec![("v".into(), Ty::Int { width: 64, signed: false })],
            )],
        };
        assert!(
            !ty_is_compaction_of(&leaf, &rich_adt),
            "SF-2: an identity-less leaf must never name-match a fuller Adt spelling"
        );
        assert!(
            !ty_is_compaction_of(&leaf, &rich_datatype),
            "SF-2: an identity-less leaf must never name-match a full Datatype definition"
        );
        assert!(
            !ty_is_compaction_of(&rich_adt, &leaf) && !ty_is_compaction_of(&rich_datatype, &leaf),
            "SF-2: the reverse direction must fail closed too"
        );
        // Byte-identical spellings are trivially the same type.
        assert!(ty_is_compaction_of(&leaf, &leaf.clone()));
    }

    /// SF-2 regression, end-to-end: two occurrences of `demo::W` that differ
    /// by an erased-identity compaction leaf (field `p` a bare back-reference
    /// in one, a full `demo::P` spelling in the other — in the wild these can
    /// be two DIFFERENT concrete types behind one generics-erased name) must
    /// be INCOMPARABLE: no compaction def is kept for `demo::W`, the poor
    /// occurrence is NOT rewritten to the rich shape (the pre-fix behavior —
    /// fabricating a shape the occurrence never carried), and the name falls
    /// to the fail-closed ambiguous collapse exactly as pre-rung-E.
    #[test]
    fn sf2_two_distinct_types_sharing_a_name_must_not_compact_match() {
        let w_poor = Ty::adt(
            "demo::W",
            vec![("p".into(), Ty::Datatype { name: "demo::P".into(), variants: vec![] })],
        );
        let w_rich = Ty::adt(
            "demo::W",
            vec![(
                "p".into(),
                Ty::adt("demo::P", vec![("v".into(), Ty::Int { width: 64, signed: false })]),
            )],
        );
        assert!(
            !ty_is_compaction_of(&w_poor, &w_rich) && !ty_is_compaction_of(&w_rich, &w_poor),
            "SF-2: spellings differing by an identity-less leaf must be incomparable"
        );
        let func = wrap_probe_function("sf2_probe", w_poor.clone(), w_rich.clone());
        let defs = collect_adt_compaction_defs(&func.body);
        assert!(
            !defs.contains_key("demo::W"),
            "SF-2: incomparable spellings must remove the name from the defs map \
             (fail-closed), got {defs:?}"
        );
        // No fabricated structure: the poor occurrence keeps its own shape.
        assert_eq!(resolve_adt_compaction(&w_poor, &defs), w_poor);
        // And the name lands in the pre-rung-E fail-closed ambiguous collapse:
        // BOTH occurrences at the same opaque back-reference.
        let ambiguous = ambiguous_adt_names(&func);
        assert!(
            ambiguous.contains("Trust.Adt.demo_W"),
            "SF-2: compaction-shaped disagreement must fall back to the \
             ambiguous-name collapse: {ambiguous:?}"
        );
        assert_eq!(
            collapse_ambiguous_tys(&w_poor, &ambiguous),
            Ty::Datatype { name: "demo::W".into(), variants: vec![] }
        );
        assert_eq!(
            collapse_ambiguous_tys(&w_rich, &ambiguous),
            Ty::Datatype { name: "demo::W".into(), variants: vec![] }
        );
    }

    /// PROBE (arity-consistency, end-to-end): the SAME ambiguous-shape
    /// scenario, run through the full `reflect_verifiable_function` +
    /// `clean_ground::inhabit_verifiable_function` pipeline. Before this fix,
    /// this exact shape (a DIFFERENT-arity occurrence of a named struct
    /// winning `reachable_adt_carriers`'s first-registration race than the
    /// one the parameter's own contract carrier used) reached the real
    /// kernel's `check_type` as an arity mismatch — `KernelRejected
    /// ("NotAFunction …")`. After the fix, the ambiguous name collapses to
    /// the opaque back-reference on BOTH sides (contract + registration), so
    /// they can never disagree: the function GROUNDS cleanly (never
    /// `KernelRejected`) and — since its return is the untouched trivial
    /// `bool`, unrelated to the ambiguous parameter — still INHABITS.
    #[test]
    fn ambiguous_adt_shape_never_reaches_kernel_rejected_and_bool_return_still_inhabits() {
        use trust_types::{
            BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        use crate::clean_ground::{InhabitOutcome, inhabit_verifiable_function};
        let wrap_1param = Ty::adt(
            "demo::Wrap2",
            vec![("x".into(), Ty::Datatype { name: "demo::Rec2".into(), variants: vec![] })],
        );
        let wrap_2param = Ty::adt(
            "demo::Wrap2",
            vec![
                ("x".into(), Ty::Datatype { name: "demo::Rec2".into(), variants: vec![] }),
                ("y".into(), Ty::Datatype { name: "demo::Other2".into(), variants: vec![] }),
            ],
        );
        let mut func = wrap_probe_function("f2", wrap_1param.clone(), wrap_2param);
        // Keep this end-to-end probe a valid Trust MIR function. The historical
        // scaffold deliberately put a Wrap carrier in `_0` while declaring a Bool
        // return; certificate-boundary validation now (correctly) rejects that
        // mismatch before reflection. Carry the competing Wrap spelling in an
        // otherwise-unused temp and make the actual return a typed Bool constant.
        func.body.locals[0].ty = Ty::Bool;
        func.body.locals.push(LocalDecl {
            index: 2,
            ty: wrap_1param,
            name: Some("alternate_wrap_shape".into()),
        });
        func.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
                span: Default::default(),
            }],
            terminator: Terminator::Return,
        }];
        assert!(trust_vcgen::validate_function(&func).is_ok());
        assert!(crate::assignment_types::all_assignments_match(&func.body));
        let outcome = inhabit_verifiable_function(&func);
        assert!(
            !matches!(outcome, InhabitOutcome::KernelRejected(_)),
            "PROBE: an ambiguous-shape struct parameter must never reach a \
             kernel arity-mismatch rejection after collapsing to the opaque \
             back-reference: {outcome:?}"
        );
        assert_eq!(
            outcome,
            InhabitOutcome::Inhabited,
            "the untouched trivial bool return still inhabits: {outcome:?}"
        );
    }

    #[test]
    fn unique_visible_shape_does_not_authorize_identity_erased_leaf() {
        let leaf_ref = Ty::Datatype { name: "collision::Leaf".into(), variants: vec![] };
        let leaf_u32 = Ty::adt(
            "collision::Leaf",
            vec![("value".into(), Ty::Int { width: 32, signed: false })],
        );
        let compact = Ty::adt("collision::Outer", vec![("leaf".into(), leaf_ref)]);
        let rich = Ty::adt("collision::Outer", vec![("leaf".into(), leaf_u32)]);
        let func = wrap_probe_function("unique_shape", rich, compact.clone());

        let defs = collect_adt_compaction_defs(&func.body);
        assert!(
            !defs.contains_key("collision::Outer"),
            "even one visible same-path shape cannot recover the erased instantiation"
        );
        assert_eq!(resolve_adt_compaction(&compact, &defs), compact);
        assert!(ambiguous_adt_names(&func).contains("Trust.Adt.collision_Outer"));
    }

    #[test]
    fn array_nested_compaction_mismatch_is_discovered_and_fails_closed() {
        let leaf_ref = Ty::Datatype { name: "array::Leaf".into(), variants: vec![] };
        let leaf_full =
            Ty::adt("array::Leaf", vec![("value".into(), Ty::Int { width: 16, signed: false })]);
        let compact = Ty::adt("array::Outer", vec![("leaf".into(), leaf_ref)]);
        let rich = Ty::adt("array::Outer", vec![("leaf".into(), leaf_full)]);
        let compact_array = Ty::Array { elem: Box::new(compact), len: 4 };
        let func = wrap_probe_function("array_compaction", rich, compact_array.clone());

        let defs = collect_adt_compaction_defs(&func.body);
        assert!(
            !defs.contains_key("array::Outer"),
            "the collector must discover the incompatible occurrence through Array"
        );
        assert_eq!(resolve_adt_compaction(&compact_array, &defs), compact_array);
        assert!(ambiguous_adt_names(&func).contains("Trust.Adt.array_Outer"));
    }

    #[test]
    fn nested_identity_erased_mismatches_terminate_unchanged() {
        let leaf_ref = Ty::Datatype { name: "nested::Leaf".into(), variants: vec![] };
        let leaf_full =
            Ty::adt("nested::Leaf", vec![("value".into(), Ty::Int { width: 8, signed: false })]);
        let middle_ref = Ty::Datatype { name: "nested::Middle".into(), variants: vec![] };
        let middle_compact = Ty::adt("nested::Middle", vec![("leaf".into(), leaf_ref)]);
        let middle_rich = Ty::adt("nested::Middle", vec![("leaf".into(), leaf_full)]);
        let outer_compact = Ty::adt("nested::Outer", vec![("middle".into(), middle_ref)]);
        let outer_partly_rich = Ty::adt("nested::Outer", vec![("middle".into(), middle_compact)]);
        let mut func = wrap_probe_function(
            "nested_compaction_fail_closed",
            outer_partly_rich,
            outer_compact.clone(),
        );
        func.body.locals.push(trust_types::LocalDecl { index: 2, ty: middle_rich, name: None });

        let defs = collect_adt_compaction_defs(&func.body);
        assert!(!defs.contains_key("nested::Outer"));
        assert!(!defs.contains_key("nested::Middle"));
        assert_eq!(resolve_adt_compaction(&outer_compact, &defs), outer_compact);
    }

    #[test]
    fn closure_call_signature_compaction_mismatch_is_discovered_and_fails_closed() {
        use trust_types::{ClosureCallKind, ClosureCallSig};

        let leaf_ref = Ty::Datatype { name: "call::Leaf".into(), variants: vec![] };
        let leaf_full =
            Ty::adt("call::Leaf", vec![("value".into(), Ty::Int { width: 32, signed: false })]);
        let compact = Ty::adt("call::Outer", vec![("leaf".into(), leaf_ref)]);
        let rich = Ty::adt("call::Outer", vec![("leaf".into(), leaf_full)]);
        let closure = |param| Ty::Closure {
            name: "call::closure".into(),
            upvars: vec![],
            call: Some(Box::new(ClosureCallSig {
                kind: ClosureCallKind::Fn,
                params: vec![param],
                ret: Some(Ty::Bool),
            })),
        };
        let compact_closure = closure(compact);
        let func =
            wrap_probe_function("closure_call_compaction", closure(rich), compact_closure.clone());

        let defs = collect_adt_compaction_defs(&func.body);
        assert!(
            !defs.contains_key("call::Outer"),
            "the collector must discover incompatible ADTs present only in Closure.call"
        );
        assert_eq!(resolve_adt_compaction(&compact_closure, &defs), compact_closure);
        assert!(ambiguous_adt_names(&func).contains("Trust.Adt.call_Outer"));
    }

    #[test]
    fn function_signature_full_shape_conflict_is_discovered() {
        use trust_types::{ClosureCallKind, ClosureCallSig, LocalDecl};

        let outer_u32 = Ty::adt(
            "call_conflict::Outer",
            vec![("value".into(), Ty::Int { width: 32, signed: false })],
        );
        let outer_bool = Ty::adt("call_conflict::Outer", vec![("value".into(), Ty::Bool)]);
        let closure = |param| Ty::Closure {
            name: "call_conflict::closure".into(),
            upvars: vec![],
            call: Some(Box::new(ClosureCallSig {
                kind: ClosureCallKind::FnOnce,
                params: vec![param],
                ret: None,
            })),
        };
        let closure_u32 = closure(outer_u32.clone());
        let mut func =
            wrap_probe_function("closure_call_conflict", closure_u32.clone(), closure_u32.clone());
        assert!(
            collect_adt_compaction_defs(&func.body).contains_key("call_conflict::Outer"),
            "identical full spellings reached through Closure.call are consistent"
        );
        func.body.locals.push(LocalDecl {
            index: 2,
            ty: Ty::FnPtr {
                sig: Box::new(FnSig { params: vec![outer_bool], ret: Box::new(Ty::Unit) }),
            },
            name: None,
        });

        let defs = collect_adt_compaction_defs(&func.body);
        assert!(
            !defs.contains_key("call_conflict::Outer"),
            "an incompatible full spelling reachable only through FnPtr must remove the name"
        );
        assert_eq!(resolve_adt_compaction(&closure_u32, &defs), closure_u32);
        assert!(ambiguous_adt_names(&func).contains("Trust.Adt.call_conflict_Outer"));
    }

    #[test]
    fn same_path_incompatible_full_shapes_remain_ambiguous() {
        let leaf_u32 = Ty::adt(
            "collision::Leaf",
            vec![("value".into(), Ty::Int { width: 32, signed: false })],
        );
        let leaf_bool = Ty::adt("collision::Leaf", vec![("value".into(), Ty::Bool)]);
        let func = wrap_probe_function("shape_collision", leaf_u32, leaf_bool);

        let defs = collect_adt_compaction_defs(&func.body);
        assert!(
            !defs.contains_key("collision::Leaf"),
            "same path with incompatible full shapes must remain fail-closed"
        );
        assert!(
            ambiguous_adt_names(&func).contains("Trust.Adt.collision_Leaf"),
            "full-shape disagreement must reach the existing ambiguity lane"
        );
    }

    /// Shared scaffold for the two ambiguous-shape probes above: a function
    /// whose return SLOT (local 0 — walked FIRST by
    /// `clean_ground::reachable_adt_carriers`, so it is what WOULD win a
    /// first-registration race) carries `local0_ty`'s shape of `demo::Wrap*`,
    /// and whose ACTUAL (sole) parameter carries `param_ty`'s DIFFERENT
    /// shape of the SAME name — reproducing the real dumps' "the contract's
    /// own parameter occurrence differs from whichever occurrence
    /// `reachable_adt_carriers` registers first" shape. `return_ty` is
    /// independently `Bool` (unaffected by the ambiguous struct), isolating
    /// the parameter-side disagreement.
    fn wrap_probe_function(
        name: &str,
        local0_ty: Ty,
        param_ty: Ty,
    ) -> trust_types::VerifiableFunction {
        use trust_types::{LocalDecl, VerifiableBody, VerifiableFunction};
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("crate::{name}"),
            span: Default::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: local0_ty, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: param_ty, name: Some("a".into()) },
                ],
                blocks: vec![],
                arg_count: 1,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn reflect_contract_composite_with_param_in_param_position_grounds_structurally() {
        // RECURSIVE DEPENDENT CARRIER (goal bullet 2 tail) — fn k<T>(x: (T, u8)) -> i32:
        // a `(T, u8)` tuple parameter now binds STRUCTURALLY at the PARAMETERIZED
        // product carrier `Prod (Param T) (BitVec 8)` (decoded by `clean_ground` to the
        // kernel `Prod T Int`), NOT the opaque `Trust.Opaque.x` over-approximation it
        // used before. The contract is `Π(T : Type) → Π(x : Prod (Var T) (BitVec 8)) →
        // Π(_ : True) → Sigma Int …`. (As with the slice-of-T case, this binding carrier
        // is universe-correct only in the REAL kernel where `Prod` takes a `Type` arg —
        // the modulo-3 kernel proof lives in clean_ground::tests; here we assert the
        // STRUCTURAL TERM SHAPE.)
        let composite = Ty::Tuple(vec![param_ty("T/#0"), Ty::Int { width: 8, signed: false }]);
        let contract = reflect_contract(
            &[("x", &composite)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("(T, u8) reflects via the parameterized product carrier");
        // Outer Π binds the type var `T` at `Type` (Sort 1).
        let ProofTerm::Pi { domain: outer_dom, codomain, .. } = &contract else {
            panic!("expected outer Π(T:Type), got {contract:?}");
        };
        assert_eq!(**outer_dom, ProofTerm::Sort(1), "outer binder is Π(T : Type)");
        // The `x` parameter binds at the parameterized product carrier
        // `Prod (Var 0) (BitVec 8)` (the bound `T` and the concrete `u8`), NOT a
        // `Trust.Opaque.*` type variable.
        let ProofTerm::Pi { domain: x_dom, .. } = &**codomain else {
            panic!("expected Π(x : …), got {codomain:?}");
        };
        let expected = app(
            app(cst(CARRIER_PROD), ProofTerm::Var(0)),
            app(app(cst(CARRIER_PROD), reflect_bitvec(8)), cst(CARRIER_UNIT)),
        );
        assert_eq!(
            **x_dom, expected,
            "x binds at Prod (Var T) (Prod (BitVec 8) Unit), the parameterized product carrier"
        );
        assert!(
            !code_mentions_opaque(x_dom),
            "the (T, u8) parameter must NOT fall to the opaque Trust.Opaque carrier"
        );
    }

    #[test]
    fn reflect_contract_composite_with_param_in_return_position_grounds_structurally() {
        // RECURSIVE DEPENDENT CARRIER (goal bullet 2 tail) — fn k<T>(x: i32) -> (T, u8):
        // a `(T, u8)` RETURN now binds STRUCTURALLY at the parameterized product carrier
        // `Prod (Param T) (BitVec 8)` (was fail-closed before, because the opaque
        // over-approximation is uninhabitable in return position). The contract TYPE
        // now BUILDS (the `Sigma` return carrier is the real `Prod (Var T) …`), with the
        // type var Pi-bound outermost. (Inhabitation — conjuring a `(T, u8)` value — is a
        // separate concern handled in clean_ground; here the TYPE grounds structurally.)
        let composite = Ty::Tuple(vec![param_ty("T/#0"), Ty::Int { width: 8, signed: false }]);
        let contract = reflect_contract(
            &[("x", &i32())],
            &Formula::Bool(true),
            "ret",
            &composite,
            &Formula::Bool(true),
        )
        .expect("a (T, u8) RETURN now grounds via the parameterized product carrier");
        // Outer Π binds the return's type var `T` at `Type` (Sort 1).
        let ProofTerm::Pi { domain: outer_dom, .. } = &contract else {
            panic!("expected outer Π(T:Type), got {contract:?}");
        };
        assert_eq!(**outer_dom, ProofTerm::Sort(1), "outer binder is Π(T : Type)");
        // The return carrier `Prod (Var T) …` occurs as the Sigma's type argument —
        // NOT the opaque carrier.
        assert!(
            !code_mentions_opaque(&contract),
            "the (T, u8) return must NOT fall to the opaque Trust.Opaque carrier"
        );
        // And the contract actually mentions the structural Prod carrier.
        assert!(
            free_type_var_consts(&contract).is_empty(),
            "the T param const is abstracted into the outer binder (none left free)"
        );
    }

    #[test]
    fn reflect_contract_non_integer_param_decodes_through_el() {
        // fn(b: bool) requires true ensures true -> i32  — b binds at El(R bool).
        let contract = reflect_contract(
            &[("b", &Ty::Bool)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("contract over a bool param should reflect via El");
        contract_is_a_type(&contract);
    }

    #[test]
    fn reflect_contract_struct_param_decodes_through_el() {
        // fn(p: Point) requires true ensures true -> i32  — p binds at El(Prod …).
        let point = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Point".into(),
            fields: vec![("x".into(), i32()), ("y".into(), i32())],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let contract = reflect_contract(
            &[("p", &point)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("contract over a struct param should reflect via El");
        contract_is_a_type(&contract);
    }

    #[test]
    fn reflect_contract_non_reflectable_param_fails_closed() {
        // A still-non-reflectable (never) parameter fails closed.
        let r = reflect_contract(
            &[("r", &Ty::Never)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        );
        assert!(matches!(r, Err(ReflectError::NeverType(_))));
    }

    /// GOAL-ITEM #3 — a contract over a FLOAT parameter now reflects (the float binds
    /// at `El (Prod …)` over its structured IEEE carrier), no longer fail-closed.
    #[test]
    fn reflect_contract_float_param_reflects_structurally() {
        let r = reflect_contract(
            &[("f", &Ty::Float { width: 32 })],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("a contract over a float param now reflects via El over the structured carrier");
        contract_is_a_type(&r);
    }

    #[test]
    fn reflect_contract_int_predicate_over_el_param_is_kernel_rejected() {
        // Honest limitation: using a non-integer (El-bound) param as an integer
        // operand builds a term the KERNEL rejects (fails closed at the boundary).
        let pre = Formula::Gt(Box::new(ivar("b")), Box::new(Formula::Int(0)));
        let contract =
            reflect_contract(&[("b", &Ty::Bool)], &pre, "ret", &i32(), &Formula::Bool(true))
                .expect("builds a term");
        // It is NOT a well-formed type: infer_type rejects the El/Int mismatch.
        assert!(infer_type(&contract, &carrier_context(), &[]).is_err());
    }

    #[test]
    fn reflect_contract_postcondition_actually_binds_return_and_param() {
        // Verify the postcondition references BOTH ret (Var 0) and x (Var 2)
        // by checking the structure resolves; if de-Bruijn were wrong, the
        // kernel check in contract_is_a_type would reject it.
        let post = Formula::Eq(
            Box::new(ivar("ret")),
            Box::new(Formula::Add(Box::new(ivar("x")), Box::new(Formula::Int(1)))),
        );
        let contract =
            reflect_contract(&[("x", &i32())], &Formula::Bool(true), "ret", &i32(), &post)
                .expect("contract with ret = x + 1");
        contract_is_a_type(&contract);
    }

    // --- trait objects (Ty::Dynamic) --------------------------------------

    #[test]
    fn reflect_ty_dynamic_is_closed_existential_const() {
        // `dyn Trait` reflects as the CLOSED existential dependent-type const
        // `Trust.Dyn.<trait>` — a REGISTERED type (`Sigma (T:Type), Vtable_<trait> T`),
        // NOT a free opaque type variable. The trait path is SANITIZED into a single
        // kernel-legal `Name` segment (so `core::fmt::Write` → `Trust.Dyn.core_fmt_Write`,
        // NOT raw `::`). Stable per-trait (the same trait shares the const; distinct
        // traits differ).
        assert_eq!(
            reflect_ty(&Ty::Dynamic { trait_name: "core::fmt::Write".into() }),
            Ok(cst("Trust.Dyn.core_fmt_Write"))
        );
        assert_eq!(
            reflect_ty(&Ty::Dynamic { trait_name: "core::fmt::Write".into() }),
            reflect_ty(&Ty::Dynamic { trait_name: "core::fmt::Write".into() })
        );
        assert_ne!(
            reflect_ty(&Ty::Dynamic { trait_name: "core::fmt::Write".into() }),
            reflect_ty(&Ty::Dynamic { trait_name: "core::hash::Hasher".into() })
        );
    }

    #[test]
    fn reflect_dyn_builds_existential_carrier_minimal_vtable() {
        // `reflect_dyn` for a trait with NO known method signatures (the only case the
        // current extractor supplies) builds the BEST sound minimal existential: the
        // `Trust.Dyn.<trait>` name + a FIELD-LESS vtable record `Trust.Dyn.Vtable.<trait>`
        // (`Sigma Type Unit` shape — an existential over an opaque-but-quantified carrier).
        let carrier = reflect_dyn("core::fmt::Write", &[]);
        assert_eq!(carrier.name, "Trust.Dyn.core_fmt_Write");
        assert_eq!(carrier.vtable_name, "Trust.Dyn.Vtable.core_fmt_Write");
        assert_eq!(carrier.vtable_ctor_name, "Trust.Dyn.Vtable.core_fmt_Write.mk");
        assert!(!carrier.has_methods(), "no extractor method info → field-less vtable record");
        // The existential name is exactly what `reflect_ty(dyn)` / `dyn_const_name` use,
        // so a `dyn`-typed value and its registered existential agree.
        assert_eq!(
            reflect_ty(&Ty::Dynamic { trait_name: "core::fmt::Write".into() }),
            Ok(cst(&carrier.name))
        );
    }

    #[test]
    fn reflect_contract_dyn_param_binds_at_closed_existential_no_outer_binder() {
        // fn use_writer(w: dyn Write) requires true ensures true -> i32 becomes
        // Π(w : Trust.Dyn.Write) → Π(_:True) → Sigma Int (λ.True). The trait object
        // binds DIRECTLY at the CLOSED existential dependent type `Trust.Dyn.Write`
        // (`Sigma (T:Type), Vtable_Write T`) — NOT a universally-abstracted `Π(D:Type)`
        // variable. So the FIRST binder is the value param `w` itself, at the
        // existential const, and there is NO outer type-variable binder.
        let dyn_write = Ty::Dynamic { trait_name: "Write".into() };
        let contract = reflect_contract(
            &[("w", &dyn_write)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("a dyn-Trait value parameter reflects as a closed existential binding");
        match &contract {
            ProofTerm::Pi { domain, .. } => {
                assert_eq!(
                    **domain,
                    cst("Trust.Dyn.Write"),
                    "the first binder is the value param `w` at the closed existential"
                );
            }
            other => panic!("expected outer Π(w : Trust.Dyn.Write), got {other:?}"),
        }
        // NO universal type-variable binder is collected for the trait object.
        assert!(
            free_type_var_consts(&contract).is_empty(),
            "a closed-existential `dyn` is NOT a universal type variable — no outer Π(D:Type)"
        );
    }

    #[test]
    fn reflect_contract_ref_mut_dyn_is_transparent_and_binds_at_same_existential() {
        // fn f(w: &mut dyn Write) -> i32 — a reference to a trait object is
        // transparent for type reflection (the common `core::fmt` shape), so `w`
        // binds at the SAME closed existential `Trust.Dyn.Write` as a bare `dyn`,
        // with NO outer type-variable binder.
        let ref_mut_dyn =
            Ty::Ref { mutable: true, inner: Box::new(Ty::Dynamic { trait_name: "Write".into() }) };
        let contract = reflect_contract(
            &[("w", &ref_mut_dyn)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("&mut dyn Write reflects at the closed existential");
        match &contract {
            ProofTerm::Pi { domain, .. } => {
                assert_eq!(**domain, cst("Trust.Dyn.Write"), "binds at the same existential");
            }
            other => panic!("expected an outer Π(w : Trust.Dyn.Write), got {other:?}"),
        }
        assert!(free_type_var_consts(&contract).is_empty(), "no outer type-variable binder");
    }

    #[test]
    fn reflect_contract_two_same_dyn_params_share_one_existential() {
        // fn g(a: dyn Write, b: dyn Write) -> i32 : two `dyn Write` parameters BOTH bind
        // at the SAME closed existential `Trust.Dyn.Write` (keyed by trait path), and
        // NEITHER introduces a universal type-variable binder.
        let dw = || Ty::Dynamic { trait_name: "Write".into() };
        let a = dw();
        let b = dw();
        let contract = reflect_contract(
            &[("a", &a), ("b", &b)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("two dyn Write params reflect");
        assert!(
            free_type_var_consts(&contract).is_empty(),
            "a closed-existential `dyn` introduces NO universal Π(D:Type) binder"
        );
        // Both value binders are at the same existential const (the two outermost Πs).
        match &contract {
            ProofTerm::Pi { domain: d1, codomain, .. } => {
                assert_eq!(**d1, cst("Trust.Dyn.Write"));
                match &**codomain {
                    ProofTerm::Pi { domain: d2, .. } => assert_eq!(**d2, cst("Trust.Dyn.Write")),
                    other => panic!("expected inner Π(b : Trust.Dyn.Write), got {other:?}"),
                }
            }
            other => panic!("expected outer Π(a : Trust.Dyn.Write), got {other:?}"),
        }
    }

    // --- type variables nested in composites (case 3) ----------------------

    #[test]
    fn reflect_contract_struct_param_nesting_dyn_grounds_via_sink_shim() {
        // COVERAGE-AGENDA #4 — fn fmt(f: Formatter{ inner: &mut dyn Write }) -> i32:
        // the `dyn` writer sink is nested inside a struct field (the real
        // `core::fmt::Formatter` shape). With the opaque-sink SHIM the `dyn` field
        // collapses to the concrete `Trust.Sort.Sink` code, so `f` binds at the REAL
        // `Trust.SortTy` carrier `El (Prod Sink Unit)` — NOT the whole-parameter opaque
        // `Trust.Opaque.f : Type` over-approximation, and NOT a `Sort 1` type variable.
        // The contract has NO outer type-variable binder (the `dyn` no longer poisons
        // grounding) and the FIRST binder is the value param `f` at the `El`-decoded
        // product. The contract kernel-checks (the `Trust.Sort.Sink` code is declared).
        let formatter = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "core::fmt::Formatter".into(),
            fields: vec![(
                "inner".into(),
                Ty::Ref {
                    mutable: true,
                    inner: Box::new(Ty::Dynamic { trait_name: "Write".into() }),
                },
            )],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let contract = reflect_contract(
            &[("f", &formatter)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("a struct param nesting dyn grounds via the Sink shim");
        contract_is_a_type(&contract);
        // The Formatter param now binds at `El (Prod Sink Unit)` — a concrete SortTy
        // code — and there is NO opaque `Π(_ : Type)` wrapper (the dyn stopped
        // poisoning grounding). The first binder's domain is the `El`-decoded product.
        let expected_domain =
            app(cst(CARRIER_EL), app(app(cst(CARRIER_PROD), cst(CARRIER_SINK)), cst(CARRIER_UNIT)));
        match &contract {
            ProofTerm::Pi { binder_name, domain, .. } => {
                assert_eq!(
                    binder_name, "f",
                    "the first binder is the value param f, not a type var"
                );
                assert_eq!(
                    **domain, expected_domain,
                    "f binds at El (Prod Sink Unit) via the Sink shim"
                );
                assert_ne!(**domain, ProofTerm::Sort(1), "no opaque Sort-1 type-var binder");
            }
            other => panic!("expected Π(f : El (Prod Sink Unit)), got {other:?}"),
        }
    }

    #[test]
    fn formatter_struct_reflects_to_named_inductive_with_sink_field() {
        // COVERAGE-AGENDA #4 — the real `core::fmt::Formatter { options:
        // FormattingOptions, buf: &mut dyn Write }` shape now REGISTERS as a named
        // inductive (it previously fell back to `Prod` on the `dyn` field). The `buf`
        // field's carrier is the concrete `Trust.Sort.Sink` opaque-atom code; the
        // concrete `options` field reflects ordinarily. So `reflect_struct` returns
        // `Some` (a real `Trust.Adt.<…>` inductive), NOT `None`.
        let options = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "core::fmt::FormattingOptions".into(),
            fields: vec![("flags".into(), Ty::Int { width: 32, signed: false })],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let formatter = Ty::Adt { adt_kind: None, layout: None,
            variants: Vec::new(),
            name: "core::fmt::Formatter".into(),
            fields: vec![
                ("options".into(), options),
                (
                    "buf".into(),
                    Ty::Ref {
                        mutable: true,
                        inner: Box::new(Ty::Dynamic { trait_name: "core::fmt::Write".into() }),
                    },
                ),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let carrier = reflect_struct(&formatter)
            .expect("Formatter now registers as a named inductive via the Sink shim");
        // The `buf` field's carrier is the abstract Sink code; the struct is NOT
        // generic (the existential `dyn` is collapsed, not Pi-bound).
        assert!(carrier.type_params.is_empty(), "the dyn field is NOT a generic type param");
        let buf = carrier.fields.iter().find(|(n, _)| n == "buf").expect("buf field present");
        assert_eq!(buf.1, cst(CARRIER_SINK), "buf field is the Trust.Sort.Sink opaque-atom code");
        // A BARE `dyn` parameter (NOT nested in a struct field) reflects to the CLOSED
        // existential const `Trust.Dyn.<trait>` (sanitized) — the Sink shim only
        // collapses a `dyn` FIELD, never a standalone `dyn` value.
        assert_eq!(
            reflect_ty(&Ty::Dynamic { trait_name: "core::fmt::Write".into() }),
            Ok(cst("Trust.Dyn.core_fmt_Write")),
            "a bare dyn parameter reflects to the closed existential const (sanitized)"
        );
        // And the reflected sink carrier is the dedicated nullary opaque inductive.
        let sink = reflect_sink();
        assert_eq!(sink.name, SINK_INDUCTIVE);
        assert!(sink.fields.is_empty(), "Trust.Sink is a structureless atom (no fields)");
    }

    #[test]
    fn reflect_contract_slice_of_generic_param_grounds_structurally() {
        // PARAMETERIZED SEQUENCE CARRIER (goal bullet 2, COMPOSITE case) — fn s<T>(xs:
        // &[T]) -> i32 : `&[T]` reflects to `Slice (Param T)`, and the `xs` parameter
        // now binds STRUCTURALLY at that PARAMETERIZED sequence carrier (NOT the
        // opaque `Trust.Opaque.xs` over-approximation it used before). The contract is
        // `Π(T : Type) → Π(xs : Slice (Var T)) → Π(_ : True) → Sigma Int …`, which
        // `clean_ground` decodes to `List T` and proves modulo 3 in the REAL kernel
        // (see `clean_ground::tests::generic_vec_param_grounds_over_parameterized…`).
        //
        // NOTE: the binding carrier `Slice (Var T)` is universe-correct only in the
        // REAL kernel (where it decodes to `List T`), NOT in the LOCAL predicative
        // `carrier_context()` checker (where `Slice : SortTy → SortTy` rejects a
        // `Sort 1` element) — exactly like a generic-struct parameter's
        // `Trust.Adt.Wrapper (Param T)` binding. So this asserts the structural
        // TERM SHAPE; the modulo-3 kernel proof lives in clean_ground.
        let slice_t = Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::Slice { elem: Box::new(param_ty("T/#0")) }),
        };
        let contract = reflect_contract(
            &[("xs", &slice_t)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("&[T] reflects via the parameterized sequence carrier");
        // Outer Π binds the type var `T` at `Type` (Sort 1).
        let ProofTerm::Pi { domain: outer_dom, codomain, .. } = &contract else {
            panic!("expected outer Π(T:Type), got {contract:?}");
        };
        assert_eq!(**outer_dom, ProofTerm::Sort(1), "outer binder is Π(T : Type)");
        // The `xs` parameter binds at the parameterized sequence carrier
        // `Slice (Var 0)` (the bound `T`), NOT a `Trust.Opaque.*` type variable.
        let ProofTerm::Pi { domain: xs_dom, .. } = &**codomain else {
            panic!("expected Π(xs : …), got {codomain:?}");
        };
        assert_eq!(
            **xs_dom,
            app(cst(CARRIER_SLICE), ProofTerm::Var(0)),
            "xs binds at Slice (Var T), the parameterized sequence carrier — not Trust.Opaque"
        );
        // And it is NOT the opaque over-approximation.
        assert!(
            !code_mentions_opaque(xs_dom),
            "the &[T] parameter must NOT fall to the opaque Trust.Opaque carrier"
        );
    }

    /// Whether a term mentions the synthetic opaque-parameter carrier
    /// (`Trust.Opaque.*`) — the fail-closed over-approximation a composite-with-var
    /// parameter used to hit. A test helper to assert the STRUCTURAL path is taken.
    fn code_mentions_opaque(term: &ProofTerm) -> bool {
        match term {
            ProofTerm::Const(n) => n.starts_with(OPAQUE_PREFIX),
            ProofTerm::App(f, a) => code_mentions_opaque(f) || code_mentions_opaque(a),
            ProofTerm::Lambda { binder_type, body, .. } => {
                code_mentions_opaque(binder_type) || code_mentions_opaque(body)
            }
            ProofTerm::Pi { domain, codomain, .. } => {
                code_mentions_opaque(domain) || code_mentions_opaque(codomain)
            }
            ProofTerm::Var(_) | ProofTerm::Sort(_) => false,
        }
    }

    #[test]
    fn reflect_contract_tuple_with_param_grounds_structurally_concrete_via_el() {
        // RECURSIVE DEPENDENT CARRIER (goal bullet 2 tail) — fn k<T>(x: (T, u8)) -> i32
        // now grounds STRUCTURALLY (the `x` param binds at `Prod (Var T) …` under an
        // outer `Π(T : Type)`); a fully-concrete tuple still decodes via El (no spurious
        // type binder when no type var is nested).
        let mixed = Ty::Tuple(vec![param_ty("T/#0"), Ty::Int { width: 8, signed: false }]);
        let c1 = reflect_contract(
            &[("x", &mixed)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("(T, u8) grounds structurally");
        // The `(T, u8)` param introduces exactly one outer `Π(T : Type)` binder
        // (structural), NOT an opaque carrier.
        assert!(
            matches!(&c1, ProofTerm::Pi { domain, .. } if **domain == ProofTerm::Sort(1)),
            "the (T, u8) param introduces a structural Π(T : Type) binder"
        );
        assert!(!code_mentions_opaque(&c1), "the (T, u8) param must NOT be opaque");
        // A fully-concrete tuple decodes through El (NOT an opaque carrier): the outer
        // binder is the value param at `El (Prod …)`, with NO `Π(_ : Type)` wrapper.
        let concrete = Ty::Tuple(vec![Ty::Bool, Ty::Int { width: 8, signed: false }]);
        let c2 = reflect_contract(
            &[("x", &concrete)],
            &Formula::Bool(true),
            "ret",
            &i32(),
            &Formula::Bool(true),
        )
        .expect("(bool, u8) decodes via El");
        contract_is_a_type(&c2);
        // No outer `Type` binder (concrete params introduce no type variable).
        assert!(
            !matches!(&c2, ProofTerm::Pi { domain, .. } if **domain == ProofTerm::Sort(1)),
            "a fully-concrete composite must NOT introduce an opaque type binder"
        );
    }

    // --- M3: pipeline bridge (FunctionSpec -> dependent type) --------------

    #[test]
    fn reflect_function_spec_bridges_real_spec_to_dependent_type() {
        use trust_types::FunctionSpec;
        // fn add_pos(x: i32) -> i32  #[requires(x > 0)] #[ensures(result > x)]
        let sig = trust_types::FnSig { params: vec![i32()], ret: Box::new(i32()) };
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result > x".to_string()],
            invariants: vec![],
        };
        let contract = reflect_function_spec(&sig, &["x"], &spec)
            .expect("real FunctionSpec should reflect to a contract");
        contract_is_a_type(&contract);
    }

    #[test]
    fn reflect_function_spec_empty_spec_is_trivial_contract() {
        use trust_types::FunctionSpec;
        let sig = trust_types::FnSig { params: vec![i32()], ret: Box::new(i32()) };
        let contract = reflect_function_spec(&sig, &["x"], &FunctionSpec::default())
            .expect("empty spec is a trivial (true => true) contract");
        contract_is_a_type(&contract);
    }

    #[test]
    fn reflect_function_spec_rejects_an_unparseable_clause() {
        use trust_types::FunctionSpec;
        let sig = trust_types::FnSig { params: vec![i32()], ret: Box::new(i32()) };
        let spec = FunctionSpec {
            requires: vec!["x > 0".to_string(), "???".to_string()],
            ensures: vec![],
            invariants: vec![],
        };
        let result = reflect_function_spec(&sig, &["x"], &spec);
        assert!(matches!(result, Err(ReflectError::SpecParse(_))));
    }

    #[test]
    fn reflect_verifiable_function_bridges_pipeline_currency() {
        use trust_types::{LocalDecl, VerifiableBody, VerifiableFunction};
        // fn double_gt(x: i32) -> i32  #[requires(x > 0)] #[ensures(_0 > x)]
        // (preconditions/postconditions are already parsed Formulas on the func.)
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32(), name: Some("_0".into()) }, // return slot
                LocalDecl { index: 1, ty: i32(), name: Some("x".into()) },  // param x
            ],
            blocks: vec![],
            arg_count: 1,
            return_ty: i32(),
        };
        let func = VerifiableFunction {
            name: "double_gt".into(),
            def_path: "crate::double_gt".into(),
            span: Default::default(),
            body,
            contracts: vec![],
            preconditions: vec![Formula::Gt(Box::new(ivar("x")), Box::new(Formula::Int(0)))],
            postconditions: vec![Formula::Gt(Box::new(ivar("_0")), Box::new(ivar("x")))],
            spec: Default::default(),
        };
        let contract =
            reflect_verifiable_function(&func).expect("a VerifiableFunction should reflect");
        contract_is_a_type(&contract);
    }

    #[test]
    fn reflect_function_spec_arity_mismatch_errors() {
        use trust_types::FunctionSpec;
        let sig = trust_types::FnSig { params: vec![i32(), i32()], ret: Box::new(i32()) };
        let r = reflect_function_spec(&sig, &["only_one"], &FunctionSpec::default());
        assert!(matches!(r, Err(ReflectError::PredicateUnsupported(_))));
    }

    // --- kernel-resolvability / context ------------------------------------

    #[test]
    fn carrier_context_declares_every_emittable_carrier() {
        let ctx = carrier_context();
        for name in [
            CARRIER_SORT_TY,
            CARRIER_NAT,
            CARRIER_BOOL,
            CARRIER_INT,
            CARRIER_UNIT,
            CARRIER_BITVEC,
            CARRIER_PROD,
            CARRIER_VEC,
            CARRIER_SLICE,
        ] {
            assert!(ctx.lookup(name).is_some(), "context missing carrier {name}");
        }
        for &w in REFLECTED_BITVEC_WIDTHS {
            assert!(ctx.lookup(&w.to_string()).is_some(), "context missing width {w}");
        }
    }

    #[test]
    fn reflected_scalars_typecheck_in_carrier_context() {
        for sort in [Sort::Bool, Sort::Int, Sort::BitVec(8), Sort::BitVec(128)] {
            infers_sort_ty(&reflect_sort(&sort).unwrap());
        }
    }

    #[test]
    fn carrier_context_is_load_bearing() {
        let term = reflect_sort(&Sort::Bool).unwrap();
        assert!(
            infer_type(&term, &KernelContext::new(), &[]).is_err(),
            "an empty context must reject the carrier — proving carrier_context is needed"
        );
    }

    #[test]
    fn reflected_composite_has_no_unresolved_constants() {
        // Ties reflect.rs to the `clean axioms` instrument: a reflected struct,
        // closed over the carrier context, references no dangling constant.
        let ctx = carrier_context();
        let ty = Ty::Tuple(vec![Ty::Bool, Ty::Int { width: 32, signed: false }]);
        let term = reflect_ty(&ty).unwrap();
        let report = axiom_closure(&term, &ctx);
        assert!(
            report.unresolved.is_empty(),
            "reflected tuple has dangling constants: {:?}",
            report.unresolved
        );
        assert!(report.axioms.contains(CARRIER_PROD));
        assert!(report.axioms.contains(CARRIER_BOOL));
    }

    // --- PHASE 4: enum reflection ------------------------------------------

    use trust_types::VariantDef;

    #[test]
    fn reflect_enum_two_variants_builds_multi_ctor_carrier() {
        // enum E { A(u32), B }
        let ty = Ty::adt_enum(
            "E",
            vec![
                VariantDef {
                    name: "A".into(),
                    discriminant: 0,
                    fields: vec![("0".into(), Ty::Int { width: 32, signed: false })],
                },
                VariantDef { name: "B".into(), discriminant: 1, fields: vec![] },
            ],
        );
        let carrier = reflect_enum(&ty).expect("a 2-variant enum reflects");
        assert!(carrier.is_enum() && !carrier.is_parameterized());
        assert_eq!(carrier.name, "Trust.Adt.E");
        assert_eq!(carrier.constructors.len(), 2);
        assert_eq!(carrier.constructors[0].name, "Trust.Adt.E.A");
        assert_eq!(carrier.constructors[0].discriminant, 0);
        assert_eq!(carrier.constructors[0].fields, vec![("0".to_string(), bv(32))]);
        assert_eq!(carrier.constructors[1].name, "Trust.Adt.E.B");
        assert!(carrier.constructors[1].fields.is_empty(), "B is nullary");
        // `reflect_struct` dispatches to `reflect_enum` for an enum Ty.
        assert_eq!(reflect_struct(&ty), Some(carrier));
    }

    #[test]
    fn reflect_enum_generic_option_is_parameterized() {
        // enum Option<T> { Some(T), None }
        let ty = Ty::adt_enum(
            "Option",
            vec![
                VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![(
                        "0".into(),
                        Ty::Unsupported {
                            kind: PARAM_KIND.into(),
                            detail: "generic parameter T/#0 needs monomorphization".into(),
                        },
                    )],
                },
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            ],
        );
        let carrier = reflect_enum(&ty).expect("Option<T> reflects parameterized");
        assert!(carrier.is_enum() && carrier.is_parameterized());
        assert_eq!(carrier.type_params, vec!["T/#0".to_string()]);
        // Some's field carrier is the bound type-param const Trust.Param.T/#0.
        assert_eq!(carrier.constructors[0].fields[0].1, cst(&param_const_name("T/#0")));
        assert_eq!(carrier.field_param_index(&carrier.constructors[0].fields[0].1), Some(0));
    }

    /// GOAL-ITEM #3 — an enum variant with a FLOAT field now reflects structurally
    /// (the float field reflects to its structured IEEE carrier, a `Prod` code that
    /// decodes to a real kernel type), so the enum is no longer forced to the Prod
    /// floor. A genuinely-non-reflectable variant field (`never`) still falls back.
    #[test]
    fn reflect_enum_with_float_field_reflects_structurally() {
        let ty = Ty::adt_enum(
            "WithFloat",
            vec![VariantDef {
                name: "F".into(),
                discriminant: 0,
                fields: vec![("0".into(), Ty::Float { width: 32 })],
            }],
        );
        let carrier = reflect_enum(&ty).expect("a float variant field now reflects structurally");
        assert!(carrier.is_enum());
        // A never variant field still falls back to Prod (genuinely non-reflectable).
        let bad = Ty::adt_enum(
            "Bad",
            vec![VariantDef {
                name: "N".into(),
                discriminant: 0,
                fields: vec![("0".into(), Ty::Never)],
            }],
        );
        assert_eq!(reflect_enum(&bad), None, "a never variant field falls back to Prod");
    }

    /// FAITHFULNESS FIX (enum sum types) — the REGRESSION LOCK for the audit hole: a
    /// concrete enum's `reflect_ty` carrier is a FAITHFUL, INJECTIVE sum type, NOT the
    /// non-injective `reflect_struct_product` over the union of variant fields. Before the
    /// fix `reflect_ty(Option<i32>) == reflect_ty(struct Wrap(i32)) == Prod (BitVec 32)
    /// Unit` (Some/None CONFLATED with a struct), `reflect_ty(IntErrorKind) == Unit ==`
    /// any fieldless enum, and `reflect_ty(Shape) == Prod-of-3 ==` a 3-field struct. This
    /// test pins that those carriers are now ALL DISTINCT.
    #[test]
    fn reflect_ty_enum_carrier_is_injective_not_struct_product() {
        let i32t = || Ty::Int { width: 32, signed: true };
        let u32t = || Ty::Int { width: 32, signed: false };

        // (1) Option<i32> (a 2-variant enum) vs struct Wrap(i32) (a 1-field struct).
        let option_i32 = Ty::adt_enum(
            "core::option::Option",
            vec![
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), i32t())],
                },
            ],
        );
        let wrap_i32 = Ty::adt("Wrap", vec![("0".into(), i32t())]);
        let opt_carrier = reflect_ty(&option_i32).expect("Option<i32> reflects");
        let wrap_carrier = reflect_ty(&wrap_i32).expect("Wrap(i32) reflects");
        assert_ne!(
            opt_carrier, wrap_carrier,
            "INJECTIVITY: a 2-variant Option carrier must be DISTINCT from a 1-field struct \
             carrier (the audit hole: they were both `Prod (BitVec 32) Unit`)"
        );
        // The Option carrier is the nominal sum-type inductive, NOT a `Prod`.
        assert_eq!(
            opt_carrier,
            cst(&adt_inductive_name("core::option::Option")),
            "Option's faithful carrier is the multi-ctor inductive `Trust.Adt.*`, not a Prod"
        );

        // (2) IntErrorKind (5 fieldless variants) vs a 1-variant fieldless enum.
        let int_error_kind = Ty::adt_enum(
            "core::num::IntErrorKind",
            vec![
                VariantDef { name: "Empty".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "InvalidDigit".into(), discriminant: 1, fields: vec![] },
                VariantDef { name: "PosOverflow".into(), discriminant: 2, fields: vec![] },
                VariantDef { name: "NegOverflow".into(), discriminant: 3, fields: vec![] },
                VariantDef { name: "Zero".into(), discriminant: 4, fields: vec![] },
            ],
        );
        let one_variant = Ty::adt_enum(
            "Singleton",
            vec![VariantDef { name: "Only".into(), discriminant: 0, fields: vec![] }],
        );
        let iek_carrier = reflect_ty(&int_error_kind).expect("IntErrorKind reflects");
        let one_carrier = reflect_ty(&one_variant).expect("1-variant enum reflects");
        assert_ne!(
            iek_carrier, one_carrier,
            "INJECTIVITY: a 5-variant fieldless enum must be DISTINCT from a 1-variant \
             fieldless enum (the audit hole: both flattened to `Unit`)"
        );
        // Neither is `Unit` any more — both are nominal sum-type inductives.
        assert_ne!(iek_carrier, cst(CARRIER_UNIT), "IntErrorKind must not flatten to Unit");
        assert_ne!(one_carrier, cst(CARRIER_UNIT), "a fieldless enum must not flatten to Unit");

        // (3) Shape { Circle(u32), Rect{w,h} } vs a plain 3-field struct — distinct
        //     carriers, AND Circle/Rect are DISTINCT constructors of the inductive.
        let shape = Ty::adt_enum(
            "Shape",
            vec![
                VariantDef {
                    name: "Circle".into(),
                    discriminant: 0,
                    fields: vec![("0".into(), u32t())],
                },
                VariantDef {
                    name: "Rect".into(),
                    discriminant: 1,
                    fields: vec![("w".into(), u32t()), ("h".into(), u32t())],
                },
            ],
        );
        let plain3 = Ty::adt(
            "Plain3",
            vec![("0".into(), u32t()), ("w".into(), u32t()), ("h".into(), u32t())],
        );
        let shape_carrier = reflect_ty(&shape).expect("Shape reflects");
        let plain3_carrier = reflect_ty(&plain3).expect("Plain3 reflects");
        assert_ne!(
            shape_carrier, plain3_carrier,
            "INJECTIVITY: a 2-variant data enum must be DISTINCT from a 3-field struct (the \
             audit hole: both flattened to a 3-`BitVec` `Prod`)"
        );
        // Circle ≠ Rect as DISTINCT constructors of the registered sum-type inductive.
        let shape_enum = reflect_enum(&shape).expect("Shape reflects as enum");
        assert_eq!(shape_enum.constructors.len(), 2);
        assert_ne!(
            shape_enum.constructors[0].name, shape_enum.constructors[1].name,
            "Circle and Rect must be DISTINCT constructors of the Shape inductive"
        );
        assert_eq!(shape_enum.constructors[0].name, "Trust.Adt.Shape.Circle");
        assert_eq!(shape_enum.constructors[1].name, "Trust.Adt.Shape.Rect");
        assert_ne!(
            shape_enum.constructors[0].discriminant, shape_enum.constructors[1].discriminant,
            "Circle and Rect carry DISTINCT discriminants (the SwitchInt tags)"
        );

        // (4) Some ≠ None — the two Option constructors are distinct (nullary None vs
        //     the i32-carrying Some).
        let opt_enum = reflect_enum(&option_i32).expect("Option reflects as enum");
        assert_eq!(opt_enum.constructors.len(), 2);
        assert!(opt_enum.constructors[0].fields.is_empty(), "None is a NULLARY constructor");
        assert_eq!(opt_enum.constructors[1].fields.len(), 1, "Some carries one i32 field");
        assert_ne!(
            opt_enum.constructors[0].name, opt_enum.constructors[1].name,
            "Some and None must be DISTINCT constructors"
        );
    }

    #[test]
    fn adt_variant_ctor_name_sanitizes() {
        assert_eq!(adt_variant_ctor_name("Trust.Adt.E", "A"), "Trust.Adt.E.A");
        // A path-y variant (defensive — variants are usually identifiers).
        assert_eq!(adt_variant_ctor_name("Trust.Adt.E", "My::V"), "Trust.Adt.E.My_V");
    }

    #[test]
    fn struct_carrier_has_no_constructors() {
        // A plain struct stays single-`.mk` (constructors empty), NOT an enum.
        let ty = Ty::adt("Pt", vec![("x".into(), Ty::Int { width: 8, signed: false })]);
        let carrier = reflect_struct(&ty).expect("struct reflects");
        assert!(!carrier.is_enum(), "a struct must not register as an enum");
        assert!(carrier.constructors.is_empty());
    }

    // --- GOAL-ITEM #2: known std containers → structural models ------------

    /// A generic-param element field (the bare `T` the extractor would bury inside
    /// `RawVec`); we model the recoverable surface form `Vec { elem: Slice T }`-ish.
    fn t_param() -> Ty {
        Ty::Unsupported {
            kind: PARAM_KIND.into(),
            detail: "generic parameter T/#0 needs monomorphization".into(),
        }
    }

    /// A realistically-shaped `Vec<T>` lowering: the def-path name, a type-erased
    /// `RawVec`-style buffer field nesting a `RawPtr` to the element, plus a `usize`
    /// length slot. The element `T` is recoverable from the nested pointer.
    fn vec_of(elem: Ty) -> Ty {
        let raw_vec = Ty::adt(
            "alloc::raw_vec::RawVec",
            vec![
                (
                    "ptr".into(),
                    Ty::adt(
                        "core::ptr::unique::Unique",
                        vec![(
                            "pointer".into(),
                            Ty::RawPtr { mutable: false, pointee: Box::new(elem) },
                        )],
                    ),
                ),
                ("cap".into(), Ty::Int { width: 64, signed: false }),
            ],
        );
        Ty::adt(
            "alloc::vec::Vec",
            vec![("buf".into(), raw_vec), ("len".into(), Ty::Int { width: 64, signed: false })],
        )
    }

    /// GOAL-ITEM #2 — a `Vec<u32>` reflects to the EXISTING slice carrier
    /// `Slice (BitVec 32)` (a Vec IS a growable slice), grounding its bounds VCs
    /// structurally over the symbolic slice length rather than the opaque internal
    /// product. The slice carrier introduces NO axiom (it is already declared).
    #[test]
    fn reflect_vec_of_concrete_is_slice_carrier() {
        let ty = vec_of(Ty::Int { width: 32, signed: false });
        let expected = app(cst(CARRIER_SLICE), bv(32));
        assert_eq!(reflect_ty(&ty), Ok(expected.clone()));
        infers_sort_ty(&expected); // resolves in the (3-axiom) carrier context
        // A Vec is NOT a named struct inductive over its internal layout.
        assert_eq!(reflect_struct(&ty), None, "Vec must not register as a struct inductive");
    }

    /// GOAL-ITEM #2 — a `Vec<T>` (generic element) reflects to `Slice (Param T)`:
    /// the bare element stays the Pi-bound type variable, so a `fn f<T>(v:&Vec<T>)`
    /// grounds with `T` abstracted outermost.
    #[test]
    fn reflect_vec_of_generic_keeps_param_element() {
        let ty = vec_of(t_param());
        let expected = app(cst(CARRIER_SLICE), cst(&param_const_name("T/#0")));
        assert_eq!(reflect_ty(&ty), Ok(expected));
    }

    /// GOAL-ITEM #2 — `String` (morally `Vec<u8>`) reflects to `Slice (BitVec 8)`
    /// even though its `u8` element is fully type-erased in the buffer.
    #[test]
    fn reflect_string_is_slice_of_u8() {
        let s = Ty::adt(
            "alloc::string::String",
            vec![("vec".into(), vec_of(Ty::Int { width: 8, signed: false }))],
        );
        assert_eq!(reflect_ty(&s), Ok(app(cst(CARRIER_SLICE), bv(8))));
    }

    /// GOAL-ITEM #2 — a transparent smart pointer `Box<u32>` reflects to its inner
    /// `reflect_ty(u32)` = `BitVec 32`; the pointer is invisible to the carrier
    /// (like `&T`). `Rc`/`Arc` behave identically.
    #[test]
    fn reflect_box_is_transparent_inner() {
        let boxed = |inner: Ty| {
            Ty::adt(
                "alloc::boxed::Box",
                vec![(
                    "0".into(),
                    Ty::adt(
                        "core::ptr::unique::Unique",
                        vec![(
                            "pointer".into(),
                            Ty::RawPtr { mutable: false, pointee: Box::new(inner) },
                        )],
                    ),
                )],
            )
        };
        assert_eq!(reflect_ty(&boxed(Ty::Int { width: 32, signed: false })), Ok(bv(32)));
        // Rc/Arc are the same transparent rule.
        let rc = Ty::adt(
            "alloc::rc::Rc",
            vec![("ptr".into(), Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Bool) })],
        );
        assert_eq!(reflect_ty(&rc), Ok(cst(CARRIER_BOOL)));
        // A box is not a named struct inductive either.
        assert_eq!(reflect_struct(&boxed(Ty::Bool)), None);
    }

    /// GOAL-ITEM #2 FAIL-CLOSED — an UNKNOWN container (a user struct that merely
    /// looks container-ish, or a foreign type) keeps the existing `Prod` path with
    /// NO regression. And `Option`/`Result` (enums) are UNTOUCHED by the table —
    /// they still route through the P4 multi-constructor inductive.
    #[test]
    fn unknown_container_and_enums_fall_through() {
        // A user `Vec`-named type NOT in std/alloc/core is not a known container.
        let user_vec =
            Ty::adt("my_crate::Vec", vec![("x".into(), Ty::Int { width: 32, signed: true })]);
        // Falls through to the Prod path (headed by Trust.Sort.Prod), not a Slice.
        match reflect_ty(&user_vec) {
            Ok(ProofTerm::App(f, _)) => match &*f {
                ProofTerm::App(prod, _) => assert_eq!(**prod, cst(CARRIER_PROD)),
                other => panic!("expected Prod head, got {other:?}"),
            },
            other => panic!("expected Prod App for an unknown container, got {other:?}"),
        }
        // Option<T> is an ENUM — the container table must NOT intercept it; it
        // reflects via reflect_enum to the parameterized inductive.
        let option = Ty::adt_enum(
            "core::option::Option",
            vec![
                VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), t_param())],
                },
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            ],
        );
        let carrier = reflect_struct(&option).expect("Option<T> reflects via the enum path");
        assert!(carrier.is_enum() && carrier.is_parameterized());
        assert_eq!(carrier.constructors.len(), 2);
    }

    /// GOAL-ITEM #2 FAIL-CLOSED — a known container whose element is NOT recoverable
    /// (an empty/ambiguous field tree) falls back to the opaque path, never a wrong
    /// `Slice`. A zero-field `alloc::vec::Vec` cannot yield an element ⇒ `Prod`/Unit.
    #[test]
    fn container_with_unrecoverable_element_fails_closed() {
        let empty_vec = Ty::adt("alloc::vec::Vec", vec![]);
        // No element recoverable ⇒ reflect_known_container is None ⇒ empty struct
        // floor (Unit), NOT a Slice.
        assert_eq!(reflect_ty(&empty_vec), Ok(cst(CARRIER_UNIT)));
        assert!(
            !matches!(reflect_ty(&empty_vec), Ok(ProofTerm::App(_, _))),
            "an unrecoverable Vec must not produce a Slice application"
        );
    }

    // ======================================================================
    // TYPE-REFLECTION COVERAGE measurement (goal: EVERY Rust type a Clean
    // dependent type, axiom_deps ⊆ the 3). The corpus of `(name, source, Ty)`
    // entries lives in the include!d fixture; this test reflects each entry and
    // classifies it as STRUCTURAL-modulo-3 or OPAQUE/unrooted, prints the honest
    // coverage map, and asserts the carriers the goal claims are structural.
    // ======================================================================

    // The corpus: `fn type_corpus() -> Vec<(&str, &str, Ty)>` + its `param` /
    // `container_adt` / `smart_ptr_adt` helpers. `Ty`/`FnSig`/`VariantDef` are all
    // already in this test module's scope (super::* + the module's `use
    // trust_types::VariantDef`), so the fixture imports NOTHING.
    include!("../fixtures/type-corpus/type_corpus.rs");

    /// The 3 foundational axioms, as the goal pins them.
    const THE_THREE: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];

    /// The verdict of classifying one corpus type.
    #[derive(Debug, Clone, PartialEq, Eq)]
    enum TypeVerdict {
        /// Reflects to a real carrier whose grounding rests on ⊆ the 3 axioms.
        Structural(String),
        /// Reflects to a free/unrooted const or fails closed — not (yet) modulo 3.
        Opaque(String),
    }

    /// Does `term`'s carrier mention a `Trust.Param.*` free const ANYWHERE (a
    /// generic type-variable position)? This is the marker that the LOCAL
    /// `carrier_context` predicative check would (incorrectly) leave UNRESOLVED,
    /// and the trigger for the REAL-KERNEL ∀(T:Type) Pi-bound grounding path.
    fn carrier_mentions_param(term: &ProofTerm) -> bool {
        match term {
            ProofTerm::Const(n) => n.starts_with(PARAM_PREFIX),
            ProofTerm::App(f, a) => carrier_mentions_param(f) || carrier_mentions_param(a),
            ProofTerm::Pi { domain, codomain, .. } => {
                carrier_mentions_param(domain) || carrier_mentions_param(codomain)
            }
            ProofTerm::Lambda { binder_type, body, .. } => {
                carrier_mentions_param(binder_type) || carrier_mentions_param(body)
            }
            ProofTerm::Var(_) | ProofTerm::Sort(_) => false,
        }
    }

    /// REAL-KERNEL modulo-3 gate for a PARAMETERIZED inductive (the STEP-2 fix):
    /// register the struct/enum carrier reflected from `ty` into a real prelude
    /// `Environment` as the `∀(T:Type)` Pi-bound inductive — EXACTLY how the depth
    /// corpus grounds parameterized inductives — and confirm the inductive AND its
    /// recursor have an EMPTY `axiom_deps` closure (⊆ the 3, NO 4th axiom). This
    /// is the grounding the LOCAL `carrier_context` checker cannot see, because it
    /// declares no `Trust.Param.*` const (the param is bound, not free). Returns
    /// `Some(detail)` when it genuinely grounds modulo 3, else `None`.
    fn generic_grounds_modulo_3_real_kernel(ty: &Ty) -> Option<String> {
        use clean_kernel::{Environment, Name};
        // A bare type variable (a naked generic param `T`, or an unnormalized
        // associated type `<T as Trait>::Out`) reflects to the bound type-variable
        // const `Trust.Param.<id>` ITSELF. In the real kernel a contract over such
        // a value binds it under an outer `Π(T : Type)` and the value's carrier IS
        // that bound `Type` variable — a genuine, axiom-free dependent binder (the
        // kernel has Π/Type primitively, ⊆ the 3). It carries no named inductive to
        // register; the Pi-bound `Type` variable is itself the modulo-3 grounding.
        if let Ok(ProofTerm::Const(n)) = reflect_ty(ty) {
            if n.starts_with(PARAM_PREFIX) {
                return Some(format!(
                    "bare type variable → Π(T:Type)-bound `Type` carrier ({n}) — \
                     axiom-free dependent binder (kernel Π/Type, ⊆ the 3)"
                ));
            }
        }
        // A composite that carries a generic field (`Wrapper<T>`, `MyEnum<T>`,
        // `Option<T>`) reflects to a PARAMETERIZED `AdtCarrier`. Register it as the
        // real `∀(T:Type)` inductive and gate on the kernel's own axiom_deps.
        if let Some(carrier) = reflect_struct(ty).filter(AdtCarrier::is_parameterized) {
            let mut env = Environment::with_prelude();
            let registry = crate::clean_ground::register_adt_carriers(
                &mut env,
                std::slice::from_ref(&carrier),
            );
            registry.get(&carrier.name)?;
            // The inductive itself: axiom_deps must be empty (⊆ the 3).
            let ind = Name::from_string(&carrier.name);
            let ind_deps = env.axiom_deps(&ind)?;
            if !ind_deps.is_empty() {
                return None;
            }
            // AND its auto-derived recursor.
            let info = env.inductive_info(&ind)?;
            if let Some(rec) = info.recursor_name.as_ref() {
                let rec_deps = env.axiom_deps(rec)?;
                if !rec_deps.is_empty() {
                    return None;
                }
            }
            return Some(format!(
                "parameterized inductive `{}` over {} `Type` param(s) registered modulo 3 \
                 (inductive + recursor axiom_deps EMPTY — the ∀(T:Type) Pi-bound form)",
                carrier.name,
                carrier.type_params.len()
            ));
        }

        // A PARAMETERIZED COMPOSITE that is not itself a named struct/enum inductive —
        // a sequence `[T; N]` / `&[T]` / `Vec<T>` or a tuple `(T, u8)` over a generic
        // element. It grounds via the `Vec<T> → List T` family (the prelude's axiom-free
        // `List`/`Prod`): a contract over a value of this type abstracts the element
        // param into an outer `Π(T:Type)` and binds the value at the decoded dependent
        // kernel type (`List (BVar T)`, `Prod (BVar T) Int`, …). Build that contract,
        // ground it, register it as a real kernel `Definition`, and gate on the kernel's
        // OWN axiom_deps being empty — EXACTLY the depth corpus's parameterized-sequence
        // grounding (`generic_vec_param_grounds_over_parameterized_sequence_carrier`).
        use clean_kernel::Declaration;
        let contract = reflect_contract(
            &[("v", ty)],
            &Formula::Bool(true),
            "ret",
            &Ty::Int { width: 32, signed: true },
            &Formula::Bool(true),
        )
        .ok()?;
        // It must actually be parameterized (an outer Π(T:Type) over a `Type` binder) —
        // i.e. the element param really abstracted. A concrete composite would not reach
        // here (no `Trust.Param.*` in its carrier), so this is the generic case.
        let expr = crate::clean_ground::to_clean_expr(&contract)?;
        let mut env = Environment::with_prelude();
        let sort = {
            use clean_kernel::TypeChecker;
            let tc = TypeChecker::new(&env);
            tc.infer_type(&expr).ok()?
        };
        let name = Name::from_string("Trust.measure.parameterized_composite");
        env.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: sort,
            value: expr,
            is_reducible: true,
        })
        .ok()?;
        let residue = env.axiom_deps(&name)?;
        if !residue.is_empty() {
            return None;
        }
        Some(
            "parameterized composite (`[T;N]`/`&[T]`/`Vec<T>`/tuple-over-T) grounds modulo 3 \
             via the `Vec<T> → List T` family — a contract over it abstracts the element \
             into Π(T:Type) and binds the value at the decoded dependent kernel type \
             (List/Prod over the prelude, axiom_deps EMPTY)"
                .to_string(),
        )
    }

    /// FAITHFULNESS FIX (enum sum types) — REAL-KERNEL modulo-3 gate for a CONCRETE
    /// (non-generic) type whose reflected carrier names one or more registered ADT
    /// inductives `Trust.Adt.*` — i.e. a CONCRETE ENUM (whose faithful carrier is the
    /// multi-constructor inductive `Trust.Adt.<Enum>` itself) OR a CONCRETE STRUCT that
    /// nests such an enum in FIELD position (e.g. `ParseIntError { kind : IntErrorKind }`,
    /// `Utf8Error { error_len : Option<u8> }`). The LOCAL `carrier_context` predicative
    /// checker cannot resolve a `Trust.Adt.*` const (it declares only the `Trust.SortTy`
    /// vocabulary), so these route to the REAL kernel instead.
    ///
    /// Registers EVERY reachable struct/enum inductive (the type's own + every nested ADT,
    /// post-order) via the SAME `reachable_adt_carriers` → `register_adt_carriers`
    /// multi-ctor path the prove/depth pipeline uses, confirms the type's own carrier was
    /// ADMITTED (the registry only admits a carrier whose inductive + recursor
    /// `axiom_deps` are EMPTY — ⊆ the 3, NO 4th axiom), and confirms the reflected
    /// top-level carrier DECODES + infers a `Sort` in that env (so the grounding is REAL,
    /// not merely a name match).
    ///
    /// This is the GENUINELY faithful grounding the audit demanded for enums: the carrier
    /// is the nominal sum type (so `Option<i32>` is DISTINCT from `struct Wrap(i32)`,
    /// `IntErrorKind` from a 1-variant enum), and the per-variant constructors keep
    /// `Some`/`None` and `Circle`/`Rect` DISTINCT — NOT the non-injective
    /// `reflect_struct_product` over the union of variant fields.
    ///
    /// Returns `None` (→ the caller's `Prod`-floor concrete-local path, sound) if the type
    /// has NO registered ADT carrier, the registry rejected its own carrier, or the
    /// top-level carrier does not decode. A GENERIC type routes through
    /// `generic_grounds_modulo_3_real_kernel` instead (handled earlier in `classify_type`).
    fn named_adt_grounds_modulo_3_real_kernel(ty: &Ty) -> Option<String> {
        use clean_kernel::{Environment, ExprKind, Name, TypeChecker};
        // The type's OWN faithful carrier (concrete enum: the multi-ctor inductive;
        // concrete struct: the single-`.mk` record). A non-ADT / known-container / generic
        // type has no own named inductive here ⇒ not this gate's job.
        let own = reflect_struct(ty)?;
        if own.is_parameterized() {
            return None; // a generic type is the `generic_grounds_modulo_3_real_kernel` job.
        }
        // Register the type's own inductive AND every nested ADT it reaches (post-order),
        // exactly as the prove/depth grounding pipeline does. The registry admits a carrier
        // ONLY if its inductive + auto-derived recursor have EMPTY `axiom_deps` (⊆ the 3).
        let func = single_local_func(ty);
        let carriers = crate::clean_ground::reachable_adt_carriers(&func);
        let mut env = Environment::with_prelude();
        let registry = crate::clean_ground::register_adt_carriers(&mut env, &carriers);
        registry.get(&own.name)?; // the type's own inductive must have been ADMITTED.
        // Re-confirm the type's own inductive + recursor rest on ONLY the 3 axioms.
        let ind = Name::from_string(&own.name);
        if !env.axiom_deps(&ind)?.is_empty() {
            return None;
        }
        let info = env.inductive_info(&ind)?;
        if let Some(rec) = info.recursor_name.as_ref() {
            if !env.axiom_deps(rec)?.is_empty() {
                return None;
            }
        }
        // The reflected TOP-LEVEL carrier must DECODE + infer a `Sort` against this env —
        // proving the grounding is real (the `Trust.Adt.*` const resolves to the
        // registered inductive), not merely a name match. A concrete enum's carrier is the
        // bare inductive const (binds directly); a struct's is `El (Prod …)` over its
        // fields (which may nest a registered enum inductive).
        let carrier = reflect_ty(ty).ok()?;
        let to_ground = if matches!(&carrier, ProofTerm::Const(n) if n.starts_with(ADT_PREFIX)) {
            carrier // a concrete enum: the inductive const is itself a `Type`.
        } else {
            app(cst(CARRIER_EL), carrier) // a struct/record: decode the `Trust.SortTy` code.
        };
        let expr = crate::clean_ground::to_clean_expr(&to_ground)?;
        let tc = TypeChecker::new(&env);
        let inferred = tc.infer_type(&expr).ok()?;
        if !matches!(inferred.kind(), ExprKind::Sort(_)) {
            return None;
        }
        // Whether the TYPE itself is the enum (so the headline names the sum type), or a
        // struct that merely NESTS one (the headline names the record over its enum field).
        let detail = if own.is_enum() {
            format!(
                "concrete enum → faithful multi-constructor inductive `{}` with {} \
                 discriminant-aware constructor(s) registered modulo 3 (inductive + \
                 recursor axiom_deps EMPTY — NO 4th axiom). INJECTIVE sum type: the carrier \
                 is the nominal inductive name (DISTINCT from any struct `Prod`), and each \
                 variant is a DISTINCT constructor (Some≠None, Circle≠Rect) — NOT the \
                 non-injective `Prod`-over-union flattening",
                own.name,
                own.constructors.len()
            )
        } else {
            format!(
                "concrete record `{}` registered modulo 3 (inductive + recursor axiom_deps \
                 EMPTY — NO 4th axiom); its field(s) ground over the nested FAITHFUL enum \
                 inductive(s) it carries (e.g. `IntErrorKind`/`Option` as a real multi-ctor \
                 sum type, NOT a flattened `Prod`), all admitted by the same axiom gate",
                own.name
            )
        };
        Some(detail)
    }

    /// REAL-KERNEL modulo-3 gate for a trait object `dyn Trait` (the dyn-Sigma
    /// front): register the existential `Trust.Dyn.<trait> := Σ(T:Type) Vtable T`
    /// into a real prelude `Environment` and confirm the vtable record, its
    /// recursor, AND the existential definition all have EMPTY `axiom_deps`, AND
    /// the carrier's `axiom_closure` (with the existential seeded as a Definition)
    /// contains NO `Trust.Dyn` free const. Returns `Some(detail)` on success.
    fn dyn_grounds_modulo_3_real_kernel(trait_name: &str) -> Option<String> {
        use clean_kernel::{Environment, Name};
        let carrier = reflect_dyn(trait_name, &[]);
        let mut env = Environment::with_prelude();
        let registry =
            crate::clean_ground::register_dyn_carriers(&mut env, std::slice::from_ref(&carrier));
        registry.get(&carrier.name)?;
        // vtable record + its recursor + the existential definition: axiom_deps = ∅.
        let vtable = Name::from_string(&carrier.vtable_name);
        if !env.axiom_deps(&vtable)?.is_empty() {
            return None;
        }
        let vinfo = env.inductive_info(&vtable)?;
        if let Some(rec) = vinfo.recursor_name.as_ref() {
            if !env.axiom_deps(rec)?.is_empty() {
                return None;
            }
        }
        let existential = Name::from_string(&carrier.name);
        if !env.axiom_deps(&existential)?.is_empty() {
            return None;
        }
        // The explicit goal gate: the carrier's `axiom_closure` has NO `Trust.Dyn`
        // free const — it resolves to the registered Definition, not an opaque const.
        let dyn_ty = reflect_ty(&Ty::Dynamic { trait_name: trait_name.into() }).ok()?;
        let mut ctx = KernelContext::new();
        for ax in THE_THREE {
            ctx.add_axiom(ax, ProofTerm::Sort(0)).ok()?;
        }
        for name in [carrier.name.as_str(), carrier.vtable_name.as_str()] {
            ctx.add_definition(name, ProofTerm::Sort(1), ProofTerm::Sort(1)).ok()?;
        }
        let report = axiom_closure(&dyn_ty, &ctx);
        let mentions_dyn_axiom = report.axioms.iter().any(|a| a.starts_with(DYN_PREFIX))
            || report.unresolved.iter().any(|u| u.starts_with(DYN_PREFIX));
        if mentions_dyn_axiom || !report.is_modulo_foundational() {
            return None;
        }
        Some(format!(
            "existential `{} := Σ(T:Type) {} T` registered modulo 3 (vtable + recursor + \
             existential axiom_deps EMPTY; NO `Trust.Dyn` free const in the closure)",
            carrier.name, carrier.vtable_name
        ))
    }

    /// REAL-KERNEL modulo-3 gate for a function pointer / fn item: it reflects to a
    /// genuine kernel `Pi` (arrow) via [`reflect_fn_sig_pi`], which `to_clean_expr`
    /// grounds directly to the native `Expr::pi`. Confirm it decodes to a real
    /// kernel type that infers a `Sort` in a prelude env (the kernel has Π
    /// primitively, ⊆ the 3). Returns `Some(detail)` on success.
    fn fn_ptr_grounds_modulo_3_real_kernel(ty: &Ty) -> Option<String> {
        use clean_kernel::{Environment, ExprKind, TypeChecker};
        let carrier = reflect_ty(ty).ok()?;
        // It must be a real Pi carrier (the fn-ptr-Pi front), not a `Trust.Sort.Fn` code.
        if !matches!(carrier, ProofTerm::Pi { .. }) {
            return None;
        }
        let expr = crate::clean_ground::to_clean_expr(&carrier)?;
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        let inferred = tc.infer_type(&expr).ok()?;
        if !matches!(inferred.kind(), ExprKind::Sort(_)) {
            return None;
        }
        Some(
            "function arrow → real kernel `Pi` (reflect(A) → reflect(B)), grounds to \
             `Expr::pi` and infers a Sort (kernel Π primitively, ⊆ the 3)"
                .to_string(),
        )
    }

    /// REAL-KERNEL modulo-3 gate for a closure/coroutine record: it registers as the
    /// single-constructor inductive `Trust.Closure.<name>` (env + call : A → B),
    /// parameterized over the call signature's `Type` vars; the inductive AND its
    /// recursor must have EMPTY `axiom_deps`. Returns `Some(detail)` on success.
    fn closure_grounds_modulo_3_real_kernel(name: &str, upvars: &[Ty]) -> Option<String> {
        use clean_kernel::{Environment, Name};
        let carrier = reflect_closure(name, upvars)?;
        let mut env = Environment::with_prelude();
        let registry =
            crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
        registry.get(&carrier.name)?;
        let ind = Name::from_string(&carrier.name);
        if !env.axiom_deps(&ind)?.is_empty() {
            return None;
        }
        let info = env.inductive_info(&ind)?;
        if let Some(rec) = info.recursor_name.as_ref() {
            if !env.axiom_deps(rec)?.is_empty() {
                return None;
            }
        }
        Some(format!(
            "closure record `{}` (env + call : A → B) registered modulo 3 (inductive + \
             recursor axiom_deps EMPTY)",
            carrier.name
        ))
    }

    /// LOCAL `carrier_context` predicative check: the existing structural path for a
    /// CONCRETE (param-free) carrier. The carrier must type-check (infer a sort)
    /// against the local context AND resolve with NO UNRESOLVED const — i.e. it is
    /// built entirely from the DECLARED carrier vocabulary (`Trust.Sort.*` / `El` /
    /// `Sigma` / numerals), with no free `Trust.Param.*` / `Trust.Dyn.*` / opaque
    /// const. Those declared carrier consts are the LOCAL predicative scaffolding
    /// (registered as `carrier_context` axioms); the carrier's grounding modulo the
    /// 3 in the REAL kernel is established separately (the scalar/struct/container
    /// fragment is the `register_adt_carriers` / depth-corpus result). So the
    /// concrete gate here is RESOLUTION (no unrooted free const), NOT a re-derivation
    /// of the real-kernel axiom_deps — checking the latter against the local
    /// scaffolding axioms would (wrongly) reject every concrete, since the
    /// scaffolding consts are themselves declared as non-foundational `carrier_context`
    /// axioms. Returns `Some(detail)` when the carrier resolves cleanly.
    fn concrete_grounds_modulo_3_local(carrier: &ProofTerm) -> Option<String> {
        let ctx = carrier_context();
        // The carrier must type-check (infer a sort) against the local context …
        infer_type(carrier, &ctx, &[]).ok()?;
        // … and resolve with NOTHING unresolved (no free `Trust.Param.*`/`Trust.Dyn.*`
        // /opaque const). A carrier that mentions an undeclared const is the OPAQUE case.
        let report = axiom_closure(carrier, &ctx);
        if !report.unresolved.is_empty() {
            return None;
        }
        Some(
            "concrete carrier resolves in `carrier_context` over the declared carrier \
             vocabulary (no unrooted free const; modulo-3 in the real kernel)"
                .to_string(),
        )
    }

    /// TYPE-ZOO #1 — REAL-KERNEL modulo-3 gate for the LENGTH-INDEXED const-generic
    /// array `[T; N]`: register `Trust.ArrayN (T:Type) : Nat → Type`, confirm the
    /// inductive + recursor have EMPTY `axiom_deps`, then decode `[i32; n]`'s carrier
    /// `Trust.ArrayN Int n` to the kernel type and confirm it infers a `Sort` (the
    /// length is a REAL `Nat` INDEX, not erased). Returns `Some(detail)` on success.
    fn arrayn_grounds_modulo_3_real_kernel(elem: &Ty, len: u64) -> Option<String> {
        use clean_kernel::{Environment, ExprKind, TypeChecker};
        let mut env = Environment::with_prelude();
        if !crate::clean_ground::register_arrayn_carrier(&mut env) {
            return None;
        }
        // The carrier `Trust.ArrayN (decode elem) <n>` (with `<n>` a real Nat numeral).
        let carrier = reflect_array_indexed(elem, len).ok()?;
        // Decode it through `El` so it grounds to the kernel `ArrayN (decode elem)
        // (Nat.lit n)`, then confirm it infers a `Sort` in the prelude env.
        let el = app(cst(CARRIER_EL), carrier);
        let expr = crate::clean_ground::to_clean_expr(&el)?;
        let tc = TypeChecker::new(&env);
        let inferred = tc.infer_type(&expr).ok()?;
        if !matches!(inferred.kind(), ExprKind::Sort(_)) {
            return None;
        }
        Some(format!(
            "length-indexed `Trust.ArrayN (T:Type) : Nat → Type` registered modulo 3 \
             (inductive + recursor axiom_deps EMPTY); `[T; {len}]` grounds to `ArrayN \
             (decode T) (Nat.lit {len})` — the const generic `N={len}` is a REAL `Nat` INDEX"
        ))
    }

    /// TYPE-ZOO #2 — REAL-KERNEL modulo-3 gate for an `impl Trait` (RPIT/TAIT) opaque
    /// return: the SAME existential `Sigma (T:Type), Vtable T` a `dyn` uses, under the
    /// `Trust.Impl.<trait>` name ([`reflect_impl_trait`] + `register_dyn_carriers`).
    /// Confirm the vtable record, its recursor, AND the existential definition all have
    /// EMPTY `axiom_deps`. Returns `Some(detail)` on success.
    fn impl_trait_grounds_modulo_3_real_kernel(trait_name: &str) -> Option<String> {
        use clean_kernel::{Environment, Name};
        let carrier = reflect_impl_trait(trait_name, &[]);
        let mut env = Environment::with_prelude();
        let registry =
            crate::clean_ground::register_dyn_carriers(&mut env, std::slice::from_ref(&carrier));
        registry.get(&carrier.name)?;
        for n in [carrier.vtable_name.as_str(), carrier.name.as_str()] {
            if !env.axiom_deps(&Name::from_string(n))?.is_empty() {
                return None;
            }
        }
        let vinfo = env.inductive_info(&Name::from_string(&carrier.vtable_name))?;
        if let Some(rec) = vinfo.recursor_name.as_ref() {
            if !env.axiom_deps(rec)?.is_empty() {
                return None;
            }
        }
        Some(format!(
            "impl Trait → existential `{} := Σ(T:Type) {} T` registered modulo 3 \
             (the `dyn` analogue under the `Trust.Impl.*` name; axiom_deps EMPTY)",
            carrier.name, carrier.vtable_name
        ))
    }

    /// TYPE-ZOO #3 — REAL-KERNEL modulo-3 gate for a MULTI-BOUND trait object
    /// `dyn A + B + Send`: the existential `Sigma (T:Type), Vtable_<A+B…> T` over the
    /// CONJOINED vtable record (markers contribute the empty obligation),
    /// [`reflect_multi_dyn`] + `register_dyn_carriers`. Confirm the vtable record, its
    /// recursor, AND the existential have EMPTY `axiom_deps`. Returns `Some(detail)`.
    fn multi_dyn_grounds_modulo_3_real_kernel(trait_name: &str) -> Option<String> {
        use clean_kernel::{Environment, Name};
        let carrier = reflect_multi_dyn(trait_name, &[]);
        let mut env = Environment::with_prelude();
        let registry =
            crate::clean_ground::register_dyn_carriers(&mut env, std::slice::from_ref(&carrier));
        registry.get(&carrier.name)?;
        for n in [carrier.vtable_name.as_str(), carrier.name.as_str()] {
            if !env.axiom_deps(&Name::from_string(n))?.is_empty() {
                return None;
            }
        }
        let vinfo = env.inductive_info(&Name::from_string(&carrier.vtable_name))?;
        if let Some(rec) = vinfo.recursor_name.as_ref() {
            if !env.axiom_deps(rec)?.is_empty() {
                return None;
            }
        }
        let bounds = split_multi_bound(trait_name);
        let markers: Vec<&String> = bounds.iter().filter(|b| is_marker_trait(b)).collect();
        Some(format!(
            "multi-bound `dyn {}` → CONJOINED existential `{} := Σ(T:Type) {} T` modulo 3 \
             ({} bound(s), {} marker(s) → empty obligation; axiom_deps EMPTY)",
            bounds.join(" + "),
            carrier.name,
            carrier.vtable_name,
            bounds.len(),
            markers.len()
        ))
    }

    /// TYPE-ZOO #4 — REAL-KERNEL modulo-3 gate for an HRTB `for<'a> fn(args) -> ret`:
    /// register the erased `Trust.Region` atom, build `Π(r : Region) → (fn arrow)`
    /// ([`reflect_hrtb_fn`]), decode it to a real kernel `Pi`, and confirm it infers a
    /// `Sort` in the prelude env (kernel `Pi`/`Type` primitively, ⊆ the 3). Returns
    /// `Some(detail)` on success.
    fn hrtb_grounds_modulo_3_real_kernel(num_regions: usize, sig: &FnSig) -> Option<String> {
        use clean_kernel::{Environment, ExprKind, Name, TypeChecker};
        let mut env = Environment::with_prelude();
        if !crate::clean_ground::register_region_carrier(&mut env) {
            return None;
        }
        // The `Trust.Region` atom must rest on only the 3 (a nullary inductive).
        if !env.axiom_deps(&Name::from_string(REGION_INDUCTIVE))?.is_empty() {
            return None;
        }
        let hrtb = reflect_hrtb_fn(num_regions, sig).ok()?;
        // The HRTB is `Π(r : El (Region-code))? …` — but Region is bound DIRECTLY as a
        // `Type` const (not `El`-wrapped). Decode through `to_clean_expr`; the
        // `Trust.Region` const grounds to the registered inductive.
        let expr = crate::clean_ground::to_clean_expr(&hrtb)?;
        let tc = TypeChecker::new(&env);
        let inferred = tc.infer_type(&expr).ok()?;
        if !matches!(inferred.kind(), ExprKind::Sort(_)) {
            return None;
        }
        Some(format!(
            "HRTB `for<'a×{num_regions}>` → real kernel `Π(r : Trust.Region) → (fn arrow)` \
             (the erased region atom registered modulo 3; the universal quantifier is a \
             genuine kernel Pi, ⊆ the 3)"
        ))
    }

    /// TYPE-ZOO #5 — REAL-KERNEL modulo-3 gate for a GAT family `<Trait>::<Out><P>`:
    /// register the PARAMETERIZED type-level-function inductive `Trust.Gat.<Trait>_<Out>
    /// (P:Type) : Type` ([`reflect_gat_family`] + `register_adt_carriers`) and confirm
    /// the inductive + recursor have EMPTY `axiom_deps`. Returns `Some(detail)`.
    fn gat_grounds_modulo_3_real_kernel(
        trait_name: &str,
        assoc: &str,
        params: &[String],
    ) -> Option<String> {
        use clean_kernel::{Environment, Name};
        let carrier = reflect_gat_family(trait_name, assoc, params)?;
        let mut env = Environment::with_prelude();
        let registry =
            crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
        registry.get(&carrier.name)?;
        let ind = Name::from_string(&carrier.name);
        if !env.axiom_deps(&ind)?.is_empty() {
            return None;
        }
        let info = env.inductive_info(&ind)?;
        if let Some(rec) = info.recursor_name.as_ref() {
            if !env.axiom_deps(rec)?.is_empty() {
                return None;
            }
        }
        Some(format!(
            "GAT `{trait_name}::{assoc}<…>` → type-level-function family `{}` over {} `Type` \
             GAT param(s), registered modulo 3 (inductive + recursor axiom_deps EMPTY)",
            carrier.name,
            carrier.type_params.len()
        ))
    }

    /// TYPE-ZOO #6 — REAL-KERNEL modulo-3 gate for a COROUTINE state machine: register
    /// its record inductive `Trust.Coroutine.<name>` (env + resume : S → Y, the
    /// suspend-point STATE `S` existentially abstracted as a `Type` param)
    /// ([`reflect_coroutine`] + `register_adt_carriers`); confirm the inductive +
    /// recursor have EMPTY `axiom_deps`. Returns `Some(detail)`.
    fn coroutine_grounds_modulo_3_real_kernel(name: &str, upvars: &[Ty]) -> Option<String> {
        use clean_kernel::{Environment, Name};
        let carrier = reflect_coroutine(name, upvars)?;
        let mut env = Environment::with_prelude();
        let registry =
            crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
        registry.get(&carrier.name)?;
        let ind = Name::from_string(&carrier.name);
        if !env.axiom_deps(&ind)?.is_empty() {
            return None;
        }
        let info = env.inductive_info(&ind)?;
        if let Some(rec) = info.recursor_name.as_ref() {
            if !env.axiom_deps(rec)?.is_empty() {
                return None;
            }
        }
        Some(format!(
            "coroutine state machine `{}` (env + resume : S → Y; the suspend-point STATE \
             `S` existentially abstracted as a `Type` param) registered modulo 3 \
             (inductive + recursor axiom_deps EMPTY)",
            carrier.name
        ))
    }

    /// NEVER (`!`) — REAL-KERNEL modulo-3 gate for the standalone bottom type: register
    /// the EMPTY inductive `Trust.Never : Type` (ZERO constructors — the Clean analogue
    /// of `False`/`Empty`) via [`crate::clean_ground::register_never_carrier`], then
    /// confirm BOTH the inductive AND its auto-derived recursor `Trust.Never.rec` have
    /// EMPTY `axiom_deps` (⊆ the 3, NO 4th axiom — an empty inductive is axiom-free).
    /// Inhabitation is NOT attempted (an empty type has no witness — that is the whole
    /// point); we ground the TYPE, not a value of it. Returns `Some(detail)` on success.
    fn never_grounds_modulo_3_real_kernel() -> Option<String> {
        use clean_kernel::{Environment, Name};
        let mut env = Environment::with_prelude();
        if !crate::clean_ground::register_never_carrier(&mut env) {
            return None;
        }
        let ind = Name::from_string(NEVER_INDUCTIVE);
        if !env.axiom_deps(&ind)?.is_empty() {
            return None;
        }
        let info = env.inductive_info(&ind)?;
        // The auto-derived recursor (`Trust.Never.rec`, the ex-falso eliminator) must
        // likewise rest on only the 3 foundational axioms.
        if let Some(rec) = info.recursor_name.as_ref() {
            if !env.axiom_deps(rec)?.is_empty() {
                return None;
            }
        } else {
            return None; // no recursor read back ⇒ not a complete inductive.
        }
        // SOUND by construction: an empty inductive is uninhabited, so inhabitation
        // stays fail-closed (no constructor → `default_inhabitant` returns None).
        if !info.constructor_names.is_empty() {
            return None; // a non-empty `Trust.Never` would be unsound — fail closed.
        }
        Some(format!(
            "never `!` → EMPTY inductive `{NEVER_INDUCTIVE} : Type` (0 constructors, the \
             Clean analogue of False/Empty), registered modulo 3 (inductive + recursor \
             `{NEVER_INDUCTIVE}.rec` axiom_deps EMPTY); uninhabited by construction, so \
             VALUE inhabitation stays fail-closed"
        ))
    }

    /// REAL-CODE COVERAGE (iterator combinators) — REAL-KERNEL modulo-3 gate for a
    /// stdlib ITERATOR ADAPTER: register the adapter's RECORD carrier
    /// `Trust.Adt.<Adapter>` (over its recovered source + closure / index / paired
    /// source) into a prelude `Environment`, together with EVERY nested carrier it
    /// references (the inner source adapter record, the closure record) collected by
    /// the SAME `reachable_adt_carriers` machinery, IN ORDER; then confirm the
    /// adapter inductive + recursor have EMPTY `axiom_deps` (⊆ the 3, NO 4th axiom).
    /// A `Copied`/`Cloned` adapter is TRANSPARENT to its source (no record of its
    /// own) — classify it via the source's verdict. Returns `Some(detail)` on success.
    fn iter_adapter_grounds_modulo_3_real_kernel(ty: &Ty) -> Option<String> {
        use clean_kernel::{Environment, Name};
        // A transparent `Copied`/`Cloned` adapter has no record of its own; its model
        // is its source iterator. Classify by recursing on the source.
        let Ty::Adt { name, .. } = ty else { return None };
        if reflect_iter_adapter_record(ty).is_none() {
            // Transparent adapter (or unrecoverable) — try the source iterator.
            if let Ok(ProofTerm::Const(n)) = reflect_ty(ty) {
                if n.starts_with(ADT_PREFIX) {
                    return Some(format!(
                        "transparent iterator adapter `{name}` → its source iterator's \
                         record carrier `{n}` (registered modulo 3)"
                    ));
                }
            }
            return None;
        }
        // Collect the adapter record + all nested records (source adapter, closure)
        // via the production reachability machinery, in post-order registration order.
        let func = single_local_func(ty);
        let carriers = crate::clean_ground::reachable_adt_carriers(&func);
        let adapter_name = reflect_iter_adapter_record(ty)?.name;
        let mut env = Environment::with_prelude();
        let registry = crate::clean_ground::register_adt_carriers(&mut env, &carriers);
        registry.get(&adapter_name)?;
        let ind = Name::from_string(&adapter_name);
        if !env.axiom_deps(&ind)?.is_empty() {
            return None;
        }
        let info = env.inductive_info(&ind)?;
        if let Some(rec) = info.recursor_name.as_ref() {
            if !env.axiom_deps(rec)?.is_empty() {
                return None;
            }
        }
        Some(format!(
            "iterator adapter record `{adapter_name}` (recovered source + closure/index) \
             registered modulo 3 over {} reachable carrier(s) (inductive + recursor \
             axiom_deps EMPTY — the closure field reuses the `Trust.Closure.*` record)",
            carriers.len()
        ))
    }

    /// A minimal `VerifiableFunction` with `ty` as its single local — the input the
    /// production `reachable_adt_carriers` walks, so the corpus gate registers an
    /// adapter exactly as the production pipeline does.
    fn single_local_func(ty: &Ty) -> VerifiableFunction {
        use trust_types::{LocalDecl, VerifiableBody, VerifiableFunction};
        let body = VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: ty.clone(), name: Some("_0".into()) }],
            blocks: vec![],
            arg_count: 0,
            return_ty: ty.clone(),
        };
        VerifiableFunction {
            name: "probe".into(),
            def_path: "crate::probe".into(),
            span: Default::default(),
            body,
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Classify ONE corpus type. Tries, in order: the family-specific REAL-KERNEL
    /// grounding (dyn / fn-ptr / closure / generic) for the families whose carrier
    /// the LOCAL predicative checker cannot resolve; then the local concrete check.
    /// A type that grounds by ANY route is STRUCTURAL-modulo-3; else OPAQUE.
    fn classify_type(ty: &Ty) -> TypeVerdict {
        // NEVER (`!`) — the standalone bottom type is the EMPTY INDUCTIVE
        // `Trust.Never` (a 0-constructor `Type`, the Clean analogue of
        // `False`/`Empty`). Dispatched FIRST — before the `reflect_ty` carrier
        // probe below — because `reflect_ty(Ty::Never)` deliberately stays
        // `Err(NeverType)` (the conservative COMPOSITION floor for `[!;N]`/`(_,!)`/
        // `!`-capture, all of which need an INHABITANT and fail closed). Reflecting
        // the TYPE does NOT require inhabiting it: the empty inductive registers +
        // grounds modulo 3 (inductive + recursor `axiom_deps` EMPTY), so the
        // standalone never type is STRUCTURAL, while VALUE-level inhabitation stays
        // fail-closed (no constructor → no `default_inhabitant`).
        if matches!(ty, Ty::Never) {
            return match never_grounds_modulo_3_real_kernel() {
                Some(d) => TypeVerdict::Structural(d),
                None => TypeVerdict::Opaque(
                    "never `!` empty inductive did NOT register modulo 3 in the real kernel".into(),
                ),
            };
        }

        // 0. fail-closed reflection ⇒ honestly opaque (e.g. a non-`!` fail-closed).
        let carrier = match reflect_ty(ty) {
            Ok(c) => c,
            Err(e) => return TypeVerdict::Opaque(format!("fail-closed: {e}")),
        };

        // TYPE-ZOO CLOSE (additive) — the six remaining families dispatch FIRST, by
        // their corpus-probe tag convention, to the dedicated real-kernel gates. These
        // route AHEAD of the base dyn/fn-ptr/closure dispatch so a tagged probe is
        // classified by its type-zoo grounding, not the base fallback. An untagged
        // dyn/fn-ptr/closure/coroutine keeps the existing base behavior below.
        match ty {
            // #1 CONST GENERICS — a fixed-size array `[T; N]` over a CONCRETE element
            // grounds at the length-indexed `Trust.ArrayN`. (A `[T; N]` over a generic
            // element keeps the existing parameterized-composite path; this probe is the
            // concrete-element length-indexed model `[i32; 4]`.)
            Ty::Array { elem, len }
                if reflect_ty(elem).is_ok() && bare_type_var(elem).is_none() =>
            {
                return match arrayn_grounds_modulo_3_real_kernel(elem, *len) {
                    Some(d) => TypeVerdict::Structural(d),
                    None => TypeVerdict::Opaque(
                        "length-indexed Trust.ArrayN did NOT ground modulo 3".into(),
                    ),
                };
            }
            // #2 impl Trait — tagged `@impl::<trait>` (an RPIT/TAIT existential).
            Ty::Dynamic { trait_name } if trait_name.starts_with("@impl::") => {
                let bare = trait_name.strip_prefix("@impl::").unwrap_or(trait_name);
                return match impl_trait_grounds_modulo_3_real_kernel(bare) {
                    Some(d) => TypeVerdict::Structural(d),
                    None => {
                        TypeVerdict::Opaque("impl Trait existential did NOT ground modulo 3".into())
                    }
                };
            }
            // #3 MULTI-BOUND dyn — a `+`-joined trait_name (`dyn A + B + Send`).
            Ty::Dynamic { trait_name } if trait_name.contains('+') => {
                return match multi_dyn_grounds_modulo_3_real_kernel(trait_name) {
                    Some(d) => TypeVerdict::Structural(d),
                    None => TypeVerdict::Opaque(
                        "multi-bound dyn existential did NOT ground modulo 3".into(),
                    ),
                };
            }
            // #5 GAT family — an Adt tagged `@gat::<Trait>::<Assoc>` with a generic param
            // field (a PARAMETERIZED associated-type family / type-level function).
            Ty::Adt { name, fields, .. } if name.starts_with("@gat::") => {
                let path = name.strip_prefix("@gat::").unwrap_or(name);
                let (tr, assoc) = path.rsplit_once("::").unwrap_or((path, "Assoc"));
                // The GAT parameters are the bare-generic-param fields' idents.
                let params: Vec<String> = fields
                    .iter()
                    .filter_map(|(_, fty)| bare_type_var(fty))
                    .filter_map(|v| v.strip_prefix(PARAM_PREFIX).map(ToString::to_string))
                    .collect();
                return match gat_grounds_modulo_3_real_kernel(tr, assoc, &params) {
                    Some(d) => TypeVerdict::Structural(d),
                    None => TypeVerdict::Opaque("GAT family did NOT ground modulo 3".into()),
                };
            }
            // #4 HRTB — a fn pointer whose signature has a REFERENCE parameter is treated
            // as the higher-ranked `for<'a> fn(&'a …)`: one region per `&`-borrowed param
            // (at least one). An ordinary fn-ptr (no reference param) keeps the base
            // fn-ptr-Pi path below.
            Ty::FnPtr { sig } if sig.params.iter().any(|p| matches!(p, Ty::Ref { .. })) => {
                let num_regions = sig.params.iter().filter(|p| matches!(p, Ty::Ref { .. })).count();
                return match hrtb_grounds_modulo_3_real_kernel(num_regions, sig) {
                    Some(d) => TypeVerdict::Structural(d),
                    None => TypeVerdict::Opaque("HRTB Π(region) did NOT ground modulo 3".into()),
                };
            }
            // #6 COROUTINE — its OWN state-record gate (distinct from the closure record).
            Ty::Coroutine { name, upvars } => {
                return match coroutine_grounds_modulo_3_real_kernel(name, upvars) {
                    Some(d) => TypeVerdict::Structural(d),
                    None => TypeVerdict::Opaque(
                        "coroutine state machine did NOT register modulo 3".into(),
                    ),
                };
            }
            _ => {}
        }

        // REAL-CODE COVERAGE (iterator combinators) — a KNOWN stdlib iterator adapter
        // reflects to its RECORD const `Trust.Adt.<Adapter>` (which the LOCAL concrete
        // checker cannot resolve, exactly like a named struct's inductive), so it
        // dispatches to the dedicated real-kernel record gate. A `Copied`/`Cloned`
        // adapter is transparent to its source's record (handled inside the gate). An
        // ADT that is NOT a recognized adapter falls through unchanged.
        if is_structural_iter_adapter(ty) {
            return match iter_adapter_grounds_modulo_3_real_kernel(ty) {
                Some(d) => TypeVerdict::Structural(d),
                None => TypeVerdict::Opaque(
                    "iterator adapter record did NOT register modulo 3 in the real kernel".into(),
                ),
            };
        }

        // 1. Family-specific real-kernel grounding for the BASE families whose carrier
        //    the LOCAL checker cannot resolve (dyn / fn-ptr / closure), so the
        //    measurement reflects the REAL kernel verdict, not the predicative one.
        match ty {
            Ty::Dynamic { trait_name } => {
                return match dyn_grounds_modulo_3_real_kernel(trait_name) {
                    Some(d) => TypeVerdict::Structural(d),
                    None => TypeVerdict::Opaque(
                        "dyn existential did NOT ground modulo 3 in the real kernel".into(),
                    ),
                };
            }
            Ty::FnPtr { .. } | Ty::FnDef { .. } => {
                return match fn_ptr_grounds_modulo_3_real_kernel(ty) {
                    Some(d) => TypeVerdict::Structural(d),
                    None => TypeVerdict::Opaque(
                        "fn-ptr did NOT decode to a real kernel Pi modulo 3".into(),
                    ),
                };
            }
            Ty::Closure { name, upvars, .. } => {
                return match closure_grounds_modulo_3_real_kernel(name, upvars) {
                    Some(d) => TypeVerdict::Structural(d),
                    None => TypeVerdict::Opaque(
                        "closure record did NOT register modulo 3 in the real kernel".into(),
                    ),
                };
            }
            _ => {}
        }

        // 2. A carrier that mentions a `Trust.Param.*` free const is a GENERIC type.
        //    The LOCAL `carrier_context` checker leaves the param UNRESOLVED, but the
        //    REAL kernel grounds it as the ∀(T:Type) Pi-bound inductive (STEP-2 fix).
        if carrier_mentions_param(&carrier) {
            return match generic_grounds_modulo_3_real_kernel(ty) {
                Some(d) => TypeVerdict::Structural(d),
                None => TypeVerdict::Opaque(
                    "generic type did NOT ground modulo 3 even in the real kernel \
                     (∀(T:Type) Pi-bound inductive failed the axiom gate)"
                        .into(),
                ),
            };
        }

        // 2b. FAITHFULNESS FIX (enum sum types) — a CONCRETE carrier that NAMES a
        //     registered ADT inductive `Trust.Adt.*` is a CONCRETE ENUM (whose faithful
        //     carrier is the multi-constructor inductive itself) OR a CONCRETE STRUCT that
        //     nests such an enum in field position (`ParseIntError`/`Utf8Error`). The
        //     LOCAL `carrier_context` checker declares only the `Trust.SortTy` vocabulary,
        //     so it cannot resolve the named inductive const — it would (incorrectly) call
        //     these OPAQUE. Route to the REAL kernel, which registers the reachable
        //     inductives (the type's own + nested) via `register_adt_carriers` and gates on
        //     EMPTY `axiom_deps`. This is the faithful, INJECTIVE sum-type grounding (the
        //     audit fix). A concrete struct with NO enum field has a pure `Prod` carrier
        //     (no `Trust.Adt.*`) and keeps the local path below — NO regression.
        if carrier_mentions_adt(&carrier) {
            return match named_adt_grounds_modulo_3_real_kernel(ty) {
                Some(d) => TypeVerdict::Structural(d),
                None => TypeVerdict::Opaque(
                    "concrete enum / record-over-enum did NOT register as a faithful \
                     multi-ctor inductive modulo 3 in the real kernel"
                        .into(),
                ),
            };
        }

        // 3. CONCRETE carrier: the existing local predicative path.
        match concrete_grounds_modulo_3_local(&carrier) {
            Some(d) => TypeVerdict::Structural(d),
            None => TypeVerdict::Opaque(
                "concrete carrier UNRESOLVED in carrier_context (axiom_deps NOT ⊆ the 3)".into(),
            ),
        }
    }

    /// FAITHFULNESS FIX (enum sum types) — whether a reflected `ProofTerm` carrier names
    /// a registered ADT inductive const `Trust.Adt.*` ANYWHERE (the type is a concrete
    /// enum, or a concrete struct nesting one as a field). The signal to route to the
    /// real-kernel named-inductive gate rather than the local predicative checker (which
    /// declares only the `Trust.SortTy` vocabulary and cannot resolve a named inductive).
    fn carrier_mentions_adt(term: &ProofTerm) -> bool {
        match term {
            ProofTerm::Const(n) => n.starts_with(ADT_PREFIX),
            ProofTerm::App(f, a) => carrier_mentions_adt(f) || carrier_mentions_adt(a),
            ProofTerm::Pi { domain, codomain, .. } => {
                carrier_mentions_adt(domain) || carrier_mentions_adt(codomain)
            }
            ProofTerm::Lambda { binder_type, body, .. } => {
                carrier_mentions_adt(binder_type) || carrier_mentions_adt(body)
            }
            ProofTerm::Var(_) | ProofTerm::Sort(_) => false,
        }
    }

    /// TYPE-REFLECTION COVERAGE — the honest coverage map over the type corpus. Each
    /// Rust type CONSTRUCTOR is reflected and classified STRUCTURAL-modulo-3 (a real
    /// Clean dependent-type carrier whose grounding rests on ⊆ the 3 axioms) or
    /// OPAQUE/unrooted (a free const / fail-closed that is NOT yet modulo 3). The
    /// generic, dyn, fn-ptr and closure families are classified by the REAL-KERNEL
    /// grounding, NOT the local predicative `carrier_context` check — so a `Wrapper<T>`
    /// counts as structural via its ∀(T:Type) Pi-bound inductive (STEP-2 fix).
    #[test]
    fn type_corpus_coverage() {
        let corpus = type_corpus();
        let total = corpus.len();
        let mut structural: Vec<&'static str> = Vec::new();
        let mut opaque: Vec<&'static str> = Vec::new();

        let mut report = String::new();
        report.push_str("\n================ TYPE-REFLECTION COVERAGE ================\n");
        report.push_str(
            "goal: EVERY Rust type is a Clean dependent type, \
             axiom_deps ⊆ {propext, Quot.sound, Classical.choice}\n",
        );
        for (name, source, ty) in &corpus {
            match classify_type(ty) {
                TypeVerdict::Structural(detail) => {
                    structural.push(name);
                    report.push_str(&format!("  [STRUCTURAL-modulo-3] {name:<22} {source}\n"));
                    report.push_str(&format!("        ↳ {detail}\n"));
                }
                TypeVerdict::Opaque(detail) => {
                    opaque.push(name);
                    report.push_str(&format!("  [OPAQUE/unrooted    ] {name:<22} {source}\n"));
                    report.push_str(&format!("        ↳ {detail}\n"));
                }
            }
        }
        report.push_str("---------------------------------------------------------\n");
        report.push_str(&format!("STRUCTURAL-modulo-3: {}/{total}\n", structural.len()));
        report.push_str(&format!("OPAQUE/unrooted    : {}/{total}\n", opaque.len()));
        report.push_str(&format!("structural set: {structural:?}\n"));
        report.push_str(&format!("opaque set    : {opaque:?}\n"));
        report.push_str("=========================================================\n");
        // Printed under `--nocapture`; the coverage map is the measurement artifact.
        println!("{report}");

        // INVARIANTS (the carriers the goal claims are structural, now incl. the
        // dyn-Sigma / fn-ptr-Pi / closure-record / generic-∀ fronts):
        let must_be_structural = [
            // scalars + pointers + concrete composites (the pre-existing structural set)
            "i8",
            "i32",
            "u8",
            "u64",
            "bool",
            "char",
            "f32",
            "f64",
            "unit",
            "ref_shared",
            // NEVER (`!`) → the EMPTY inductive `Trust.Never` (Clean analogue of False/
            // Empty); the TYPE is structural modulo 3, INHABITATION stays fail-closed.
            "never",
            "ptr_const",
            "struct_named",
            "struct_tuple",
            "enum_c_like",
            "enum_data",
            "vec",
            "string",
            "box",
            "option",
            "result",
            "array",
            "slice",
            "tuple3",
            "str",
            // REAL-CODE COVERAGE (collections) — maps → association-list `Slice (Prod K V)`
            "hashmap",
            "btreemap",
            // REAL-CODE COVERAGE (HashMap entry API) — `Entry<K,V>` → 2-variant enum
            "hashmap_entry",
            // REAL-CODE COVERAGE (iterator combinators) — adapters → real record carriers
            "slice_iter",
            "chars",
            "iter_map",
            "iter_filter",
            "iter_enumerate",
            "iter_zip",
            "iter_copied",
            // REAL-CODE COVERAGE (string-pattern iterators) — split/lines/char_indices →
            // real record carriers (remaining-input byte list + optional needle)
            "split_whitespace",
            "str_lines",
            "char_indices",
            "str_split",
            "str_splitn",
            // REAL-CODE COVERAGE (stdlib error enums/structs) — discriminant enum +
            // thin wrapper structs ground modulo 3 exactly like any user enum/struct
            "int_error_kind",
            "parse_int_error",
            "utf8_error",
            // dyn → Sigma existential (NO Trust.Dyn free const)
            "dyn_trait",
            // fn-ptr / fn-def → real kernel Pi
            "fn_ptr",
            "fn_def",
            // closures → record inductive
            "closure_fn",
            "closure_fnmut",
            "closure_fnonce",
            // generics → ∀(T:Type) Pi-bound inductive (STEP-2 fix)
            "struct_generic",
            "enum_generic",
            "option_generic",
            "const_generic_array",
            "assoc_type",
            // TYPE-ZOO CLOSE — the six remaining families as REAL Clean dependent types:
            "const_generic_indexed", // #1 length-indexed Trust.ArrayN (N a real Nat index)
            "impl_trait",            // #2 impl Trait → existential Σ(T:Type) Vtable T
            "dyn_multi_bound",       // #3 dyn A + B + Send → conjoined-vtable existential
            "hrtb_fn",               // #4 for<'a> Fn → Π(r : Trust.Region) over the fn arrow
            "gat_family",            // #5 GAT → parameterized type-level-function family
            "coroutine",             // #6 coroutine → state record (env + resume : S → Y)
        ];
        for name in must_be_structural {
            assert!(
                structural.contains(&name),
                "`{name}` MUST be STRUCTURAL-modulo-3 but was classified OPAQUE — \
                 a carrier regressed. Map:\n{report}"
            );
        }

        // The goal gate: dyn carries NO `Trust.Dyn` free const (it is a registered
        // existential), so it is structural — assert that explicitly here too.
        assert!(
            structural.contains(&"dyn_trait"),
            "dyn Trait must be the registered Sigma existential, NOT a Trust.Dyn free const"
        );

        // Sanity: counts partition the corpus.
        assert_eq!(structural.len() + opaque.len(), total, "every corpus type is classified");
    }

    /// PRODUCTION-WIRING GATE — the six TYPE-ZOO carriers are emitted by the MAIN
    /// `reflect_ty` grounding pipeline (the one mirsem/§6/the prover consume), NOT only by
    /// the dedicated `reflect_array_indexed`/`reflect_impl_trait`/… entry points. For EACH
    /// type-zoo corpus probe, the PRODUCTION `reflect_ty(probe_ty)` output is asserted to be
    /// EXACTLY the carrier the dedicated entry point builds — so the 54/55 coverage is
    /// ACTUAL in production, not merely measured through a side channel. A regression that
    /// reverted any arm to its fallback (`Ty::Array`→`Trust.Sort.Vec`, single-`dyn`-only,
    /// `Ty::Coroutine`→closure record, …) would fail HERE.
    #[test]
    fn type_zoo_carriers_are_emitted_by_production_reflect_ty() {
        let corpus = type_corpus();
        let by_name = |n: &str| {
            corpus.iter().find(|(name, _, _)| *name == n).map(|(_, _, t)| t.clone()).unwrap()
        };

        // #1 CONST GENERICS — `[i32; 4]` reflects to the length-indexed `Trust.ArrayN`, NOT
        // the length-erased `Trust.Sort.Vec`. The production arm == the dedicated entry point.
        let arr = by_name("const_generic_indexed");
        let arr_carrier = reflect_ty(&arr).expect("array reflects");
        assert_eq!(
            arr_carrier,
            reflect_array_indexed(&Ty::Int { width: 32, signed: true }, 4).unwrap(),
            "PRODUCTION reflect_ty([i32;4]) must be the length-indexed Trust.ArrayN carrier"
        );
        // The head is `Trust.ArrayN`, NOT `Trust.Sort.Vec`.
        let head_is = |term: &ProofTerm, c: &str| {
            let mut h = term;
            while let ProofTerm::App(f, _) = h {
                h = f;
            }
            matches!(h, ProofTerm::Const(n) if n == c)
        };
        assert!(head_is(&arr_carrier, CARRIER_ARRAYN), "array head is Trust.ArrayN");
        assert!(!head_is(&arr_carrier, CARRIER_VEC), "array head is NOT the erased Trust.Sort.Vec");

        // #2 impl Trait — `@impl::Iterator` reflects to the DISTINCT `Trust.Impl.*` existential
        // const, NOT a `Trust.Dyn.*`.
        let imp = by_name("impl_trait");
        let imp_carrier = reflect_ty(&imp).expect("impl Trait reflects");
        assert_eq!(
            imp_carrier,
            cst(&impl_trait_const_name("core::iter::Iterator")),
            "PRODUCTION reflect_ty(@impl::Iterator) must be the Trust.Impl.* existential const"
        );
        assert!(
            matches!(&imp_carrier, ProofTerm::Const(n) if n.starts_with(IMPL_TRAIT_PREFIX)),
            "impl Trait uses the Trust.Impl.* name, not Trust.Dyn.*"
        );

        // #3 MULTI-BOUND dyn — keyed on the WHOLE `+`-joined string (distinct from `dyn A`).
        let multi = by_name("dyn_multi_bound");
        let multi_carrier = reflect_ty(&multi).expect("multi-bound dyn reflects");
        assert_eq!(
            multi_carrier,
            cst(&reflect_multi_dyn("core::fmt::Debug + core::clone::Clone + Send", &[]).name),
            "PRODUCTION reflect_ty(dyn A + B + Send) must be the conjoined existential const"
        );
        // Distinct from the single-bound `dyn core::fmt::Debug`.
        assert_ne!(
            reflect_ty(&multi).unwrap(),
            reflect_ty(&Ty::Dynamic { trait_name: "core::fmt::Debug".into() }).unwrap(),
            "the multi-bound existential is keyed on the whole `+`-joined string"
        );

        // #4 HRTB — a fn-ptr with a reference param reflects to `Π(r : Trust.Region) → arrow`.
        let hrtb = by_name("hrtb_fn");
        let hrtb_carrier = reflect_ty(&hrtb).expect("HRTB reflects");
        match &hrtb_carrier {
            ProofTerm::Pi { domain, .. } => {
                assert_eq!(
                    **domain,
                    cst(CARRIER_REGION),
                    "the for<'a> binder is Π(r : Trust.Region)"
                );
            }
            other => panic!("HRTB must be Π(region) → arrow, got {other:?}"),
        }
        let Ty::FnPtr { sig } = &hrtb else { panic!("hrtb_fn probe is a fn-ptr") };
        assert_eq!(
            hrtb_carrier,
            reflect_hrtb_fn(1, sig).unwrap(),
            "production == dedicated HRTB entry"
        );

        // #5 GAT — `@gat::Iterator::Item` over a `Type` param reflects to the parameterized
        // `Trust.Gat.*` family APPLIED to its param const.
        let gat = by_name("gat_family");
        let gat_carrier = reflect_ty(&gat).expect("GAT reflects");
        assert!(
            head_is(&gat_carrier, &gat_family_name("core::iter::Iterator", "Item")),
            "PRODUCTION reflect_ty(@gat::Iterator::Item<P>) must head with the Trust.Gat.* family"
        );
        // It is an APPLICATION (family applied to ≥1 GAT param), not a bare const.
        assert!(
            matches!(gat_carrier, ProofTerm::App(_, _)),
            "the GAT family is applied to its param"
        );

        // #6 COROUTINE — reflects to its OWN state record `Trust.Coroutine.*`, DISTINCT from a
        // closure's `Trust.Closure.*`.
        let coro = by_name("coroutine");
        let coro_carrier = reflect_ty(&coro).expect("coroutine reflects");
        assert!(
            head_is(&coro_carrier, &coroutine_inductive_name("{coroutine#0}")),
            "PRODUCTION reflect_ty(coroutine) must head with the Trust.Coroutine.* state record"
        );
        // NOT the closure record name (a coroutine carries a suspend-point state).
        assert!(
            !head_is(&coro_carrier, &closure_inductive_name("{coroutine#0}")),
            "a coroutine is NOT the Trust.Closure.* record"
        );
    }

    // ======================================================================
    // EXPANDED TRUST TYPES COVERAGE — the verification types Trust adds BEYOND
    // Rust (refinement / liquid subset, invariant-carrying, spec'd-dependent-
    // function) as REAL Clean DEPENDENT types modulo 3. Each probe reflects via
    // its dedicated entry point and is classified by GROUNDING the carrier in the
    // REAL clean-kernel prelude (`ground_verification_type`) and confirming the
    // verdict is `Modulo3` (transitive `axiom_deps` EMPTY — ⊆ the 3, NO 4th axiom).
    // The refinement subset reuses the prelude `Subtype`; the spec'd function is a
    // kernel `Π … → Subtype …`. A DELIBERATELY fail-closed probe (a refinement over
    // an uninhabitable base) is recorded as FAIL-CLOSED, NOT structural.
    // ======================================================================

    /// The verdict of classifying one EXPANDED-TRUST-TYPE probe.
    #[derive(Debug, Clone, PartialEq, Eq)]
    enum VTypeVerdict {
        /// The carrier grounded in the real kernel prelude with EMPTY `axiom_deps`
        /// (⊆ the 3 — a real Clean dependent type modulo 3).
        StructuralModulo3,
        /// The carrier did NOT ground modulo 3 (residue / kernel-rejected) — a hole.
        NotModulo3(String),
        /// The probe FAILED CLOSED at reflection (no faithful carrier) — SOUND.
        FailClosed(String),
    }

    /// Classify ONE verification-type probe by GROUNDING its carrier in the real
    /// clean-kernel prelude and gating on the kernel's own `axiom_deps` being empty.
    fn classify_verification_type(probe: &VerificationTypeProbe) -> VTypeVerdict {
        use clean_kernel::Environment;
        match &probe.carrier {
            Err(e) => VTypeVerdict::FailClosed(format!("{e}")),
            Ok(carrier) => {
                let mut env = Environment::with_prelude();
                match crate::clean_ground::ground_verification_type(
                    &mut env,
                    carrier,
                    &format!("Trust.measure.vtype.{}", probe.name),
                ) {
                    crate::clean_ground::GroundOutcome::Modulo3 => VTypeVerdict::StructuralModulo3,
                    crate::clean_ground::GroundOutcome::Residue(r) => {
                        VTypeVerdict::NotModulo3(format!("residue: {r:?}"))
                    }
                    crate::clean_ground::GroundOutcome::KernelRejected(m) => {
                        VTypeVerdict::NotModulo3(format!("kernel rejected: {m}"))
                    }
                    crate::clean_ground::GroundOutcome::NotGrounded => {
                        VTypeVerdict::NotModulo3("not grounded (to_clean_expr fail-closed)".into())
                    }
                }
            }
        }
    }

    /// EXPANDED-TRUST-TYPES COVERAGE — the honest coverage map over the verification
    /// types Trust adds beyond Rust. Each is reflected to its Clean dependent carrier
    /// and classified STRUCTURAL-modulo-3 (grounds in the real kernel prelude with
    /// EMPTY `axiom_deps`) / FAIL-CLOSED (sound — no faithful carrier) / NOT-modulo-3.
    /// The refinement subset is the prelude `Subtype` (a dependent SUBSET type); the
    /// spec'd function is a kernel `Π … → Subtype …`. Both rest on ⊆ the 3 (NO 4th
    /// axiom — the prelude `Subtype`/`Pi` are foundationally grounded).
    #[test]
    fn expanded_trust_types_coverage() {
        let corpus = verification_type_corpus();
        let total = corpus.len();
        let mut structural: Vec<&'static str> = Vec::new();
        let mut fail_closed: Vec<&'static str> = Vec::new();
        let mut not_modulo_3: Vec<&'static str> = Vec::new();

        let mut report = String::new();
        report.push_str("\n========== EXPANDED TRUST TYPES COVERAGE ==========\n");
        report.push_str(
            "goal: every Trust VERIFICATION type (refinement {v:T|φ}, invariant-carrying, \
             spec'd-dependent-function) is a Clean DEPENDENT type, axiom_deps ⊆ \
             {propext, Quot.sound, Classical.choice}\n",
        );
        for probe in &corpus {
            match classify_verification_type(probe) {
                VTypeVerdict::StructuralModulo3 => {
                    structural.push(probe.name);
                    report.push_str(&format!(
                        "  [STRUCTURAL-modulo-3] {:<26} {}\n",
                        probe.name, probe.source
                    ));
                    report.push_str(
                        "        ↳ grounds to the prelude `Subtype`/`Pi` dependent type; \
                         axiom_deps EMPTY (⊆ the 3, NO 4th axiom)\n",
                    );
                }
                VTypeVerdict::FailClosed(d) => {
                    fail_closed.push(probe.name);
                    report.push_str(&format!(
                        "  [FAIL-CLOSED (sound) ] {:<26} {}\n",
                        probe.name, probe.source
                    ));
                    report.push_str(&format!("        ↳ {d}\n"));
                }
                VTypeVerdict::NotModulo3(d) => {
                    not_modulo_3.push(probe.name);
                    report.push_str(&format!(
                        "  [NOT-modulo-3 (HOLE) ] {:<26} {}\n",
                        probe.name, probe.source
                    ));
                    report.push_str(&format!("        ↳ {d}\n"));
                }
            }
        }
        report.push_str("---------------------------------------------------\n");
        report.push_str(&format!("STRUCTURAL-modulo-3: {}/{total}\n", structural.len()));
        report.push_str(&format!("FAIL-CLOSED (sound): {}/{total}\n", fail_closed.len()));
        report.push_str(&format!("NOT-modulo-3 (hole): {}/{total}\n", not_modulo_3.len()));
        report.push_str(&format!("structural set: {structural:?}\n"));
        report.push_str(&format!("fail-closed set: {fail_closed:?}\n"));
        report.push_str("===================================================\n");
        println!("{report}");

        // Every refinement / invariant / spec'd-function probe that reflects MUST
        // ground modulo 3 in the real kernel (the prelude `Subtype`/`Pi` dependent
        // types). A regression that broke the `Trust.Sigma → Subtype` grounding, or
        // that made a refinement carrier depend on a 4th axiom, would fail HERE.
        let must_be_structural = [
            "refine_pos_i32",       // {v:i32 | v>0}            → Subtype Int (λv. 0<v)
            "refine_bounded_u8",    // {v:u8  | v<128}          → Subtype Int (λv. v<128)
            "refine_bool_true",     // {v:bool| v}              → Subtype Bool (λv. v=true)
            "invariant_nonneg_i32", // i32 #[invariant(v>=0)]   → Subtype Int (λv. 0<=v)
            "spec_fn_inc",          // fn(x>0) -> {r | r>x}     → Π(x:Int),P → Subtype Int …
            "spec_fn_total",        // fn(true) -> {r | r>=0}   → Π … → Subtype …
        ];
        for name in must_be_structural {
            assert!(
                structural.contains(&name),
                "`{name}` MUST be a STRUCTURAL-modulo-3 Clean dependent type but was not — \
                 the refinement/spec carrier failed to ground modulo 3. Map:\n{report}"
            );
        }

        // The negative control is SOUNDLY fail-closed (a refinement over `!` has no
        // witness carrier — a quantified Σ over a real carrier beats an opaque const).
        assert!(
            fail_closed.contains(&"refine_never_fail_closed"),
            "a refinement over the uninhabitable `!` base MUST fail closed (no witness carrier)"
        );

        // NO unsoundness: nothing is a NOT-modulo-3 hole (every probe is either a real
        // dependent type modulo 3, or soundly fail-closed).
        assert!(
            not_modulo_3.is_empty(),
            "no verification type may be a NOT-modulo-3 hole, got {not_modulo_3:?}:\n{report}"
        );

        // Counts partition the corpus.
        assert_eq!(
            structural.len() + fail_closed.len() + not_modulo_3.len(),
            total,
            "every verification-type probe is classified"
        );
    }

    /// PRODUCTION GROUNDING — the refinement subset carrier is EXACTLY the prelude
    /// `Subtype`, the SAME dependent SUBSET type the postcondition Σ grounds to. This
    /// pins the equivalence: `{v:T|φ}` reflects to `Trust.Sigma R(T) (λv. φ)`, and
    /// `to_clean_expr` decodes that `CARRIER_SIGMA` head to the kernel `Subtype` — so
    /// a refinement type IS a `Subtype`, not a bespoke carrier.
    #[test]
    fn refinement_carrier_is_the_prelude_subtype() {
        // `{v : i32 | v > 0}` → `Trust.Sigma <Int-carrier> (λ v. Gt v 0)`.
        let pred =
            Formula::Gt(Box::new(Formula::Var("v".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let carrier =
            reflect_refinement("v", &Ty::Int { width: 32, signed: true }, &pred).expect("refines");
        // The HEAD constant is `CARRIER_SIGMA` (the same one the postcondition pair uses).
        let mut head = &carrier;
        while let ProofTerm::App(f, _) = head {
            head = f;
        }
        assert!(
            matches!(head, ProofTerm::Const(n) if n == CARRIER_SIGMA),
            "a refinement type heads with Trust.Sigma (→ prelude Subtype), got {head:?}"
        );
        // It DECODES to a kernel Expr whose head is the prelude `Subtype` const.
        let expr = crate::clean_ground::to_clean_expr(&carrier)
            .expect("the refinement subset grounds to a kernel Expr");
        let s = format!("{expr:?}");
        assert!(
            s.contains("Subtype"),
            "the refinement subset decodes to the prelude `Subtype` dependent type, got: {s}"
        );
    }

    // === GOAL-ITEM 3 — FAITHFUL DISPATCH (pure-data term builders) ============

    /// STATIC DISPATCH — distinct impls of the SAME (trait, method) at DIFFERENT
    /// concrete types get DISTINCT definition names, so a wrong-impl dispatch can
    /// never alias onto the right one (the naming precondition for fail-closed).
    #[test]
    fn static_dispatch_names_are_distinct_per_concrete_impl() {
        let d_i32 = reflect_static_dispatch(
            "core::fmt::Display",
            "fmt",
            "i32",
            cst("Trust.Int.add"),
            cst(PROP_INT),
        );
        let d_u8 = reflect_static_dispatch(
            "core::fmt::Display",
            "fmt",
            "u8",
            cst("Trust.Int.mul"),
            cst(PROP_INT),
        );
        assert!(d_i32.name.starts_with(DISPATCH_PREFIX));
        assert_ne!(d_i32.name, d_u8.name, "distinct concrete impls → distinct dispatch names");
        // The SAME (trait, method, concrete) is stable (two call sites share one def).
        assert_eq!(d_i32.name, dispatch_def_name("core::fmt::Display", "fmt", "i32"));
    }

    /// GENERIC MONOMORPHIZATION — substituting the generic param carrier with a
    /// concrete carrier replaces EVERY occurrence, and the result no longer
    /// mentions the param (the monomorphized body is concrete, not the opaque).
    #[test]
    fn substitute_param_replaces_every_occurrence_and_erases_the_param() {
        // A body `id : Param → Param` shaped `λ(x : Trust.Param.T/#0). x` whose
        // binder TYPE is the param carrier (the generic occurrence to monomorphize).
        let body = ProofTerm::Lambda {
            binder_name: "x".into(),
            binder_type: Box::new(cst(&param_const_name("T/#0"))),
            body: Box::new(ProofTerm::Var(0)),
        };
        assert!(body_mentions_param(&body, "T/#0"), "the generic body references the param");
        // Monomorphize at `i32` (carrier `Trust.Sort.Int`).
        let mono = substitute_param(&body, "T/#0", &cst(CARRIER_INT));
        assert!(!body_mentions_param(&mono, "T/#0"), "monomorphized body no longer opaque in T");
        // The binder type is now the concrete carrier.
        let ProofTerm::Lambda { binder_type, .. } = &mono else { panic!("still a λ") };
        assert!(matches!(&**binder_type, ProofTerm::Const(n) if n == CARRIER_INT));
    }

    /// A body that does NOT mention the param is not genuinely generic in it —
    /// `body_mentions_param` returns false, so a caller declines a vacuous
    /// "monomorphization" (guarding against an Eq.refl-on-equal-terms shortcut).
    #[test]
    fn body_not_mentioning_param_is_not_monomorphizable() {
        let body = cst("Trust.Int.add"); // no Param carrier anywhere
        assert!(!body_mentions_param(&body, "T/#0"));
        // Substitution is a no-op (structurally unchanged).
        assert_eq!(substitute_param(&body, "T/#0", &cst(CARRIER_INT)), body);
    }

    /// CLOSURE DISPATCH — the invocation definition name derives from the closure
    /// inductive name (a closure named `c` invokes as `Trust.ClosureCall.c`),
    /// keeping the closure record and its invocation linked but distinct.
    #[test]
    fn closure_call_name_derives_from_closure_inductive() {
        assert_eq!(closure_call_name("c"), "Trust.ClosureCall.c");
        assert_eq!(closure_inductive_name("c"), "Trust.Closure.c");
        // Distinct closures get distinct invocation defs.
        assert_ne!(closure_call_name("c"), closure_call_name("d"));
    }
}
