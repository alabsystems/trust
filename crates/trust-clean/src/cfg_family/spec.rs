// Trust: M4 v0 — CfgFamilySpec, the typed Rust description of a bounded CFG
// family (reports/m4-general-cfg-induction-framework-design-2026-07-07.md
// §4.1). A `CfgFamilySpec` is a compile-time-constant description (~20-40
// lines) that `plan.rs` compiles into a visit trace and `emit.rs` renders
// into Lean.
//
// ANTI-INJECTION (design §2, requirement 4): every field below is a typed
// enum or a `&'static` literal fixed at compile time by the family author —
// never a runtime string. `emit.rs` renders Lean source ONLY by matching on
// these enums and formatting their payload numerals/idents; there is no path
// from an arbitrary caller-supplied string into a `r#"…"#` Lean fragment.
//
// CLOSED BY DESIGN: the enums here intentionally do NOT cover `Switch`,
// integer-guard `CondBr`, `Unreachable`, `Call`/interprocedural, or aggregate
// instructions beyond the ones listed — requesting them is a Rust compile
// error (no variant exists), not a silent misgeneration. `ComposeLevel` has
// no `C2` variant at all: a ground fuel-k(k>=2) corollary is not a value
// this type can hold, so the "no ground multi-visit `stepNWithContext`"
// design ban (B2/E2) is enforced by the type system, not by a runtime check
// that a bug could bypass. `ComposeLevel::C1` IS representable (the design's
// "candidate, measure before trusting" tier) but `plan.rs` refuses it
// unconditionally in v0 — see `envelope.rs`'s `UnmeasuredComposition`: v0
// does not implement the v0.5 measurement harness, so there is no evidence
// basis to assert C1 in gate-loaded sources yet.

/// Lean integer/bool type literal. Closed vocabulary (extend deliberately —
/// each new variant needs a `width()`/`lean()` arm and, for the symbolic-core
/// templates, a bit-width-appropriate `ValueLit`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TyLit {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    Bool,
}

impl TyLit {
    /// The fully-qualified `TrustIr.Ty.*` constructor.
    #[must_use]
    pub const fn lean(self) -> &'static str {
        match self {
            TyLit::I8 => "TrustIr.Ty.I8",
            TyLit::I16 => "TrustIr.Ty.I16",
            TyLit::I32 => "TrustIr.Ty.I32",
            TyLit::I64 => "TrustIr.Ty.I64",
            TyLit::I128 => "TrustIr.Ty.I128",
            TyLit::U8 => "TrustIr.Ty.U8",
            TyLit::U16 => "TrustIr.Ty.U16",
            TyLit::U32 => "TrustIr.Ty.U32",
            TyLit::U64 => "TrustIr.Ty.U64",
            TyLit::U128 => "TrustIr.Ty.U128",
            TyLit::Bool => "TrustIr.Ty.Bool",
        }
    }

    /// Integer bit width, or `None` for `Bool` (which carries no
    /// `semIntBinOp`-style width argument).
    #[must_use]
    pub const fn width(self) -> Option<u32> {
        match self {
            TyLit::I8 | TyLit::U8 => Some(8),
            TyLit::I16 | TyLit::U16 => Some(16),
            TyLit::I32 | TyLit::U32 => Some(32),
            TyLit::I64 | TyLit::U64 => Some(64),
            TyLit::I128 | TyLit::U128 => Some(128),
            TyLit::Bool => None,
        }
    }

    /// A width-matching `TyLit` for rendering purposes. `semIntBinOp` (and
    /// every value the emitter renders from a [`crate::cfg_family::plan::ResolvedInst`])
    /// carries only a bare `Nat` width, never a signedness bit — the
    /// `TrustIr.Value.int {w} {v}` rendering is IDENTICAL for `I8`/`U8`, so
    /// which signed/unsigned variant this picks is immaterial; it exists
    /// only so callers that need "some `TyLit` of this width" (to reuse
    /// `Known::as_value_lean`) have one.
    #[must_use]
    pub const fn from_width(width: u32) -> TyLit {
        match width {
            8 => TyLit::I8,
            16 => TyLit::I16,
            32 => TyLit::I32,
            64 => TyLit::I64,
            _ => TyLit::I128,
        }
    }
}

/// A GROUND (fully concrete) value literal — `TrustIr.Value.int`/`.bool`.
#[derive(Debug, Clone, Copy)]
pub enum ValueLit {
    Int { width: u32, value: i128 },
    Bool(bool),
}

impl ValueLit {
    /// Render the `TrustIr.Value.*` literal. Negative integers are
    /// parenthesized (`(-5)`) — Lean's greedy application parser needs the
    /// grouping wherever this ends up spliced as an argument to something
    /// else (which is everywhere `emit.rs` uses it).
    #[must_use]
    pub fn lean(self) -> String {
        match self {
            ValueLit::Int { width, value } if value < 0 => {
                format!("TrustIr.Value.int {width} ({value})")
            }
            ValueLit::Int { width, value } => format!("TrustIr.Value.int {width} {value}"),
            ValueLit::Bool(b) => format!("TrustIr.Value.bool {b}"),
        }
    }
}

/// One block-parameter argument or instruction operand's abstract binding at
/// the theorem head: either a ground literal, or a symbolic identifier
/// universally bound (`∀ ident : ty.leanCarrier, …`) at the head of every
/// per-visit lemma that mentions it.
#[derive(Debug, Clone, Copy)]
pub enum ArgSpec {
    Ground(ValueLit),
    /// `ident` becomes a Lean binder name; MUST be a valid Lean identifier
    /// (family authors are trusted code, not runtime input — see the module
    /// doc's anti-injection note).
    Symbolic {
        ident: &'static str,
        ty: TyLit,
    },
}

/// A binary op, closed to the three ops the value-arm bridge ([`ARMS`] in
/// `trustir_bridge.rs`) has already proven under the `Hyp::NoOverflowLo/Hi`
/// side condition (`bridge_add`/`bridge_sub`/`bridge_mul`, all "Form B" —
/// see `trustir_bridge.rs`'s `ArmForm::B`). Every other `semIntBinOp` arm
/// (`UDiv`, float ops, bitwise ops, …) needs its own cited-lemma + hypothesis
/// shape (guarded division, no side condition, …) before it can be a
/// `InstSpec::BinOp` operand here — a mechanical but real per-op extension,
/// deliberately not attempted in v0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOpLit {
    Add,
    Sub,
    Mul,
}

impl BinOpLit {
    #[must_use]
    pub const fn lean(self) -> &'static str {
        match self {
            BinOpLit::Add => "TrustIr.BinOp.Add",
            BinOpLit::Sub => "TrustIr.BinOp.Sub",
            BinOpLit::Mul => "TrustIr.BinOp.Mul",
        }
    }

    /// The already-loaded (by [`ARMS`]) value-arm bridge lemma name this op
    /// cites when its operands are symbolic (E6: the generated family's
    /// dependency closure).
    #[must_use]
    pub const fn bridge_lemma(self) -> &'static str {
        match self {
            BinOpLit::Add => "bridge_add",
            BinOpLit::Sub => "bridge_sub",
            BinOpLit::Mul => "bridge_mul",
        }
    }

    /// The Clean/Lean-core value-level function `bridge_<op>` equates
    /// `semIntBinOp` to.
    #[must_use]
    pub const fn value_fn(self) -> &'static str {
        match self {
            BinOpLit::Add => "Int.add",
            BinOpLit::Sub => "Int.sub",
            BinOpLit::Mul => "Int.mul",
        }
    }

    /// A DIFFERENT op's value function, used only to build a T8
    /// wrong-final-value forgery probe: claims `other lhs rhs` instead of
    /// the true `self.value_fn() lhs rhs`. Any pair of DISTINCT ops works —
    /// the probe only needs a claim the kernel cannot prove equal to the
    /// true one for symbolic (free) operands, not a claim that differs for
    /// every concrete instantiation.
    #[must_use]
    pub const fn subtract_variant(self) -> &'static str {
        match self {
            BinOpLit::Add => "Int.sub",
            BinOpLit::Sub | BinOpLit::Mul => "Int.add",
        }
    }

    /// Constant-fold two GROUND operands (used only on the all-ground path,
    /// where the generated visit is a plain `rfl` and never cites
    /// `bridge_<op>` — the planner does not need to reprove no-overflow for
    /// that path, matching T1/T2's "ground visit" shape exactly).
    #[must_use]
    pub const fn fold(self, l: i128, r: i128) -> i128 {
        match self {
            BinOpLit::Add => l + r,
            BinOpLit::Sub => l - r,
            BinOpLit::Mul => l * r,
        }
    }
}

/// One instruction in a block body. v0 closes this to `BinOp` — the
/// symbolic-core motive table (design §3, T3/T4) is per-shape (`UnOp`,
/// `ICmp`, `Overflow`, `Cast` each need their own `Except`/`Bool`/pair motive
/// and cited-lemma family); adding a variant is the natural v0.5+ extension,
/// not a redesign, but each one is a real, unmeasured combination until
/// exercised.
#[derive(Debug, Clone, Copy)]
pub enum InstSpec {
    BinOp { op: BinOpLit, ty: TyLit, lhs: u32, rhs: u32 },
}

/// A block terminator. v0 closes this to `Return`/`Br` (unconditional) —
/// `CondBr` (branching) is the v1 target (design §7 "v1 — branching"); adding
/// it here before the per-guard-literal planner support lands would let a
/// spec silently request an unbounded/undecidable trace.
#[derive(Debug, Clone, Copy)]
pub enum TermSpec {
    Return(&'static [u32]),
    /// Unconditional branch to `target` (an index into `CfgFamilySpec::blocks`).
    Br {
        target: usize,
        args: &'static [u32],
    },
}

/// One basic block. `dests[i]` is `insts[i]`'s `bodyResultDests` row — v0
/// requires exactly one destination id per instruction (single-result
/// instructions only, matching `InstSpec`'s current closed vocabulary).
#[derive(Debug, Clone, Copy)]
pub struct BlockSpec {
    pub params: &'static [(u32, TyLit)],
    pub insts: &'static [InstSpec],
    pub dests: &'static [u32],
    pub term: TermSpec,
}

/// The composition level asserted for a `BoundedRun` claim (design §3, T5).
/// `C2` (ground `f := 0` corollary) deliberately has NO variant — see the
/// module doc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComposeLevel {
    /// C0 — conjunction of per-visit lemmas, safe by construction. The only
    /// level the v0 gate asserts.
    C0,
    /// C1 — transitive prefix chain (`Eq.trans`-composed). Representable so
    /// the type vocabulary matches the design, but `plan.rs` refuses it
    /// unconditionally until the v0.5 measurement harness lands (see
    /// `envelope::EnvelopeError::UnmeasuredComposition`).
    C1,
}

/// What a family claims about its trace. v0 closes this to `BoundedRun` —
/// `Diverges`/T7 (unbounded-fuel induction) is v2 scope (design §7).
#[derive(Debug, Clone, Copy)]
pub enum ClaimSpec {
    BoundedRun { compose: ComposeLevel },
}

/// Which mode(s) run this family's probes/visits. v0's two registered
/// families are both cheap (a single visit) so both run in both modes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModeSlice {
    AllModes,
    FullOnly,
}

/// The whole family: a bounded CFG, its entry point/arguments, and one
/// claim. ~20-40 lines per family (design §4.4's cost model).
#[derive(Debug, Clone, Copy)]
pub struct CfgFamilySpec {
    /// Prefix for every generated Lean identifier — must be unique across
    /// the whole cumulative gate `Environment` (E7; checked by
    /// `envelope::check_registry_unique` over [`GENERATED_FAMILIES`]).
    pub name: &'static str,
    pub blocks: &'static [BlockSpec],
    pub entry: usize,
    pub entry_args: &'static [ArgSpec],
    pub claims: &'static [ClaimSpec],
    pub mode: ModeSlice,
}
