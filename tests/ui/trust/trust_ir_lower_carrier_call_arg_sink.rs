//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//! STATUS ON MAIN (2026-09-24). Written on the seal line with b9bf2c898a (2026-09-08). Main
//! closed the `Direct` half on its own on 2026-09-22 (the callarg-unit fix: the typed sink in
//! `lower_call_args` now covers local AND signed extern callees, tagged
//! `Call(opaque carrier typed argument)` rather than the `Call(opaque carrier typed sink)`
//! spelling below). The CLOSURE half was still open there: on the sealed trust-7d5533b2 (main
//! of 2026-09-23) this file WARNed `CallArgTypeMismatch { callee:
//! "dispatch_closure::{closure#0}", arg_index: 1, expected: "ptr", actual: "()" }`, because
//! `lower_closure_call_untupled` still passed `callee_is_local = false`. The port that carries
//! this file passes the real flag. The prose below is the seal-line record, unchanged.
//!
//! Trust (wave-CSA): a UNIT `()` handed to a call argument slot where the callee's declaration
//! says `ptr` — the CALL-ARGUMENT typed sink of the wave-CS opaque-carrier contract, the one
//! sink of the four that was never wired up.
//!
//! THE DEFECT. `lower_enum_match_opaque` (wave-EMO) lowers a `match` over an OPAQUE-LANE enum —
//! one `register_enum` declined end-to-end (`is_opaque_lane_enum`) — as an N-way nondeterministic
//! split, and binds EVERY payload binding of EVERY arm to one fresh
//! `Const { ty: Ty::Unit, value: PhantomData }`, joined to `opaque_carrier_locals`. Its stated
//! premise is that "every value-needing use of it fails closed at its own site or rides an opaque
//! channel". A plain VarRef READ of a carrier local is neither: the `ExprKind::VarRef` arm hands
//! the raw `Ty::Unit` value straight back, `lower_expr` SUCCEEDS, and `lower_call_args` pushes it
//! into argument 0 of a LOCAL callee whose spliced `Function` declares the real mapped param —
//! `lower_fn` signs `&Self` as `Ty::Ptr`. The assembled module then carries a `()` across a call
//! edge that declares a pointer, and final Trust-IR module validation is right to reject it:
//!
//!   CallArgTypeMismatch { block: 1, callee: "<Memory as Backend>::line_count", arg_index: 0,
//!                         expected: "ptr", actual: "()" }
//!
//! i.e. a unit passed where the RECEIVER POINTER belongs. The producer's own #189 note at
//! `foreach_summary_scan` (removed with the wave-ER summary on 2026-10-01) already NAMED this
//! sink — "the implicit `Return` (nn's ReturnTypeMismatch), a struct/tuple `InsertField` (ny's
//! OperandTypeMismatch), a call argument, or a join parameter" — and
//! `Return(opaque carrier typed sink)` /
//! `Join(opaque carrier typed sink)` were built; the call-argument one was not.
//!
//! THE TRIGGER is "the payload STRUCT declines the enum's registration", not "the payload is
//! written" and not "the call is a method call". Here `Memory`/`Disk` carry a `Ty::Tuple` field,
//! which `struct_layout_resolvable` refuses, so `enum_variant_field_admissible` refuses the
//! payload, so `register_enum` declines `Store` and the whole match falls to the opaque lane.
//!
//! MEASURED on seal trust-ec48b535 with this file's flags, over <home>/aterm: 68
//! occurrences of exactly this row — 31 in `aterm-scrollback` (lib) and 37 in (lib test), every
//! one of them `arg_index: 0, expected: "ptr", actual: "()"`, and nothing else. Every one is the
//! same source shape: `match self { ScrollbackStorage::Memory(sb) => sb.m() }` (the `dispatch!`
//! delegation macro, one row per delegated method, block 1 = the Memory arm and block 2 = the
//! Disk arm) plus `LineContent::len`'s `match self { Self::Inline(b) => b.len(), .. }`.
//! `-Ztrust-dump=ir` cannot show the module: it dumps only a unit that VALIDATES.
//!
//! THE FIX IS TO DECLINE, not to repair. The payload of an opaque enum has no address in this
//! abstraction — that is WHY the lane binds a fact-free unit const — so the only alternatives to
//! declining are inventing a pointer or shipping the contradiction. A body that does not lower
//! costs coverage; a call whose argument type contradicts its callee's declaration is a lie the
//! validator is right to catch. `lower_call_args` now consults
//! `opaque_carrier_value_spellings` for every argument of a LOCAL callee and fails the body
//! closed with `Call(opaque carrier typed sink)` when the ledgered spelling disagrees with
//! `map_ty` of the argument's own ground-truth rustc type — keyed on the LEDGER DISAGREEMENT
//! (the #189 rule), so a carrier whose spelling AGREES with the position stays legal and an
//! unledgered value is untouched. `callee_is_local` is wave-RK2's gate for wave-RK2's reason: a
//! bodyless declaration is signed `params: [], is_vararg: true`, so the validator's zip over an
//! extern edge is vacuous and no such edge can mismatch.
//!
//! THREE ENTRY POINTS, ALL GATED. `lower_call_args` is reached from exactly three call sites —
//! `CalleeKind::Direct`, `CalleeKind::FnPtr`, and `lower_closure_call_untupled` — and the first
//! cut of this fix wired up only the first. `FnPtr` is correct at `false` (it emits
//! `Inst::CallIndirect`, and `CallArgTypeMismatch` is raised only from `Inst::Call` and
//! `Inst::Invoke`), but the CLOSURE path hardcoded `false` behind a comment asserting the
//! locality flag was "inert either way" — true of the drop lanes it was written for, false of
//! this gate, which keys on `callee_is_local` alone. Measured on the seal, pre-fix:
//!
//!   CallArgTypeMismatch { block: 1, callee: "dispatch_closure::{closure#0}", arg_index: 1,
//!                         expected: "ptr", actual: "()" }
//!
//! `arg_index: 1` because argument 0 is the synthesized env pointer the `ClosureCall` arm pushes
//! itself. Every other `Inst::Call` emitter in the producer builds its arguments from block
//! params or a fresh `Alloca` (the closure adapter, the coroutine-resume slot) or targets a
//! non-local callee (the opaque-lane `Option` read), and the receiver-place carrier class is
//! refused by `place_carrier_reaches_real_params` at the splice — so with the closure path
//! threaded, no argument slot of a local callee is left ungated.
//!
//! WHY NOT A WHOLE-BODY FLAG. The obvious-looking alternative is a `value_carrier_reaches_real_
//! params` twin of the place-carrier guard: one bit on the body, refused at the splice. That
//! predicate is blunt by construction — it lives in `crate_module.rs`, after rustc types and
//! `map_ty` are gone, so it can only ask "does this body hold a carrier AND make any local call
//! with parameters", never "does THIS value's ledgered spelling disagree with THIS position".
//! `carrier_agrees` below is the counterexample: it holds a wave-EMO carrier and calls a local
//! one-parameter fn with it, so the blunt rule refuses it — while it validates today and must
//! keep lowering. Sink-keyed and ledger-keyed is the more precise rule, and the enumeration
//! above is what makes it complete.
//!
//! WHAT THIS FILE PINS: the module carries ZERO validation errors. Pre-fix it carried four —
//! two from `dispatch_ufcs` (one per arm, the aterm `dispatch!` shape verbatim), one from
//! `dispatch_method`, and one from `dispatch_closure` — while `carrier_discarded` and
//! `carrier_agrees` contributed none. Those two are the controls, and they must STAY lowering:
//! `carrier_discarded` is a carrier that reaches no typed sink at all, and `carrier_agrees` is a
//! carrier that reaches an argument slot whose spelling it MATCHES. If a rebuild leaves either
//! declining, the guard has been keyed on carrier membership instead of on the disagreement.

pub struct Memory {
    pub window: (u32, u32),
    pub lines: usize,
}

pub struct Disk {
    pub window: (u32, u32),
    pub lines: usize,
}

pub trait Backend {
    fn line_count(&self) -> usize;
}

// Both impls are LOCAL and trivially spliceable, so each one's `Function` really does declare
// `params: [ptr]` — which is what makes the `()` argument a validator-visible contradiction
// rather than a vacuous zip against a bodyless declaration.
impl Backend for Memory {
    fn line_count(&self) -> usize {
        self.lines
    }
}

impl Backend for Disk {
    fn line_count(&self) -> usize {
        self.lines
    }
}

impl Memory {
    pub fn cold_lines(&self) -> usize {
        7
    }
}

// `register_enum` declines `Store`: the payload structs carry a `Ty::Tuple` field, which
// `struct_layout_resolvable` refuses, so `enum_variant_field_admissible` refuses the payload.
// `is_opaque_lane_enum(Store)` is therefore true and every `match` on it takes the wave-EMO lane.
pub enum Store {
    Mem(Memory),
    Dsk(Disk),
}

// The aterm `dispatch!` shape verbatim: UFCS trait call, the carrier local passed as argument 0.
// Must DECLINE (`Call(opaque carrier typed sink)`), never emit `call @<Memory as Backend>
// ::line_count(())`. Two arms => the pre-fix rows were block 1 and block 2.
pub fn dispatch_ufcs(s: &Store) -> usize {
    match s {
        Store::Mem(b) => Backend::line_count(b),
        Store::Dsk(b) => Backend::line_count(b),
    }
}

// The same launder through METHOD-call syntax and an inherent callee — the receiver needs no
// autoref (`b` is already `&Memory`), so THIR hands the carrier to argument 0 directly and the
// wave-MC/wave-RS receiver-place carriers (which set `place_path_carrier` and are already refused
// at the splice) are not on this path at all. That is why the existing guard never saw it.
pub fn dispatch_method(s: &Store) -> usize {
    match s {
        Store::Mem(b) => b.cold_lines(),
        Store::Dsk(_) => 0,
    }
}

// Negative control: a carrier that is only REBOUND and DISCARDED reaches no typed sink, so it
// must keep lowering — the untyped consumers are the sanctioned ones (the `rebind_and_discard`
// discipline of `trust_ir_lower_carrier_typed_sink.rs`, at the argument position).
pub fn carrier_discarded(s: &Store) -> usize {
    match s {
        Store::Mem(b) => {
            let q = b;
            let _ = q;
            1
        }
        Store::Dsk(_) => 0,
    }
}

// The CLOSURE-CALL argument slot. A capture-free local closure resolves to
// `CalleeKind::ClosureCall` with `admit_callee(resolved)` — a LOCAL callee whose spliced
// `Function` declares `(env: Ptr, x: Ptr)` — and its arguments are built by
// `lower_closure_call_untupled`, which used to hand `lower_call_args` a hardcoded
// `callee_is_local: false`. The carrier therefore sailed straight into argument 1.
pub fn dispatch_closure(s: &Store) -> usize {
    let f = |x: &Memory| x.lines;
    match s {
        Store::Mem(b) => f(b),
        Store::Dsk(_) => 0,
    }
}

// ---- The AGREEING control (the gate is keyed on the ledger DISAGREEMENT, not on membership).
//
// `Pair` carries a `Ty::Tuple` field, so `enum_variant_field_admissible` refuses it and
// `register_enum` declines `Leaf`; `map_ty(Leaf)` is therefore the opaque-lane `Ty::Unit`. That
// makes `Leaf` inadmissible as `Nest`'s payload too, so `Nest` is an opaque-lane enum and the
// match below takes the wave-EMO lane, binding `b` to the fact-free `Const { ty: Ty::Unit }`.
// `takes_opaque` is a LOCAL callee whose parameter `Leaf` maps to `Ty::Unit` as well — so the
// carrier's ledgered spelling AGREES with the position, the module is well-typed, and the body
// must keep lowering. Verified on seal trust-ec48b535 to validate with zero errors BEFORE the
// fix; a post-fix decline here would mean the guard refuses carriers rather than contradictions.
pub struct Pair {
    pub t: (u8, u8),
}

pub enum Leaf {
    L(Pair),
    R,
}

pub enum Nest {
    N(Leaf),
    Z,
}

pub fn takes_opaque(_x: Leaf) -> usize {
    1
}

pub fn carrier_agrees(e: Nest) -> usize {
    match e {
        Nest::N(b) => takes_opaque(b),
        Nest::Z => 0,
    }
}

fn main() {
    let m = Store::Mem(Memory { window: (1, 2), lines: 3 });
    let d = Store::Dsk(Disk { window: (4, 5), lines: 6 });
    let _ = dispatch_ufcs(&m);
    let _ = dispatch_ufcs(&d);
    let _ = dispatch_method(&m);
    let _ = dispatch_closure(&m);
    let _ = carrier_discarded(&d);
    let _ = carrier_agrees(Nest::N(Leaf::L(Pair { t: (1, 2) })));
    let _ = carrier_agrees(Nest::Z);
    let _ = Leaf::R;
    if let Store::Mem(mm) = &m {
        let _ = mm.window.0;
    }
}
