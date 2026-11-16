//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//! STATUS ON MAIN (2026-09-24). Carried from the seal line (test: 056fc5e104; fix: the
//! `ExprKind::Field` hunk of b9bf2c898a, where the rebase had moved it). On the sealed
//! trust-7d5533b2 (main of 2026-09-23) this file still WARNed `OperandTypeMismatch
//! { op: "extract_field", role: "field", .. }` in `read`. The seal line's locator rewrite
//! (naming the instruction instead of a candidate set) is NOT carried: main has its own
//! struct- and call-family locators since 2026-09-22. The prose below is the seal-line record.
//!
//! Trust (task-B): a STRUCT-TYPED VALUE FIELD READ must not be the only body in the crate that
//! spells a local ADT the degraded way. Two spellings of one type is a producer defect, and here
//! it surfaces as an `OperandTypeMismatch` on the extract.
//!
//! THE DEFECT. `lower_expr`'s `ExprKind::Field` arm built the field's type as
//!
//!     ty::Adt(a, ga) if a.is_struct() && a.did().is_local()
//!         => self.struct_ty_rmw_opaque(*a, *ga, None).unwrap_or_else(|| self.map_ty(expr_ty))
//!
//! — the opaque-tolerant builder FIRST. That builder replaces every non-pure-value sibling with
//! a `Ty::Unit` placeholder, so it registers `@Inner { bool, () }` where `map_ty`'s `Adt` arm
//! registers the faithful `@Inner { bool, ptr }`. `register_struct` dedups only PER BODY on
//! `(DefId, GenericArgs)` — so each body keeps whichever builder ran first — and crate assembly's
//! `Module::add_struct_def` dedups STRUCTURALLY, so the two field lists land on two distinct
//! crate-level `StructId`s carrying ONE name. This is the same builder pair as wave-RETSPLIT
//! (`trust_ir_lower_decl_ret_spelling_split.rs`), reached from the VALUE read side instead of
//! the reference side, and colliding at an instruction instead of at a declaration.
//!
//! WHY IT IS FATAL RATHER THAN MERELY UGLY. `InstrNode::result_tys` types a `Call` result from
//! the CALLEE's declared `FuncTy::returns` — the callee's FAITHFUL spelling. The caller's extract
//! declares its own DEGRADED spelling. Final module validation therefore reports
//!
//!     OperandTypeMismatch { block: 0, op: "extract_field", role: "field",
//!                           expected: "struct.0", actual: "struct.2" }
//!
//! two ids, one `Inner`. On THIS reduction the locator already names `` `read` `` (measured on
//! seal trust-ec48b535 with this file's flags: the module has exactly one `extract_field` in
//! block 0, so even the old whole-module candidate walk had one candidate). The anonymity is a
//! property of the REAL crate, quoted under THE MEASUREMENT below — 176 candidates there — not
//! of this file; a small reduction cannot exhibit it.
//!
//! THE TRIGGER, stated so it can be refuted. `read` must reach `Inner` ONLY through the chained
//! value read, and the sibling must not be a pure value. Measured on seal trust-ec48b535 with
//! this file's flags:
//!
//!   `fn read() -> bool { make().a.ok }`               1 error   (Inner named nowhere else)
//!   `fn read() -> Inner { make().a }`                 0 errors  (signature maps Inner faithfully first)
//!   `fn read() -> bool { let x = make(); x.a.ok }`    0 errors  (the `let` maps it first)
//!   sibling `p: u64` / `[u64; 2]` / `(u64, u64)`      0 errors  (pure value — kept real)
//!   sibling `d: Deep` (another LOCAL struct)          0 errors  (pure value; recursion registers it)
//!   sibling `p: *const u8` / `Vec<u8>` / `String` / `Box<u8>`   1 error
//!   `make` in ANOTHER CRATE                           0 errors  (`is_local()` false — `map_ty` route)
//!
//! THE MEASUREMENT. Seal trust-ec48b535, `targo trust check --allow-l0-gaps --workspace
//! --all-targets` on aterm, 328 units: `aterm-forge` (lib test) fails with
//!
//!   error: trust-ir-lower semantic finalization failed: final Trust-IR module validation failed
//!   [OperandTypeMismatch] in one of 176 candidate functions: attest::VendoredFork::markers, …
//!   OperandTypeMismatch { block: 0, op: "extract_field", role: "field",
//!                         expected: "struct.186", actual: "struct.282" }
//!
//! Bisected (module tests, then test fn) to `mirror::tests::
//! a_row_may_declare_more_dependencies_than_the_lock_resolved`, whose first statement is
//! `assert!(emit_fx(&fx).0.ok)` — `emit_fx` returns `(Outcome, EmitStats)`, `Outcome` carries a
//! `String`, and the test names `Outcome` nowhere else. That is the shape below.
//!
//! THE FIX. The `ExprKind::Field` arm now pins the FAITHFUL spelling first and consults the
//! opaque-tolerant builder only when `map_ty` yields no `Ty::Struct`, so this SITE no longer
//! INTRODUCES a degraded spelling. It does NOT make the spelling of an ADT order-independent
//! crate-wide, and this file must not claim it does: `register_struct` dedups on
//! `(DefId, canonical_adt_args)` and IGNORES the field list, so `map_ty`'s struct output is a
//! function of what the BODY already registered. Measured on seal trust-ec48b535:
//!
//!   pub fn f(o: &mut Inner) -> usize { o.ok = false; let x = make(); x.b }
//!     struct @Inner { bool, ptr } id=0            // `make`, faithful
//!     struct @Outer { struct.0, usize } id=1
//!     struct @Inner { bool, () }  id=2            // `f`, from the RMW WRITE `o.ok =`
//!     struct @Outer { struct.2, usize } id=3      // `map_ty(Outer)` in `f`, from the DEGRADED id
//!
//! So a body whose RMW write of the ADT precedes the read still pins the degraded spelling and
//! stays red — `pub fn read(o: &mut Inner) -> bool { o.ok = false; make().a.ok }` reproduces the
//! same `expected: "struct.0", actual: "struct.2"` row. What the fix buys is the COMMON case
//! where the read is the body's first mention of the ADT, which is the shape the green rows
//! above and the aterm-forge measurement below both have. The probe rolls back its `unsupported`
//! tags (it is a REGISTRATION, not a lowering decision, so a clean body must not go dirty because
//! this site asked a question) while KEEPING `opaque_collapse` if the probe declined a sibling
//! lane, so the scorecard does not start counting a placeholder-carrying body as MODELLED.
//!
//! WHAT THIS FILE DOES NOT COVER. Being `check-pass`, it pins only that the crate stops
//! ABORTING; a UI test cannot read the assembled module, so it cannot tell "one spelling" from
//! "the check was deleted". The discriminating pins are the unit tests
//! `crate_module::final_module_validation_gate_tests::an_operand_type_mismatch_names_the_instruction_and_the_two_spellings`
//! (two ids under one name are REPORTED as such) and
//! `crate_module::final_module_validation_gate_tests::an_unmatched_spelling_degrades_to_the_op_walk_and_never_to_a_guess`.
//!
//! NOT COVERED, and honest about it:
//!
//!   * The OTHER callers of `struct_ty_rmw_opaque` (the `(*p).f` read/write lanes, the
//!     interior-offset lane, the opaque-Option lanes) can still register a degraded spelling in a
//!     body where another body is faithful. Only the value-read site is changed here, because
//!     that is the one this measurement reaches.
//!   * The ORDER-DEPENDENCE itself, which lives in `register_struct`'s dedup key. Any of those
//!     sites running earlier IN THE SAME BODY still wins, and `map_ty` will then compose parents
//!     out of the degraded id (measured above). Fixing that means re-registering or upgrading a
//!     `StructDef` on a field-list change, which is a wider change than this defect warrants.

pub struct Inner {
    pub ok: bool,
    // A raw pointer is not a pure value, so the opaque-tolerant builder collapses it to a
    // `Ty::Unit` placeholder. `Vec<u8>` / `String` / `Box<u8>` are the same row.
    pub p: *const u8,
}

pub struct Outer {
    pub a: Inner,
    pub b: usize,
}

fn make() -> Outer {
    Outer { a: Inner { ok: true, p: core::ptr::null() }, b: 0 }
}

// `Inner` is named NOWHERE in this signature or its locals: the chained value read is the first
// and only registration of it in this body.
pub fn read() -> bool {
    make().a.ok
}

fn main() {}
