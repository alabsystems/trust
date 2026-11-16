//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//! Trust (wave-RETSPLIT): two bodies that spell ONE callee's return type as two different
//! module types must mint two bodyless declarations — not one poisoned row that aborts the
//! whole crate.
//!
//! THE DEFECT. `crate_module::decl_id` interns a fail-closed declaration on
//! `(key, definition, concrete_key)` and treats the call sites' RESULT TYPE as a checked fact
//! about that row: a second observation that disagreed set `ret_conflict`, and
//! `append_declarations` turned that into a fatal producer error. The disagreement is not a
//! disagreement about the CALLEE, though — it is the producer spelling one source type twice:
//!
//!   * `struct_ty_rmw_opaque` (the RMW/opaque struct builder) registers a struct with `Ty::Unit`
//!     PLACEHOLDER siblings for every non-pure field. Its own doc: `written_field` is `Some(i)`
//!     at a field WRITE through a reference and `None` at a whole-struct/field READ through one,
//!     and BOTH routes go through this builder;
//!   * `map_ty`'s `Adt` arm registers the same struct FAITHFULLY;
//!   * `register_struct` dedups only PER BODY on `(DefId, GenericArgs)`, so each body keeps
//!     whichever builder ran first, and `Module::add_struct_def` dedups STRUCTURALLY — so the
//!     two field lists land on two distinct crate-level `StructId`s.
//!
//! The trigger is therefore "the struct was reached through the RMW/opaque builder EARLIER IN
//! THIS BODY than the call", not "the struct was written". Measured on seal trust-dac08891 with
//! this file's flags, one `-> S` `local-unlowered` callee plus one read-only observer:
//!
//!   `fn f(p: &S)     -> u32 { let _ = p.a;    let s = make(); s.a }`   1 error  (SHARED read)
//!   `fn f(p: &mut S) -> u32 { p.a = 1;        let s = make(); s.a }`   1 error  (write)
//!   `fn f(p: &mut S) -> u32 { let s = make(); let _ = p.a;   s.a }`    0 errors (after the call)
//!   `fn f(mut p: S)  -> u32 { p.a = 1;        let s = make(); s.a }`   0 errors (by value)
//!   `fn f() -> u32 { let mut v = other(); v.a = 1; let s = make(); s.a }`
//!                                                                     0 errors (LOCAL, by value)
//!
//! `make` below is `local-unlowered` (its nested loop fails closed, so there is no spliced
//! body to link), `read_only` observes it returning the faithful `S`, and `ref_then_call`
//! touches `p.a` through a SHARED reference FIRST — registering the degraded `S` before the call
//! — and then observes the same `make` returning that one. Two `Ty::Struct` ids, one declaration,
//! fatal. (A `&mut` write in place of the read is the same file; the reference, not the write, is
//! what routes through the builder.)
//!
//! THE MEASUREMENT. Seal trust-dac08891 (2026-09-08), `targo trust check --allow-l0-gaps
//! --workspace --all-targets` on aterm: 309 units reached, 3 fatal, two of them this defect —
//!
//!   error: trust-ir-lower semantic finalization failed: conflicting bodyless declaration
//!   observations for FuncId 252 key "local-unlowered:profiles::hardened|concrete-v1:019a00.."
//!   name "profiles::hardened"; ... FuncId 281 ... "profiles::standard" ... FuncId 334 ...
//!   "profiles::permissive"                                    (aterm-policy, lib test)
//!
//!   error: trust-ir-lower semantic finalization failed: conflicting bodyless declaration
//!   observations for FuncId 710 key "local-unlowered:mirror::verify|concrete-v1:013ad5e3.."
//!   ... FuncId 966 key "havoc:std::result::Result::<T, E>::unwrap|concrete-v1:019f452e.."
//!                                                             (aterm-forge, lib test)
//!
//! (The message is quoted as the SEAL emitted it. It now names the contradicted fact —
//! `observations (result type)` vs `(signature)` — because the two halves are retired by
//! unrelated work and telling them apart otherwise needs a compiler rebuild.)
//!
//! aterm reaches `Policy` through references beside bodies that call the `-> Policy` profile
//! constructors — `aterm-policy/src/limits.rs:349` `from_policy(policy: &Policy)`,
//! `engine.rs:277` `self.policy.defaults.unmatched` — which is this file's shape at crate scale.
//! HONESTY: the specific aterm body PAIR that registers the two spellings was NOT isolated;
//! doing that needs the failing unit reproduced standalone. What is measured is the message and
//! the mechanism, reduced to the lines below. (An earlier note here blamed the by-value local
//! writes `future.schema_version = 9_999` / `out.ok = false`; those are refuted by the fifth
//! probe row above, which is green.) Pre-fix this file emits the same error for `make`, and a
//! near-miss module that validates clean dumps the two spellings side by side as
//! `struct @S { u32, struct.8 } size=32 align=8 id=9` (no reference route) against
//! `struct @S { u32, () } id=10` (reference route; the layout is dropped by `register_struct`'s
//! coherence gate).
//!
//! THE FIX, and why it is not a weakening. There is no weaker observation to record: a
//! declaration's "unknown" return spelling is `returns: []`, which is a POSITIVE claim of
//! "returns nothing" (`is_vararg` covers only the params side), so demoting would trade this
//! fatal error for `InstrResultArityMismatch` at every site that binds a result — the #189
//! family of ABI lies. `decl_id` therefore SPLITS: the contradicting observation gets its own
//! row keyed `|ret:{spelling}` (the suffix `ret_key` already uses, appended only on the
//! contradicting path so every other module keeps byte-identical keys). Each declaration's
//! signature then agrees with every instruction that names it, and two uninterpreted bodyless
//! functions are strictly WEAKER than either merged signature — a consumer can lose facts that
//! way, never invent them. Resolution is by `FuncId`; `emitted_decl_name` already mints
//! reserved injective names for exactly this collision, and `append_clean_origin` already
//! strips `|ret:`/`|nres:` suffixes when it matches a `local-unlowered:` key to its emitted
//! row, so both rows still link to the one Clean definition.
//!
//! WHAT THIS FILE DOES NOT COVER, and cannot. Being `check-pass`, it pins only that the crate
//! stops ABORTING; it cannot tell a split from a suppression (deleting the `errors.push` in
//! `append_declarations` would satisfy it too), because a UI test cannot read the assembled
//! module. The discriminating pin is the unit test
//! `crate_module::authority_tests::
//! contradicting_result_type_observations_split_instead_of_poisoning`, which asserts two rows,
//! their two keys, their two `returns` lists, and that no
//! `!trust_conflicting_declaration::` placeholder is emitted.
//!
//! The sibling contradiction — two EXACT `Constant::FnDef` signatures for one concrete key, and
//! a name / ABI / `local_def_index` mismatch — is still a fatal `DeclSigState::Conflict`, and
//! the split deliberately does NOT reach it: `decl_id`'s split predicate re-checks name, ABI and
//! `local_def_index`, so an observation that contradicts the row on identity as well merges and
//! refuses (pinned by `identity_contradiction_merges_and_refuses_instead_of_splitting`). Neither
//! is reduced here and neither is in the aterm measurement (none of the FIVE failing keys —
//! `profiles::{hardened,standard,permissive}`, `mirror::verify`,
//! `std::result::Result::<T, E>::unwrap` — has a reify site).

pub struct S {
    pub a: u32,
    pub b: Vec<u32>,
}

// `local-unlowered`: the nested loop fails the body closed, so every call site declares.
pub fn make() -> S {
    let mut i = 0u32;
    while i < 3 {
        let mut j = 0u32;
        while j < 3 {
            j += 1;
        }
        i += 1;
    }
    S { a: i, b: Vec::new() }
}

pub fn read_only() -> u32 {
    let s = make();
    s.a
}

// A SHARED reference read is enough: it routes through `struct_ty_rmw_opaque` in the
// `written_field: None` (whole-struct read) mode, registering the degraded `S` before the call.
pub fn ref_then_call(p: &S) -> u32 {
    let _ = p.a;
    let s = make();
    s.a
}

fn main() {}
