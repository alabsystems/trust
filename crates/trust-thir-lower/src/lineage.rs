//! Trust (L1, artifact-lineage attestation): the per-body lineage digest.
//!
//! Before this module existed, THREE objects claimed to be "the body the flip compiled":
//! the per-body mini-module `flip_registry::record_green` stores, the row for that body in
//! the assembled crate artifact (`crate_module`), and the MIR re-derived at the flip
//! (`trust_ir_flip`). Nothing connected them — the A1 double-build pin and the A6 flip
//! event concerned DIFFERENT objects. This module mints ONE digest at the `mir_built`
//! hook, over the intact per-body mini-module PLUS its callee-identity ledger, and every
//! downstream carrier (registry entry, flip event log line, coverage row) states exactly
//! that value. "Which row of the artifact is the body the flip selected?" therefore
//! becomes a question with a mechanical answer — digest equality — instead of no answer
//! at all. Read "What this establishes, and what it does not" below before quoting that
//! anywhere: this is the plumbing that makes the correspondence STATEABLE, not a proof
//! that the assembled row is semantically the body that was proved.
//!
//! # What the digest binds
//!
//! * The mini-module content, via [`Module::stable_digest`] — trust-ir's whole-module
//!   G19 build-determinism fingerprint (domain `trust_ir.module.v2`, cross-process
//!   determinism contract + conformance test `build_determinism.rs`). REUSED, not
//!   reimplemented: this module adds framing around that digest, never a second
//!   module hash.
//! * The callee-identity ledger (`Lowered::callees`), canonically framed below. The
//!   ledger is a REAL input to the flip (`to_mir::lower_ir_to_mir` spells every
//!   `TerminatorKind::Call` func operand from it), so two identical modules with
//!   different ledgers are different compile inputs and MUST digest differently.
//!
//! The two byte-strings are joined under the domain-separated
//! [`trust_ir::ProofDigest::sha256_domain`] hasher with this module's own domain, so a
//! lineage digest can never be confused with a bare module digest.
//!
//! `DefId`/`CrateNum` raw indices appear in the callee framing. They are stable within
//! one compiler session (the only scope where registry/artifact/flip matching happens)
//! and reproducible across identical clean builds (deterministic crate loading), which
//! is exactly the acceptance scope; they are NOT stable across compiler versions or
//! changed dependency graphs, and the `v1` domain suffix is the upgrade path.
//!
//! # Where the value surfaces
//!
//! | carrier | field | minted at |
//! |---|---|---|
//! | flip registry entry | [`crate::flip_registry::GreenBody::lineage`] | `record_green` |
//! | flip event (`info!` "compiled from trust-ir") | `lineage` | logged at `try_flip` / `try_flip_ctfe`, after re-derivation |
//! | published coverage row | `lineage` (+ `func_id`, the row's index into the assembled `module.functions`) | `crate_module::record`, before assembly |
//!
//! The coverage sidecar is not a loose companion: `artifact_publication` commits the
//! binary module, the canonical text, and `coverage.json` as ONE set behind a single
//! commit marker, so a consumer that sees the marker sees a row set that belongs to that
//! binary.
//!
//! # Fail-closed
//!
//! No digest, no green: `flip_registry::green_body` — the sole constructor of a registry
//! entry — refuses when this computation refuses (e.g. a mini-module that does not carry
//! exactly one function), so a flip event can never fire without a lineage digest to log. And the flip RE-DERIVES the digest from the payload it took and
//! declines on any mismatch ([`crate::flip::derive_flip_body`]), so the value the event
//! publishes always describes the bytes that event is about.
//!
//! # What this establishes, and what it does not
//!
//! ESTABLISHED: the object the flip compiled and the object the artifact row was built
//! from are the same PRE-ASSEMBLY value, and that value is named by a digest that is
//! reproducible across processes (trust-ir's G19 contract) and that changes if either the
//! module content or the callee ledger changes.
//!
//! NOT ESTABLISHED (do not read the digest as more than it is):
//!
//! * **The canonical-remapping certificate.** Assembly sorts bodies, assigns fresh dense
//!   `FuncId`s, re-interns type/enum/struct tables and rewrites callees. The row's
//!   `func_id` ADDRESSES the resulting function, and the row's `lineage` NAMES the input
//!   it came from — but nothing here proves the assembled function still means what the
//!   pre-assembly mini-module meant. That proof does not exist. The digest is what makes
//!   it stateable (both sides now name one object); it does not discharge it.
//! * **Tamper evidence.** The registry is in-process Session state and the flip event is
//!   a `tracing` line. This is a lineage record for a cooperating toolchain, not a signed
//!   attestation against an adversary who controls the compiler.
//! * **Anything about the emitted machine code.** The digest binds trust-ir to trust-ir.
//!   The MIR→codegen leg below it is the differential gate's business, not this module's.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use rustc_span::def_id::DefId;
use trust_ir::{Module, ProofDigest};

use crate::{CalleeRef, SiteArg, SiteTy};

/// Domain tag for the lineage digest. Versioned: any change to the framing below MUST
/// bump the suffix so old and new digests can never collide silently.
pub const BODY_LINEAGE_DOMAIN: &str = "trust_thir_lower.body_lineage.v1";

/// Compute the lineage digest of one per-body mini-module + its callee ledger.
///
/// MUST be called on the INTACT hook-time `Lowered` (before `crate_module::record`
/// removes `functions[0]` for assembly) — the whole point is that `record_green`,
/// `crate_module::record`, and therefore the flip event and the coverage row, all
/// digest the SAME object.
///
/// Fails closed (`Err`) when the module does not carry exactly one function: a
/// body-less or multi-function module is not a per-body lowering, and attesting it
/// would name the wrong object.
pub fn body_lineage_digest(module: &Module, callees: &[CalleeRef]) -> Result<ProofDigest, String> {
    if module.functions.len() != 1 {
        return Err(format!(
            "per-body lineage digest requires exactly one function in the mini-module, found {}",
            module.functions.len()
        ));
    }
    let module_digest = module.stable_digest();
    let mut bytes = Vec::with_capacity(32 + 8 + callees.len() * 64);
    bytes.extend_from_slice(&module_digest.bytes);
    encode_u64(&mut bytes, callees.len() as u64);
    for callee in callees {
        encode_callee(&mut bytes, callee);
    }
    Ok(ProofDigest::sha256_domain(BODY_LINEAGE_DOMAIN, &bytes))
}

fn encode_u32(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_be_bytes());
}

fn encode_u64(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_be_bytes());
}

/// Length-prefixed UTF-8 — unambiguous concatenation (no delimiter injection).
fn encode_str(out: &mut Vec<u8>, s: &str) {
    encode_u64(out, s.len() as u64);
    out.extend_from_slice(s.as_bytes());
}

fn encode_bool(out: &mut Vec<u8>, b: bool) {
    out.push(u8::from(b));
}

fn encode_def_id(out: &mut Vec<u8>, def_id: DefId) {
    encode_u32(out, def_id.krate.as_u32());
    encode_u32(out, def_id.index.as_u32());
}

/// Every field of [`CalleeRef`] enters the framing — the ledger decides how the shim
/// spells calls at flip time, so omitting a field would let two different compile
/// inputs share a digest. Field order is struct declaration order; bind by full
/// destructure so a future field cannot silently escape the digest.
fn encode_callee(out: &mut Vec<u8>, callee: &CalleeRef) {
    let CalleeRef {
        func_id,
        is_local,
        def_index,
        def_id,
        def_path,
        force_havoc,
        site_def_id,
        site_args,
        ret_ty,
        ret_ty_conflict,
    } = callee;
    encode_u32(out, func_id.index());
    encode_bool(out, *is_local);
    encode_u32(out, *def_index);
    encode_def_id(out, *def_id);
    encode_str(out, def_path);
    encode_bool(out, *force_havoc);
    encode_def_id(out, *site_def_id);
    match site_args {
        None => out.push(0),
        Some(args) => {
            out.push(1);
            encode_u64(out, args.len() as u64);
            for arg in args {
                encode_site_arg(out, arg);
            }
        }
    }
    // Trust (#178): the agreed call-result type and its poison flag DO enter the digest — they
    // pick the bodyless declaration's signature at crate assembly, so two inputs that differ only
    // here produce different modules. `{:?}` is sufficient framing: `Ty` is a closed enum whose
    // Debug is injective for the table-free fragment this field is restricted to, and the length
    // prefix in `encode_str` keeps it unambiguous against the neighbouring fields.
    match ret_ty {
        None => out.push(0),
        Some(t) => {
            out.push(1);
            encode_str(out, &format!("{t:?}"));
        }
    }
    encode_bool(out, *ret_ty_conflict);
}

fn encode_site_arg(out: &mut Vec<u8>, arg: &SiteArg) {
    match arg {
        SiteArg::ErasedRegion => out.push(0),
        SiteArg::Ty(t) => {
            out.push(1);
            encode_site_ty(out, t);
        }
    }
}

/// Discriminant-tagged recursive framing. `SiteTy` is the finite region/const-free
/// fragment (`encode_ty` fails closed on anything else), so recursion is bounded by
/// the encoded type's own structure.
fn encode_site_ty(out: &mut Vec<u8>, t: &SiteTy) {
    match t {
        SiteTy::Bool => out.push(0),
        SiteTy::Char => out.push(1),
        SiteTy::Str => out.push(2),
        SiteTy::Int(i) => {
            out.push(3);
            encode_str(out, i.name_str());
        }
        SiteTy::Uint(u) => {
            out.push(4);
            encode_str(out, u.name_str());
        }
        SiteTy::Float(f) => {
            out.push(5);
            encode_str(out, f.name_str());
        }
        SiteTy::Adt(did, args) => {
            out.push(6);
            encode_def_id(out, *did);
            encode_u64(out, args.len() as u64);
            for a in args {
                encode_site_ty(out, a);
            }
        }
        SiteTy::Tuple(ts) => {
            out.push(7);
            encode_u64(out, ts.len() as u64);
            for a in ts {
                encode_site_ty(out, a);
            }
        }
        SiteTy::Array(elem, len) => {
            out.push(8);
            encode_site_ty(out, elem);
            encode_u64(out, *len);
        }
        SiteTy::Slice(elem) => {
            out.push(9);
            encode_site_ty(out, elem);
        }
    }
}

#[cfg(test)]
mod tests {
    use rustc_span::def_id::{CrateNum, DefId, DefIndex};
    use trust_ir::{BlockId, FuncId, FuncTy, Function, Module};

    use super::body_lineage_digest;
    use crate::CalleeRef;

    fn probe_module(fn_name: &str) -> Module {
        let mut module = Module::new("lineage_probe");
        let ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(Function::new(FuncId::new(0), fn_name, ty, BlockId::new(0)));
        module
    }

    fn probe_callee(force_havoc: bool) -> CalleeRef {
        let def_id = DefId { krate: CrateNum::from_u32(0), index: DefIndex::from_u32(7) };
        CalleeRef {
            func_id: FuncId::new(1),
            is_local: true,
            def_index: 7,
            def_id,
            def_path: "lineage_probe::callee".to_string(),
            force_havoc,
            site_def_id: def_id,
            site_args: Some(Vec::new()),
            // Trust (#178): the UNKNOWN spelling, byte-identical to what
            // `admit_callee` writes (see the `self.callees.push` site in `lib.rs`)
            // — a callee no site has bound a result from. This probe is about the
            // lineage digest, so it must use the producer's own default rather
            // than invent a return type the digest would then depend on.
            ret_ty: None,
            ret_ty_conflict: false,
        }
    }

    /// Determinism at this seam: the same body (module + ledger), digested twice from
    /// independently constructed values, produces the same digest. (Cross-process
    /// determinism of the inner module digest is trust-ir's G19 conformance test;
    /// this pins the framing added here.)
    #[test]
    fn test_lineage_digest_same_body_twice_returns_same_digest() {
        let a = body_lineage_digest(&probe_module("probe"), &[probe_callee(false)])
            .expect("single-function module must digest");
        let b = body_lineage_digest(&probe_module("probe"), &[probe_callee(false)])
            .expect("single-function module must digest");
        assert_eq!(a, b, "identical (module, ledger) inputs must produce identical digests");
    }

    /// A perturbed BODY must change the digest (the module content is bound).
    #[test]
    fn test_lineage_digest_perturbed_body_returns_different_digest() {
        let base = body_lineage_digest(&probe_module("probe"), &[]).expect("digest");
        let perturbed = body_lineage_digest(&probe_module("probe_perturbed"), &[]).expect("digest");
        assert_ne!(base, perturbed, "a perturbed body must not share the original's digest");
    }

    /// A perturbed LEDGER must change the digest even when the module is untouched —
    /// the ledger is a real flip input, not metadata.
    #[test]
    fn test_lineage_digest_perturbed_ledger_returns_different_digest() {
        let module = probe_module("probe");
        let base = body_lineage_digest(&module, &[probe_callee(false)]).expect("digest");
        let havoced = body_lineage_digest(&module, &[probe_callee(true)]).expect("digest");
        assert_ne!(base, havoced, "the callee ledger must be bound by the digest");
        let empty = body_lineage_digest(&module, &[]).expect("digest");
        assert_ne!(base, empty, "dropping a ledger row must change the digest");
    }

    /// Fail-closed: a module that is not a single-body lowering refuses to digest.
    #[test]
    fn test_lineage_digest_bodyless_module_fails_closed() {
        let module = Module::new("no_bodies");
        let error = body_lineage_digest(&module, &[])
            .expect_err("a function-less module must not receive a lineage digest");
        assert!(error.contains("exactly one function"), "refusal must state the invariant");
    }
}
