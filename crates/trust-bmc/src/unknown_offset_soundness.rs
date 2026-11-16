//! Verifier-lane soundness of the bridge's UNKNOWN-OFFSET field address (2026-09-29).
//!
//! Since 2026-09-28 `trust_ir_bridge` spells a field address it cannot place (a base
//! with no layout) as the object at an unknown offset — `%off = undef u64;
//! gep u8 %base[%off]` — instead of the retired `index * size_of(field)` guess. A
//! verifier that consumed that address as ANY concrete offset could prove a property
//! of the wrong field. The bridge's IR reaches a prover here through trust-mc's CHC
//! lane only (the bridge's planners emit CHC requests only), and that lane has two
//! layers, measured separately over bundles the bridge's own production lowering
//! builds (the `direct_shadow_differential::mir_lane_bundle` recipe):
//!
//! 1. THE PRODUCTION GATE. `NativeTrustIrChcPdrRunner::solve_bundle_native_proof_grade*`
//!    refuses the whole bundle before translation — every `GEP` is refused
//!    ("without authenticated allocation/provenance and index bounds"), and so is an
//!    `Alloca` whose pointer a `GEP` uses. So no field address, exact or unknown,
//!    earns a verdict on the production lane today: it is fail-closed, not havoc.
//! 2. THE TRANSLATOR behind it (the gate bypassed, the typed CHC engine solving the
//!    translated VC directly), which is what would answer if the gate ever admitted a
//!    `GEP`. Here the unknown offset must never be read as a concrete offset. Both
//!    unknown-offset rows are now REFUSAL rows: the offset is `undef u64`, poison
//!    under trust-ir's canonical semantics, so the `GEP` consuming it is not
//!    executable and trust-mc's operand-consumption guard refuses it
//!    (`OperandConsumption`; fail-closed since trust-mc c88bca8d7, first pinned in
//!    Trust at 8862c94337 on 2026-11-02; it was havoc before that guard). trust-ir
//!    has no in-body choice opcode (SPEC_RATIFICATIONS §13), so the bridge has no
//!    executable spelling for an offset it cannot place short of changing the
//!    function's signature. The one executable unknown is a root parameter, and a
//!    `u64` parameter offset is refused too, at the load (it may read outside the
//!    object; `a_root_parameter_offset_is_refused_at_the_load`). Both refusals come
//!    before the translator reads the address, so the property this module was
//!    written for (the translator models an unknown offset as havoc, never as a
//!    concrete offset) is no longer measured here; it is moot while the guard
//!    refuses every unknown-offset read:
//!    * `100 / s.b` with `s = S { a: 1, b: 0 }` holds only if the field were read at
//!      the WRONG place (`s.a` is 1): through an unknown offset it is refused;
//!    * `100 / (s.b | 1)` holds for every value, and through the unknown offset it is
//!      refused too (it asserted PROVED until the guard; the expectation changed in
//!      BMC-LANE-1, 2026-11-06, docs/DECISION_QUEUE.md);
//!    * the same property through rustc's EXACT address of `s.b` IS proved, and so is
//!      the falsifier: the address resolved to byte 0 — what a consumer reading the
//!      unknown offset as offset 0 would compute — proves the false property. So the
//!      rows above do not pass on a harness that proves nothing through a field
//!      address;
//!    * the control: rustc's exact address of `s.b` does not prove `100 / s.b`.
//!
//! The unknown-offset rows run twice: over `S` with NO layout (the bridge's own
//! output) and over `S` WITH rustc's layout, respelled to the unknown-offset form —
//! the demanding case, where the consumer holds a layout it could be tempted to use.
//!
//! Test-only by construction (the `mod` line in `lib.rs` is `cfg(all(test, ..))`), and
//! the one `SourceGenerationAuthority` mint sits in `mod tests` for the production-issuer
//! census, exactly as in `direct_shadow_differential`.

use std::time::Duration;

use sha2::Digest as _;
use trust_ir::{
    Inst, Module, NativeVerificationBundle, ProofDigest, ProofId, PublicObligationIdentity,
};
use trust_types::{
    AdtLayoutInfo, AggregateKind, AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl,
    Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, UnwindEdge,
    VerifiableBody, VerifiableFunction,
};

const SOLVE_TIMEOUT: Duration = Duration::from_secs(20);

/// What the division's divisor is, as a function of the value read through `&s.b`.
#[derive(Debug, Clone, Copy)]
enum Divisor {
    /// `d = *r` — nonzero only if the read returned `s.a`.
    Field,
    /// `d = *r | 1` — nonzero for every value.
    FieldOrOne,
}

/// `struct S { a: u32, b: u32 }`, with or without rustc's layout (offsets [0, 4]).
fn s_ty(laid_out: bool) -> Ty {
    let mut s = Ty::adt("S", vec![("a".into(), Ty::u32()), ("b".into(), Ty::u32())]);
    if laid_out && let Ty::Adt { layout, .. } = &mut s {
        *layout = Some(Box::new(AdtLayoutInfo {
            size: 8,
            align: 4,
            field_offsets: vec![0, 4],
            repr: "rust".to_string(),
        }));
    }
    s
}

fn u32_const(value: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(value, 32))
}

fn function(s: Ty, divisor: Divisor) -> VerifiableFunction {
    // The planner refuses a row with no source span (`MissingObligationSourceSpan`),
    // exactly as production would; the span names this fixture's division.
    let span = SourceSpan {
        file: "unknown_offset_soundness.rs".to_string(),
        line_start: 7,
        col_start: 5,
        line_end: 7,
        col_end: 12,
    };
    let assign = |local: usize, rvalue: Rvalue| Statement::Assign {
        place: Place::local(local),
        rvalue,
        span: span.clone(),
    };
    let divisor_rvalue = match divisor {
        Divisor::Field => Rvalue::Use(Operand::Copy(Place::local(3))),
        Divisor::FieldOrOne => {
            Rvalue::BinaryOp(BinOp::BitOr, Operand::Copy(Place::local(3)), u32_const(1))
        }
    };
    VerifiableFunction {
        name: "read_b_and_divide".to_string(),
        def_path: "unknown_offset_soundness::read_b_and_divide".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: s, name: Some("s".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("r".into()),
                },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("d".into()) },
                LocalDecl { index: 5, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        assign(
                            1,
                            Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: "S".into(),
                                    variant: 0,
                                    active_field: None,
                                    args: None,
                                },
                                vec![u32_const(1), u32_const(0)],
                            ),
                        ),
                        assign(
                            2,
                            Rvalue::Ref {
                                mutable: false,
                                place: Place { local: 1, projections: vec![Projection::Field(1)] },
                            },
                        ),
                        assign(
                            3,
                            Rvalue::Use(Operand::Copy(Place {
                                local: 2,
                                projections: vec![Projection::Deref],
                            })),
                        ),
                        assign(4, divisor_rvalue),
                        assign(
                            5,
                            Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(4)),
                                u32_const(0),
                            ),
                        ),
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place::local(5)),
                        expected: false,
                        msg: AssertMessage::DivisionByZero,
                        target: BlockId(1),
                        span: span.clone(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        0,
                        Rvalue::BinaryOp(
                            BinOp::Div,
                            u32_const(100),
                            Operand::Copy(Place::local(4)),
                        ),
                    )],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The bridge's production lowering of `func`, with the 64-bit target profile the
/// proof-grade runner demands (production stamps the session target here).
fn lowered(func: &VerifiableFunction) -> Module {
    let mut module = trust_ir_bridge::lower_functions_to_trust_ir("unknown_offset", [func])
        .expect("the fixture lowers");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    });
    module
}

/// The one GEP of the function, as (block index, node index).
fn the_gep(module: &Module) -> (usize, usize) {
    let sites: Vec<(usize, usize)> = module.functions[0]
        .blocks
        .iter()
        .enumerate()
        .flat_map(|(b, block)| {
            block
                .body
                .iter()
                .enumerate()
                .filter(|(_, node)| matches!(node.inst, Inst::GEP { .. }))
                .map(move |(n, _)| (b, n))
        })
        .collect();
    let [site] = sites.as_slice() else { panic!("expected exactly one GEP, got {sites:?}") };
    *site
}

/// The node defining `value` in the function, as (block index, node index).
fn definition(module: &Module, value: trust_ir::value::ValueId) -> (usize, usize) {
    module.functions[0]
        .blocks
        .iter()
        .enumerate()
        .find_map(|(b, block)| {
            block.body.iter().position(|node| node.results.first() == Some(&value)).map(|n| (b, n))
        })
        .unwrap_or_else(|| panic!("value {value:?} has no defining node"))
}

/// The GEP's single index value.
fn gep_index(module: &Module) -> trust_ir::value::ValueId {
    let (b, n) = the_gep(module);
    let Inst::GEP { indices, .. } = &module.functions[0].blocks[b].body[n].inst else {
        unreachable!("the_gep returns a GEP")
    };
    let [index] = indices.as_slice() else { panic!("a field address has one index") };
    *index
}

/// Does the function's field address name no offset (the bridge's unknown-offset
/// spelling: an `undef u64` index into a `u8` GEP)?
fn names_no_offset(module: &Module) -> bool {
    let (b, n) = definition(module, gep_index(module));
    let (gb, gn) = the_gep(module);
    matches!(module.functions[0].blocks[b].body[n].inst, Inst::Undef { ty: trust_ir::ty::Ty::U64 })
        && matches!(
            module.functions[0].blocks[gb].body[gn].inst,
            Inst::GEP { pointee_ty: trust_ir::ty::Ty::U8, inbounds: false, .. }
        )
}

/// Respell a laid-out base's exact field address (`gep u32 %s[1]`) as the bridge's
/// unknown-offset form, value ids unchanged: the index's constant becomes `undef u64`
/// and the GEP steps bytes, not inbounds.
fn respell_as_unknown_offset(module: &mut Module) {
    let (b, n) = definition(module, gep_index(module));
    let (gb, gn) = the_gep(module);
    let blocks = &mut module.functions[0].blocks;
    assert!(
        matches!(blocks[b].body[n].inst, Inst::Const { .. }),
        "a laid-out base's field address has a constant index"
    );
    blocks[b].body[n].inst = Inst::Undef { ty: trust_ir::ty::Ty::U64 };
    let Inst::GEP { pointee_ty, inbounds, .. } = &mut blocks[gb].body[gn].inst else {
        unreachable!("the_gep returns a GEP")
    };
    *pointee_ty = trust_ir::ty::Ty::U8;
    *inbounds = false;
}

/// Respell a laid-out base's exact field address with its offset supplied by a new ROOT
/// `u64` parameter: `gep u8 %s[%off]`, `%off` an entry parameter. A root parameter is
/// a nondeterministic input over its type's value domain (trust-ir SPEC_RATIFICATIONS
/// §13), so this is an executable unknown offset.
fn respell_offset_as_a_root_parameter(module: &mut Module) {
    let (gb, gn) = the_gep(module);
    let func_ty = module.functions[0].ty;
    let mut signature = module.func_type(func_ty).expect("the function's signature exists").clone();
    signature.params.push(trust_ir::ty::Ty::U64);
    let widened = module.add_func_type(signature).expect("a signature id");
    let func = &mut module.functions[0];
    func.ty = widened;
    let off = func.fresh_value_ids().take().expect("a fresh value id");
    let entry = func.entry;
    func.blocks
        .iter_mut()
        .find(|block| block.id == entry)
        .expect("the entry block exists")
        .params
        .push((off, trust_ir::ty::Ty::U64));
    let Inst::GEP { pointee_ty, inbounds, indices, .. } = &mut func.blocks[gb].body[gn].inst else {
        unreachable!("the_gep returns a GEP")
    };
    *pointee_ty = trust_ir::ty::Ty::U8;
    *inbounds = false;
    *indices = vec![off];
}

/// Resolve the address to field `a` — `gep u32 %s[0]`, byte 0 — which is what a
/// consumer reading an unknown offset as offset 0 would compute.
fn resolve_to_offset_zero(module: &mut Module) {
    let (b, n) = definition(module, gep_index(module));
    let node = &mut module.functions[0].blocks[b].body[n];
    let Inst::Const { value, .. } = &mut node.inst else {
        panic!("the falsifier starts from a laid-out base's constant index")
    };
    *value = trust_ir::Constant::Int(0);
}

/// Plan the bundle exactly as `direct_shadow_differential::mir_lane_bundle` does:
/// per-row public identity minted over the canonical projection, one owner bound to a
/// digest of the function it was lowered from.
fn bundle(mut module: Module, func: &VerifiableFunction) -> NativeVerificationBundle {
    let minted: Vec<(ProofId, PublicObligationIdentity)> = module
        .proof_obligations
        .iter()
        .map(|obligation| {
            let source = obligation.source.as_ref().expect("bridge rows carry a source");
            let public_obligation_id = format!("unknown-offset:{}", source.assertion_id);
            assert!(trust_ir::proof::is_canonical_public_obligation_id(&public_obligation_id));
            let projection = trust_verifier_api::TrustObligation {
                obligation_id: public_obligation_id.clone(),
                kind: match obligation.kind {
                    trust_ir::ObligationKind::ArithmeticSafety => {
                        trust_verifier_api::ObligationKind::ArithmeticSafety
                    }
                    ref other => panic!("fixture minted an unexpected row kind {other:?}"),
                },
                contract_id: None,
                proof_item_id: None,
                source: trust_verifier_api::SourceLocation::default(),
                description: obligation.description.clone(),
                required_strength: None,
                summary_facts: Vec::new(),
                metadata: Vec::new(),
            };
            let hex = projection.canonical_semantic_digest_sha256().expect("canonical digest");
            let mut digest = [0_u8; 32];
            for (index, pair) in hex.as_bytes().chunks_exact(2).enumerate() {
                digest[index] = u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16)
                    .expect("canonical digest is hex");
            }
            (
                obligation.id,
                PublicObligationIdentity {
                    obligation_id: public_obligation_id,
                    semantic_digest: ProofDigest::sha256(digest),
                },
            )
        })
        .collect();
    assert!(!minted.is_empty(), "the division mints at least one obligation");
    for (id, public) in minted {
        let obligation =
            module.proof_obligations.iter_mut().find(|row| row.id == id).expect("row exists");
        obligation.source.as_mut().expect("checked above").public = Some(public);
    }
    let bytes = serde_json::to_vec(func).expect("the fixture serializes");
    let digest: [u8; 32] = sha2::Sha256::digest(&bytes).into();
    let owners = [trust_ir_bridge::NativeBundleOwner {
        function: module.functions[0].id,
        source_digest: ProofDigest::sha256(digest),
    }];
    trust_ir_bridge::native_verification_bundle_from_module_owners(module, &owners)
        .expect("the MIR-compatibility planner accepts the module")
}

fn runner() -> trust_mc_driver::NativeTrustIrChcPdrRunner {
    trust_mc_driver::NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default()
            .with_engine(trust_mc_core::ChcPdrEngine::AdaptivePortfolio)
            .with_timeout(SOLVE_TIMEOUT),
    )
}

/// The TRANSLATOR's verdict with the production gate bypassed: the bundle's one CHC
/// request, translated with the full safety profile and solved by the typed engine.
/// `Ok(())` when proved AND replayed; otherwise the status and the translator's
/// diagnostics.
fn translator_verdict(bundle: &NativeVerificationBundle) -> Result<(), String> {
    let rows = trust_mc_trust_bmc::trust_mc_chc_pdr_obligations_from_native_bundle(
        bundle,
        &trust_mc_trust_bmc::TranslateOptions::default(),
    )
    .expect("the bundle translates");
    let [row] = rows.as_slice() else { panic!("one CHC request, got {}", rows.len()) };
    // The typed runner's own proof boundary: a candidate counts as PROVED only after
    // its fresh exact replay installs the private authority, the same bar the bundle
    // runner applies before it reports a row proved.
    let verification = trust_mc_driver::NativeTypedChcPdrRunner::with_options(
        trust_mc_core::ChcPdrSolveOptions::default()
            .with_engine(trust_mc_core::ChcPdrEngine::AdaptivePortfolio)
            .with_timeout(SOLVE_TIMEOUT),
    )
    .solve_full_verification_with_fresh_exact_replay(row.obligation.clone())
    .expect("the typed solve runs");
    match verification.authorized_native_proof() {
        Ok(_) => Ok(()),
        Err(error) => Err(format!(
            "{:?} (no replayed proof: {error}); diagnostics: {:?}",
            verification.outcome.status, row.diagnostics
        )),
    }
}

#[cfg(test)]
mod tests {
    use trust_ir::SourceGenerationAuthority;

    use super::*;

    /// Solve `module` through the PRODUCTION runner entry, with the authority
    /// production mints at this seam. The ONE mint, here in `mod tests` for the
    /// production-issuer census. `Err` carries the runner's refusal.
    fn production(module: Module, func: &VerifiableFunction) -> Result<(), String> {
        let mut bundle = bundle(module, func);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
            .expect("the freshly planned in-process bundle mints authority");
        let evidence = runner()
            .solve_bundle_native_proof_grade_with_source_authority(&bundle, &authority)
            .map_err(|error| format!("REFUSED: {error}"))?;
        if !evidence.obligations.is_empty()
            && evidence.refuted.is_empty()
            && evidence.not_proved.is_empty()
        {
            Ok(())
        } else {
            Err(format!(
                "not proved: {} refuted, {:?}",
                evidence.refuted.len(),
                evidence.not_proved.iter().map(|row| &row.reason).collect::<Vec<_>>()
            ))
        }
    }

    fn translator(module: Module, func: &VerifiableFunction) -> Result<(), String> {
        translator_verdict(&bundle(module, func))
    }

    /// The unknown-offset module for `divisor`: the bridge's own output over a
    /// layout-less `S`, or the laid-out `S`'s exact address respelled.
    fn unknown_offset_module(laid_out: bool, divisor: Divisor) -> (Module, VerifiableFunction) {
        let func = function(s_ty(laid_out), divisor);
        let mut module = lowered(&func);
        if laid_out {
            assert!(!names_no_offset(&module), "a laid-out base names its offset\n{module}");
            respell_as_unknown_offset(&mut module);
        }
        assert!(names_no_offset(&module), "the address names no offset\n{module}");
        (module, func)
    }

    #[test]
    fn the_production_gate_refuses_a_field_address_exact_or_unknown() {
        for (laid_out, respell) in [(false, false), (true, true), (true, false)] {
            let func = function(s_ty(laid_out), Divisor::FieldOrOne);
            let mut module = lowered(&func);
            if respell {
                respell_as_unknown_offset(&mut module);
            }
            let unknown = names_no_offset(&module);
            let printed = module.to_string();
            match production(module, &func) {
                Err(refusal) => assert!(
                    refusal.starts_with("REFUSED")
                        && (refusal.contains("GEP") || refusal.contains("Alloca")),
                    "laid_out={laid_out} unknown={unknown}: the gate must refuse the field \
                     address itself, got {refusal}\n{printed}"
                ),
                Ok(()) => panic!(
                    "laid_out={laid_out} unknown={unknown}: the production gate admitted a GEP \
                     field address — the translator rows below are now the production lane, \
                     re-read this module's doc\n{printed}"
                ),
            }
        }
    }

    #[test]
    fn a_property_of_the_wrong_field_is_not_proved_through_an_unknown_offset() {
        for laid_out in [false, true] {
            let (module, func) = unknown_offset_module(laid_out, Divisor::Field);
            let printed = module.to_string();
            let verdict = translator(module, &func);
            assert!(
                verdict.as_ref().is_err_and(|reason| reason.contains("OperandConsumption")),
                "laid_out={laid_out}: `100 / s.b` with s.b == 0 through a poison offset must be \
                 refused by the consumption guard (a PROVED here means the translator read it \
                 as a concrete offset): {verdict:?}\n{printed}"
            );
        }
    }

    #[test]
    fn an_unknown_offset_is_refused_even_for_a_property_of_every_value() {
        // This row asserted PROVED until trust-mc's operand-consumption guard
        // (c88bca8d7, in Trust since 8862c94337); BMC-LANE-1 (2026-11-06) changed the
        // expectation to the refusal. The unknown offset is `undef u64`,
        // poison, and the `GEP` consuming it is not executable; reading it as a fresh
        // value was the havoc model the guard retired. A refusal, never a proof of
        // anything about the bytes it addresses (docs/DECISION_QUEUE.md BMC-LANE-1).
        for laid_out in [false, true] {
            let (module, func) = unknown_offset_module(laid_out, Divisor::FieldOrOne);
            let printed = module.to_string();
            let verdict = translator(module, &func);
            assert!(
                verdict.as_ref().is_err_and(|reason| reason.contains("OperandConsumption")),
                "laid_out={laid_out}: `100 / (x | 1)` through a poison offset must be refused \
                 by the consumption guard: {verdict:?}\n{printed}"
            );
        }
    }

    #[test]
    fn a_property_of_every_value_is_proved_through_the_exact_address() {
        // The positive control for the rows above: the harness does prove through a
        // field address. rustc's exact address of `s.b`, and `100 / (s.b | 1)`.
        let func = function(s_ty(true), Divisor::FieldOrOne);
        let module = lowered(&func);
        assert!(!names_no_offset(&module));
        let printed = module.to_string();
        let verdict = translator(module, &func);
        assert!(verdict.is_ok(), "`100 / (s.b | 1)` at the exact address: {verdict:?}\n{printed}");
    }

    #[test]
    fn resolving_the_unknown_offset_to_zero_would_prove_the_false_property() {
        // THE FALSIFIER. Byte 0 is `s.a` == 1, so a consumer that read the unknown
        // offset as 0 proves `100 / s.b` safe while `s.b` is 0. It must be PROVED here —
        // otherwise the rows above could be passing because this harness proves nothing
        // through a field address at all.
        let func = function(s_ty(true), Divisor::Field);
        let mut module = lowered(&func);
        resolve_to_offset_zero(&mut module);
        let printed = module.to_string();
        let verdict = translator(module, &func);
        assert!(
            verdict.is_ok(),
            "the offset-0 falsifier must prove the (false-for-s.b) property: {verdict:?}\n{printed}"
        );
    }

    #[test]
    fn the_exact_address_of_the_right_field_is_not_proved() {
        // The control on the exact lane: rustc's layout names byte 4, `s.b` is 0, and
        // the division by it is not proved.
        let func = function(s_ty(true), Divisor::Field);
        let module = lowered(&func);
        assert!(!names_no_offset(&module));
        let printed = module.to_string();
        assert!(translator(module, &func).is_err(), "`100 / s.b` with s.b == 0\n{printed}");
    }

    #[test]
    fn a_root_parameter_offset_is_refused_at_the_load() {
        // An EXECUTABLE unknown offset: a root `u64` parameter, a nondeterministic input
        // over its value domain (SPEC_RATIFICATIONS §13), which the guard grants
        // definedness. The address `gep u8 %s[%off]` is then executable, but the load
        // through it may read outside the 8-byte object, so the guard refuses the
        // loaded value (`OperandConsumption` at its first consumer), for the
        // every-value property too. So no spelling of an unknown offset, poison or
        // executable, reaches the translator's address model past the guard; were one
        // to, the wrong-field row above is the havoc-not-concrete check to restore.
        for divisor in [Divisor::Field, Divisor::FieldOrOne] {
            let func = function(s_ty(true), divisor);
            let mut module = lowered(&func);
            respell_offset_as_a_root_parameter(&mut module);
            let printed = module.to_string();
            let verdict = translator(module, &func);
            assert!(
                verdict.as_ref().is_err_and(|reason| reason.contains("OperandConsumption")),
                "{divisor:?}: a load through a root-parameter offset must be refused by the \
                 consumption guard: {verdict:?}\n{printed}"
            );
        }
    }
}
