//! Trust (L1, artifact-lineage attestation): the CANONICAL-REMAPPING certificate — structure half.
//!
//! # The gap this closes, stated exactly
//!
//! [`crate::lineage`] mints one digest per body over the INTACT per-body mini-module plus its
//! callee ledger, and the flip event and the artifact's coverage row both state it. That makes
//! "which row of the artifact is the body the flip compiled?" a question with a mechanical
//! answer. It leaves a second question open, and `lineage`'s own module docs name it under
//! *NOT ESTABLISHED*:
//!
//! > Assembly sorts bodies, assigns fresh dense `FuncId`s, re-interns type/enum/struct tables
//! > and rewrites callees. The row's `func_id` ADDRESSES the resulting function, and the row's
//! > `lineage` NAMES the input it came from — but nothing here proves the assembled function
//! > still means what the pre-assembly mini-module meant.
//!
//! The digest cannot answer that by construction: the two objects are DIFFERENT VALUES on
//! purpose (that is what "remapping" means), so they have different digests, and no amount of
//! hashing relates them. What can be checked is what the remapping is NOT ALLOWED to change.
//! `crate_module::prepare_body_tables` mutates exactly five things — the source-provenance
//! seal, block-parameter types, embedded `Ty`s inside instructions, a promoted-borrow
//! `GlobalId`, and span/scope FILE IDS — and `assemble`'s pass 2 mutates exactly three more —
//! a `Call` callee, a `CallIndirect` signature id, and a reified `FnDef` constant's target and
//! signature. Every one of those is an ID or a `Ty`. NONE of them may change the program's
//! shape: not the block set, not the instruction sequence, not the SSA numbering, not which
//! opcode sits where, not a proof annotation, and not a source line or column.
//!
//! [`certify_remap_shape`] is that invariant, executable. A body whose remap violates it is
//! REFUSED — not spliced, recorded in coverage as un-spliced — because an assembled function
//! that has drifted from the mini-module the flip compiled would make the artifact row a false
//! statement about the shipped code.
//!
//! # Why this is not circular
//!
//! It does not re-derive the remapping and compare (that would test nothing but determinism).
//! It states an INDEPENDENT invariant — "these fields are untouched" — and checks it against
//! the actual output. A walker that skips a block, a `Vec` that loses an element, an
//! `inst_embedded_tys_mut` arm that rebuilds an instruction as a different variant, a
//! renumbering that shifts an SSA id: each produces a certificate failure without the checker
//! knowing anything about how the remap is implemented.
//!
//! # Where it runs, and why THERE
//!
//! In `assemble`'s PASS 1, immediately after `prepare_body_tables` — the pass that does every
//! table remap, and the pass where refusal is free. `assemble`'s own comment states the
//! constraint that decides this: *"all fallibility lives HERE, before a `FuncId` is assigned,
//! so pass 2 can never desync the dense id space by refusing late."* A certificate that could
//! only fail in pass 2 would have no sound way to act on the failure.
//!
//! Pass 2 is therefore covered by ARGUMENT rather than by a second check, and the argument is
//! narrow enough to state: its loop walks `&mut f.blocks[..].body[..]` and writes only through
//! `*callee`, `*sig`, `*fid` and `*ty` bindings taken from `match &mut node.inst` arms. It
//! cannot add, drop or reorder a node, cannot renumber a result, and cannot change an
//! instruction's variant, because it never assigns to `node.inst` or to any `Vec` itself. If
//! that ever stops being true, this module's guarantee stops covering pass 2 and the
//! certificate must be re-sited.
//!
//! # What it does NOT establish
//!
//! * **Semantic equality.** Preserved shape plus remapped ids is not a proof that the
//!   assembled function DENOTES what the mini-module denoted; a map that sends a body's
//!   `TyId(3)` to an assembled entry holding a different type passes every check here. That
//!   is the content half of the certificate, and it does not exist yet.
//! * **Anything about the emitted machine code.** This binds trust-ir to trust-ir.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use std::mem::discriminant;

use trust_ir::{Block, Function, InstrNode};

/// Certify that assembly's remap of `before` into `after` preserved everything a remap is not
/// allowed to touch. `Err` carries the first violation, in enough detail to locate it.
///
/// `before` is the per-body mini-module's function as the producer emitted it (the object
/// [`crate::lineage::body_lineage_digest`] hashed); `after` is what `prepare_body_tables`
/// produced for the assembled module.
///
/// Deliberately NOT compared, each because assembly rewrites it on purpose:
///
/// * `id` — pass 1 assigns a fresh dense `FuncId`.
/// * `name` — `assemble` replaces it with the def path (plus the `{const-init}` /
///   `{static-init}` marker), since a mini-module name is not a crate-unique identity.
/// * `ty` — re-interned into the assembled module's func-type table.
/// * `calling_conv` — set to `Rust` for every spliced body (#180).
/// * `source_provenance` — deliberately dropped: the per-body carrier authenticates the
///   mini-module's semantic image, which assembly changes.
/// * every `Ty`, `GlobalId`, `FuncId` and span/scope FILE id — the remap itself.
pub fn certify_remap_shape(before: &Function, after: &Function) -> Result<(), String> {
    if before.entry != after.entry {
        return Err(format!(
            "remap changed the entry block: {:?} -> {:?}",
            before.entry, after.entry
        ));
    }
    if before.linkage != after.linkage {
        return Err(format!("remap changed linkage: {:?} -> {:?}", before.linkage, after.linkage));
    }
    // The scope TABLE is re-interned span-by-span (`remap_func_scopes`), which may not add or
    // drop an entry: node `scope` fields are indices into it, so a length change silently
    // re-points them.
    let (before_scopes, after_scopes) =
        (before.scopes.as_ref().map(Vec::len), after.scopes.as_ref().map(Vec::len));
    if before_scopes != after_scopes {
        return Err(format!(
            "remap changed the lexical scope table: {before_scopes:?} entries -> {after_scopes:?}"
        ));
    }
    if before.blocks.len() != after.blocks.len() {
        return Err(format!(
            "remap changed the block count: {} -> {}",
            before.blocks.len(),
            after.blocks.len()
        ));
    }
    for (index, (before_block, after_block)) in before.blocks.iter().zip(&after.blocks).enumerate()
    {
        certify_block(index, before_block, after_block)?;
    }
    Ok(())
}

fn certify_block(index: usize, before: &Block, after: &Block) -> Result<(), String> {
    if before.id != after.id {
        return Err(format!("remap renumbered block {index}: {:?} -> {:?}", before.id, after.id));
    }
    // Parameter TYPES are remapped; the parameter VALUES are the block's SSA identity and are
    // not.
    if before.params.len() != after.params.len() {
        return Err(format!(
            "remap changed block {:?}'s parameter count: {} -> {}",
            before.id,
            before.params.len(),
            after.params.len()
        ));
    }
    for (position, ((before_value, _), (after_value, _))) in
        before.params.iter().zip(&after.params).enumerate()
    {
        if before_value != after_value {
            return Err(format!(
                "remap renumbered block {:?} parameter {position}: {before_value:?} -> \
                 {after_value:?}",
                before.id
            ));
        }
    }
    if before.body.len() != after.body.len() {
        return Err(format!(
            "remap changed block {:?}'s instruction count: {} -> {}",
            before.id,
            before.body.len(),
            after.body.len()
        ));
    }
    for (position, (before_node, after_node)) in before.body.iter().zip(&after.body).enumerate() {
        certify_node(before.id, position, before_node, after_node)?;
    }
    Ok(())
}

fn certify_node(
    block: trust_ir::BlockId,
    position: usize,
    before: &InstrNode,
    after: &InstrNode,
) -> Result<(), String> {
    // The OPCODE. Only the ids and `Ty`s inside an instruction are remapped; the variant is
    // the instruction's identity and a change here means the walk rebuilt it as a different
    // operation. `discriminant` compares exactly that and nothing else, so this check needs no
    // per-variant enumeration and cannot rot as `Inst` grows.
    if discriminant(&before.inst) != discriminant(&after.inst) {
        return Err(format!(
            "remap changed the instruction at {block:?}[{position}] to a different opcode"
        ));
    }
    if before.results != after.results {
        return Err(format!(
            "remap renumbered the results at {block:?}[{position}]: {:?} -> {:?}",
            before.results, after.results
        ));
    }
    // Proof annotations and per-call proof context name module obligations, which assembly
    // does not renumber for a spliced body. Silent loss here would strip a body's obligations
    // while leaving its code — an artifact that claims less than the body it describes.
    if before.proofs != after.proofs {
        return Err(format!("remap changed the proof annotations at {block:?}[{position}]"));
    }
    if before.proof_context != after.proof_context {
        return Err(format!("remap changed the proof context at {block:?}[{position}]"));
    }
    if before.scope != after.scope {
        return Err(format!(
            "remap changed the lexical scope at {block:?}[{position}]: {:?} -> {:?}",
            before.scope, after.scope
        ));
    }
    // The SOURCE POSITION. `remap_node_span` re-interns the FILE id against the assembled
    // module's file table and drops the whole span when the body's file id is dangling — both
    // documented — so the line and column are what must survive, and only when a span survived
    // at all.
    match (before.span, after.span) {
        (Some(before_span), Some(after_span)) => {
            if (before_span.line, before_span.col) != (after_span.line, after_span.col) {
                return Err(format!(
                    "remap moved the source position at {block:?}[{position}]: {}:{} -> {}:{}",
                    before_span.line, before_span.col, after_span.line, after_span.col
                ));
            }
        }
        // A dangling per-body file id drops the span (`remap_node_span`); documented, and a
        // debugger-visible loss rather than a semantic one.
        (Some(_), None) | (None, None) => {}
        (None, Some(after_span)) => {
            return Err(format!(
                "remap INVENTED a source position at {block:?}[{position}]: {}:{}",
                after_span.line, after_span.col
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use trust_ir::{
        BinOp, Block, BlockId, Constant, FuncId, FuncTyId, Function, Inst, InstrNode,
        ProofAnnotation, SourceSpan, Ty, ValueId,
    };

    use super::certify_remap_shape;

    /// A two-block body with parameters, results, a span and a proof annotation — enough
    /// surface that every clause of the certificate has something to compare.
    fn probe() -> Function {
        let mut f = Function::new(FuncId::new(0), "probe", FuncTyId::new(0), BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.params.push((ValueId::new(0), Ty::U64));
        entry.body.push(InstrNode {
            inst: Inst::Const { ty: Ty::U64, value: Constant::Int(1) },
            results: vec![ValueId::new(1)],
            proofs: Vec::new(),
            span: Some(SourceSpan { file: 0, line: 2, col: 32 }),
            proof_context: None,
            scope: None,
        });
        entry.body.push(InstrNode {
            inst: Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            results: vec![ValueId::new(2)],
            proofs: vec![ProofAnnotation::NoOverflow],
            span: Some(SourceSpan { file: 0, line: 2, col: 28 }),
            proof_context: None,
            scope: None,
        });
        entry.body.push(InstrNode {
            inst: Inst::Return { values: vec![ValueId::new(2)] },
            results: Vec::new(),
            proofs: Vec::new(),
            span: Some(SourceSpan { file: 0, line: 2, col: 35 }),
            proof_context: None,
            scope: None,
        });
        f.blocks.push(entry);
        f
    }

    /// THE POSITIVE CASE, and it is not a formality: it is the whole reason the certificate can
    /// be fail-closed. Every mutation assembly is ALLOWED to make is applied here at once — the
    /// fresh dense `FuncId`, the def-path name, the re-interned signature, the `Rust` calling
    /// convention, remapped embedded types, and a re-interned span FILE id — and the
    /// certificate must still pass. A checker that rejected any of these would silently stop
    /// bodies from splicing.
    #[test]
    fn test_every_legitimate_assembly_rewrite_still_certifies() {
        let before = probe();
        let mut after = before.clone();
        after.id = FuncId::new(7);
        after.name = "crate::path::probe".to_string();
        after.ty = FuncTyId::new(3);
        after.calling_conv = trust_ir::CallingConv::Rust;
        for block in &mut after.blocks {
            for (_, ty) in &mut block.params {
                *ty = Ty::Struct(trust_ir::StructId::new(9));
            }
            for node in &mut block.body {
                if let Inst::Const { ty, .. } = &mut node.inst {
                    *ty = Ty::Struct(trust_ir::StructId::new(9));
                }
                if let Some(span) = node.span.as_mut() {
                    span.file = 11;
                }
            }
        }
        certify_remap_shape(&before, &after).expect(
            "the certificate must accept every rewrite assembly legitimately performs — \
             otherwise it silently costs splice coverage",
        );
    }

    /// A dangling per-body file id drops the span. Documented in `remap_node_span`, so it is
    /// admitted — asserted here so that admission is a decision rather than an oversight.
    #[test]
    fn test_a_dropped_span_is_admitted_but_an_invented_one_is_not() {
        let before = probe();
        let mut dropped = before.clone();
        dropped.blocks[0].body[0].span = None;
        certify_remap_shape(&before, &dropped)
            .expect("a dangling file id drops the span; that is a documented outcome");

        let mut invented = before.clone();
        invented.blocks[0].body[0].span = None;
        let mut after = invented.clone();
        after.blocks[0].body[0].span = Some(SourceSpan { file: 0, line: 99, col: 1 });
        certify_remap_shape(&invented, &after)
            .expect_err("a span the mini-module never carried must not appear during assembly");
    }

    /// THE NEGATIVE CONTROLS — one per clause. Each perturbation is a class of remap defect:
    /// a walker that skips a block, a `Vec` that loses an element, a rebuild that changes the
    /// opcode, a renumbering that shifts SSA identity, an annotation dropped on the floor, a
    /// scope table that changed length, a source position that moved.
    #[test]
    fn test_every_shape_perturbation_is_refused() {
        let before = probe();

        let mut entry_moved = before.clone();
        entry_moved.entry = BlockId::new(1);
        assert!(certify_remap_shape(&before, &entry_moved).is_err(), "entry block moved");

        let mut block_dropped = before.clone();
        block_dropped.blocks.clear();
        assert!(certify_remap_shape(&before, &block_dropped).is_err(), "block dropped");

        let mut block_renumbered = before.clone();
        block_renumbered.blocks[0].id = BlockId::new(4);
        assert!(certify_remap_shape(&before, &block_renumbered).is_err(), "block renumbered");

        let mut param_dropped = before.clone();
        param_dropped.blocks[0].params.clear();
        assert!(certify_remap_shape(&before, &param_dropped).is_err(), "block param dropped");

        let mut param_renumbered = before.clone();
        param_renumbered.blocks[0].params[0].0 = ValueId::new(42);
        assert!(certify_remap_shape(&before, &param_renumbered).is_err(), "block param renumbered");

        let mut instruction_dropped = before.clone();
        instruction_dropped.blocks[0].body.remove(1);
        assert!(certify_remap_shape(&before, &instruction_dropped).is_err(), "instruction dropped");

        let mut opcode_changed = before.clone();
        opcode_changed.blocks[0].body[1].inst =
            Inst::Const { ty: Ty::U64, value: Constant::Int(0) };
        assert!(certify_remap_shape(&before, &opcode_changed).is_err(), "opcode changed");

        let mut result_renumbered = before.clone();
        result_renumbered.blocks[0].body[1].results = vec![ValueId::new(99)];
        assert!(certify_remap_shape(&before, &result_renumbered).is_err(), "result renumbered");

        let mut proof_dropped = before.clone();
        proof_dropped.blocks[0].body[1].proofs.clear();
        assert!(certify_remap_shape(&before, &proof_dropped).is_err(), "proof annotation dropped");

        let mut scope_stamped = before.clone();
        scope_stamped.blocks[0].body[1].scope = Some(3);
        assert!(certify_remap_shape(&before, &scope_stamped).is_err(), "node scope changed");

        let mut scopes_grown = before.clone();
        scopes_grown.scopes = Some(Vec::new());
        assert!(certify_remap_shape(&before, &scopes_grown).is_err(), "scope table appeared");

        let mut position_moved = before.clone();
        position_moved.blocks[0].body[0].span = Some(SourceSpan { file: 0, line: 900, col: 1 });
        assert!(certify_remap_shape(&before, &position_moved).is_err(), "source position moved");
    }

    /// The certificate must be reflexive: an unremapped body certifies against itself. A
    /// checker that failed here would refuse every table-free body (the `prepare_body_tables`
    /// fast path returns the function essentially untouched).
    #[test]
    fn test_an_untouched_body_certifies_against_itself() {
        let before = probe();
        certify_remap_shape(&before, &before.clone())
            .expect("a body assembly did not have to remap must certify");
    }

    /// **THE WIRING PIN.** Every test above proves the PREDICATE is correct. None of them
    /// proves `assemble` READS it: `assemble` is reached only through fixtures whose remap is
    /// already shape-preserving, so deleting the call site leaves the whole suite green. That
    /// is the measured "mutation C" hole this crate has already paid for twice (see
    /// `flip_registry::tests::test_the_lane_gate_aggregate_is_read_by_record_green`), and the
    /// house answer is to pin the call site by SOURCE TEXT.
    ///
    /// Goes RED if the certificate is deleted from `assemble`, called somewhere that is not
    /// pass 1, or evaluated without acting on the result.
    #[test]
    fn test_the_certificate_is_read_by_crate_assembly() {
        let assembler = include_str!("crate_module.rs");
        // Needle assembled at run time so this test's own source could not satisfy it if the
        // two files were ever merged.
        let call = format!("{}::{}(", "crate::remap_certificate", "certify_remap_shape");
        assert_eq!(
            assembler.matches(call.as_str()).count(),
            1,
            "crate assembly must invoke the remapping certificate exactly once — a second \
             caller means some other pass now decides the same question, and none means the \
             certificate is a function nothing calls",
        );
        let at = assembler.find(call.as_str()).expect("the call site must exist");
        // It must be a REFUSAL that skips the body, not a logged observation: `assemble`'s
        // pass 1 owns the dense `FuncId` space, and `continue` before `assigned.push` is the
        // only way to decline without desyncing it.
        let tail = &assembler[at..];
        let open = tail.find('{').expect("the refusal must open a block");
        let close = tail.find('}').expect("the refusal must close it");
        assert!(open < close, "the refusal's block must be well-formed");
        assert!(
            tail[open..close].contains(&format!("{};", "continue")),
            "the certificate must REFUSE the body — `continue` before a `FuncId` is assigned. \
             Any other body (a log, a counter) would splice a function whose shape has drifted \
             from the mini-module the flip compiled",
        );
        assert!(
            assembler[..at].ends_with("if ") || assembler[..at].contains("if crate"),
            "the certificate must be the condition of an `if`, not a bound value a later line \
             may or may not consult",
        );
    }
}
