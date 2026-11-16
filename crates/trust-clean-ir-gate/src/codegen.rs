// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Step 3.6's third binding, restricted to identity ABI legalization.
//!
//! The published token is reauthenticated before inspecting the relocated
//! function. Whole-function equality then permits only the function id,
//! linkage and visibility supplied by the compiler's placement table to
//! change. The caller remains responsible for authenticating that table and
//! looking up both signatures in their actual modules.
//!
//! Since WS5.2 the published name is already the Rust link symbol. Renaming
//! it here would change the entity the kernel-gated computation implements.
//! Type tables are unchanged on the compiler lane; neither the type id nor
//! the signature may change. Current carrier-gated bodies contain no calls,
//! so this reader grants no call-edge relocation or ABI rewriting permission.
//!
//! No backend calls this reader yet. Success supplies no proof grade and
//! does not make a serialized body-gate stamp an admission token.

use trust_ir::ty::FuncTy;
use trust_ir::value::FuncId;
use trust_ir::{Function, Linkage, Visibility};

use crate::{GateRefusal, GatedShape, PublishedTrustIrFaithful};

/// Compiler-owned placement of an already authenticated published function.
/// These values are expectations, never independently asserted authority.
#[derive(Clone, Copy, Debug)]
pub struct CodegenRelocation {
    /// The published definition's id in the codegen module.
    pub function_id: FuncId,
    /// Linkage selected by the compiler for that definition.
    pub linkage: Linkage,
    /// Visibility selected by the compiler for that definition.
    pub visibility: Visibility,
}

/// Check exact relocation of a published subject without weakening its gate.
///
/// The consumer must obtain `published` from its current session's authenticated
/// ledger, obtain `relocation` from its compiler identity/placement tables,
/// resolve each signature through its module, and retain the checked function
/// unchanged through compilation. This function deliberately cannot authenticate
/// a cached/imported stamp without the in-memory published token; the session
/// check belongs to the ledger owner, not this TyCtxt-free reader.
pub fn authenticate_codegen(
    published: &PublishedTrustIrFaithful,
    published_signature: &FuncTy,
    published_function: &Function,
    codegen_signature: &FuncTy,
    codegen_function: &Function,
    relocation: CodegenRelocation,
) -> Result<(), GateRefusal> {
    published.authenticate_function(published_signature, published_function)?;

    if !matches!(
        published.shape(),
        GatedShape::WrappingBinOp
            | GatedShape::Projection { .. }
            | GatedShape::ConstantUint { .. }
            | GatedShape::Composed { .. }
    ) {
        return Err(GateRefusal::new(
            "codegen-shape",
            "the codegen relocation reader covers only the four call-free carrier shapes",
        ));
    }

    if published_signature != codegen_signature {
        return Err(GateRefusal::new(
            "codegen-signature",
            "Clean codegen requires identity ABI legalization; the signature changed",
        ));
    }
    // The compiler module clears these channels. Accepting their removal here
    // would silently grant a second transformation beyond identity relocation.
    // Current gated carrier subjects have neither; future coverage must earn a
    // separate rule rather than inherit permission to discard authority data.
    if published_function.summary.is_some() || published_function.source_provenance.is_some() {
        return Err(GateRefusal::new(
            "codegen-metadata",
            "Clean identity relocation does not discard summaries or source provenance",
        ));
    }

    let mut expected = published_function.clone();
    expected.id = relocation.function_id;
    expected.linkage = relocation.linkage;
    expected.visibility = relocation.visibility;
    if &expected != codegen_function {
        return Err(GateRefusal::new(
            "codegen-function",
            "the codegen function differs from its authenticated published subject beyond id, linkage or visibility",
        ));
    }
    Ok(())
}
