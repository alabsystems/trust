// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Owned live input/output custody for the EXISTING faithful extractor.
//! No proof authority, source preservation theorem or serialized restore path.

use trust_types::VerifiableFunction;

use super::nominal_body::NominalBodyObservation;

/// The actual immutable compiler snapshot and the exact existing producer's
/// owned output. Unsupported residue is retained. A mutable/decoded function,
/// matching name/digest, or other emitter result cannot construct this object.
/// Rustc query/provider and extractor correctness remain explicit TCB premises.
pub struct FaithfulNominalCapture<'tcx> {
    source: NominalBodyObservation<'tcx>,
    function: VerifiableFunction,
}

impl<'tcx> FaithfulNominalCapture<'tcx> {
    pub fn source(&self) -> &NominalBodyObservation<'tcx> {
        &self.source
    }
    /// Existing consumers borrow THIS exact produced function. Cloning or
    /// serializing it yields ordinary data, never the live source/capture pair.
    pub fn function(&self) -> &VerifiableFunction {
        &self.function
    }
}

/// Pair a genuine live input with the existing shared extractor's own output.
/// This does not validate arbitrary output as source semantics: no supplied
/// function is accepted and no output check mints proof or admission authority.
pub fn capture_faithful_nominal_body<'tcx>(
    source: NominalBodyObservation<'tcx>,
) -> FaithfulNominalCapture<'tcx> {
    let function = source.extract_faithful();
    FaithfulNominalCapture { source, function }
}
