//! Compiler-owned bounds for primitive-integer `ToString` results.
//!
//! The extractor records these only after its existing real-alloc diagnostic-item,
//! selected-impl and instantiated-Self checks. They are not serialized into MIR,
//! fixtures, proof bundles or census identities. A decoded function has no table.
//! This is a trusted standard-library contract, not a proof of Rust formatting.

use std::collections::BTreeMap;

use trust_types::{BlockId, Operand, Place, Terminator, Ty, VerifiableFunction};

/// The audited decimal formatter's maximum byte length, including a possible sign.
/// Width is the instantiated primitive's actual target width, never a path spelling.
#[must_use]
pub fn primitive_decimal_max_bytes(ty: &Ty) -> Option<u8> {
    let Ty::Int { width, signed } = ty else { return None };
    match (*width, *signed) {
        (8, false) => Some(3),
        (16, false) => Some(5),
        (32, false) => Some(10),
        (64, false) => Some(20),
        (128, false) => Some(39),
        (8, true) => Some(4),
        (16, true) => Some(6),
        (32, true) => Some(11),
        (64, true) => Some(20),
        (128, true) => Some(40),
        _ => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Entry {
    primitive: Ty,
    call_digest: String,
}

/// Non-serializable, function-bound facts supplied only by the authenticated
/// compiler producer. Public construction is a trusted embedding API, like
/// `ElemSizeTable`; it is not authority granted to a decoded MIR field.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PrimitiveDecimalStringTable {
    owner: Option<String>,
    bound_body: Option<String>,
    // A duplicate is sticky-unavailable, including an equal duplicate. The producer
    // must supply exactly one observation of each actual call site.
    entries: BTreeMap<usize, Option<Entry>>,
}

pub(crate) fn body_digest(func: &VerifiableFunction) -> Option<String> {
    let bytes = trust_types::stable_model_json_bytes(&func.body).ok()?;
    Some(trust_types::stable_sha256_hex_parts(&[
        b"trust.vcgen.primitive-decimal-body.v1\0",
        &bytes,
    ]))
}

fn call_digest(call: &Terminator) -> Option<String> {
    let bytes = trust_types::stable_model_json_bytes(call).ok()?;
    Some(trust_types::stable_sha256_hex_parts(&[
        b"trust.vcgen.primitive-decimal-call.v1\0",
        &bytes,
    ]))
}

impl PrimitiveDecimalStringTable {
    /// Start an empty table for this immutable lowered body. A serialization
    /// refusal keeps the table unavailable. Later body edits do not rebind it.
    #[must_use]
    pub fn for_function(func: &VerifiableFunction) -> Self {
        Self {
            owner: Some(func.def_path.clone()),
            bound_body: body_digest(func),
            entries: BTreeMap::new(),
        }
    }

    /// Record one call already admitted by the extractor's real `TyCtxt`
    /// classifier, with its normalized primitive Self type and actual returned
    /// std String's `Freeze` result. This does not perform those compiler checks
    /// itself; only the compiler owns this trusted embedding API. The Freeze
    /// license survives opaque/sequence lowering, never arbitrary shared ADTs.
    pub fn record_authenticated_call(
        &mut self,
        block: BlockId,
        call: &Terminator,
        primitive: Ty,
        returned_string_is_freeze: bool,
    ) {
        let incoming = returned_string_is_freeze
            .then(|| primitive_decimal_max_bytes(&primitive))
            .flatten()
            .and_then(|_| call_digest(call))
            .map(|call_digest| Entry { primitive, call_digest });
        self.entries.entry(block.0).and_modify(|entry| *entry = None).or_insert(incoming);
    }

    /// Whether this table can be installed on exactly this body.
    #[must_use]
    pub(crate) fn matches_body(&self, func: &VerifiableFunction) -> bool {
        self.owner.as_ref() == Some(&func.def_path)
            && self.bound_body.is_some()
            && self.bound_body == crate::generate::primitive_decimal_body_digest_for(func)
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.values().all(Option::is_none)
    }

    /// Re-check the exact call and matching shared primitive receiver. Mutation
    /// and alias licensing of the returned String are separate consumer duties.
    pub(crate) fn max_bytes_at(&self, func: &VerifiableFunction, block: BlockId) -> Option<u8> {
        let entry = self.entries.get(&block.0)?.as_ref()?;
        let call = &func
            .body
            .blocks
            .get(block.0)
            .filter(|b| b.id == block)
            .or_else(|| func.body.blocks.iter().find(|b| b.id == block))?
            .terminator;
        let Terminator::Call {
            args,
            dest,
            target: Some(_),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            ..
        } = call
        else {
            return None;
        };
        if args.len() != 1 || !dest.projections.is_empty() {
            return None;
        }
        let (Operand::Copy(place) | Operand::Move(place)) = &args[0] else { return None };
        let receiver = crate::place_ty_cow(func, place)?;
        let Ty::Ref { mutable: false, inner } = receiver.as_ref() else { return None };
        if inner.as_ref() != &entry.primitive {
            return None;
        }
        // The real trait returns String. If lowering could not retain its standard
        // type, do not lend a numeric result contract to an opaque destination.
        let dest_ty = crate::place_ty_cow(func, &Place::local(dest.local))?;
        if !matches!(dest_ty.as_ref(), Ty::Adt { name, .. }
            if crate::generate::collection_range::is_std_string_adt_name(name))
        {
            return None;
        }
        if call_digest(call).as_ref() != Some(&entry.call_digest) {
            return None;
        }
        primitive_decimal_max_bytes(&entry.primitive)
    }
}
