// trust-types/boundary.rs: Trust boundary analysis types
//
// Identifies where data crosses between trusted and untrusted zones
// (public API surfaces, FFI calls, unsafe blocks, trait impls, module
// boundaries) and feeds boundary information into VC generation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::FxHashMap;

use serde::{Deserialize, Serialize};

use crate::model::SourceSpan;

/// Classification of a code region's trust level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustZone {
    /// Internal, verified code. Full invariants hold.
    Trusted,
    /// External caller or input source. No invariants assumed.
    Untrusted,
    /// Third-party crate or system library. Partial trust.
    External,
    /// Foreign function interface. Minimal trust, unsafe by nature.
    Ffi,
}

impl TrustZone {
    /// Returns true if data entering this zone from outside needs validation.
    #[must_use]
    pub fn requires_input_validation(&self) -> bool {
        matches!(self, TrustZone::Trusted)
    }

    /// Returns true if data leaving this zone needs output guarantees.
    #[must_use]
    pub fn requires_output_guarantee(&self) -> bool {
        matches!(self, TrustZone::Trusted | TrustZone::External)
    }
}

/// What kind of code construct creates a trust boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BoundaryKind {
    /// A `pub fn` visible to external callers.
    PublicApi,
    /// An `extern "C"` or other FFI call.
    FfiCall,
    /// An `unsafe { }` block.
    UnsafeBlock,
    /// A trait implementation (data crosses trait boundary).
    TraitImpl,
    /// A `pub(crate)` or inter-module boundary.
    ModuleBoundary,
}

impl BoundaryKind {
    /// Human-readable label for diagnostics.
    #[must_use]
    pub fn label(&self) -> &'static str {
        match self {
            BoundaryKind::PublicApi => "public API",
            BoundaryKind::FfiCall => "FFI call",
            BoundaryKind::UnsafeBlock => "unsafe block",
            BoundaryKind::TraitImpl => "trait implementation",
            BoundaryKind::ModuleBoundary => "module boundary",
        }
    }
}

/// A single trust boundary crossing detected in the code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustBoundary {
    /// Zone the data comes from.
    pub from_zone: TrustZone,
    /// Zone the data enters.
    pub to_zone: TrustZone,
    /// Source location of the boundary crossing.
    pub location: SourceSpan,
    /// Fully qualified path of the function at the boundary.
    pub function_path: String,
    /// What kind of construct creates this boundary.
    pub kind: BoundaryKind,
}

impl TrustBoundary {
    /// Returns true if this crossing goes from a less-trusted to a more-trusted zone,
    /// meaning input validation VCs should be generated.
    #[must_use]
    pub fn needs_precondition(&self) -> bool {
        matches!(
            (self.from_zone, self.to_zone),
            (TrustZone::Untrusted, TrustZone::Trusted)
                | (TrustZone::Ffi, TrustZone::Trusted)
                | (TrustZone::External, TrustZone::Trusted)
        )
    }

    /// Returns true if this crossing goes from a trusted zone outward,
    /// meaning output guarantee VCs should be generated.
    #[must_use]
    pub fn needs_postcondition(&self) -> bool {
        matches!(
            (self.from_zone, self.to_zone),
            (TrustZone::Trusted, TrustZone::External)
                | (TrustZone::Trusted, TrustZone::Ffi)
                | (TrustZone::Trusted, TrustZone::Untrusted)
        )
    }

    /// Returns true if this boundary involves FFI (either direction).
    #[must_use]
    pub fn is_ffi(&self) -> bool {
        self.from_zone == TrustZone::Ffi
            || self.to_zone == TrustZone::Ffi
            || self.kind == BoundaryKind::FfiCall
    }
}

/// Result of trust boundary analysis for a module or crate.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BoundaryAnalysis {
    /// All detected trust boundary crossings.
    pub boundaries: Vec<TrustBoundary>,
    /// Map from function path to its assigned trust zone.
    pub zones: FxHashMap<String, TrustZone>,
}

impl BoundaryAnalysis {
    /// Create an empty analysis.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a boundary crossing.
    pub fn add_boundary(&mut self, boundary: TrustBoundary) {
        self.boundaries.push(boundary);
    }

    /// Assign a trust zone to a function path.
    pub fn set_zone(&mut self, function_path: impl Into<String>, zone: TrustZone) {
        self.zones.insert(function_path.into(), zone);
    }

    /// Look up the trust zone for a function, defaulting to Trusted for internal code.
    #[must_use]
    pub fn zone_for(&self, function_path: &str) -> TrustZone {
        self.zones.get(function_path).copied().unwrap_or(TrustZone::Trusted)
    }

    /// Boundaries that require precondition VCs (untrusted -> trusted).
    #[must_use]
    pub fn precondition_boundaries(&self) -> Vec<&TrustBoundary> {
        self.boundaries.iter().filter(|b| b.needs_precondition()).collect()
    }

    /// Boundaries that require postcondition VCs (trusted -> external).
    #[must_use]
    pub fn postcondition_boundaries(&self) -> Vec<&TrustBoundary> {
        self.boundaries.iter().filter(|b| b.needs_postcondition()).collect()
    }

    /// All FFI-related boundaries.
    #[must_use]
    pub fn ffi_boundaries(&self) -> Vec<&TrustBoundary> {
        self.boundaries.iter().filter(|b| b.is_ffi()).collect()
    }

    /// Number of detected boundaries.
    #[must_use]
    pub fn boundary_count(&self) -> usize {
        self.boundaries.len()
    }

    /// True if no boundaries were detected.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.boundaries.is_empty()
    }
}

/// Classify a function as a trust boundary based on visibility and attributes.
///
/// This is a heuristic classifier that examines function metadata to determine
/// if it sits at a trust boundary. Used by trust-mir-extract to build
/// `BoundaryAnalysis` during MIR traversal.
#[must_use]
pub fn classify_boundary(
    function_path: &str,
    is_pub: bool,
    is_unsafe: bool,
    is_extern: bool,
    is_trait_impl: bool,
) -> Option<TrustBoundary> {
    let kind = if is_extern {
        BoundaryKind::FfiCall
    } else if is_unsafe {
        BoundaryKind::UnsafeBlock
    } else if is_trait_impl {
        BoundaryKind::TraitImpl
    } else if is_pub {
        BoundaryKind::PublicApi
    } else {
        return None;
    };

    let (from_zone, to_zone) = match kind {
        BoundaryKind::FfiCall => (TrustZone::Ffi, TrustZone::Trusted),
        BoundaryKind::UnsafeBlock => (TrustZone::Untrusted, TrustZone::Trusted),
        BoundaryKind::TraitImpl => (TrustZone::External, TrustZone::Trusted),
        BoundaryKind::PublicApi => (TrustZone::Untrusted, TrustZone::Trusted),
        BoundaryKind::ModuleBoundary => (TrustZone::Trusted, TrustZone::Trusted),
    };

    Some(TrustBoundary {
        from_zone,
        to_zone,
        location: SourceSpan::default(),
        function_path: function_path.to_string(),
        kind,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trust_zone_requires_input_validation() {
        assert!(TrustZone::Trusted.requires_input_validation());
        assert!(!TrustZone::Untrusted.requires_input_validation());
        assert!(!TrustZone::External.requires_input_validation());
        assert!(!TrustZone::Ffi.requires_input_validation());
    }

    #[test]
    fn test_trust_zone_requires_output_guarantee() {
        assert!(TrustZone::Trusted.requires_output_guarantee());
        assert!(TrustZone::External.requires_output_guarantee());
        assert!(!TrustZone::Untrusted.requires_output_guarantee());
        assert!(!TrustZone::Ffi.requires_output_guarantee());
    }

    #[test]
    fn test_boundary_needs_precondition() {
        let boundary = TrustBoundary {
            from_zone: TrustZone::Untrusted,
            to_zone: TrustZone::Trusted,
            location: SourceSpan::default(),
            function_path: "crate::process_input".into(),
            kind: BoundaryKind::PublicApi,
        };
        assert!(boundary.needs_precondition());
        assert!(!boundary.needs_postcondition());
    }

    #[test]
    fn test_boundary_needs_postcondition() {
        let boundary = TrustBoundary {
            from_zone: TrustZone::Trusted,
            to_zone: TrustZone::External,
            location: SourceSpan::default(),
            function_path: "crate::send_response".into(),
            kind: BoundaryKind::ModuleBoundary,
        };
        assert!(!boundary.needs_precondition());
        assert!(boundary.needs_postcondition());
    }

    #[test]
    fn test_ffi_boundary_detection() {
        let ffi = TrustBoundary {
            from_zone: TrustZone::Ffi,
            to_zone: TrustZone::Trusted,
            location: SourceSpan::default(),
            function_path: "crate::ffi_callback".into(),
            kind: BoundaryKind::FfiCall,
        };
        assert!(ffi.is_ffi());
        assert!(ffi.needs_precondition());
    }

    #[test]
    fn test_internal_boundary_no_vcs() {
        let internal = TrustBoundary {
            from_zone: TrustZone::Trusted,
            to_zone: TrustZone::Trusted,
            location: SourceSpan::default(),
            function_path: "crate::internal_helper".into(),
            kind: BoundaryKind::ModuleBoundary,
        };
        assert!(!internal.needs_precondition());
        assert!(!internal.needs_postcondition());
        assert!(!internal.is_ffi());
    }

    #[test]
    fn test_boundary_analysis_operations() {
        let mut analysis = BoundaryAnalysis::new();
        assert!(analysis.is_empty());
        assert_eq!(analysis.boundary_count(), 0);

        analysis.set_zone("crate::public_fn", TrustZone::Trusted);
        analysis.set_zone("external::lib", TrustZone::External);

        assert_eq!(analysis.zone_for("crate::public_fn"), TrustZone::Trusted);
        assert_eq!(analysis.zone_for("external::lib"), TrustZone::External);
        assert_eq!(analysis.zone_for("unknown::fn"), TrustZone::Trusted);

        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Untrusted,
            to_zone: TrustZone::Trusted,
            location: SourceSpan::default(),
            function_path: "crate::process".into(),
            kind: BoundaryKind::PublicApi,
        });
        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Trusted,
            to_zone: TrustZone::External,
            location: SourceSpan::default(),
            function_path: "crate::send".into(),
            kind: BoundaryKind::ModuleBoundary,
        });
        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Ffi,
            to_zone: TrustZone::Trusted,
            location: SourceSpan::default(),
            function_path: "crate::ffi_entry".into(),
            kind: BoundaryKind::FfiCall,
        });

        assert_eq!(analysis.boundary_count(), 3);
        assert!(!analysis.is_empty());
        assert_eq!(analysis.precondition_boundaries().len(), 2);
        assert_eq!(analysis.postcondition_boundaries().len(), 1);
        assert_eq!(analysis.ffi_boundaries().len(), 1);
    }

    #[test]
    fn test_classify_boundary_pub_fn() {
        let boundary = classify_boundary("crate::public_fn", true, false, false, false);
        assert!(boundary.is_some());
        let b = boundary.unwrap();
        assert_eq!(b.kind, BoundaryKind::PublicApi);
        assert_eq!(b.from_zone, TrustZone::Untrusted);
        assert_eq!(b.to_zone, TrustZone::Trusted);
        assert!(b.needs_precondition());
    }

    #[test]
    fn test_classify_boundary_extern() {
        let boundary = classify_boundary("crate::extern_fn", false, false, true, false);
        assert!(boundary.is_some());
        let b = boundary.unwrap();
        assert_eq!(b.kind, BoundaryKind::FfiCall);
        assert!(b.is_ffi());
    }

    #[test]
    fn test_classify_boundary_unsafe() {
        let boundary = classify_boundary("crate::unsafe_fn", false, true, false, false);
        assert!(boundary.is_some());
        let b = boundary.unwrap();
        assert_eq!(b.kind, BoundaryKind::UnsafeBlock);
        assert!(b.needs_precondition());
    }

    #[test]
    fn test_classify_boundary_trait_impl() {
        let boundary = classify_boundary("crate::impl_trait", false, false, false, true);
        assert!(boundary.is_some());
        let b = boundary.unwrap();
        assert_eq!(b.kind, BoundaryKind::TraitImpl);
    }

    #[test]
    fn test_classify_boundary_private_fn_no_boundary() {
        let boundary = classify_boundary("crate::private_fn", false, false, false, false);
        assert!(boundary.is_none());
    }

    #[test]
    fn test_classify_boundary_extern_takes_priority() {
        // extern + pub + unsafe: extern wins
        let boundary = classify_boundary("crate::ffi", true, true, true, false);
        assert!(boundary.is_some());
        assert_eq!(boundary.unwrap().kind, BoundaryKind::FfiCall);
    }

    #[test]
    fn test_boundary_kind_labels() {
        assert_eq!(BoundaryKind::PublicApi.label(), "public API");
        assert_eq!(BoundaryKind::FfiCall.label(), "FFI call");
        assert_eq!(BoundaryKind::UnsafeBlock.label(), "unsafe block");
        assert_eq!(BoundaryKind::TraitImpl.label(), "trait implementation");
        assert_eq!(BoundaryKind::ModuleBoundary.label(), "module boundary");
    }

    #[test]
    fn test_serialization_roundtrip() {
        let mut analysis = BoundaryAnalysis::new();
        analysis.set_zone("crate::f", TrustZone::Trusted);
        analysis.add_boundary(TrustBoundary {
            from_zone: TrustZone::Untrusted,
            to_zone: TrustZone::Trusted,
            location: SourceSpan::default(),
            function_path: "crate::f".into(),
            kind: BoundaryKind::PublicApi,
        });

        let json = serde_json::to_string(&analysis).expect("serialize");
        let roundtrip: BoundaryAnalysis = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.boundary_count(), 1);
        assert_eq!(roundtrip.zone_for("crate::f"), TrustZone::Trusted);
    }
}
