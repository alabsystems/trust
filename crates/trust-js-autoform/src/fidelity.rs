// fidelity: the pinned evidence this floor is judged by, loaded from a manifest
// the elaborator has no writer for.
//
// The doctrine's third prohibition on an untrusted frontend — after "may not
// assert a proposition" and "may not introduce an unchecked assumption" — is
// "may not narrow its own validation evidence". That one is the easiest to
// break by accident: a lowering that fails on `f64::MAX` is fixed either by
// fixing the lowering or by dropping `f64::MAX` from the corpus, and only one
// of those is honest. When the corpus is a `const` in the same file as the
// lowering, nothing distinguishes the two edits.
//
// So the sample set, the caps, the array shapes, the oracle, and the (empty)
// waiver list live in `fidelity-manifest.json`, a
// `trust.frontend.fidelity-manifest.v1` whose digest covers every value.
// `include_str!` fixes the bytes at compile time — a running elaborator cannot
// reach them at all — and the digest makes shrinking the corpus a visible edit
// to a reviewed file rather than a one-line constant change.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_types::frontend_firewall::{
    FidelityAxis, FidelityManifest, FrontendLanguage, FrontendOrigin,
};

/// The pinned manifest source. Compile-time bytes: there is no runtime path
/// that writes them.
const MANIFEST_SOURCE: &str = include_str!("../fidelity-manifest.json");

/// The manifest's expected identity, pinned here as well as in the file so a
/// wholesale replacement of the file is a mismatch, not a silent substitution.
pub const MANIFEST_ID: &str = "trustjs.autoform.fidelity.v1";

/// The one admissible oracle: the tier-0 faithful interpreter. Named here so
/// swapping the oracle is a two-place edit that the manifest digest catches.
pub const ORACLE_NAME: &str = "trust-js-interp";

/// The scalar input domain's manifest key.
const SCALAR_DOMAIN: &str = "ieee754-edge-corners";
/// The array-shape input domain's manifest key (the fold lane).
const ARRAY_DOMAIN: &str = "fold-array-shapes";

/// The fidelity evidence, resolved once and shared.
///
/// Every accessor is by shared reference and every field is `Copy` or a slice,
/// so a caller can read the corpus and cannot replace it.
pub struct FidelityPin {
    manifest: FidelityManifest,
    base_samples: Vec<f64>,
    max_samples: usize,
    array_corpus: Vec<Vec<f64>>,
    fold_max_samples: usize,
}

impl FidelityPin {
    /// The manifest's verified digest, quoted in the artifact record so a
    /// reader can tell which evidence a lowering was judged by.
    #[must_use]
    pub fn digest(&self) -> &str {
        self.manifest.digest()
    }

    /// The manifest's identity.
    #[must_use]
    pub fn id(&self) -> &str {
        self.manifest.id()
    }

    /// The fixed edge-case value set, in priority order (most important first,
    /// so a reduced per-parameter list still covers the critical corners).
    #[must_use]
    pub fn base_samples(&self) -> &[f64] {
        &self.base_samples
    }

    /// The cap on total checked scalar samples.
    #[must_use]
    pub fn max_samples(&self) -> usize {
        self.max_samples
    }

    /// The array shapes the fold lane is checked over.
    #[must_use]
    pub fn array_corpus(&self) -> &[Vec<f64>] {
        &self.array_corpus
    }

    /// The cap on total checked fold samples.
    #[must_use]
    pub fn fold_max_samples(&self) -> usize {
        self.fold_max_samples
    }

    /// A [`FrontendOrigin`] for material this floor produced from `artifact`.
    ///
    /// Every proposal leaving this crate carries one, so the firewall can tell
    /// frontend-derived material from authoritative material without asking the
    /// producer to be honest about it after the fact.
    #[must_use]
    pub fn origin(&self, artifact: impl Into<String>) -> FrontendOrigin {
        FrontendOrigin::new(FrontendLanguage::JavaScript, artifact, "trust-js-autoform")
    }
}

/// The process-wide pinned evidence.
///
/// # Panics
///
/// If the checked-in manifest does not parse, does not carry
/// [`MANIFEST_ID`], or fails its own digest. That is a build-time defect in a
/// compile-time constant, not a runtime condition: continuing would mean
/// checking a lowering against an unknown corpus, which is worse than not
/// running at all.
#[must_use]
pub fn pin() -> &'static FidelityPin {
    static PIN: std::sync::OnceLock<FidelityPin> = std::sync::OnceLock::new();
    PIN.get_or_init(|| load().unwrap_or_else(|e| panic!("pinned fidelity manifest: {e}")))
}

fn load() -> Result<FidelityPin, String> {
    let manifest = FidelityManifest::parse(MANIFEST_SOURCE)?;
    if manifest.id() != MANIFEST_ID {
        return Err(format!("manifest id is {:?}, want {MANIFEST_ID:?}", manifest.id()));
    }
    if manifest.language() != FrontendLanguage::JavaScript {
        return Err(format!("manifest language is {}, want javascript", manifest.language()));
    }

    // Exactly one oracle. `sole` rather than `select` on purpose: an elaborator
    // that has no choice to make has no choice to get wrong.
    let oracle = manifest.sole(FidelityAxis::Oracle).map_err(|e| e.to_string())?;
    if oracle.name != ORACLE_NAME {
        return Err(format!("manifest oracle is {:?}, want {ORACLE_NAME:?}", oracle.name));
    }

    // No waiver is admissible at this floor. A refusal is always available and
    // always sound, so there is nothing a waiver could buy except a weaker
    // claim wearing the same words.
    if manifest.entries().iter().any(|e| e.axis == FidelityAxis::Waiver) {
        return Err("this floor admits no fidelity waivers".to_string());
    }

    let scalar = manifest
        .select(FidelityAxis::InputDomain, SCALAR_DOMAIN)
        .map_err(|e| e.to_string())?;
    let base_samples = read_samples(&scalar.payload["samples"])?;
    let max_samples = read_cap(&scalar.payload["max_samples"])?;

    let arrays = manifest
        .select(FidelityAxis::InputDomain, ARRAY_DOMAIN)
        .map_err(|e| e.to_string())?;
    let fold_max_samples = read_cap(&arrays.payload["max_samples"])?;
    let shapes = arrays.payload["shapes"]
        .as_array()
        .ok_or_else(|| format!("{ARRAY_DOMAIN}.shapes is not an array"))?;
    let array_corpus =
        shapes.iter().map(read_samples).collect::<Result<Vec<Vec<f64>>, String>>()?;

    if base_samples.is_empty() || array_corpus.is_empty() {
        return Err("an empty input domain proves nothing".to_string());
    }
    Ok(FidelityPin { manifest, base_samples, max_samples, array_corpus, fold_max_samples })
}

fn read_cap(value: &serde_json::Value) -> Result<usize, String> {
    let n = value.as_u64().ok_or_else(|| format!("cap {value} is not a non-negative integer"))?;
    let n = usize::try_from(n).map_err(|_| format!("cap {n} does not fit this target"))?;
    if n == 0 { Err("a zero sample cap checks nothing".to_string()) } else { Ok(n) }
}

/// Read a sample list. Each sample is `{ "repr": <js spelling>, "bits": <hex> }`
/// and BOTH have to agree: `bits` is the authority (it is exact for `-0`, `NaN`
/// payloads, and `f64::MIN_POSITIVE`, which a decimal spelling is not), and
/// `repr` is what a reader auditing the manifest actually reads. A hand-edit
/// that changes one and forgets the other fails closed rather than checking a
/// different value than the file appears to say.
fn read_samples(value: &serde_json::Value) -> Result<Vec<f64>, String> {
    let items = value.as_array().ok_or_else(|| format!("sample list {value} is not an array"))?;
    items
        .iter()
        .map(|item| {
            let bits_hex = item["bits"]
                .as_str()
                .ok_or_else(|| format!("sample {item} has no `bits` string"))?;
            let bits = u64::from_str_radix(bits_hex, 16)
                .map_err(|e| format!("sample bits {bits_hex:?}: {e}"))?;
            let v = f64::from_bits(bits);
            let repr = item["repr"]
                .as_str()
                .ok_or_else(|| format!("sample {item} has no `repr` string"))?;
            let canonical = trust_js_value::projection_number_repr(v);
            if repr != canonical {
                return Err(format!(
                    "sample bits {bits_hex} denote {canonical}, but the manifest reads {repr}"
                ));
            }
            Ok(v)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_pinned_manifest_loads_and_is_what_the_floor_expects() {
        let pin = pin();
        assert_eq!(pin.id(), MANIFEST_ID);
        assert_eq!(pin.max_samples(), 4096);
        assert_eq!(pin.fold_max_samples(), 4096);
        // The corner cases the whole floor rests on. If any of these ever leaves
        // the manifest, this test says so before a scorecard does.
        let samples = pin.base_samples();
        assert!(samples.iter().any(|v| v.is_nan()));
        assert!(samples.iter().any(|v| *v == f64::INFINITY));
        assert!(samples.iter().any(|v| *v == f64::NEG_INFINITY));
        assert!(samples.iter().any(|v| *v == 0.0 && v.is_sign_negative()));
        assert!(samples.iter().any(|v| *v == f64::MAX));
        assert!(samples.iter().any(|v| *v == f64::MIN_POSITIVE));
        assert_eq!(samples.len(), 18);
        // The array lane keeps the empty array, a NaN-bearing shape, and a
        // signed-zero-bearing shape.
        let arrays = pin.array_corpus();
        assert!(arrays.iter().any(std::vec::Vec::is_empty));
        assert!(arrays.iter().any(|a| a.iter().any(|v| v.is_nan())));
        assert!(arrays.iter().any(|a| a.iter().any(|v| *v == 0.0 && v.is_sign_negative())));
    }

    #[test]
    fn a_shrunk_corpus_does_not_load() {
        // The attack this pins down: publishing a smaller domain under the
        // pinned digest.
        let mut file: serde_json::Value = serde_json::from_str(MANIFEST_SOURCE).unwrap();
        let entries = file["entries"].as_array_mut().unwrap();
        for entry in entries.iter_mut() {
            if entry["name"] == SCALAR_DOMAIN {
                let samples = entry["payload"]["samples"].as_array_mut().unwrap();
                samples.truncate(2);
            }
        }
        let err = FidelityManifest::parse(&file.to_string()).unwrap_err();
        assert!(err.contains("digest drift"), "{err}");
    }

    #[test]
    fn a_sample_whose_bits_and_spelling_disagree_is_refused() {
        // `repr` is what a reviewer reads; `bits` is what gets checked. They
        // must not be able to say different things.
        let disagreeing = serde_json::json!([{ "repr": "1", "bits": "4000000000000000" }]);
        let err = read_samples(&disagreeing).unwrap_err();
        assert!(err.contains("but the manifest reads"), "{err}");
    }
}
