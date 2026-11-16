// Trust: real source for checked enum-helper return inference.
// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.
// `coverage_supports` retains the original trust-ir-laws decision table.

#[derive(Clone, Copy)]
pub enum CoverageBound {
    Unbounded,
    UnwindBounded { depth: u64 },
    ModelBounded { size: u64 },
    Unrecorded,
}

pub fn coverage_supports(far: CoverageBound, needs: CoverageBound) -> bool {
    match (far, needs) {
        (_, CoverageBound::Unrecorded) => true,
        (CoverageBound::Unbounded, CoverageBound::Unbounded) => true,
        (CoverageBound::Unbounded, CoverageBound::UnwindBounded { .. }) => true,
        (CoverageBound::Unbounded, CoverageBound::ModelBounded { .. }) => true,
        (
            CoverageBound::UnwindBounded { depth: have },
            CoverageBound::UnwindBounded { depth: need },
        ) => have >= need,
        (
            CoverageBound::ModelBounded { size: have },
            CoverageBound::ModelBounded { size: need },
        ) => have >= need,
        _ => false,
    }
}

#[derive(Clone, Copy)]
#[repr(i8)]
pub enum SignedTag {
    Low = -3,
    High = 7,
}

pub fn signed_tag_is_low(tag: SignedTag) -> bool {
    match tag {
        SignedTag::Low => true,
        SignedTag::High => false,
    }
}

pub fn signed_tag_forward(tag: SignedTag) -> bool {
    signed_tag_is_low(tag)
}

pub fn coverage_reflexive(depth: u64) -> bool {
    coverage_supports(
        CoverageBound::UnwindBounded { depth },
        CoverageBound::UnwindBounded { depth },
    )
}

pub fn coverage_wrong(depth: u64) -> bool {
    coverage_supports(
        CoverageBound::UnwindBounded { depth },
        CoverageBound::ModelBounded { size: depth },
    )
}

pub fn coverage_constants() -> bool {
    coverage_supports(CoverageBound::Unbounded, CoverageBound::Unbounded)
}

pub fn coverage_bounded_against_unbounded(depth: u64) -> bool {
    coverage_supports(CoverageBound::UnwindBounded { depth }, CoverageBound::Unbounded)
}

pub fn coverage_zero_against_unbounded() -> bool {
    coverage_supports(CoverageBound::UnwindBounded { depth: 0 }, CoverageBound::Unbounded)
}

pub fn coverage_large_against_unbounded() -> bool {
    coverage_supports(CoverageBound::UnwindBounded { depth: 16 }, CoverageBound::Unbounded)
}

pub fn coverage_unbounded_against_bounded(depth: u64) -> bool {
    coverage_supports(CoverageBound::Unbounded, CoverageBound::UnwindBounded { depth })
}

pub fn coverage_depths(have: u64, need: u64) -> bool {
    coverage_supports(
        CoverageBound::UnwindBounded { depth: have },
        CoverageBound::UnwindBounded { depth: need },
    )
}

pub fn coverage_depths_reversed(have: u64, need: u64) -> bool {
    coverage_supports(
        CoverageBound::UnwindBounded { depth: need },
        CoverageBound::UnwindBounded { depth: have },
    )
}
