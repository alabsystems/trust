//! Trust: pure comparison of rustc-observed source ABI facts with emitted types.
//! This checks transport only; it grants no source license or proof grade.

use trust_ir::{ClosureTyId, Module, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Scalar {
    Int { bits: u32, signed: bool },
    Pointer,
    Float { bits: u32 },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct RegisterUse {
    pub gpr: usize,
    pub fp: usize,
}

impl RegisterUse {
    pub(super) fn integer(words: usize) -> Self { Self { gpr: words, fp: 0 } }
    pub(super) fn add(&mut self, other: Self) {
        self.gpr += other.gpr;
        self.fp += other.fp;
    }
}

impl Scalar {
    pub(super) fn bytes(self) -> u64 {
        match self {
            Self::Int { bits, .. } | Self::Float { bits } => u64::from(bits / 8),
            Self::Pointer => 8,
        }
    }

    pub(super) fn agrees(self, ty: &Ty) -> bool {
        match (self, ty) {
            (Self::Pointer, Ty::Ptr) => true,
            (Self::Float { bits: 32 }, Ty::F32) | (Self::Float { bits: 64 }, Ty::F64) => true,
            (Self::Int { bits, signed }, ty) => {
                let observed = match ty {
                    Ty::I8 => (8, true),
                    Ty::I16 => (16, true),
                    Ty::I32 => (32, true),
                    Ty::I64 | Ty::Isize => (64, true),
                    Ty::U8 => (8, false),
                    Ty::U16 => (16, false),
                    Ty::U32 | Ty::Char => (32, false),
                    Ty::U64 | Ty::Usize => (64, false),
                    _ => return false,
                };
                observed == (bits, signed)
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Extension {
    None,
    Zext,
    Sext,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Lane {
    pub scalar: Scalar,
    pub extension: Extension,
    pub inreg: bool,
}

#[derive(Clone, Debug)]
pub(super) enum Transport {
    Ignore,
    Direct(Lane),
    Pair([Lane; 2]),
}

#[derive(Clone, Debug)]
pub(super) struct ObservedFrame {
    pub size: u64,
    pub align: u64,
    pub offsets: Vec<u64>,
    pub captures: Vec<Scalar>,
}

/// Actual scalar transport, including Darwin C unsigned8/16 zero extension
/// on both arguments and results. P retains the declared width and extension;
/// the independent output gate must check the full writer-owned contract.
pub(super) fn scalar_transport(ty: &Ty, lane: Lane, apple_c: bool) -> Result<RegisterUse, String> {
    if lane.inreg || !lane.scalar.agrees(ty) {
        return Err("source scalar type or InReg placement disagrees with emitted ABI".into());
    }
    if matches!(lane.scalar, Scalar::Float { .. }) {
        return if lane.extension == Extension::None {
            Ok(RegisterUse { gpr: 0, fp: 1 })
        } else { Err("floating-point source ABI cannot carry integer extension attributes".into()) };
    }
    match lane.extension {
        Extension::None if apple_c && matches!(ty, Ty::I8 | Ty::I16) => {
            Err("Darwin C signed scalar lost its actual Sext contract".into())
        }
        Extension::None => Ok(RegisterUse::integer(1)),
        Extension::Zext if apple_c && matches!(ty, Ty::U8 | Ty::U16) => Ok(RegisterUse::integer(1)),
        Extension::Sext if apple_c && matches!(ty, Ty::I8 | Ty::I16) => Ok(RegisterUse::integer(1)),
        _ => Err("source scalar extension is not represented by this native ABI lane".into()),
    }
}

/// The native AArch64 aggregate carrier is one or two 8-byte words. Rustc's
/// ScalarPair can differ: e.g. two u32 fields occupy two Rust registers but
/// one native aggregate word. Refuse that drift, do not flatten by guesswork.
pub(super) fn closure_transport(
    module: &Module,
    id: ClosureTyId,
    observed: &ObservedFrame,
    transport: &Transport,
) -> Result<usize, String> {
    if observed.captures.iter().any(|scalar| matches!(scalar, Scalar::Float { .. })) {
        return Err("source FP captures require a separately checked aggregate ABI".into());
    }
    module.validate_closure_layouts().map_err(|e| format!("source closure layout: {e}"))?;
    let closure = module.closure_type(id).ok_or("source closure type is missing")?;
    let layout = module
        .closure_layout_descriptor(id)
        .map_err(|e| format!("source closure descriptor: {e}"))?
        .ok_or("source closure has no observed frame")?;
    if layout.size != observed.size
        || layout.align != observed.align
        || layout.capture_offsets != observed.offsets
        || closure.captures.len() != observed.captures.len()
        || observed.offsets.len() != observed.captures.len()
        || !observed.captures.iter().zip(&closure.captures).all(|(a, b)| a.agrees(b))
    {
        return Err("emitted closure frame/captures disagree with rustc's exact environment".into());
    }
    // The native carrier's totals are derived in declaration order. Declared
    // offsets remain source-observed; the backend uses those physical offsets.
    let mut size = 0u64;
    let mut align = 1u64;
    for scalar in &observed.captures {
        let field = scalar.bytes();
        if field == 0 || field > 8 || !field.is_power_of_two() {
            return Err("source capture has no audited native scalar carrier".into());
        }
        align = align.max(field);
        size = size.div_ceil(field) * field + field;
    }
    size = size.div_ceil(align) * align;
    // Trust: Ignore is valid only for the exact empty, align-one source frame.
    // A nonempty environment never inherits this physical omission.
    if observed.captures.is_empty() {
        return if size == observed.size && align == observed.align
            && matches!(transport, Transport::Ignore)
        {
            Ok(0)
        } else {
            Err("empty source environment does not have its exact ignored ABI".into())
        };
    }
    if size != observed.size || align != observed.align {
        return Err("source environment totals disagree with the native aggregate carrier".into());
    }
    let plain = |lane: &Lane| lane.extension == Extension::None && !lane.inreg;
    match transport {
        Transport::Direct(lane)
            if observed.captures.len() == 1
                && size <= 8
                && observed.offsets == [0]
                && plain(lane)
                && lane.scalar == observed.captures[0] =>
        {
            Ok(1)
        }
        Transport::Pair(lanes)
            if observed.captures.len() == 2
                && size > 8
                && size <= 16
                && lanes.iter().all(plain) =>
        {
            let mut physical = [0, 1];
            physical.sort_by_key(|&i| observed.offsets[i]);
            if observed.offsets[physical[0]] != 0
                || observed.offsets[physical[1]] != 8
                || lanes[0].scalar != observed.captures[physical[0]]
                || lanes[1].scalar != observed.captures[physical[1]]
            {
                return Err(
                    "rustc closure pair does not match the two native argument words".into()
                );
            }
            Ok(2)
        }
        _ => Err("source closure pass mode disagrees with the native aggregate carrier".into()),
    }
}

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(test)]
#[path = "agreement/tests.rs"]
mod tests;
