#![feature(pattern_types, pattern_type_macro)]
#![allow(dead_code)]
use std::pat::pattern_type;

// fix11 (L2): a local struct whose field type names a constant whose whole CTFE closure is leaf.
// `core`'s shapes: `niche_types::NonZeroU32Inner` (an open pattern range, whose end is the
// anonymous constant `<u32 as RangePattern>::MAX`) and `DecimalSeq` (`[u8; Self::MAX_DIGITS]`).
pub struct NzInner(pattern_type!(u32 is 1..));
pub struct Nz { v: NzInner, tag: u8 }
pub struct DSeq { num_digits: usize, digits: [u8; Self::MAX_DIGITS] }
impl DSeq { pub const MAX_DIGITS: usize = 768; }
const N: usize = 3;
pub struct Arr { a: [u16; N * 2], b: u8 }
pub fn nz(x: Nz) -> Nz { x }
pub fn dseq_len(d: DSeq) -> usize { d.num_digits }
pub fn arr(x: Arr) -> Arr { x }

// `TypeId`'s shape: the one call a leaf constant may make, `size_of` over a pointer to `()`.
pub struct TypeIdLike { d: [*const (); 16 / std::mem::size_of::<*const ()>()], b: u8 }
pub fn type_id_like(x: TypeIdLike) -> TypeIdLike { x }

// Decline controls: the constant's evaluation would run a body that is not a leaf.
const fn four() -> usize { 4 }
pub struct Call { a: [u8; four()], b: u8 }
pub fn call(x: Call) -> Call { x }
pub struct SizeOfAdt { a: [u8; std::mem::size_of::<Arr>()], b: u8 }
pub fn size_of_adt(x: SizeOfAdt) -> SizeOfAdt { x }

// The cycle shape: a const fn that sizes a struct and names it. Evaluating `sized()` from
// inside `mir_built(sized)` would demand `mir_built(sized)` again (E0391). The funnel must
// decline it, and the compile itself is the check.
pub struct Cyc { a: [u8; sized()], b: u8 }
pub const fn sized() -> usize {
    let _r: Option<&Cyc> = None;
    4
}
pub fn cyc(x: Cyc) -> Cyc { x }
