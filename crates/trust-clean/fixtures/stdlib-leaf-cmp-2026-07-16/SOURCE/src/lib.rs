//! Intent fixture for the cmp min/max/clamp stdlib leaf harvest (P1 family).
//!
//! Two sections, both compiled by the exactly hashed stage1 trustc in TOOLCHAIN.sha256:
//!
//!  A. INTENT WRAPPERS — call the real `core::cmp` min/max/clamp fns at concrete
//!     integer widths. A probe crate records only its OWN bodies, so each wrapper
//!     dumps as a single opaque `Call` terminator to the core callee (the callee
//!     stays opaque). This is WHY the certified family must be sliced from a
//!     `library/core` dump (../dumps/), and WHY the only cmp min/max/clamp bodies
//!     present there are the GENERIC ones (`Self`/`T` param): integer `min`/`max`
//!     are un-overridden default methods, and the overridden per-int `clamp`
//!     parent body is elided by its `const_assert!` `const {}` (only `do_panic`
//!     leaves survive) — see PROVENANCE.md.
//!
//!  B. SELECT-LANE-REACH CONTROLS — hand-inlined, MONOMORPHIC, primitive-compare
//!     reimplementations of the exact same select shapes the core generic bodies
//!     use (`Ord::min` = `if other < self { other } else { self }`, etc.). These
//!     dump as concrete-int local bodies and are run through the SAME gate to
//!     show the guarded/select lane REACHES the concrete-int cmp shape — proving
//!     the wall blocking the real stdlib bodies is monomorphization / extraction,
//!     NOT recognizer capability. They are controls, NOT certified stdlib.
//!
//! Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
#![allow(clippy::all)]

// ---- A. intent wrappers (resolve to the generic core cmp bodies) ----
pub fn w_ord_min_i32(a: i32, b: i32) -> i32 { core::cmp::Ord::min(a, b) }
pub fn w_ord_max_i32(a: i32, b: i32) -> i32 { core::cmp::Ord::max(a, b) }
pub fn w_cmp_min_i32(a: i32, b: i32) -> i32 { core::cmp::min(a, b) }
pub fn w_cmp_max_i32(a: i32, b: i32) -> i32 { core::cmp::max(a, b) }
pub fn w_clamp_i32(x: i32, lo: i32, hi: i32) -> i32 { x.clamp(lo, hi) }
pub fn w_min_u8(a: u8, b: u8) -> u8 { a.min(b) }
pub fn w_max_u8(a: u8, b: u8) -> u8 { a.max(b) }

// ---- B. select-lane-reach controls (concrete-int, primitive `Lt`/`Gt`) ----
// min: mirror `Ord::min(self=a, other=b) = if other < self { other } else { self }`
pub fn ctl_min_i32(a: i32, b: i32) -> i32 { if b < a { b } else { a } }
// max: mirror `Ord::max(self=a, other=b) = if other < self { self } else { other }`
pub fn ctl_max_i32(a: i32, b: i32) -> i32 { if b < a { a } else { b } }
// clamp: mirror concrete `clamp` (minus the min<=max assert): two nested selects
pub fn ctl_clamp_i32(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo { lo } else if x > hi { hi } else { x }
}
pub fn ctl_min_u8(a: u8, b: u8) -> u8 { if b < a { b } else { a } }
pub fn ctl_max_u8(a: u8, b: u8) -> u8 { if b < a { a } else { b } }
