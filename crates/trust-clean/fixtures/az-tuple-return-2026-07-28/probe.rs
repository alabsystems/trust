// az (Dst, bool) tuple-return mono-family probe (2026-07-28, Track B).
// Re-derivation of the report §4.1(2) probe: exercises the u16→u8 and i32→i16
// az cast families at concrete types so codegen's mono inventory contains the
// `az::overflowing_cast::<Src, Dst>` instances the crate dump lacks (W16).
// az's fns are all `#[inline]`, so a plain call at -O is inlined OUT of the
// mono graph; fn-pointer REIFICATION forces each instance to exist as a mono
// item regardless of inlining. Observational only — the mono hook grants no
// proof authority.
#![allow(dead_code)]

fn main() {
    // The free-fn mono instances the impl bodies delegate to (report §4.1 cause a):
    let f1 = az::overflowing_cast::<u16, u8> as fn(u16) -> (u8, bool);
    let f2 = az::overflowing_cast::<i32, i16> as fn(i32) -> (i16, bool);
    let f3 = az::wrapping_cast::<u16, u8> as fn(u16) -> u8;
    let f4 = az::wrapping_cast::<i32, i16> as fn(i32) -> i16;
    let f5 = az::checked_cast::<u16, u8> as fn(u16) -> Option<u8>;
    let f6 = az::checked_cast::<i32, i16> as fn(i32) -> Option<i16>;
    let v = (
        f1(1),
        f2(70_000),
        f3(2),
        f4(3),
        f5(4),
        f6(5),
    );
    core::hint::black_box(v);
}
