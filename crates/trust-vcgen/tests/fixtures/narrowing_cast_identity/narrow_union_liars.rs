// UNION-SIBLING-WRITE-1 (wave-24 review of VC-NARROW-CAST-FALSE-REFUTE-1, 2026-10-12):
// the fields of a union OVERLAP, so a write to one rewrites its siblings. The place-name
// algebra took `u.0` and `u.1` for disjoint storage: a fact about `u.0` (the narrowing
// cast's identity `x <= 255 => u.0 == x`, or a widening cast's `u.0 == x`) survived a
// write of `u.1` and bounded the value the sibling write replaced. Every `u*` / `uw*`
// function below panics for some input (stock rustc 1.97.1): `u_dst_add(0)`,
// `u_dst_idx(0)`, `u_src_idx(200)`, `uw_dst_add(0)`, `uw_src_add(200)`. `u_dst_add_ctl`
// is correct on every input. On the stage 1 of 51eac007f3, advisory, `u_dst_add`'s
// overflow row was kernel-certified and its check elided (the binary printed 71); the
// widening twins `uw_*` were elided the same way before that commit too.
#![allow(dead_code)]

pub union V { pub a: u8, pub b: i8 }
pub union U { pub a: u32, pub b: f32 }
pub union V2 { pub a: u64, pub b: i64 }

// Destination side: `u.a` is the narrowing cast's destination; `u.b = -56` makes it 200.
pub fn u_dst_add(x: u32) -> u8 {
    let mut u = V { a: 0 };
    u.a = x as u8;
    u.b = -56;
    if x < 0x80 { (unsafe { u.a }) + 0x7f } else { 0 }
}
pub fn u_dst_idx(x: u32) -> u8 {
    let arr = [0u8; 0x80];
    let mut u = V { a: 0 };
    u.a = x as u8;
    u.b = -56;
    if x < 0x80 { arr[unsafe { u.a } as usize] } else { 0 }
}
// Source side: the guard reads `u.a` after the sibling write replaced it.
pub fn u_src_idx(x: u32) -> u8 {
    let arr = [0u8; 0x80];
    let mut u = U { a: x };
    let b = unsafe { u.a } as u8;
    u.b = f32::from_bits(5);
    if unsafe { u.a } < 0x80 { arr[b as usize] } else { 0 }
}
// The widening twins: `dest == src` of a widening cast, the same staleness.
pub fn uw_dst_add(x: u32) -> u64 {
    let mut u = V2 { a: 0 };
    u.a = x as u64;
    u.b = -1;
    if x < 0x80 { (unsafe { u.a }) + 0x7f } else { 0 }
}
pub fn uw_src_add(x: u32) -> u64 {
    let mut u = U { a: x };
    let b = unsafe { u.a } as u64;
    u.b = f32::from_bits(5);
    if unsafe { u.a } < 0x80 { b + (u64::MAX - 0x7f) } else { 0 }
}
// Control: no sibling write; the guard bounds `u.a`.
pub fn u_dst_add_ctl(x: u32) -> u8 {
    let mut u = V { a: 0 };
    u.a = x as u8;
    if x < 0x80 { (unsafe { u.a }) + 0x7f } else { 0 }
}
