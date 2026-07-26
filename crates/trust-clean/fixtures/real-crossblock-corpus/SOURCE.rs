// xblock_src — reconstructed generating source for
// fixtures/real-crossblock-corpus/count_ret.json (commit a4ea5c0876).
// The REAL cross-block copy-back loop: the counter commit i := Move(_t.0)
// lands in bb3 while the Goto-header back-edge is in bb4, because the
// trailing accumulator statement w = w.wrapping_mul(3) sits between the
// increment and the back-edge. Recognized by resolve_guard_counter_update.
//
// Dump with:
//   trustc --crate-type lib \
//     -Ztrust-dump=mir-only:<dir> -Ztrust-policy=advisory <this file>
//
// NOTE ON RECONSTRUCTION: the original xblock_src.rs was a scratch file that
// was never checked in. The function text (lines 19-27) is exactly pinned by
// the spans + MIR embedded in the checked-in count_ret.json; this header
// (lines 1-18) is NOT pinned by the dump and is authored for the
// reconstruction. The re-dump byte-comparison validates the fn text.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#![allow(unused)]
pub fn count_ret(n: u32) -> u32 {
    let mut i: u32 = 0;
    let mut w: u32 = 7;
    while i < n {
        i += 1;
        w = w.wrapping_mul(3);
    }
    i
}
