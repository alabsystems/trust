// KNOWN SILENT FALSE-ACCEPT (found 2026-07-10) — iterator sum/product overflow.
//
// `(1..=n).product::<i32>()` overflows for n >= 13 (13! = 6_227_020_800 >
// i32::MAX), so in debug it panics "attempt to multiply with overflow". stock
// rustc compiles it (valid Rust); trustc exits 0 with ZERO obligations and ZERO
// output — a SILENT accept of a panicking program.
//
// Root cause: the multiply happens INSIDE the library `Iterator::product` impl,
// so no caller-visible `Rvalue::BinaryOp` exists. trust-vcgen `overflow_arith_call`
// (generate.rs:15542) DELIBERATELY excludes sum/product ("modeling them soundly
// needs an accumulation invariant we do not have; flagging them unconditionally
// would false-FAIL ordinary bounded sums"). The trust-ir bridge
// (`closure_driving_consumer_call`, lower.rs:10570) ALREADY mints a sound UNKNOWN
// `PanicFreedom` obligation for it — but that lives only in the non-decisive
// trust-ir SHADOW spine (a Pillar-4 gap: the universal IR's sound obligation does
// not reach the verdict).
//
// POLICY DECIDED (owner, 2026-07-10): RUNTIME-CHECKED DEMOTION. FIX IMPLEMENTED in
// `crates/` (trust-vcgen `iterator_integer_fold_call` mints an
// `UnsupportedMir { kind: "iterator-fold-overflow" }` obligation → Unknown →
// runtime-checked in the default lane, like the `m[&k]` map-index backstop). It is
// HONESTLY accounted and delegated to the runtime overflow check, never silently
// verified, never false-FAILED. Unit-pinned by
// `crates/trust-vcgen/tests/iterator_fold_overflow.rs`.
//
// It stays in pending/. The obligation is an UNMARKED UnsupportedMir (no
// `panic-freedom-unverified` marker), so per the current-source rc doctrine
// (non-Failed → "reported, not errors") it should land runtime-checked at rc 0
// (option C). BUT this is E2E-UNVERIFIED: the available binary (84e63de6c1)
// predates that doctrine and gives rc 1 for sibling runtime-checked cases
// (`m[&k]`, `slice::repeat`), so it cannot predict the rebuilt rc. The fix is
// SOUND EITHER WAY — whether it demotes (rc 0) or rejects (rc 1), the silent
// 0-obligation accept is closed and it is never a false-accept; only the drop-in
// (Pillar-5) outcome is uncertain until a rebuild. (An earlier version of this
// note claimed rc 0 "verified on the live binary" — that was a pipe-`$?` misread
// of grep's exit, not trustc's.) E2E blocked on the 1.98/1.99 stage0.
#![crate_type = "lib"]

pub fn factorial_like(n: i32) -> i32 {
    // Overflows i32 for n >= 13 → debug panic "attempt to multiply with overflow".
    (1..=n).product()
}

pub fn trigger() -> i32 {
    factorial_like(13)
}
