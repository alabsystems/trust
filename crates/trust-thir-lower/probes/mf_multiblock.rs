// Trust (lane K) — the MULTI-BLOCK storage-marker fidelity probe.
//
// Compile with the trust driver and read both channels:
//
//   trustc --edition 2021 --crate-type=lib --crate-name=kprobe \
//     -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Zdump-mir=all -Zdump-mir-dir=MIR \
//     -Ztrust-dump=ir:IR probes/mf_multiblock.rs --out-dir OUT
//
// `IR/kprobe.coverage.json`'s `derived_mir.markers_exact` is the oracle's verdict.
//
// WHAT BUILT DOES FOR A LET-FREE STRUCTURED `if` / `&&` / `||`, measured on every shape below
// (`-Zdump-mir=all`, this compiler) — identical in all of them:
//
//   HEAD:   StorageLive(c_res)                    // the condition's own result temp
//           StorageLive(t); t = copy p            // each NON-CONSTANT condition operand, in order
//           c_res = <op>(..)
//           switchInt(move c_res) -> [0: TRAMP, otherwise: THEN]
//   THEN:   StorageDead(operand temps, REVERSE)   <arm>   goto JOIN
//   TRAMP:  goto ELSE                             // EMPTY, always on the FALSE (`0`) edge
//   ELSE:   StorageDead(operand temps, REVERSE)   <arm>   goto JOIN
//   JOIN:   StorageDead(c_res)
//
// Three marker groups therefore land in blocks OTHER than the one that minted them, and the
// empty TRAMP block is load-bearing: `mir_differential::canon_markers` walks the RAW CFG with no
// goto threading, so a derived body missing that block has every fine index after it shifted.

// ---- IN the planned class (expected `markers_exact: true`) --------------------------------
#[inline(never)]
pub fn min_if(a: u32, b: u32) -> bool {
    if a == 0 { b == 1 } else { b == 2 }
}

// Short-circuit `&&` as a real CFG.
#[inline(never)]
pub fn andand(a: u32, s: u32, e: u32) -> bool {
    a >= s && a < e
}

// `||` — the producer emits the arms in the opposite target order; the correspondence still holds.
#[inline(never)]
pub fn oror(a: u32, s: u32, e: u32) -> bool {
    a >= s || a < e
}

// A cast in one arm.
#[inline(never)]
pub fn cast_if(v: u64) -> u32 {
    if v > 100 { 0 } else { v as u32 }
}

// A nested diamond in the THEN arm.
#[inline(never)]
pub fn nested_if(a: u32, b: u32) -> u32 {
    if a == 0 {
        if b == 0 { 1 } else { 2 }
    } else {
        3
    }
}

// `clean_kernel`'s `expr::bvar_in_range`, verbatim: a nested diamond in the ELSE arm, 21 markers
// over 9 built blocks — the body lane K was funded for.
#[inline(never)]
pub fn bvar_in_range(idx: u32, start: u32, end: u32) -> bool {
    if end == u32::MAX {
        idx >= start
    } else {
        idx >= start && idx < end
    }
}

// ---- OUT of the planned class, each for a named reason. NOT a to-do list. ------------------

// A checked add in one arm: the producer emits `add.overflow` + `select` + `assert`, none of
// which is in the admitted instruction set (an `Assert` splits the MIR chain mid-block, so a
// marker's canonical position `(fine block, assigns seen)` is no longer the one the plan
// computes). Built additionally leaves the `(u32, bool)` overflow pair UNMARKED, which is a
// third rule the plan does not model. Stays `markers_exact: false`.
#[inline(never)]
pub fn one_arm_temp(a: u32, b: u32) -> u32 {
    if a == 0 { b } else { b + 1 }
}

// THE LOST-FLIP TRIPWIRE, and the reason bare-param conditions are refused OUTRIGHT.
//
// `param_cond` and `match_bool` lower to BYTE-IDENTICAL trust-ir instruction streams
// (`condbr %0, bb1, bb2` / `br bb3(%1)` / `br bb3(%2)` / `ret %3`) and NEITHER opens a scope, so
// the wave-MF `scopes.is_none()` firewall does not separate them either. Their built bodies are
// opposite:
//
//   param_cond  StorageLive(_4); _4 = copy _1; switchInt(move _4) ... StorageDead(_4)
//   match_bool  PlaceMention(_1); switchInt(copy _1) ...              ZERO storage markers
//
// So `match_bool` is `markers_exact: TRUE` today and FLIPS. A plan that minted a marked temp for
// a bare-param condition would take that flip away — silently, in any corpus that happens to
// contain no such body. Requiring the condition to be a MARKED RESULT of the head block is what
// keeps `match_bool` out; it is forced by this pair, not a conservatism.
#[inline(never)]
pub fn param_cond(a: bool, x: u32, y: u32) -> u32 {
    if a { x } else { y }
}

#[inline(never)]
pub fn match_bool(c: bool, x: u32, y: u32) -> u32 {
    match c {
        true => x,
        false => y,
    }
}

// RIGHT-NESTED, in a multi-block body: `clean_kernel`'s `tc::heartbeat_profiler::types::clamp_u32`
// verbatim. Built evaluates left-to-right — `StorageLive(_3); _3 = copy _1; StorageLive(_4);
// _4 = const MAX as u64; _2 = Gt(move _3, move _4)` — so the cast's temp is LIVED AFTER the left
// operand's. The producer emits the cast as a separate SSA instruction BEFORE the comparison, and
// the shim's linear walk reproduces that order, not built's. This is wave-MF's documented
// right-nested boundary, unchanged by lane K: `clamp_u32` stays `markers_exact: false`.
#[inline(never)]
pub fn clamp_u32(value: u64) -> u32 {
    if value > u32::MAX as u64 { u32::MAX } else { value as u32 }
}

// A SOURCE `let` in a multi-block body: `clean_kernel`'s `env::native_reducers_bool_ext::nat_gcd`
// verbatim. Outside the wave-MF firewall (`func.scopes.is_some()`) before multi-block support is
// even consulted, and additionally a LOOP (a back edge), which the diamond recognizer refuses.
//
// It also carries a THIRD, independent blocker that no shim-side emission can touch: built's own
// MIR contains `bb8: { StorageDead(_13); unreachable; }`, a statically UNREACHABLE block (nothing
// branches to it) holding a storage marker, and `canon_markers` fail-closes on a marker in any
// block its walk does not reach. The one real cleanup block, `bb12: { resume; }`, is marker-free —
// so this is dead code in BUILT, not an unwind-subgraph question.
#[inline(never)]
pub fn nat_gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// A source `let` plus an early `return`: `clean_kernel`'s `env::native_reducers_sint::to_signed`
// verbatim. Built's FIRST marker is `StorageLive(_3)` on a `_3: ()` local — the value of the
// `if ... { return ...; }` STATEMENT — which has no counterpart anywhere in the instruction
// stream. Both `to_signed` bodies refuse at that line (`built mk b0.0:live s0:()`).
#[inline(never)]
pub fn to_signed(val: u64, bits: u32) -> i64 {
    if bits == 64 {
        return val as i64;
    }
    let sign_bit = 1u64 << (bits - 1);
    if val & sign_bit != 0 {
        val as i64 - (1i64 << bits)
    } else {
        val as i64
    }
}
