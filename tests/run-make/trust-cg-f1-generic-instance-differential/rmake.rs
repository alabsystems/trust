//! Trust (owner ruling D17's compensating control; step 2 increment 3): a TEST-ORACLE
//! DIFFERENTIAL over a generic-instance corpus.
//!
//! D17 admits a GENERIC instance body on the instance lane with no per-instance MIR seam
//! differential and moves that cross-check to "a test-oracle differential over a
//! generic-instance corpus". This is it. Every subject is compiled twice from the same source:
//!
//! * on the LLVM lane (the default backend, `-Ztrust-verify=off`) — the oracle;
//! * on F1 (`-Zcodegen-backend=trust-cg -Ztrust-cg-frontend=trust-ir`, the DEFAULT strict
//!   proven-output gate);
//!
//! at BOTH `-Copt-level=0` (overflow checks on, so any arithmetic in a generic body is an
//! `Assert` F1 refuses `[unfaithful-panic]`) and `-Copt-level=2` (overflow checks off, where D17
//! admits and ships ARITHMETIC generic bodies, and a generic without `#[inline(never)]` is
//! spliced only as an inlined body). Each exported `extern "C" fn tN(u64) -> u64` is then RUN on
//! edge inputs (each call in a forked child, so a trap is reported as a signal instead of killing
//! the run) and the two lanes' outputs must be byte-for-byte EQUAL; each compared F1 build must
//! also disclose at least one spliced GENERIC instance in its coverage artifact, so a subject
//! that stopped instantiating a generic cannot silently become a monomorphic differential. Rows
//! where F1 must REFUSE are part of the corpus: each names the class and the reason it must
//! print, and must write no rlib.
//!
//! The corpus is seeded from the increment's review probes (widths `u8..i64`, trait dispatch,
//! generic -> monomorphic -> generic chains, an associated-type width, two instances of one body,
//! a generic `extern "C"` callee, wrapping arithmetic through a trait-provided constant, `i8`
//! negation, `u32` subtraction, shifts) plus a cross-crate row: an F1-built rlib whose narrow,
//! trait-dispatched and sign-dependent generic instances an LLVM-built binary links to and calls
//! directly (share-generics), each symbol checked defined in the F1 object and undefined in the
//! LLVM one.
//!
//! Trust (step 2 increment 5, sub-step 5.4.2; plan critique M3): THE COMPILER-LANE LEG. Every
//! subject is compiled a third time on F1's opt-in compiler lane (`-Ztrust-cg-f1-backend=compiler`:
//! one codegen module per crate, trust-cg's `Compiler::compile`, real calls, shipped only through
//! the call-event gate) under the same strict default (D17). Each row either equals the LLVM lane
//! on every input or is refused with a named class, and every row whose outcome DIFFERS from the
//! default lane's is listed in `COMPILER_LANE_DIFFERS` with its reason. A subject that ships must
//! still disclose its spliced GENERIC instance (D17's per-function disclosure).

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::{File, Object, ObjectSymbol};
use run_make_support::{bin_name, cc, rfs, run, rust_lib_name, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

/// Edge inputs: every width boundary a `u8..u64` / `i8..i64` instance can observe.
const INPUTS: &[&str] = &[
    "0",
    "1",
    "2",
    "7",
    "127",
    "128",
    "255",
    "256",
    "65535",
    "65536",
    "2147483647",
    "2147483648",
    "4294967295",
    "4294967296",
    "9223372036854775807",
    "9223372036854775808",
    "18446744073709551615",
];

#[derive(Clone, Copy)]
enum Expect {
    /// F1 compiles it under the strict gate and every output equals the LLVM lane's.
    Same,
    /// F1 must refuse it; every needle must appear in its stderr.
    Refused(&'static [&'static str]),
}

struct Subject {
    name: &'static str,
    source: &'static str,
    /// At `-Copt-level=0` (overflow checks on).
    o0: Expect,
    /// At `-Copt-level=2` (overflow checks off).
    o2: Expect,
}

const PANIC: Expect = Expect::Refused(&["[unfaithful-panic]"]);

const CORPUS: &[Subject] = &[
    Subject {
        name: "ident_widths",
        source: r#"#[inline(never)] fn id<T>(x: T) -> T { x }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { id::<u8>(x as u8) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { id::<u16>(x as u16) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t2(x: u64) -> u64 { id::<u32>(x as u32) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t3(x: u64) -> u64 { id::<u64>(x) }
#[unsafe(no_mangle)] pub extern "C" fn t4(x: u64) -> u64 { id::<i64>(x as i64) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t5(x: u64) -> u64 { id::<i8>(x as i8) as i64 as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t6(x: u64) -> u64 { id::<i16>(x as i16) as i64 as u64 }
"#,
        o0: Expect::Same,
        o2: Expect::Same,
    },
    Subject {
        name: "trait_widths_xor",
        source: r#"trait W: Copy { fn w(self) -> u64; fn inc(self) -> Self; }
impl W for u8 { #[inline(never)] fn w(self) -> u64 { self as u64 } #[inline(never)] fn inc(self) -> u8 { self ^ 0x81 } }
impl W for u16 { #[inline(never)] fn w(self) -> u64 { self as u64 } #[inline(never)] fn inc(self) -> u16 { self ^ 0x8001 } }
impl W for u32 { #[inline(never)] fn w(self) -> u64 { self as u64 } #[inline(never)] fn inc(self) -> u32 { self ^ 0x8000_0001 } }
impl W for u64 { #[inline(never)] fn w(self) -> u64 { self } #[inline(never)] fn inc(self) -> u64 { self ^ 0x8000_0000_0000_0000 } }
#[inline(never)] fn go<T: W>(x: T) -> u64 { x.inc().w() }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { go::<u8>(x as u8) }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { go::<u16>(x as u16) }
#[unsafe(no_mangle)] pub extern "C" fn t2(x: u64) -> u64 { go::<u32>(x as u32) }
#[unsafe(no_mangle)] pub extern "C" fn t3(x: u64) -> u64 { go::<u64>(x) }
#[unsafe(no_mangle)] pub extern "C" fn t4(x: u64) -> u64 { go::<u8>(x as u8) ^ go::<u16>(x as u16) ^ go::<u32>(x as u32) ^ go::<u64>(x) }
"#,
        o0: Expect::Same,
        o2: Expect::Same,
    },
    Subject {
        name: "g_m_g_chain",
        source: r#"#[inline(never)] fn g2<T>(x: u64) -> u64 { x ^ 0x55 }
#[inline(never)] fn m1(x: u64) -> u64 { g2::<u32>(x) ^ 0x300 }
#[inline(never)] fn g1<T>(x: u64) -> u64 { m1(x) ^ 0x7000 }
#[inline(never)] fn g<T>(x: u64) -> u64 { x ^ 0x10 }
#[inline(never)] fn m2(x: u64) -> u64 { g::<u8>(x) ^ 0x20 }
#[inline(never)] fn mm(x: u64) -> u64 { m2(x) ^ 0x40 }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { g1::<u8>(x) }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { mm(x) ^ 0x80 }
#[unsafe(no_mangle)] pub extern "C" fn t2(x: u64) -> u64 { m2(x) ^ g::<u16>(x) }
"#,
        o0: Expect::Same,
        o2: Expect::Same,
    },
    Subject {
        name: "assoc_type_width",
        source: r#"trait Wid { fn w(self) -> u64; }
impl Wid for u8 { #[inline(never)] fn w(self) -> u64 { self as u64 } }
impl Wid for u32 { #[inline(never)] fn w(self) -> u64 { self as u64 } }
trait HasOut { type Out: Wid; fn mk(x: u64) -> Self::Out; }
impl HasOut for u8 { type Out = u8; #[inline(never)] fn mk(x: u64) -> u8 { x as u8 } }
impl HasOut for u16 { type Out = u32; #[inline(never)] fn mk(x: u64) -> u32 { x as u32 } }
#[inline(never)] fn g<T: HasOut>(x: u64) -> u64 { T::mk(x).w() }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { g::<u8>(x) }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { g::<u16>(x) }
"#,
        o0: Expect::Same,
        o2: Expect::Same,
    },
    Subject {
        name: "two_instances_one_body",
        source: r#"pub trait Tag { fn tag() -> u64; }
impl Tag for u8 { #[inline(never)] fn tag() -> u64 { 8 } }
impl Tag for u16 { #[inline(never)] fn tag() -> u64 { 16 } }
#[inline(never)] fn pick<T: Tag>(x: u64) -> u64 { x ^ T::tag() }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { pick::<u8>(x) }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { pick::<u16>(x) }
#[unsafe(no_mangle)] pub extern "C" fn t2(x: u64) -> u64 { pick::<u8>(x) ^ pick::<u16>(x) }
"#,
        o0: Expect::Same,
        o2: Expect::Same,
    },
    Subject {
        name: "extern_c_generic",
        source: r#"#[inline(never)] extern "C" fn cg<T>(x: u64) -> u64 { x ^ 0x45 }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { cg::<u8>(x) }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { cg::<u8>(x) ^ cg::<u16>(x) }
"#,
        o0: Expect::Same,
        o2: Expect::Same,
    },
    Subject {
        name: "signedness_via_trait",
        source: r#"trait Lt: Copy { fn lt(a: Self, b: Self) -> bool; }
impl Lt for i64 { #[inline(never)] fn lt(a: i64, b: i64) -> bool { a < b } }
impl Lt for u64 { #[inline(never)] fn lt(a: u64, b: u64) -> bool { a < b } }
#[inline(never)] fn cmp<T: Lt>(a: T, b: T) -> u64 { if T::lt(a, b) { 1 } else { 0 } }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { cmp::<i64>(x as i64, 5) }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { cmp::<u64>(x, 5) }
"#,
        o0: Expect::Same,
        o2: Expect::Same,
    },
    // ---- rows F1 must REFUSE -------------------------------------------------------------
    Subject {
        name: "overflow_check_in_generic",
        source: r#"#[inline(never)] fn inc<T>(x: u64) -> u64 { x + 1 }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { inc::<u8>(x) }
"#,
        o0: PANIC,
        o2: Expect::Same,
    },
    Subject {
        name: "shift_check_in_generic",
        source: r#"#[inline(never)] fn sh<T>(x: u64) -> u64 { x << 1 }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { sh::<u8>(x) }
"#,
        o0: PANIC,
        o2: Expect::Same,
    },
    Subject {
        name: "self_recursion",
        source: r#"#[inline(never)] fn r<T>(n: u64) -> u64 { if n == 0 { 0 } else { r::<T>(n ^ 1) ^ n } }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { r::<u8>(x & 1) }
"#,
        o0: Expect::Refused(&["[instance-assembly]", "calls itself"]),
        o2: Expect::Refused(&["[instance-assembly]", "calls itself"]),
    },
    Subject {
        name: "closure_in_generic",
        source: r#"#[inline(never)] fn g<T>(x: u64) -> u64 { let c = |y: u64| y ^ 1; c(x) }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { g::<u8>(x) }
"#,
        o0: Expect::Refused(&["[instance-assembly]", "is an unresolved callee"]),
        o2: Expect::Refused(&["[instance-assembly]", "is an unresolved callee"]),
    },
    Subject {
        name: "drop_param_generic",
        source: r#"pub struct U;
impl Drop for U { #[inline(never)] fn drop(&mut self) {} }
#[inline(never)] fn consume<T>(_t: T, x: u64) -> u64 { x ^ 1 }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { consume::<U>(U, x) }
"#,
        o0: Expect::Refused(&["[elided-drop]"]),
        o2: Expect::Refused(&["[elided-drop]"]),
    },
    // ---- ARITHMETIC generic bodies: refused at -O0 (checked), shipped and compared at -O2 ----
    Subject {
        name: "wrapping_add_through_trait_constant",
        source: r#"trait K { fn k() -> u8; }
impl K for u8 { #[inline(never)] fn k() -> u8 { 200 } }
impl K for u16 { #[inline(never)] fn k() -> u8 { 100 } }
trait K16 { fn k16() -> u16; }
impl K16 for u8 { #[inline(never)] fn k16() -> u16 { 60000 } }
#[inline(never)] fn addk<T: K>(x: u8) -> u8 { x + T::k() }
#[inline(never)] fn addk16<T: K16>(x: u16) -> u16 { x + T::k16() }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { addk::<u8>(x as u8) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { addk::<u16>(x as u8) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t2(x: u64) -> u64 { addk16::<u8>(x as u16) as u64 }
"#,
        o0: PANIC,
        o2: Expect::Same,
    },
    Subject {
        name: "i8_negation",
        source: r#"#[inline(never)] fn neg<T>(x: i8) -> i8 { -x }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { neg::<u8>(x as i8) as i64 as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { neg::<u16>(x as i8) as u8 as u64 }
"#,
        o0: PANIC,
        o2: Expect::Same,
    },
    Subject {
        name: "u32_subtraction",
        source: r#"#[inline(never)] fn sub<T>(a: u32, b: u32) -> u32 { a - b }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { sub::<u8>(x as u32, 7) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { sub::<u16>(5, x as u32) as u64 }
"#,
        o0: PANIC,
        o2: Expect::Same,
    },
    // No `#[inline(never)]`: at -O2 the MIR inliner removes `plain::<u8>` from the inventory, so
    // F1 splices it ONLY as an inlined body (see `the_inlined_generic_has_no_own_symbol`).
    // Variable shift AMOUNTS: at -O2 every one is masked by Rust's semantics (`n & 7`, `n & 31`,
    // `n & 63`) and compared. At -O0 each carries a `ShiftInRange` check.
    //
    // Trust (2026-10-03, shift-count mask): the NARROW row was refused at -O2 with "a narrow shift
    // whose amount the IR does not prove in range" — the producer emitted the bare trust-ir
    // shift, which is undefined at or above BITS, so the gate had no IR semantics to render. The
    // producer now emits Rust's count mask (`emit_masked_shift_count`: `amount & (BITS - 1)`),
    // the in-range side condition holds by construction, and the row is compared like the wide
    // ones. MEASURED (2026-10-04, stage 1 with trust-cg): the mask alone was not enough — the
    // gate discharged the `amount < 8` side condition with ay only, graded `shl` [VALIDATED],
    // and the strict default refused it. The condition now carries its own kernel certificate
    // (`KernelRecheckableWithSideConditions`) and `shl` ships [PROVED]. The caller `t0` still
    // grades [VALIDATED]: its value refutation (the callee's shift composed with the caller's
    // `lshr`-derived amount) exports at 3284 steps, over the reviewed 2048-step kernel
    // re-check frontier (`MAX_RECHECKABLE_REFUTATION_STEPS`), and no O(1) reflect arm covers
    // the composite. So the row is refused BY GRADE, naming `t0` and not `shl`.
    Subject {
        name: "variable_shifts_wide",
        source: r#"#[inline(never)] fn shr32<T>(x: u32, n: u32) -> u32 { x >> n }
#[inline(never)] fn shl64<T>(x: u64, n: u32) -> u64 { x << n }
#[inline(never)] fn sar64<T>(x: i64, n: u32) -> i64 { x >> n }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { shr32::<u8>(x as u32, (x >> 32) as u32) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t1(x: u64) -> u64 { shl64::<u8>(x, (x >> 8) as u32) }
#[unsafe(no_mangle)] pub extern "C" fn t2(x: u64) -> u64 { sar64::<u8>(x as i64, (x >> 8) as u32) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn t3(x: u64) -> u64 { shl64::<u16>(x, x as u32) }
"#,
        o0: PANIC,
        o2: Expect::Same,
    },
    Subject {
        name: "variable_shift_narrow",
        source: r#"#[inline(never)] fn shl<T>(x: u8, n: u32) -> u8 { x << n }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { shl::<u8>(x as u8, (x >> 8) as u32) as u64 }
"#,
        o0: PANIC,
        o2: Expect::Refused(&["function `t0` could not be proven", "[VALIDATED] (ay-only authority)"]),
    },
    Subject {
        name: "inlined_generic",
        source: r#"fn plain<T>(x: u64) -> u64 { x ^ 0x33 }
#[unsafe(no_mangle)] pub extern "C" fn t0(x: u64) -> u64 { plain::<u8>(x) }
"#,
        o0: Expect::Same,
        o2: Expect::Same,
    },
];

/// Trust (step 2 increment 5, sub-step 5.4.2): the compiler-lane rows whose outcome differs from
/// the default lane's, `(subject, opt-level, outcome)`. MEASURED on this branch's stage 1
/// (2026-10-08). On the compiler lane a generic instance is a REAL CALL (`bl`), proved by the
/// call-event gate, where the default lane splices it into its caller; strict ships only a
/// closed-[PROVED] object (`CerReport::ships`).
const COMPILER_LANE_DIFFERS: &[(&str, &str, Expect)] = &[
    // A generic callee that still grades [VALIDATED] (ay-only) on the call-event gate makes
    // strict refuse the object by policy (plan §3's strict-grade parity risk, 5.5/5.8). Since the
    // Darwin narrow scalar physical ABI contracts (bb594a04d3 C-u8, 15f62e2bb2 C-u16, 5fef1eddf6
    // signed C8/C16), a caller's edge to a narrow `u8`/`u16`/`i8` callee closes [PROVED] in the
    // same kernel conjunction, so `ident_widths`, `trait_widths_xor` and `assoc_type_width` (both
    // levels) and `i8_negation` at -O2 ship and equal the LLVM lane. Measured 2026-11-08: a stage
    // 1 of 2026-11-02 (ad3c581466) refuses `ident_widths` -O0 with exactly `t0 ([VALIDATED])`
    // and `t1 ([VALIDATED])`, the callers of `id::<u8>` and `id::<u16>`; a stage 1 of d59a1ff978
    // closes all 14 functions [PROVED].
    ("wrapping_add_through_trait_constant", "2", POLICY_VALIDATED),
    ("variable_shifts_wide", "2", POLICY_VALIDATED),
    ("variable_shift_narrow", "2", POLICY_VALIDATED),
    // `cmp::<T>` calls `T::lt`, whose result is a `bool`: a caller's edge to a `bool` result is
    // Unknown (INC5.4-BOOLRET), so `cmp` is not closed and strict refuses.
    (
        "signedness_via_trait",
        "0",
        Expect::Refused(&["[f1-output-gate:policy]", "(Unknown; blocked by []"]),
    ),
    (
        "signedness_via_trait",
        "2",
        Expect::Refused(&["[f1-output-gate:policy]", "(Unknown; blocked by []"]),
    ),
    // At -O2 `plain::<u8>` is not in rustc's inventory; the compiler lane refuses inventory
    // residue the instance lane spliced (INC5.4-SCOPE), where the default lane inlines it.
    ("inlined_generic", "2", Expect::Refused(&["[codegen-module]", "INC5.4-SCOPE"])),
    // Trust (PKG-CP slice 1, DECISION_QUEUE PKG-CP-CONSUMER-SITING-1): the compiler lane no
    // longer refuses an -O0 overflow/shift check `[unfaithful-panic]`; it sites the check at
    // rustc's panic entry and its `core::panic::Location` record, a relocated read-only global.
    // The object reader refuses that relocation until its admission lands
    // (cp/pkg-cp-location-global), so each row is still refused, now by the object gate, and
    // writes no rlib. MEASURED 2026-11-12 on a stage 1 of this branch.
    ("overflow_check_in_generic", "0", SITED),
    ("shift_check_in_generic", "0", SITED),
    ("wrapping_add_through_trait_constant", "0", SITED),
    ("i8_negation", "0", SITED),
    ("u32_subtraction", "0", SITED),
    ("variable_shifts_wide", "0", SITED),
    ("variable_shift_narrow", "0", SITED),
];

/// A check sited at rustc's panic entry (PKG-CP) whose object the reader refuses.
const SITED: Expect = Expect::Refused(&[
    "sited at rustc's panic entry and location (PKG-CP)",
    "[f1-output-gate:object]",
    "carries relocations",
]);

const POLICY_VALIDATED: Expect = Expect::Refused(&["[f1-output-gate:policy]", "[VALIDATED]"]);

fn compile(
    source_file: &str,
    crate_name: &str,
    out: &str,
    f1: bool,
    opt: &str,
) -> run_make_support::Rustc {
    rfs::create_dir(out);
    let mut cmd = rustc();
    cmd.input(source_file)
        .crate_name(crate_name)
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg(format!("-Copt-level={opt}"))
        .arg("-Ztrust-verify=off")
        .out_dir(out)
        .env_remove(TRUST_NO_VERIFY_ENV);
    if f1 {
        cmd.arg("-Zunstable-options")
            .arg("-Zcodegen-backend=trust-cg")
            .arg("-Ztrust-cg-frontend=trust-ir")
            .arg("-Ztrust-ir-lower");
    }
    cmd
}

/// The one `.o` member of `rlib`.
fn object_member(rlib: &str) -> Vec<u8> {
    let data = rfs::read(rlib);
    let archive = ArchiveFile::parse(&*data).expect("rlib is an archive");
    let mut objects = Vec::new();
    for member in archive.members() {
        let member = member.expect("archive member");
        if member.name().ends_with(b".o") {
            objects.push(member.data(&*data).expect("member data").to_vec());
        }
    }
    assert_eq!(objects.len(), 1, "one codegen unit, one object");
    objects.pop().unwrap()
}

/// A C driver that runs every `tN` on every input, each call in a forked child.
fn driver(functions: &[String]) -> String {
    let mut c = String::from(
        "#include <stdint.h>\n#include <stdio.h>\n#include <unistd.h>\n#include <sys/wait.h>\n",
    );
    for f in functions {
        c.push_str(&format!("extern uint64_t {f}(uint64_t);\n"));
    }
    c.push_str("typedef uint64_t (*F)(uint64_t);\n");
    c.push_str(&format!("F fs[] = {{{}}};\n", functions.join(", ")));
    c.push_str(&format!(
        "const char *names[] = {{{}}};\n",
        functions.iter().map(|f| format!("\"{f}\"")).collect::<Vec<_>>().join(", ")
    ));
    c.push_str(&format!(
        "uint64_t xs[] = {{{}}};\n",
        INPUTS.iter().map(|x| format!("{x}ULL")).collect::<Vec<_>>().join(", ")
    ));
    c.push_str(
        "int main(void) {\n\
         for (unsigned j = 0; j < sizeof(fs) / sizeof(fs[0]); j++) {\n\
         printf(\"%s:\", names[j]);\n\
         for (unsigned i = 0; i < sizeof(xs) / sizeof(xs[0]); i++) {\n\
         fflush(stdout);\n\
         pid_t p = fork();\n\
         if (p == 0) { uint64_t r = fs[j](xs[i]); printf(\" %llu\", (unsigned long long)r); fflush(stdout); _exit(0); }\n\
         int st; waitpid(p, &st, 0);\n\
         if (WIFSIGNALED(st)) printf(\" SIG%d\", WTERMSIG(st)); else if (WEXITSTATUS(st)) printf(\" EXIT%d\", WEXITSTATUS(st));\n\
         }\n\
         printf(\"\\n\");\n\
         }\n\
         return 0;\n\
         }\n",
    );
    c
}

fn run_lane(tag: &str, object: &[u8], functions: &[String]) -> String {
    rfs::write(format!("{tag}.o"), object);
    rfs::write(format!("{tag}.c"), driver(functions));
    cc().input(format!("{tag}.c")).input(format!("{tag}.o")).out_exe(&tag).run();
    run(&tag).stdout_utf8()
}

fn exported_functions(source: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| {
            let at = line.find("pub extern \"C\" fn ")? + "pub extern \"C\" fn ".len();
            let rest = &line[at..];
            Some(rest[..rest.find('(')?].to_string())
        })
        .collect()
}

fn main() {
    let mut compared = 0;
    let mut refused = 0;
    for subject in CORPUS {
        let crate_name = format!("dx_{}", subject.name);
        let source_file = format!("{crate_name}.rs");
        rfs::write(&source_file, subject.source);
        for (opt, expect) in [("0", subject.o0), ("2", subject.o2)] {
            let tag = format!("{}_o{opt}", subject.name);
            let f1_out = format!("out_{tag}_f1");
            match expect {
                Expect::Same => {
                    let f1 = compile(&source_file, &crate_name, &f1_out, true, opt).run();
                    let stderr = f1.stderr_utf8();
                    assert!(!stderr.contains("internal compiler error"), "{stderr}");
                    assert!(stderr.contains(" 0 refuted"), "{tag}: {stderr}");
                    // A GENERIC instance was really spliced: the D17 disclosure names one.
                    let coverage = rfs::read_to_string(format!(
                        "{f1_out}/{crate_name}.trust-instance-coverage.json"
                    ));
                    assert!(
                        coverage.contains("\"kind\": \"generic-instance\""),
                        "{tag}: no spliced generic instance:\n{coverage}"
                    );
                    let llvm_out = format!("out_{tag}_llvm");
                    compile(&source_file, &crate_name, &llvm_out, false, opt).run();
                    let functions = exported_functions(subject.source);
                    let lib = rust_lib_name(&crate_name);
                    let oracle = run_lane(
                        &format!("{tag}_llvm"),
                        &object_member(&format!("{llvm_out}/{lib}")),
                        &functions,
                    );
                    let f1 = run_lane(
                        &format!("{tag}_f1"),
                        &object_member(&format!("{f1_out}/{lib}")),
                        &functions,
                    );
                    assert_eq!(
                        f1, oracle,
                        "{tag}: F1 and the LLVM oracle disagree on executed output"
                    );
                    assert!(!oracle.contains("SIG"), "{tag}: the corpus must not trap: {oracle}");
                    compared += 1;
                }
                Expect::Refused(needles) => {
                    let f1 = compile(&source_file, &crate_name, &f1_out, true, opt).run_fail();
                    let stderr = f1.stderr_utf8();
                    assert!(!stderr.contains("internal compiler error"), "{stderr}");
                    for needle in needles {
                        assert!(stderr.contains(needle), "{tag}: missing `{needle}`:\n{stderr}");
                    }
                    assert!(
                        !std::path::Path::new(&f1_out).join(rust_lib_name(&crate_name)).exists(),
                        "{tag}: a refused crate writes no rlib"
                    );
                    refused += 1;
                }
            }
        }
    }
    // EXACT: 18 subjects, 14 of them compared at one or both levels. A compared build that turns
    // into a refusal (or back) must be a deliberate edit here, never silent.
    assert_eq!((compared, refused), (22, 14), "the corpus changed shape");

    the_inlined_generic_has_no_own_symbol();
    cross_crate_share_generics();
    compiler_lane_leg();
}

/// Trust (step 2 increment 5, sub-step 5.4.2): the corpus on the compiler lane, strict (D17).
fn compiler_lane_leg() {
    let mut compared = 0;
    let mut refused = 0;
    for subject in CORPUS {
        let crate_name = format!("dx_{}", subject.name);
        let source_file = format!("{crate_name}.rs");
        for (opt, default_lane) in [("0", subject.o0), ("2", subject.o2)] {
            let tag = format!("{}_o{opt}_compiler", subject.name);
            let expect = COMPILER_LANE_DIFFERS
                .iter()
                .find(|(name, level, _)| *name == subject.name && *level == opt)
                .map_or(default_lane, |(_, _, expect)| *expect);
            let out = format!("out_{tag}");
            let mut cmd = compile(&source_file, &crate_name, &out, true, opt);
            cmd.arg("-Ztrust-cg-f1-backend=compiler");
            match expect {
                Expect::Same => {
                    let stderr = cmd.run().stderr_utf8();
                    assert!(!stderr.contains("internal compiler error"), "{tag}: {stderr}");
                    assert!(
                        stderr.contains("codegen_module"),
                        "{tag}: the compiler lane:\n{stderr}"
                    );
                    assert!(stderr.contains(" 0 refuted"), "{tag}: {stderr}");
                    let coverage = rfs::read_to_string(format!(
                        "{out}/{crate_name}.trust-instance-coverage.json"
                    ));
                    assert!(
                        coverage.contains("\"kind\": \"generic-instance\""),
                        "{tag}: no spliced generic instance:\n{coverage}"
                    );
                    let functions = exported_functions(subject.source);
                    let lib = rust_lib_name(&crate_name);
                    let llvm_out = format!("out_{tag}_llvm");
                    compile(&source_file, &crate_name, &llvm_out, false, opt).run();
                    let oracle = run_lane(
                        &format!("{tag}_llvm"),
                        &object_member(&format!("{llvm_out}/{lib}")),
                        &functions,
                    );
                    let got = run_lane(&tag, &object_member(&format!("{out}/{lib}")), &functions);
                    assert_eq!(got, oracle, "{tag}: the compiler lane and LLVM disagree");
                    compared += 1;
                }
                Expect::Refused(needles) => {
                    let stderr = cmd.run_fail().stderr_utf8();
                    assert!(!stderr.contains("internal compiler error"), "{tag}: {stderr}");
                    // Trust (PKG-CP): the compiler lane sites checks; it never refuses one as
                    // an unfaithful panic.
                    assert!(!stderr.contains("[unfaithful-panic]"), "{tag}: {stderr}");
                    for needle in needles {
                        assert!(stderr.contains(needle), "{tag}: missing `{needle}`:\n{stderr}");
                    }
                    assert!(
                        !std::path::Path::new(&out).join(rust_lib_name(&crate_name)).exists(),
                        "{tag}: a refused crate writes no rlib"
                    );
                    refused += 1;
                }
            }
        }
    }
    // EXACT, measured: 17 rows ship and equal LLVM, 19 are refused by name (2026-11-08; was
    // 10 and 26 before the seven narrow/trait rows above closed [PROVED]).
    assert_eq!((compared, refused), (17, 19), "the compiler-lane corpus changed shape");
}

/// At -O2 `plain::<u8>` is not in the codegen inventory (the MIR inliner folded it into `t0`), so
/// F1 splices its body only INTO `t0`: its coverage row says so, and at -O0 it is its own symbol.
fn the_inlined_generic_has_no_own_symbol() {
    for (opt, own) in [("0", true), ("2", false)] {
        let coverage = rfs::read_to_string(format!(
            "out_inlined_generic_o{opt}_f1/dx_inlined_generic.trust-instance-coverage.json"
        ));
        let row = coverage
            .lines()
            .find(|line| line.contains("5plainhE") && line.contains("\"generic-instance\""))
            .unwrap_or_else(|| panic!("-O{opt}: no row for `plain::<u8>`:\n{coverage}"));
        assert!(row.contains(&format!("\"emitted_as_own_symbol\": {own}")), "-O{opt}: {row}");
        assert!(row.contains("\"inlined_into\": [\"t0\"]"), "-O{opt}: {row}");
    }
}

/// An F1-built rlib exports generic INSTANCES (share-generics at opt-level 0), and an LLVM-built
/// binary calls each DIRECTLY on the edge inputs. Its output must equal the all-LLVM build's
/// (whose first and last lines are pinned), each symbol must be DEFINED (and global) in the F1
/// upstream object, and UNDEFINED in the LLVM downstream object, so it is the F1 bytes that run.
///
/// Two upstreams: the identity at full width, trait-dispatched `pick::<u8>`/`pick::<u16>`, the
/// narrow `ident::<i8>`/`ident::<i16>` (argument and return extension on Apple arm64) and the
/// sign-dependent `cmp::<i64>`/`cmp::<u64>`; and, with `-Coverflow-checks=off` so D17 ships them,
/// the ARITHMETIC `addk::<u8>`/`addk::<u16>` (wrapping add through a trait-provided constant),
/// `neg::<u8>` (i8 negation) and `sub::<u8>` (u32 subtraction), whose standalone bytes nothing
/// else executes.
fn cross_crate_share_generics() {
    cross_crate(
        "up",
        r#"#[inline(never)] pub fn ident<T>(x: T) -> T { x }
#[unsafe(no_mangle)] pub extern "C" fn up_t0(x: u64) -> u64 { ident::<u64>(x) ^ 7 }
pub trait Tag { fn tag() -> u64; }
impl Tag for u8 { #[inline(never)] fn tag() -> u64 { 8 } }
impl Tag for u16 { #[inline(never)] fn tag() -> u64 { 16 } }
#[inline(never)] pub fn pick<T: Tag>(x: u64) -> u64 { x ^ T::tag() }
#[unsafe(no_mangle)] pub extern "C" fn up_pick8(x: u64) -> u64 { pick::<u8>(x) }
#[unsafe(no_mangle)] pub extern "C" fn up_pick16(x: u64) -> u64 { pick::<u16>(x) }
#[unsafe(no_mangle)] pub extern "C" fn up_id8(x: u64) -> u64 { ident::<i8>(x as i8) as i64 as u64 }
#[unsafe(no_mangle)] pub extern "C" fn up_id16(x: u64) -> u64 { ident::<i16>(x as i16) as i64 as u64 }
pub trait Lt: Copy { fn lt(a: Self, b: Self) -> bool; }
impl Lt for i64 { #[inline(never)] fn lt(a: i64, b: i64) -> bool { a < b } }
impl Lt for u64 { #[inline(never)] fn lt(a: u64, b: u64) -> bool { a < b } }
#[inline(never)] pub fn cmp<T: Lt>(a: T, b: T) -> u64 { if T::lt(a, b) { 1 } else { 0 } }
#[unsafe(no_mangle)] pub extern "C" fn up_cmp_i(x: u64) -> u64 { cmp::<i64>(x as i64, 5) }
#[unsafe(no_mangle)] pub extern "C" fn up_cmp_u(x: u64) -> u64 { cmp::<u64>(x, 5) }
"#,
        &[
            "up::ident::<u64>(x)",
            "up::up_t0(x)",
            "up::pick::<u8>(x)",
            "up::pick::<u16>(x)",
            "up::ident::<i8>(x as i8)",
            "up::ident::<i16>(x as i16)",
            "up::cmp::<i64>(x as i64, 5)",
            "up::cmp::<u64>(x, 5)",
        ],
        // v0: `ident::<u64>` `y`, `<i8>` `a`, `<i16>` `s`; `pick::<u8>` `h`, `<u16>` `t`;
        // `cmp::<i64>` `x`, `<u64>` `y`.
        &[
            "2up5identyE",
            "2up5identaE",
            "2up5identsE",
            "2up4pickhE",
            "2up4picktE",
            "2up3cmpxE",
            "2up3cmpyE",
        ],
        &[],
        ("0 7 8 16 0 0 1 1", "18446744073709551615 18446744073709551608 18446744073709551607 \
          18446744073709551599 -1 -1 1 0"),
    );
    cross_crate(
        "up2",
        r#"pub trait K { fn k() -> u8; }
impl K for u8 { #[inline(never)] fn k() -> u8 { 200 } }
impl K for u16 { #[inline(never)] fn k() -> u8 { 100 } }
#[inline(never)] pub fn addk<T: K>(x: u8) -> u8 { x + T::k() }
#[inline(never)] pub fn neg<T>(x: i8) -> i8 { -x }
#[inline(never)] pub fn sub<T>(a: u32, b: u32) -> u32 { a - b }
#[unsafe(no_mangle)] pub extern "C" fn up2_addk8(x: u64) -> u64 { addk::<u8>(x as u8) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn up2_addk16(x: u64) -> u64 { addk::<u16>(x as u8) as u64 }
#[unsafe(no_mangle)] pub extern "C" fn up2_neg(x: u64) -> u64 { neg::<u8>(x as i8) as i64 as u64 }
#[unsafe(no_mangle)] pub extern "C" fn up2_sub(x: u64) -> u64 { sub::<u8>(x as u32, 7) as u64 }
"#,
        &[
            "up2::addk::<u8>(x as u8)",
            "up2::addk::<u16>(x as u8)",
            "up2::neg::<u8>(x as i8)",
            "up2::sub::<u8>(x as u32, 7)",
        ],
        // v0: `addk::<u8>` `h`, `<u16>` `t`; `neg::<u8>`; `sub::<u8>`.
        &["3up24addkhE", "3up24addktE", "3up23neghE", "3up23subhE"],
        &["-Coverflow-checks=off"],
        ("200 100 0 4294967289", "199 99 1 4294967288"),
    );
}

/// One upstream/downstream pair: `upstream` built on both lanes with `flags`, a downstream that
/// prints `calls` for every input, the symbol checks over `instances`, and the oracle's pinned
/// `(first, last)` lines.
fn cross_crate(
    krate: &str,
    upstream: &str,
    calls: &[&str],
    instances: &[&str],
    flags: &[&str],
    (first, last): (&str, &str),
) {
    let up_file = format!("{krate}.rs");
    rfs::write(&up_file, upstream);
    let inputs = INPUTS.join(", ");
    let placeholders = vec!["{}"; calls.len()].join(" ");
    let down_file = format!("down_{krate}.rs");
    rfs::write(
        &down_file,
        format!(
            "fn main() {{\n    for x in [{inputs}u64] {{\n        println!(\"{placeholders}\", {});\n    }}\n}}\n",
            calls.join(", ")
        ),
    );
    let mut outputs = Vec::new();
    for (lane, f1) in [("llvm", false), ("f1", true)] {
        let out = format!("out_{krate}_{lane}");
        let built = compile(&up_file, krate, &out, f1, "0").args(flags).run();
        assert!(!built.stderr_utf8().contains("internal compiler error"));
        let rlib = format!("{out}/{}", rust_lib_name(krate));
        let exe = format!("down_{krate}_{lane}");
        rustc()
            .input(&down_file)
            .edition("2021")
            .arg("-Cpanic=abort")
            .arg("-Ccodegen-units=1")
            .arg("-Ztrust-verify=off")
            .args(flags)
            .extern_(krate, &rlib)
            .output(bin_name(&exe))
            .env_remove(TRUST_NO_VERIFY_ENV)
            .run();
        outputs.push(run(&exe).stdout_utf8());
        if f1 {
            let up_object = object_member(&rlib);
            let up_file = File::parse(&*up_object).expect("the F1 upstream object");
            for fragment in instances {
                let symbol = up_file
                    .symbols()
                    .find(|s| s.name().is_ok_and(|n| n.contains(fragment)))
                    .unwrap_or_else(|| panic!("F1 upstream object lacks `{fragment}`"));
                assert!(
                    symbol.is_definition() && symbol.is_global(),
                    "`{fragment}` must be DEFINED and global in the F1 upstream object"
                );
            }
            // The downstream's own object: every instance is a reference, not a local copy.
            let down_obj = format!("down_{krate}_obj.o");
            rustc()
                .input(&down_file)
                .crate_name(format!("down_{krate}_obj"))
                .edition("2021")
                .arg("-Cpanic=abort")
                .arg("-Ccodegen-units=1")
                .arg("-Ztrust-verify=off")
                .args(flags)
                .extern_(krate, &rlib)
                .emit("obj")
                .output(&down_obj)
                .env_remove(TRUST_NO_VERIFY_ENV)
                .run();
            let down_object = rfs::read(&down_obj);
            let down_file = File::parse(&*down_object).expect("the LLVM downstream object");
            for fragment in instances {
                let found: Vec<_> = down_file
                    .symbols()
                    .filter(|s| s.name().is_ok_and(|n| n.contains(fragment)))
                    .collect();
                assert!(!found.is_empty(), "the downstream never references `{fragment}`");
                assert!(
                    found.iter().all(|s| s.is_undefined()),
                    "`{fragment}` must be UNDEFINED in the LLVM downstream object (it links the \
                     F1 instance, not a copy of its own)"
                );
            }
        }
    }
    assert_eq!(outputs[1], outputs[0], "{krate}: the F1-built generic instances agree with LLVM");
    let lines: Vec<&str> = outputs[0].lines().collect();
    assert_eq!(lines.len(), INPUTS.len(), "{krate}: the oracle ran every input");
    assert_eq!((lines[0], lines[lines.len() - 1]), (first, last), "{krate}: the oracle itself");
}
