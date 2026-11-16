//! Trust (step 2 increment 5, sub-step 5.4.3; plan
//! `docs/design/2026-10-08-step2-inc5-step4-compiler-lane-plan.md` §3): RULE-9 ABI LEGALIZATION on
//! F1's compiler lane, `-Ztrust-cg-f1-backend=compiler`, against rustc's real `FnAbi`.
//!
//! Each subject is a library crate of `pub` Rust-ABI functions whose arguments or results rustc
//! does not pass as one scalar: `Option<u64>`, `(u64, u64)`, `&[u8]`, a 24-byte struct, an sret
//! result and a zero-sized argument (the plan's six), plus a `repr(Rust)`-REORDERED two-field
//! struct (`S2 { a: u32, b: u64 }`, whose `ScalarPair` puts field `b` first: INC5.4-LAYOUT-ORDER)
//! and a `Direct` newtype. Each crate calls its own subject too, so the legalization runs at a
//! definition's entry and returns AND at a call site.
//!
//! * PASS MODES, MEASURED FIRST (critique L6): `abi_probe.rs` asks rustc on this tree, through
//!   `#[rustc_abi(debug)]`, how it passes each subject's slots, and pins the answer. The pass mode
//!   is target-dependent (the old `&T`-arm note that `&[u64]` arrives as `Cast` is contradicted
//!   by the `&[u8]` `Pair` measurement), so a drift fails here first, not as a wrong legalization.
//! * ALLOW-UNKNOWN (at `-Copt-level=0` and `2`): every crate the lane admits compiles, its object
//!   DEFINES each subject function (so it is the F1 bytes the driver runs), and an LLVM-built Rust
//!   driver linked against it (calling each subject DIRECTLY through rustc's Rust ABI, so a
//!   legalization that disagreed with rustc's would read the wrong registers or memory) prints
//!   exactly what it prints linked against the LLVM-built crate.
//! * GRADES, as measured (stage 1 of the 5.4.3 branch, trust-cg `e7acae8b1`; tuple row
//!   re-measured on the 1.101 stage 1): every function of every subject is Unknown, at both
//!   levels, each for a pinned reason — except `tup_mix`, which closes to `[PROVED]` at
//!   `-O2` only (grades are pinned per opt level). P cannot place a
//!   non-tuple pair, a struct, an sret result or a dropped non-`()` argument (the gate's
//!   `check_fixed_placement`; Unknown until step 5.10), a function with a pair result has no P
//!   (plan §3), and trust-cg lowers an aggregate copy to a `memmove` call the gate pairs with no
//!   IR site. So the STRICT (default) policy refuses each crate by name, and that is pinned too.
//! * REFUSED BY NAME: `Option<u64>` (`[unsupported-abi]`, INC5.4-PAIR-ENUM: trust-cg lowers no enum
//!   `MakeAggregate`). `(u64, u64)` was refused here too until the 1.101 toolchain: trust-cg
//!   admits a declared tuple layout only when it equals its declaration-order byte layout
//!   (WS7.7), rustc 1.101 lays a pair out in declaration order, so the pair now compiles and
//!   is driven against the LLVM oracle like the other compiling subjects. A tuple rustc
//!   reorders still refuses module-wide; `trust-cg-f1-census-complete`'s `tuple3.rs`
//!   (`(u8, u64, u8)` at offsets `[8, 0, 9]`) pins that discriminating sibling.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::{File, Object, ObjectSymbol};
use run_make_support::{bin_name, rfs, run, rust_lib_name, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

const INPUTS: &[&str] = &["0", "1", "2", "7", "16", "255", "256", "65535", "18446744073709551615"];

/// What the compiler lane does with a subject crate, as measured.
#[derive(Clone, Copy)]
enum Lane {
    /// Compiles under allow-unknown. `grades`: `(function, [(grade, reason needle); 2])`
    /// for EVERY function of the crate, one pair per opt level (`-O0`, then `-O2`); the
    /// strict policy refuses the crate naming each function its opt level leaves unclosed.
    /// Per-opt because 1.101 closes `tup_mix` to `[PROVED]` at `-O2` only; every other
    /// measured grade is so far opt-invariant and repeats its pair.
    Compiles { grades: &'static [(&'static str, [(&'static str, &'static str); 2])] },
    /// Refused; every needle appears in the one fatal, and no rlib is written.
    Refused(&'static [&'static str]),
}

struct Subject {
    name: &'static str,
    source: &'static str,
    /// Expressions over `x: u64` the driver prints, one line per input.
    calls: &'static [&'static str],
    lane: Lane,
}

/// The gate cannot place the producer signature (`check_fixed_placement`).
const UNPLACED: &str = "disagrees with its producer signature";
/// A caller's edge to a callee P does not place.
const CALLEE_UNPLACED: &str = "is called under a signature";
/// trust-cg's aggregate copy, a runtime-helper call with no IR site.
const MEMMOVE: &str = "to `memmove` have no IR counterpart";

const SUBJECTS: &[Subject] = &[
    Subject {
        name: "option",
        source: r#"#[inline(never)] pub fn opt_get(x: Option<u64>) -> u64 { match x { Some(v) => v ^ 5, None => 7 } }
#[inline(never)] pub fn opt_via(x: u64) -> u64 { opt_get(if x & 1 == 0 { Some(x) } else { None }) }
"#,
        calls: &[
            "legal_option::opt_get(if x % 3 == 0 { None } else { Some(x) })",
            "legal_option::opt_via(x)",
        ],
        lane: Lane::Refused(&["[unsupported-abi]", "opt_get", "INC5.4-PAIR-ENUM"]),
    },
    Subject {
        name: "tuple",
        source: r#"#[inline(never)] pub fn tup_mix(t: (u64, u64)) -> u64 { t.0 ^ (t.1 << 3) }
#[inline(never)] pub fn tup_swap(t: (u64, u64)) -> (u64, u64) { (t.1, t.0) }
#[inline(never)] pub fn tup_via(x: u64) -> u64 { let (a, b) = tup_swap((x, x ^ 9)); tup_mix((a, b)) }
"#,
        calls: &[
            "legal_tuple::tup_mix((x, x.wrapping_add(1)))",
            "{ let (a, b) = legal_tuple::tup_swap((x, !x)); a ^ b.rotate_left(1) }",
            "legal_tuple::tup_via(x)",
        ],
        // Compiles since 1.101 (see the header): the pair's declared layout now
        // agrees with trust-cg's declaration-order byte layout. Grades measured
        // on the 1.101 stage 1: the pair store leaves P's frame model, a pair
        // result has no P (plan §3), and the via-caller's edge to the pair
        // result does not place.
        lane: Lane::Compiles {
            grades: &[
                // At `-O2` the pair store stays inside P's frame model and the
                // function closes; the needle is the certificate's own grade.
                ("tup_mix", [
                    ("Unknown", "addresses memory outside the function's frame"),
                    ("[PROVED]", "\"[PROVED]\""),
                ]),
                ("tup_swap", [
                    ("Unknown", "P has no placement for this function"),
                    ("Unknown", "P has no placement for this function"),
                ]),
                ("tup_via", [
                    ("Unknown", "P has no placement for the callee"),
                    ("Unknown", "P has no placement for the callee"),
                ]),
            ],
        },
    },
    Subject {
        name: "slice",
        source: r#"#[inline(never)] pub fn slice_len(s: &[u8]) -> u64 { s.len() as u64 }
#[inline(never)] pub fn slice_via(s: &[u8]) -> u64 { slice_len(s) ^ 0x40 }
"#,
        calls: &[
            "legal_slice::slice_len(&BUF[..(x % 17) as usize])",
            "legal_slice::slice_via(&BUF[(x % 5) as usize..])",
        ],
        lane: Lane::Compiles {
            grades: &[
                ("slice_len", [("Unknown", "P passes a FatPtr(Slice("), ("Unknown", "P passes a FatPtr(Slice(")]),
                ("slice_via", [("Unknown", "P passes a FatPtr(Slice("), ("Unknown", "P passes a FatPtr(Slice(")]),
            ],
        },
    },
    Subject {
        name: "byval",
        source: r#"pub struct S24 { pub a: u64, pub b: u64, pub c: u64 }
#[inline(never)] pub fn s24_mix(s: S24) -> u64 { s.a ^ (s.b << 7) ^ (s.c >> 13) }
#[inline(never)] pub fn s24_via(x: u64) -> u64 { s24_mix(S24 { a: x, b: x ^ 1, c: x ^ 2 }) }
"#,
        calls: &[
            "legal_byval::s24_mix(legal_byval::S24 { a: x, b: !x, c: x.rotate_left(5) })",
            "legal_byval::s24_via(x)",
        ],
        lane: Lane::Compiles {
            grades: &[
                ("s24_mix", [("Unknown", UNPLACED), ("Unknown", UNPLACED)]),
                ("s24_via", [("Unknown", MEMMOVE), ("Unknown", MEMMOVE)]),
            ],
        },
    },
    Subject {
        name: "sret",
        source: r#"pub struct S24 { pub a: u64, pub b: u64, pub c: u64 }
#[inline(never)] pub fn s24_make(x: u64) -> S24 { S24 { a: x, b: x * 3, c: !x } }
#[inline(never)] pub fn s24_roundtrip(x: u64) -> u64 { let s = s24_make(x); s.a ^ s.b ^ (s.c << 9) }
"#,
        calls: &[
            "{ let s = legal_sret::s24_make(x); s.a ^ s.b.rotate_left(1) ^ s.c.rotate_left(2) }",
            "legal_sret::s24_roundtrip(x)",
        ],
        lane: Lane::Compiles {
            grades: &[
                ("s24_make", [("Unknown", "an sret result is Unknown until step 5.10"), ("Unknown", "an sret result is Unknown until step 5.10")]),
                ("s24_roundtrip", [("Unknown", MEMMOVE), ("Unknown", MEMMOVE)]),
            ],
        },
    },
    Subject {
        name: "zst",
        source: r#"pub struct Marker;
#[inline(never)] pub fn zst_arg(x: u64, _m: Marker) -> u64 { x ^ 0x33 }
#[inline(never)] pub fn zst_via(x: u64) -> u64 { zst_arg(x, Marker) << 1 }
"#,
        calls: &["legal_zst::zst_arg(x, legal_zst::Marker)", "legal_zst::zst_via(x)"],
        lane: Lane::Compiles {
            grades: &[
                ("zst_arg", [("Unknown", "P ignores a Struct("), ("Unknown", "P ignores a Struct(")]),
                ("zst_via", [("Unknown", CALLEE_UNPLACED), ("Unknown", CALLEE_UNPLACED)]),
            ],
        },
    },
    Subject {
        name: "pairstruct",
        source: r#"pub struct S2 { pub a: u32, pub b: u64 }
#[inline(never)] pub fn s2_mix(s: S2) -> u64 { s.b ^ ((s.a as u64) << 7) }
#[inline(never)] pub fn s2_make(x: u64) -> S2 { S2 { a: (x >> 3) as u32, b: x ^ 0x55 } }
#[inline(never)] pub fn s2_via(x: u64) -> u64 { s2_mix(s2_make(x)) ^ s2_mix(S2 { a: x as u32, b: !x }) }
"#,
        calls: &[
            "legal_pairstruct::s2_mix(legal_pairstruct::S2 { a: (x as u32) ^ 9, b: x << 2 })",
            "{ let s = legal_pairstruct::s2_make(x); (s.a as u64) ^ s.b.rotate_left(3) }",
            "legal_pairstruct::s2_via(x)",
        ],
        lane: Lane::Compiles {
            grades: &[
                ("s2_mix", [("Unknown", "P passes a Struct("), ("Unknown", "P passes a Struct(")]),
                ("s2_make", [("Unknown", "P has no placement for this function"), ("Unknown", "P has no placement for this function")]),
                ("s2_via", [("Unknown", CALLEE_UNPLACED), ("Unknown", CALLEE_UNPLACED)]),
            ],
        },
    },
    Subject {
        name: "newtype",
        source: r#"pub struct W(pub u64);
#[inline(never)] pub fn w_step(w: W) -> W { W((w.0 << 1) ^ 3) }
#[inline(never)] pub fn w_via(x: u64) -> u64 { w_step(w_step(W(x))).0 }
"#,
        calls: &["legal_newtype::w_step(legal_newtype::W(x)).0", "legal_newtype::w_via(x)"],
        lane: Lane::Compiles {
            grades: &[
                ("w_step", [("Unknown", UNPLACED), ("Unknown", UNPLACED)]),
                ("w_via", [("Unknown", CALLEE_UNPLACED), ("Unknown", CALLEE_UNPLACED)]),
            ],
        },
    },
];

/// `abi_probe.rs`: rustc's `FnAbi` for every subject signature, printed by
/// `#[rustc_abi(debug)]` (which reports it as an error, so the probe always fails to compile).
const ABI_PROBE: &str = r#"#![feature(rustc_attrs)]
#![crate_type = "lib"]
pub struct S24 { pub a: u64, pub b: u64, pub c: u64 }
pub struct Marker;
pub struct S2 { pub a: u32, pub b: u64 }
pub struct W(pub u64);
#[rustc_abi(debug)] pub fn opt_get(x: Option<u64>) -> u64 { match x { Some(v) => v, None => 7 } }
#[rustc_abi(debug)] pub fn tup_swap(t: (u64, u64)) -> (u64, u64) { (t.1, t.0) }
#[rustc_abi(debug)] pub fn slice_len(s: &[u8]) -> u64 { s.len() as u64 }
#[rustc_abi(debug)] pub fn s24_mix(s: S24) -> u64 { s.a ^ s.b ^ s.c }
#[rustc_abi(debug)] pub fn s24_make(x: u64) -> S24 { S24 { a: x, b: x, c: x } }
#[rustc_abi(debug)] pub fn zst_arg(x: u64, _m: Marker) -> u64 { x }
#[rustc_abi(debug)] pub fn s2_make(x: u64) -> S2 { S2 { a: x as u32, b: x } }
#[rustc_abi(debug)] pub fn w_step(w: W) -> W { w }
"#;

/// The `FnAbi` debug print of `function`: from its `fn_abi_of(..)` error to the next one.
fn fn_abi<'a>(stderr: &'a str, function: &str) -> &'a str {
    let head = format!("error: fn_abi_of({function})");
    let start =
        stderr.find(&head).unwrap_or_else(|| panic!("no FnAbi print for `{function}`:\n{stderr}"));
    let rest = &stderr[start + head.len()..];
    let end = rest.find("error: fn_abi_of(").map_or(stderr.len(), |e| start + head.len() + e);
    &stderr[start..end]
}

/// The pass modes rustc gives each subject on this tree (critique L6), pinned.
fn measure_pass_modes() {
    rfs::write("abi_probe.rs", ABI_PROBE);
    let stderr = rustc()
        .input("abi_probe.rs")
        .edition("2021")
        .arg("-Ztrust-verify=off")
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run_fail()
        .stderr_utf8();
    let compact = |s: &str| s.split_whitespace().collect::<String>();
    let modes = |f: &str| compact(fn_abi(&stderr, f));
    let show = |f: &str| fn_abi(&stderr, f).to_string();
    // `Option<u64>`: a (tag, payload) pair.
    assert!(modes("opt_get").contains("mode:Pair("), "Option<u64>:\n{}", show("opt_get"));
    // `(u64, u64)`: a pair, argument and result.
    assert_eq!(modes("tup_swap").matches("mode:Pair(").count(), 2, "{}", show("tup_swap"));
    // `&[u8]`: (data, length), a pair, not `Cast`.
    assert!(modes("slice_len").contains("mode:Pair("), "&[u8]:\n{}", show("slice_len"));
    assert!(!modes("slice_len").contains("mode:Cast"), "&[u8]:\n{}", show("slice_len"));
    // A 24-byte struct: through a pointer, not on the stack, no metadata; and returned so.
    // (1.101 spelling: `on_stack: false` is `mode: Pointer` inside `Indirect`, and a
    // sized indirect carries no metadata by construction — metadata is the separate
    // `IndirectUnsized` mode, which trust-cg's `abi_shape` maps to `has_meta`.)
    let s24 = modes("s24_mix");
    assert!(
        s24.contains("mode:Indirect{")
            && s24.contains("mode:Pointer")
            && !s24.contains("IndirectUnsized"),
        "S24 argument:\n{}",
        show("s24_mix")
    );
    assert!(modes("s24_make").contains("mode:Indirect{"), "S24 result:\n{}", show("s24_make"));
    // A zero-sized argument: not passed.
    assert!(modes("zst_arg").contains("mode:Ignore"), "Marker:\n{}", show("zst_arg"));
    // The reordered pair: `ScalarPair(I64, I32)`, field `a` (u32) at offset 8, `b` at 0.
    let s2 = modes("s2_make");
    assert!(s2.contains("mode:Pair("), "S2:\n{}", show("s2_make"));
    assert!(s2.contains("offsets:[Size(8bytes),Size(0bytes),]"), "S2 layout:\n{}", show("s2_make"));
    // The newtype: one scalar, `Direct`, argument and result.
    assert_eq!(modes("w_step").matches("mode:Direct(").count(), 2, "{}", show("w_step"));
}

/// An rlib of `source`: F1's compiler lane (`gate` its output-gate policy; `None` the default,
/// strict), or LLVM (the oracle).
fn compile(
    source: &str,
    krate: &str,
    out: &str,
    f1: Option<Option<&str>>,
    opt: &str,
) -> run_make_support::Rustc {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input(source)
        .crate_name(krate)
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Coverflow-checks=off")
        .arg(format!("-Copt-level={opt}"))
        .arg("-Ztrust-verify=off")
        .out_dir(out)
        .env_remove(TRUST_NO_VERIFY_ENV);
    if let Some(gate) = f1 {
        cmd.arg("-Zunstable-options")
            .arg("-Zcodegen-backend=trust-cg")
            .arg("-Ztrust-cg-frontend=trust-ir")
            .arg("-Ztrust-ir-lower")
            .arg("-Ztrust-cg-f1-backend=compiler");
        if let Some(gate) = gate {
            cmd.arg(format!("-Ztrust-cg-output-gate={gate}"));
        }
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

/// An LLVM-built driver linked against `rlib`, printing `calls` on every input.
fn drive(subject: &Subject, rlib: &str, tag: &str, opt: &str) -> String {
    let krate = format!("legal_{}", subject.name);
    let placeholders = vec!["{}"; subject.calls.len()].join(" ");
    let driver = format!(
        "static BUF: [u8; 24] = [0; 24];\nfn main() {{\n    for x in [{}u64] {{\n        println!(\"{placeholders}\", {});\n    }}\n}}\n",
        INPUTS.join(", "),
        subject.calls.join(", ")
    );
    let file = format!("driver_{tag}.rs");
    rfs::write(&file, driver);
    let exe = format!("driver_{tag}");
    rustc()
        .input(&file)
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Coverflow-checks=off")
        .arg(format!("-Copt-level={opt}"))
        .arg("-Ztrust-verify=off")
        .extern_(&krate, rlib)
        .output(bin_name(&exe))
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    run(&exe).stdout_utf8()
}

fn main() {
    measure_pass_modes();
    for subject in SUBJECTS {
        let krate = format!("legal_{}", subject.name);
        let source = format!("{krate}.rs");
        rfs::write(&source, subject.source);
        let lib = rust_lib_name(&krate);
        for (opt_index, opt) in ["0", "2"].into_iter().enumerate() {
            let tag = format!("{}_o{opt}", subject.name);
            let llvm_out = format!("out_{tag}_llvm");
            compile(&source, &krate, &llvm_out, None, opt).run();
            let oracle = drive(subject, &format!("{llvm_out}/{lib}"), &format!("{tag}_llvm"), opt);
            assert_eq!(oracle.lines().count(), INPUTS.len(), "{tag}: the oracle ran every input");

            let out = format!("out_{tag}_au");
            let mut built = compile(&source, &krate, &out, Some(Some("allow-unknown")), opt);
            match subject.lane {
                Lane::Refused(needles) => {
                    let stderr = built.run_fail().stderr_utf8();
                    assert!(!stderr.contains("internal compiler error"), "{tag}: {stderr}");
                    for needle in needles {
                        assert!(stderr.contains(needle), "{tag}: missing `{needle}`:\n{stderr}");
                    }
                    assert!(
                        !std::path::Path::new(&out).join(&lib).exists(),
                        "{tag}: a refused crate writes no rlib"
                    );
                }
                Lane::Compiles { grades } => {
                    let stderr = built.run().stderr_utf8();
                    assert!(!stderr.contains("internal compiler error"), "{tag}: {stderr}");
                    assert!(stderr.contains(" 0 refuted"), "{tag}:\n{stderr}");
                    // It is the F1 bytes the driver runs: the object defines every subject.
                    let object = object_member(&format!("{out}/{lib}"));
                    let file = File::parse(&*object).expect("the F1 object");
                    for (function, _) in grades {
                        assert!(
                            file.symbols().any(|s| s.is_definition()
                                && s.is_global()
                                && s.name().is_ok_and(|n| n.contains(function))),
                            "{tag}: the F1 object does not define `{function}`"
                        );
                    }
                    let f1 = drive(subject, &format!("{out}/{lib}"), &format!("{tag}_f1"), opt);
                    assert_eq!(f1, oracle, "{tag}: the compiler lane and LLVM disagree");

                    let certificates =
                        rfs::read_to_string(format!("{out}/{krate}.trust-cg-certificates.json"));
                    let json: serde_json::Value =
                        serde_json::from_str(&certificates).expect("certificates JSON");
                    let certs = json["certificates"].as_array().expect("certificates");
                    assert_eq!(certs.len(), grades.len(), "{tag}: one certificate per function");
                    for (function, per_opt) in grades {
                        let (grade, reason) = per_opt[opt_index];
                        let cert = certs
                            .iter()
                            .find(|c| c["symbol"].as_str().is_some_and(|s| s.contains(function)))
                            .unwrap_or_else(|| panic!("{tag}: no certificate for `{function}`"));
                        assert_eq!(cert["grade"].as_str(), Some(grade), "{tag}: `{function}`");
                        assert!(
                            cert.to_string().contains(reason),
                            "{tag}: `{function}` is {grade} for another reason than `{reason}`: \
                             {cert}"
                        );
                    }

                    // STRICT, the default policy: refused, naming every UNCLOSED function.
                    // A function this opt level closes (`[PROVED]`) ships under strict and
                    // is not named; every subject still has an unclosed function at both
                    // levels, so the crate is refused either way.
                    let strict_out = format!("out_{tag}_strict");
                    let stderr = compile(&source, &krate, &strict_out, Some(None), opt)
                        .run_fail()
                        .stderr_utf8();
                    assert!(stderr.contains("[f1-output-gate:policy]"), "{tag}:\n{stderr}");
                    for (function, per_opt) in grades {
                        let (grade, _) = per_opt[opt_index];
                        if grade == "[PROVED]" {
                            assert!(
                                !stderr.contains(&format!("{function} (")),
                                "{tag}: strict names the closed `{function}`:\n{stderr}"
                            );
                        } else {
                            assert!(
                                stderr.contains(function)
                                    && stderr.contains(&format!("({grade};")),
                                "{tag}: strict does not name `{function}` ({grade}):\n{stderr}"
                            );
                        }
                    }
                    assert!(
                        !std::path::Path::new(&strict_out).join(&lib).exists(),
                        "{tag}: strict writes no rlib"
                    );
                }
            }
        }
    }
}
