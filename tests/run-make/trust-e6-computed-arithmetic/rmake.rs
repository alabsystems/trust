// Trust (TG14): actual compiler admissions, operator mutant, and independent
// citation count after a refused import, in both ordinary verification modes.
use run_make_support::{rfs, rustc};

fn arithmetic(op: &str) -> String {
    format!(
        r#"
#![allow(dead_code)]
pub fn budget(cost: u8, limit: u8, held: u8) -> bool {{ cost <= limit.wrapping_{op}(held) }}
clean {{
    theorem budget_exact (cost limit held : UInt8) :
        trust_import_arithmetic__budget cost limit held = decide (cost <= limit - held) := rfl
}}
"#
    )
}

fn checked_arithmetic() -> String {
    let mut source = String::from("#![allow(dead_code)]\n");
    for width in [8, 16, 32, 64] {
        source.push_str(&format!(r#"
            pub fn checked_u{width}(cost: u{width}, limit: u{width}, held: u{width}) -> bool {{
                match limit.checked_sub(held) {{ Some(left) => cost <= left, None => false }}
            }}
            pub fn wrap_u{width}(cost: u{width}, limit: u{width}, held: u{width}) -> bool {{ cost <= limit.wrapping_sub(held) }}
            clean {{
                theorem wrap_exact_u{width} (cost limit held : UInt{width}) :
                    trust_import_checked__wrap_u{width} cost limit held = decide (cost <= limit - held) := rfl
                theorem checked_exact_u{width} (cost limit held : UInt{width}) :
                    trust_import_checked__checked_u{width} cost limit held =
                    Bool.and (Bool.not (Nat.blt (UInt{width}.toNat limit) (UInt{width}.toNat held))) (decide (cost <= limit - held)) := rfl
            }}
        "#));
    }
    source
}

// Trust (R22): PF6's keeps_room body from aterm 1bd6b35, with the
// contract/binding it can acquire after TG14. The consumer stays unchanged.
fn capacity_room() -> &'static str {
    r#"
#![allow(dead_code)]
clean {
    def spec_keeps_room (held cost need limit : UInt64) : Bool :=
        decide (held <= limit) && (decide (cost <= limit - held) && decide (need <= limit - held - cost))
}
pub fn keeps_room(held: u64, cost: u64, need: u64, limit: u64) -> bool
    ensures result == spec_keeps_room(held, cost, need, limit) by keeps_room_is_exact
{
    held <= limit
        && (cost <= limit.wrapping_sub(held) && need <= limit.wrapping_sub(held).wrapping_sub(cost))
}
clean {
    theorem keeps_room_is_exact (held cost need limit : UInt64) :
        trust_import_room__keeps_room held cost need limit = spec_keeps_room held cost need limit := rfl
}
"#
}

fn mixed(bad: bool) -> String {
    let mut source = String::from("#![allow(dead_code)]\n");
    for i in 0..3 {
        source.push_str(&format!(
            "pub fn id{i}(x: u8) -> u8 ensures result == x by exact{i} {{ x }}\n"
        ));
    }
    if bad {
        source.push_str("pub fn shift(x: u8) -> u8 { x << 1 }\nclean { theorem refused (x : UInt8) : trust_import_mixed__shift x = x := rfl }\n");
    }
    for i in 0..3 {
        source.push_str(&format!(
            "clean {{ theorem exact{i} (x : UInt8) : trust_import_mixed__id{i} x = x := rfl }}\n"
        ));
    }
    source
}


fn arithmetic_variants() -> String {
    let mut source = String::from("#![allow(dead_code)]\n");
    let mut proofs = String::new();
    for width in [8, 16, 32, 64] {
        for signed in [false, true] {
            let scalar = format!("{}{width}", if signed { "i" } else { "u" });
            let zero = if signed {
                format!("(BitVec.ofNat {width} 0)")
            } else {
                format!("(UInt{width}.ofNat 0)")
            };
            for op in ["add", "sub", "mul"] {
                source.push_str(&format!(r#"
                    pub fn checked_{scalar}_{op}(cost: {scalar}, limit: {scalar}, held: {scalar}) -> bool {{
                        match limit.checked_{op}(held) {{ Some(left) => cost <= left, None => false }}
                    }}
                    pub fn wrap_{scalar}_{op}(cost: {scalar}, limit: {scalar}, held: {scalar}) -> bool {{ cost <= limit.wrapping_{op}(held) }}
                "#));
                for form in ["wrap", "checked"] {
                    proofs.push_str(&format!(r#"
                        theorem {form}_at_zero_{scalar}_{op} :
                            trust_import_variants__{form}_{scalar}_{op} {zero} {zero} {zero} = Bool.true := rfl
                    "#));
                }
            }
        }
    }
    source.push_str(&format!("clean {{\n{proofs}\n}}\n"));
    source
}

fn plain_arithmetic() -> &'static str {
    r#"
#![allow(dead_code)]
pub fn raw_sub(cost: u8, limit: u8, held: u8) -> bool { cost <= limit - held }
clean {
    theorem raw_is_not_unconditionally_total (cost limit held : UInt8) :
        trust_import_plain__raw_sub cost limit held = decide (cost <= limit - held) := rfl
}
"#
}

fn forward_references(bad: bool) -> String {
    let mut source = String::from("#![allow(dead_code)]\n");
    for i in 0..3 {
        source.push_str(&format!("pub fn id{i}(x: u8) -> u8 ensures result == x by exact{i} {{ x }}\n"));
    }
    source.push_str("clean { theorem exact0 (x : UInt8) : trust_import_forward__id0 x = forward_spec x := rfl }\n");
    if bad {
        source.push_str("pub fn shift(x: u8) -> u8 { x << 1 }\nclean { theorem refused (x : UInt8) : trust_import_forward__shift x = x := rfl }\n");
    }
    source.push_str("clean { def forward_spec (x : UInt8) : UInt8 := x }\n");
    for i in 1..3 {
        source.push_str(&format!("clean {{ theorem exact{i} (x : UInt8) : trust_import_forward__id{i} x = x := rfl }}\n"));
    }
    source
}

fn main() {
    for optimization in [0, 3] {
        for mode in ["off", "on"] {
            rfs::write("forward.rs", forward_references(false));
            let forward = rustc()
                .input("forward.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .env_remove("TRUST_NO_VERIFY")
                .arg(format!("-Copt-level={optimization}"))
                .run()
                .stderr_utf8();
            assert_eq!(forward.matches("kernel-discharges this postcondition statement").count(), 3, "forward-reference baseline: {forward}");
            rfs::write("forward.rs", forward_references(true));
            let forward_bad = rustc()
                .input("forward.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .env_remove("TRUST_NO_VERIFY")
                .arg(format!("-Copt-level={optimization}"))
                .run_fail()
                .stderr_utf8();
            assert_eq!(forward_bad.matches("kernel-discharges this postcondition statement").count(), 3, "a refused island broke independent forward references: {forward_bad}");
            rfs::write("variants.rs", arithmetic_variants());
            let variants = rustc()
                .input("variants.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .env_remove("TRUST_NO_VERIFY")
                .arg(format!("-Copt-level={optimization}"))
                .run()
                .stderr_utf8();
            assert!(variants.contains("48 declaration(s) registered"), "all carrier/operator imports must check: {variants}");
            rfs::write("plain.rs", plain_arithmetic());
            let plain = rustc()
                .input("plain.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .arg("-Ztrust-policy=advisory")
                .env_remove("TRUST_NO_VERIFY")
                .arg("-Coverflow-checks=yes")
                .arg(format!("-Copt-level={optimization}"))
                .run_fail()
                .stderr_utf8();
            assert!(plain.contains("NoPanic"), "plain arithmetic must retain its overflow obligation: {plain}");
            rfs::write("room.rs", capacity_room());
            let room = rustc()
                .input("room.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .env_remove("TRUST_NO_VERIFY")
                .arg(format!("-Copt-level={optimization}"))
                .run()
                .stderr_utf8();
            assert!(
                room.contains(
                    "citation `keeps_room_is_exact` kernel-discharges this postcondition statement"
                ),
                "R22 keeps_room contract was not discharged: {room}"
            );
            rfs::write("checked.rs", checked_arithmetic());
            let checked = rustc()
                .input("checked.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .env_remove("TRUST_NO_VERIFY")
                .arg(format!("-Copt-level={optimization}"))
                .run()
                .stderr_utf8();
            for width in [8, 16, 32, 64] {
                assert!(
                    checked.contains(&format!("checked_exact_u{width}")),
                    "checked import u{width}: {checked}"
                );
            }

            rfs::write("arithmetic.rs", arithmetic("sub"));
            let good = rustc()
                .input("arithmetic.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .env_remove("TRUST_NO_VERIFY")
                .arg(format!("-Copt-level={optimization}"))
                .run()
                .stderr_utf8();
            assert!(good.contains("budget_exact"), "{good}");
            rfs::write("arithmetic.rs", arithmetic("add"));
            let mutant = rustc()
                .input("arithmetic.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .env_remove("TRUST_NO_VERIFY")
                .arg(format!("-Copt-level={optimization}"))
                .run_fail()
                .stderr_utf8();
            assert!(
                mutant.contains("did not elaborate"),
                "the imported operator mutant must fail its theorem: {mutant}"
            );
            assert!(
                !mutant.contains("no checked E6 program admission"),
                "the operator mutant must be readable, rather than failing the shape gate: {mutant}"
            );
            rfs::write("mixed.rs", mixed(false));
            let baseline = rustc()
                .input("mixed.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .env_remove("TRUST_NO_VERIFY")
                .arg(format!("-Copt-level={optimization}"))
                .run()
                .stderr_utf8();
            let count = baseline.matches("kernel-discharges this postcondition statement").count();
            assert_eq!(count, 3, "baseline citation count: {baseline}");
            rfs::write("mixed.rs", mixed(true));
            let failed = rustc()
                .input("mixed.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .env_remove("TRUST_NO_VERIFY")
                .arg(format!("-Copt-level={optimization}"))
                .run_fail()
                .stderr_utf8();
            assert!(
                failed.contains("cannot be imported into the Clean kernel"),
                "shape diagnostic missing: {failed}"
            );
            assert_eq!(
                failed.matches("kernel-discharges this postcondition statement").count(),
                count,
                "a refused import changed independent citation count: {failed}"
            );
            assert!(
                !failed.contains("environment is tainted"),
                "crate-wide taint returned: {failed}"
            );
            let bare = mixed(true).replace(
                "theorem refused (x : UInt8) : trust_import_mixed__shift x = x := rfl",
                "theorem refused : trust_import_missing = trust_import_missing := rfl",
            );
            rfs::write("mixed.rs", bare);
            let bare = rustc()
                .input("mixed.rs")
                .crate_type("lib")
                .arg(format!("-Ztrust-verify={mode}"))
                .env_remove("TRUST_NO_VERIFY")
                .arg(format!("-Copt-level={optimization}"))
                .run_fail()
                .stderr_utf8();
            assert!(
                bare.contains("no checked E6 program admission"),
                "an unapplied import was generalized: {bare}"
            );
            assert_eq!(
                bare.matches("kernel-discharges this postcondition statement").count(),
                count,
                "an unapplied missing import tainted independent citations: {bare}"
            );
        }
    }
}
