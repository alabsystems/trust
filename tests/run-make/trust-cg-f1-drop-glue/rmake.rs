//! Trust (step 2 increment 4c, `docs/design/2026-09-29-step2-inc4-drops.md` §4 and §7.3): DROP
//! GLUE AS TRUST-IR, and the resolution of every `Inst::Drop` to a call of it.
//!
//! PART 1 — THE GLUE ORACLE (owner ruling D18 OD-2: synthesized glue splices under D17's rule,
//! structural checks plus THIS test-oracle differential). Channel C of the instance-flip probe
//! runs `drop_glue_oracle::check_glue` on every drop-glue item the collector lists for
//! `corpus.rs`: the synthesized glue's events against rustc's own drop shim
//! (`instance_mir(Shim(DropGlue(T)))`: same `Drop::drop` call, same child drops in the same
//! order per variant), and the synthesized body EXECUTED by trust-ir's reference interpreter on
//! rustc's own tag for every inhabited variant (`tag_for_variant`), its calls required to equal
//! the shim's at rustc's offsets. Every local-closed row must read `glue=match`, and the corpus
//! must report 0 misses, 0 extras, 0 differing rows. Each design §4.3 refusal the corpus reaches
//! is pinned by class. The TEST-ONLY mutation `TRUST_IR_GLUE_MUTATE` shows the oracle is not
//! vacuous: a dropped destructor is a miss, reversed fields an order disagreement, and shifted
//! offsets or skewed tags are caught by EXECUTION alone.
//!
//! PART 2 — THE LANE ON F1 (`-Ztrust-cg-frontend=trust-ir`, the default strict output gate).
//! BEFORE this increment every drop-glue item was refused `[synthesized-instance]` and every
//! drop-bearing body reached the converter with its `Inst::Drop`, refused by name. AFTER: a glue
//! item lowers from its synthesized body; a drop resolves to a call of its glue (the
//! postcondition: no `Inst::Drop` reaches the converter), and a drop whose glue this cut does not
//! synthesize refuses the body naming why. Under a non-strict output-gate policy the lane is
//! inactive and everything is as before (D17's condition).

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

fn channel_c(mutation: Option<&str>) -> String {
    let mut cmd = rustc();
    cmd.input("corpus.rs")
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ccodegen-units=1")
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-instance-flip-probe=*")
        .out_dir("probe");
    if let Some(m) = mutation {
        cmd.env("TRUST_IR_GLUE_MUTATE", m);
    }
    cmd.run().stderr_utf8()
}

fn summary_field(stderr: &str, field: &str) -> usize {
    let line = stderr
        .lines()
        .find(|l| l.starts_with("TRUST-WALLA-PROBE C summary"))
        .unwrap_or_else(|| panic!("channel C printed no summary:\n{stderr}"));
    line.split_whitespace()
        .find_map(|kv| kv.strip_prefix(&format!("{field}=")))
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| panic!("summary has no `{field}`: {line}"))
}

/// The glue rows, by the type they drop (`args=[T]`, rendered by rustc).
fn glue_rows(stderr: &str) -> Vec<(String, String)> {
    stderr
        .lines()
        .filter(|l| l.starts_with("TRUST-WALLA-PROBE C sym=") && l.contains(" kind=shim-drop-glue "))
        .map(|l| {
            let glue = l.split_whitespace().find_map(|kv| kv.strip_prefix("glue=")).unwrap_or("");
            let args = l.split(" args=").nth(1).unwrap_or("").to_string();
            (args, glue.to_string())
        })
        .collect()
}

fn verdict<'a>(rows: &'a [(String, String)], ty: &str) -> &'a str {
    let found: Vec<&(String, String)> = rows.iter().filter(|(args, _)| args == ty).collect();
    assert_eq!(found.len(), 1, "exactly one glue row drops `{ty}`: {rows:#?}");
    &found[0].1
}

/// The types of the corpus whose glue is synthesized and must agree with rustc's shim.
const LOCAL_CLOSED: &[&str] = &[
    "[A]",
    "[B]",
    "[E]",
    "[M]",
    "[N]",
    "[R]",
    "[U]",
    "[A2]",
    "[Md]",
    "[Empty]",
    "[Never]",
    "[Outer]",
    "[Single]",
    "[std::option::Option<A>]",
    "[(A, u8, B, (Empty, A))]",
    "[(Empty, A)]",
    "[[A; 3_usize]]",
    "[[A]]",
    "[[Outer; 2_usize]]",
    "[[Outer]]",
    "[[[Outer; 2_usize]; 2_usize]]",
    "[[[Outer; 2_usize]]]",
];

fn f1(input: &str, out: &str, extra: &[&str]) -> run_make_support::Rustc {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input(input)
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .args(extra)
        .out_dir(out)
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

fn main() {
    // ── PART 1: the oracle over the corpus ─────────────────────────────────────────────────
    let probe = channel_c(None);
    let rows = glue_rows(&probe);
    for ty in LOCAL_CLOSED {
        assert_eq!(verdict(&rows, ty), "match", "the glue of `{ty}` must agree with rustc's shim");
    }
    let closure = rows
        .iter()
        .filter(|(args, _)| args.starts_with("[Closure(") && args.contains("drop_closure"))
        .collect::<Vec<_>>();
    assert_eq!(closure.len(), 1, "one closure environment's glue: {rows:#?}");
    assert_eq!(closure[0].1, "match", "a closure environment's glue agrees with rustc's shim");
    // The refusals of design §4.3 the corpus reaches, by class.
    assert_eq!(verdict(&rows, "[std::boxed::Box<A, std::alloc::Global>]"), "refused-upstream-body");
    assert_eq!(verdict(&rows, "[std::vec::Vec<u8, std::alloc::Global>]"), "refused-upstream-body");
    assert_eq!(verdict(&rows, "[Packed]"), "refused-shape");
    let coroutine = rows.iter().filter(|(args, _)| args.starts_with("[Coroutine(")).collect::<Vec<_>>();
    assert_eq!(coroutine.len(), 1, "{rows:#?}");
    assert_eq!(coroutine[0].1, "refused-shape", "a coroutine's glue is refused by shape");
    assert!(probe.contains("coroutine glue (`coroutine_drop`)"), "the refusal names why:\n{probe}");
    assert!(
        probe.contains("as std::ops::Drop>::drop` is in crate `alloc`"),
        "an `alloc` destructor is an upstream body:\n{probe}"
    );
    for field in ["glue_differs", "glue_misses", "glue_extras", "glue_oracle_failed", "panics"] {
        assert_eq!(summary_field(&probe, field), 0, "`{field}` must be 0:\n{probe}");
    }
    assert!(summary_field(&probe, "glue_match") >= LOCAL_CLOSED.len() + 1);

    // The oracle is not vacuous: each TEST-ONLY mutation of the producer is caught.
    for (mutation, needle) in [
        ("drop-dtor", "misses=[Destructor"),
        ("reverse-fields", "order_agrees=false"),
        ("shift-offsets", "executed=Err("),
        ("skew-tags", "executed=Err("),
    ] {
        let mutated = channel_c(Some(mutation));
        let differs = summary_field(&mutated, "glue_differs");
        assert!(differs > 0, "`{mutation}`: the oracle must catch it:\n{mutated}");
        assert!(
            mutated.lines().any(|l| l.contains("glue-detail") && l.contains(needle)),
            "`{mutation}`: a differing row names `{needle}`:\n{mutated}"
        );
        if matches!(mutation, "shift-offsets" | "skew-tags") {
            // Invisible to the structural comparison: only the executed glue disagrees.
            assert_eq!(summary_field(&mutated, "glue_misses"), 0, "{mutated}");
            assert_eq!(summary_field(&mutated, "glue_extras"), 0, "{mutated}");
        }
    }

    // ── PART 2: the lane on F1 ─────────────────────────────────────────────────────────────
    part2();
}

/// The refusal lines of a refused F1 compile that name `needle` (a symbol fragment).
fn refusal_line<'a>(stderr: &'a str, needle: &str) -> &'a str {
    stderr
        .lines()
        .find(|l| l.contains("e.g.") && l.contains(needle))
        .unwrap_or_else(|| panic!("no refusal names `{needle}`:\n{stderr}"))
}

fn part2() {
    // (1) RESOLVED: under the default strict gate `make`'s drop became a call of the synthesized
    // glue, so the converter refuses the CALL (no real calls before increment 5), never the
    // `Drop`: the postcondition, seen from outside. Trust (BMC-LANE-1 step 1b): `_t`'s slot is
    // handed to that call by pointer, so the converter's aggregate-slot walk is what refuses the
    // `Call`, before the instruction mapper would.
    let strict = f1("resolve.rs", "resolve-strict", &[]).run_fail().stderr_utf8();
    let make = refusal_line(&strict, "7resolve4make");
    assert!(
        make.contains("unsupported memory shape") && make.contains("is used by `Call`"),
        "the drop is a glue call: {make}"
    );
    assert!(
        !strict.contains("unsupported instruction `Drop`"),
        "no `Inst::Drop` reaches the converter under the strict gate:\n{strict}"
    );
    // The glue ITEM lowers from its synthesized body; what refuses it now is the F1 ABI lane's
    // coverage of its `&mut T` argument, not the absence of a body.
    let glue = refusal_line(&strict, "9drop_glue");
    assert!(glue.contains("unsupported ABI type/pass mode `&mut T`"), "{glue}");
    assert!(!strict.contains("[synthesized-instance]"), "{strict}");

    // (2) INACTIVE under a non-strict policy (D17's condition): exactly as before 4c.
    let relaxed = f1("resolve.rs", "resolve-allow", &["-Ztrust-cg-output-gate=allow-unknown"])
        .run_fail()
        .stderr_utf8();
    let make = refusal_line(&relaxed, "7resolve4make");
    // Trust (BMC-LANE-1 step 1b): the `Drop` takes `_t`'s slot by pointer, so the aggregate-slot
    // walk names it.
    assert!(
        make.contains("unsupported memory shape") && make.contains("is used by `Drop`"),
        "the floor refuses by name: {make}"
    );
    let glue = refusal_line(&relaxed, "9drop_glue");
    assert!(glue.contains("Shim(DropGlue("), "the glue item is synthesized-instance: {glue}");

    // (3) REFUSAL PINS (design §4.3), each naming why, under the strict gate.
    // A destructor the producer declined: no admitted body for the glue to call.
    let declined = f1("declined.rs", "declined", &[]).run_fail().stderr_utf8();
    let make2 = refusal_line(&declined, "8declined5make2");
    assert!(declined.contains("[producer-declined]"), "{declined}");
    assert!(
        make2.contains(
            "drop of `A` does not resolve: its destructor `<A as std::ops::Drop>::drop` has no \
             admitted handoff body"
        ),
        "{make2}"
    );
    // A shape this cut does not synthesize.
    let packed = f1("packed.rs", "packed", &[]).run_fail().stderr_utf8();
    let mk = refusal_line(&packed, "6packed2mk");
    assert!(packed.contains("[synthesized-instance]"), "{packed}");
    assert!(mk.contains("`P` is a packed struct with a needs-drop field"), "{mk}");
    // A destructor in another crate: `[upstream-body]` (increment 6).
    rustc()
        .input("dep.rs")
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .out_dir("dep-out")
        .run();
    let user = f1("user.rs", "user", &[]).extern_("dep", "dep-out/libdep.rlib").run_fail().stderr_utf8();
    let consume = refusal_line(&user, "4user7consume");
    assert!(user.contains("[upstream-body]"), "{user}");
    assert!(
        consume.contains(
            "drop of `dep::Fd` does not resolve: the destructor `<dep::Fd as std::ops::Drop>::drop` \
             is in crate `dep`"
        ),
        "{consume}"
    );
}
