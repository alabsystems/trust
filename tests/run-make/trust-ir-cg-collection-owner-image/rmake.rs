//! A struct that OWNS a slot-modeled collection (`Nat { limbs: Vec<u64> }`,
//! `Name { s: String }`) crossing a by-value boundary is REFUSED by
//! trust-ir-cg with a refusal that names the class and the fix, and the
//! fixture it is refused on is CORRECT (it runs and asserts values on the LLVM
//! lane), so the day the inline-collection-image lane lands this file flips
//! from a refusal pin to a value pin by editing only `main` below.
//!
//! The refusal that stopped the stage1 `library/std` build at `trust-bignum`
//! (21 functions, every one of which returns a `Nat` by value) and at
//! `addr2line::demangle_auto` (the `String` twin):
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... memory aggregate leaf
//!            alloc::vec::Vec<u64, alloc::alloc::Global> is not a single scalar
//!            (wide/fat or non-scalar ABI)
//!
//! raised from `classify_func_ty` -> `memory_aggregate_layout` ->
//! `validate_memory_aggregate_field_leaves` on the RETURN type `Nat`, before a
//! single statement of the body is looked at. The walker's text named itself:
//! a `Vec` IS one scalar in this backend's model — the ADDRESS of its own
//! `{ptr,cap,len}` frame slot — which is exactly why it must never be written
//! into an aggregate's memory image (the [TCG-BOX-SLOT-ESCAPE] class), and why
//! a rustc-layout byte image would not do either (rustc orders `Vec<u64>` as
//! `{cap, ptr, len}`; the slot model as `{ptr, cap, len}`). The backend has no
//! representation for an aggregate that owns a collection, and now says so as
//! `[TCG-COLLECTION-IMAGE]` with the options.
//!
//! UPDATE (trust-cg bc26bd820, pinned by 990826872e). A bare default-Global
//! `Vec`/`String` local is no longer slot-modeled: it is a checked standalone
//! header laid out by rustc. The CONTAINING aggregate still has no qualified
//! inline image, so `Nat`/`Name` keep refusing with the same class, now worded
//! "... do not yet share a qualified inline image ... Failing closed; extend the
//! containing aggregate transport using rustc's actual layout and ownership
//! semantics" — the remedy replaced the old "Options: (1) ..." list. The pin
//! below tracks the class, the type, the reason and the fail-closed remedy.
//!
//! This is the FIRST of several gates on the shape. Measured on the bare
//! `Vec<u64>` twin with the same compiler: a by-value `Vec` RETURN is refused
//! at `TerminatorKind::Return` ("returning an intercepted collection ... would
//! escape its frame-local {ptr,cap,len} slot"), and the -O3 `vec![x]` body is
//! refused on `PointerCoercion::Unsize ... Box<[u64]>`. So the refusal text is
//! what this test pins; the VALUES are pinned on the LLVM control so the
//! fixture is known-good before any lane claims it.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

const FIXTURE: &str = r#"
pub struct Nat { limbs: Vec<u64> }
pub struct Name { s: String }

impl Nat {
    pub const ZERO: Nat = Nat { limbs: Vec::new() };
    #[inline(never)]
    pub fn from_u64(v: u64) -> Nat {
        if v == 0 { Nat::ZERO } else { Nat { limbs: vec![v] } }
    }
    #[inline(never)]
    pub fn from_limbs(mut limbs: Vec<u64>) -> Nat {
        while limbs.last() == Some(&0) { limbs.pop(); }
        Nat { limbs }
    }
    #[inline(never)]
    pub fn add_limb(&self, x: u64) -> Nat {
        let mut limbs = self.limbs.clone();
        limbs.push(x);
        Nat::from_limbs(limbs)
    }
    #[inline(never)]
    pub fn limbs(&self) -> &[u64] { &self.limbs }
}

#[inline(never)]
pub fn make_name(n: u64) -> Name { Name { s: format!("n{n}") } }
#[inline(never)]
pub fn name_len(n: &Name) -> usize { n.s.len() }

fn main() {
    // Values, not just "it ran": the length lane, the contents behind the data
    // lane, the empty (dangling-pointer) const image, and a drop at scope end.
    let z = Nat::from_u64(0);
    assert_eq!(z.limbs().len(), 0);
    let a = Nat::from_u64(7);
    assert_eq!(a.limbs(), &[7]);
    let b = a.add_limb(9);
    assert_eq!(b.limbs(), &[7, 9]);
    let c = Nat::from_limbs(vec![1, 0, 0]);
    assert_eq!(c.limbs(), &[1]);
    let n = make_name(42);
    assert_eq!(name_len(&n), 3);
    drop(b);
    drop(c);
    println!("collection-owner round trips ok");
}
"#;

fn main() {
    rfs::write("owner.rs", FIXTURE);

    for level in ["0", "3"] {
        // The CONTROL: the same fixture through the default backend RUNS and
        // asserts every value. A refusal pinned on a wrong fixture pins nothing.
        let control = format!("owner_llvm_o{level}");
        rustc()
            .input("owner.rs")
            .crate_type("bin")
            .crate_name(&control)
            .opt_level(level)
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .panic("abort")
            .run();
        run(&control).assert_stdout_contains("collection-owner round trips ok");

        // The SUBJECT: trust-ir-cg refuses, names the class, carries the fix,
        // and no longer blames the leaf walker. When the inline-collection-image
        // lane lands, replace `run_fail()` + the stderr asserts with `.run()`
        // and `run(&subject).assert_stdout_contains(..)` — nothing else changes.
        let subject = format!("owner_tcg_o{level}");
        rustc()
            .input("owner.rs")
            .crate_type("bin")
            .crate_name(&subject)
            .opt_level(level)
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            // The verifier is a separate axis; this test is about codegen alone.
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .panic("abort")
            .run_fail()
            .assert_stderr_contains("[TCG-MIR-UNSUPPORTED]")
            .assert_stderr_contains("[TCG-COLLECTION-IMAGE]")
            .assert_stderr_contains("Vec<u64")
            .assert_stderr_contains("do not yet share a qualified inline image")
            .assert_stderr_contains("Failing closed; extend the containing aggregate transport")
            .assert_stderr_not_contains("is not a single scalar (wide/fat or non-scalar ABI)");
    }
}
