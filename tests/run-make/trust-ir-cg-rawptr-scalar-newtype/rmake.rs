//! `&raw const/mut` of a POINTER-NEWTYPE local — one field, a thin reference —
//! yields the local's REAL address at -O0 and -O3, and the remaining deliberate
//! exclusions keep refusing BY NAME.
//!
//! THE GAP. `rust_ty_to_trust_ir_ty` maps `struct Ref1<'a>(&'a u64)` to ONE POINTER
//! scalar. That single fact steered the local away from BOTH address mechanisms:
//!
//!   * `compute_scalar_cell_locals`' `RawPtr`-referent pass cells a referent only
//!     when its scalar is NOT pointer-like (the clause that keeps `Vec`-as-`Ptr`
//!     off the cell path), and
//!   * `compute_memory_backed_locals` rule (4h) needs `memory_backed_local_layout`,
//!     which returns `None` for every type the scalar mapping accepts.
//!
//! So the local had no address at all, and BOTH spellings failed closed:
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... Rvalue::RawPtr (unsupported &raw shape:
//!            source local _6 projection [Deref] type &Show<'_, Nat>;
//!            base bound=false entry_arg=false)
//!
//! measured as a REFUSAL, never a wrong address — while the same struct with a
//! NON-pointer leaf (`struct N(u64)`) compiled and ran correctly through that very
//! pass. This is the shape `trust-ir-cg-formatter-write-fmt`'s own positive leg
//! needs: `Argument::new_display::<Show<'_, Nat>>` inlines to `&raw const (*_6)`
//! where `_6 = &_7` and `_7: Show<'_, Nat>` is exactly such a newtype, and
//! `<Show as Display>::fmt` later reads `(*self).0` back through the pointer stored
//! in the `Argument`.
//!
//! WHAT THE CELL BUYS. Field 0's storage IS the whole local's storage for this shape
//! (the property `local_is_single_scalar_storage` names), so the cell holds the
//! local's own bytes at its own address — precisely what `&raw` must hand out.
//! Case (3) is what makes that testable: the pointer must observe a LATER write to
//! the local (`before*10 + after` = 19), which a copy taken at `&raw` time could not
//! deliver; case (4) asserts the pointer IS `&s as *const _`.
//!
//! THE EXCLUSIONS, pinned as refusals so widening any of them is deliberate (the
//! `Vec<u64>` one has been CLOSED and is now a positive value pin; see below):
//!
//!   * `Box<u64>` — a needs-drop single-scalar local. `lower_drop_terminator`
//!     resolves the pointer through the local's own binding, so the cell is not
//!     taken and the `&raw` keeps refusing.
//!   * `Vec<u64>` — CLOSED by trust-cg bc26bd820 (pinned by 990826872e). It was
//!     slot-modeled: its one `Ptr` was the address of the bridge's `{ptr,cap,len}`
//!     FRAME SLOT, not the vector's bytes, so a cell would have handed out the wrong
//!     object. A bare default-Global `Vec` local is now a checked standalone header
//!     laid out by rustc, so `&raw const v` names the real header. Per the rule
//!     below, the case became a positive assertion rather than being deleted: the
//!     pointer must be the local's own address (identity), and reading the length
//!     AND the elements through it must match the LLVM control at -O0 and -O3.
//!   * a PROJECTED WRITE through the pointer (`(*p).0 = r`): once the local is
//!     celled, `checked_scalar_cell_projection` demands an exact zero-offset,
//!     full-allocation PRIMITIVE scalar field chain, and a reference field is not
//!     primitive — so it refuses with [TCG-SCALAR-CELL-LAYOUT] rather than storing
//!     through a cell it cannot prove aliases the field exactly. Reads through the
//!     pointer and whole-local writes are unaffected (cases 1-6).
//!
//! Every negative carries an LLVM control, so a refusal can never be confused with a
//! broken fixture. If an exclusion is ever closed, replace the case with the positive
//! assertion — do not delete it.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

const POS: &str = r#"
// A POINTER-NEWTYPE: one field, a thin reference. `rust_ty_to_trust_ir_ty` maps it
// to ONE pointer scalar, which is exactly why `&raw` of it had no address.
struct Ref1<'a>(&'a u64);
// The same shape over a RAW pointer, with a ZST sibling field.
struct Cur(*const u8, ());

#[inline(never)]
fn read_ref1(p: *const Ref1<'_>) -> u64 { unsafe { *(*p).0 } }
#[inline(never)]
fn read_cur(p: *const Cur) -> u8 { unsafe { *(*p).0 } }

// (1) `&raw const s` DIRECTLY of the newtype local.
#[inline(never)]
fn direct(n: u64) -> u64 { let v = n; let s = Ref1(&v); read_ref1(&raw const s) }

// (2) `&raw const (*r)` THROUGH a reference to the newtype local — the
// `Argument::new_display::<Show<..>>(&Show(..))` shape that stopped `render_all`.
#[inline(never)]
fn via_ref(n: u64) -> u64 { let v = n; let s = Ref1(&v); let r = &s; read_ref1(r) }

// (3) ALIASING, read direction: the pointer must observe a LATER write to the
// local itself. A materialized copy taken at `&raw` time would return the OLD
// value here, so this is what proves the pointer addresses the real object.
#[inline(never)]
fn observes_later_write(a: u64, b: u64) -> u64 {
    let x = a;
    let y = b;
    let mut s = Ref1(&x);
    let p = &raw const s;
    let before = read_ref1(p);
    s = Ref1(&y);
    let after = read_ref1(p);
    before * 10 + after
}

// (4) IDENTITY: the raw pointer is the local's own address, not a copy.
#[inline(never)]
fn identity(n: u64) -> u64 {
    let v = n;
    let s = Ref1(&v);
    let p = &raw const s;
    let q = &s as *const Ref1<'_>;
    (p == q) as u64
}

// (5) The raw-pointer newtype with a ZST sibling, through a reference.
#[inline(never)]
fn cur_via_ref(b: u8) -> u8 { let v = b; let c = Cur(&v as *const u8, ()); let r = &c; read_cur(r) }

// (6) An ENTRY-ARG reference (worked before the fix; pinned so it keeps working).
#[inline(never)]
fn via_param(s: &Ref1<'_>) -> u64 { read_ref1(s) }

fn main() {
    let n = std::hint::black_box(42u64);
    println!("{}", direct(n));
    println!("{}", via_ref(n));
    println!("{}", observes_later_write(std::hint::black_box(1), std::hint::black_box(9)));
    println!("{}", identity(n));
    println!("{}", cur_via_ref(std::hint::black_box(7u8)));
    let v = std::hint::black_box(5u64);
    println!("{}", via_param(&Ref1(&v)));
}
"#;

const BOXED: &str = r#"
// A NEEDS-DROP single-scalar local: `Box<u64>` maps to one pointer scalar too, but
// the drop lane resolves the pointer through the local's OWN binding, so the cell is
// NOT taken for it and `&raw const b` keeps refusing BY NAME.
#[inline(never)]
fn read(p: *const Box<u64>) -> u64 { unsafe { **p } }
#[inline(never)]
fn f(n: u64) -> u64 { let b = Box::new(n); read(&raw const b) }
fn main() { println!("{}", f(std::hint::black_box(42))); }
"#;

const VECED: &str = r#"
// A bare default-Global `Vec<u64>` local: once slot-modeled (its single `Ptr` was the
// address of a `{ptr,cap,len}` frame slot), now a checked standalone header. The
// raw pointer must address the REAL header: (1) the length, (2) the elements read
// back through it, and (3) identity with `&v as *const _`.
#[inline(never)]
fn len_of(p: *const Vec<u64>) -> u64 { unsafe { (*p).len() as u64 } }
#[inline(never)]
fn sum_of(p: *const Vec<u64>) -> u64 { unsafe { (*p).iter().sum() } }
#[inline(never)]
fn f(n: u64) -> u64 { let v = vec![n, n + 1, n + 2]; len_of(&raw const v) }
#[inline(never)]
fn g(n: u64) -> u64 { let v = vec![n, n + 10, n + 100]; sum_of(&raw const v) }
#[inline(never)]
fn h(n: u64) -> u64 {
    let v = vec![n, n];
    let p = &raw const v;
    let q = &v as *const Vec<u64>;
    (p == q) as u64
}
fn main() {
    println!("{}", f(std::hint::black_box(1)));
    println!("{}", g(std::hint::black_box(1)));
    println!("{}", h(std::hint::black_box(1)));
}
"#;

/// What `veced.rs` prints (LLVM backend, -O0 and -O3): `f`, `g`, `h`.
const VECED_STDOUT: &str = "3\n113\n1\n";

const PROJWRITE: &str = r#"
// A PROJECTED WRITE through the raw pointer of a celled pointer-newtype:
// `(*p).0 = r`. Once the local is celled, `checked_scalar_cell_projection`
// requires an exact zero-offset, full-allocation PRIMITIVE scalar field chain,
// and a reference field is not primitive — so this refuses BY NAME rather than
// storing through a cell it cannot prove aliases the field exactly.
struct Ref1<'a>(&'a u64);
#[inline(never)]
fn opaque<'a>(r: &'a u64) -> &'a u64 { std::hint::black_box(r) }
#[inline(never)]
fn f(a: u64, b: u64) -> u64 {
    let x = a;
    let y = b;
    let mut s = Ref1(&x);
    let p = &raw mut s;
    unsafe { (*p).0 = opaque(&y); }
    *s.0
}
fn main() { println!("{}", f(std::hint::black_box(1), std::hint::black_box(9))); }
"#;

/// What `pos.rs` prints (measured under the LLVM backend at -O0 and -O3):
/// `direct`, `via_ref`, `observes_later_write`, `identity`, `cur_via_ref`, `via_param`.
const POS_STDOUT: &str = "42\n42\n19\n1\n7\n5\n";

fn main() {
    rfs::write("pos.rs", POS);
    rfs::write("boxed.rs", BOXED);
    rfs::write("veced.rs", VECED);
    rfs::write("projwrite.rs", PROJWRITE);

    for opt in ["0", "3"] {
        // POSITIVE. The LLVM control first: the fixture is valid Rust with the
        // stated answers, so a trust-ir-cg difference can only be the backend.
        let control = format!("pos_llvm{opt}");
        rustc()
            .input("pos.rs")
            .crate_type("bin")
            .crate_name("pos")
            .output(&control)
            .opt_level(opt)
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run();
        let want = run(&control).stdout_utf8();
        assert_eq!(
            want, POS_STDOUT,
            "the LLVM control disagrees with the expected values at -O{opt}; the fixture changed"
        );

        let bin = format!("pos{opt}");
        rustc()
            .input("pos.rs")
            .crate_type("bin")
            .crate_name("pos")
            .output(&bin)
            .opt_level(opt)
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here
            // with [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            // The verifier is a separate axis; this test is about codegen alone.
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            // Unwinding is not the subject.
            .arg("-Cpanic=abort")
            .run();
        assert_eq!(
            run(&bin).stdout_utf8(),
            want,
            "trust-ir-cg -O{opt}: a `&raw` of a pointer-newtype local produced the wrong \
             address (case 3 fails when the pointer addresses a copy, case 4 when it is \
             not the local's own address)"
        );

        // The CLOSED `Vec` exclusion, now a positive value pin. Control first.
        let veced_control = format!("veced_llvm{opt}");
        rustc()
            .input("veced.rs")
            .crate_type("bin")
            .crate_name("veced")
            .output(&veced_control)
            .opt_level(opt)
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run();
        let veced_want = run(&veced_control).stdout_utf8();
        assert_eq!(
            veced_want, VECED_STDOUT,
            "the LLVM control disagrees with the expected veced values at -O{opt}"
        );
        let veced_bin = format!("veced{opt}");
        rustc()
            .input("veced.rs")
            .crate_type("bin")
            .crate_name("veced")
            .output(&veced_bin)
            .opt_level(opt)
            .arg("-Zcodegen-backend=trust-ir-cg")
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run();
        assert_eq!(
            run(&veced_bin).stdout_utf8(),
            veced_want,
            "trust-ir-cg -O{opt}: `&raw const` of a Vec<u64> local did not address the real \
             header (wrong length, wrong elements, or not the local's own address)"
        );

        // NEGATIVE, one per remaining exclusion. Control first, then the refusal BY NAME.
        for (name, src, diagnostic) in [
            ("boxed", "boxed.rs", "Rvalue::RawPtr (unsupported &raw shape:"),
            ("projwrite", "projwrite.rs", "[TCG-SCALAR-CELL-LAYOUT]"),
        ] {
            let neg_control = format!("{name}_llvm{opt}");
            rustc()
                .input(src)
                .crate_type("bin")
                .crate_name(name)
                .output(&neg_control)
                .opt_level(opt)
                .arg("-Ztrust-verify=off")
                .arg("-Cdebuginfo=0")
                .arg("-Cpanic=abort")
                .run();
            let neg_want = run(&neg_control).stdout_utf8();
            assert!(!neg_want.is_empty(), "{name}: the LLVM control printed nothing");

            rustc()
                .input(src)
                .crate_type("bin")
                .crate_name(name)
                .output(&format!("{name}{opt}"))
                .opt_level(opt)
                .arg("-Zcodegen-backend=trust-ir-cg")
                .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
                .arg("-Ztrust-verify=off")
                .arg("-Cdebuginfo=0")
                .arg("-Cpanic=abort")
                .run_fail()
                .assert_stderr_contains("[TCG-MIR-UNSUPPORTED]")
                .assert_stderr_contains(diagnostic);
        }
    }
}
