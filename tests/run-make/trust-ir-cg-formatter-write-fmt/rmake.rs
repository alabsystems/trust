//! A `Formatter`-receiver `write!(f, ..)` — the body of every `Display`/`Debug`
//! impl — compiles under trust-ir-cg and writes the right bytes; a body that
//! mixes it with an intercepted `format!` keeps both lanes apart; and a
//! recognised consumer whose interception DECLINES fails closed by name.
//!
//! Regression pin for the refusal that stopped the stage1 build at
//! `trust-bignum` (`<Nat as Debug>::fmt`, `<ParseNatError as Display>::fmt`):
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... Ty::core::fmt::rt::ArgumentType<'{erased}>
//!
//! raised for the -O3-inlined `Formatter::write_fmt`, whose `Arguments::as_str`
//! probes the low bit of the argument-array pointer (`_22 = copy _8 as usize
//! (Transmute)`) while the chain that builds the `Arguments` had been seeded dead
//! by TYPE. The fix takes the per-use proof (`fmt_locals_proved_only_intercepted`)
//! for every crate, gives the plumbing types their rustc layout, and fails closed
//! by name (`[TCG-FMT-DECLINED]`) when a recognised consumer declines.
//!
//! TWO GAPS, ONE LANDABLE UNIT. Once that chain is live, the body of
//! `Formatter::write_fmt` — a LOCAL mono item at -O0 (`-Zprint-mono-items`
//! lists `std::fmt::Formatter::<'_>::write_fmt @@ ..[Internal]`) and inlined into
//! each impl at -O3 — is lowered, and its `self.buf.write_str(s)` arm is
//!
//!     _0 = <dyn core::fmt::Write>::write_str(..)   // `_0: fmt::Result`, memory-backed
//!
//! which `lower_virtual_call_terminator` refused ("virtual call returning a
//! by-value aggregate into a memory-backed destination is not yet supported") at
//! BOTH opt levels. That lane now stores the result exactly as the direct lane
//! does; its own pin is `trust-ir-cg-virtual-call-memory-dest`. Neither half
//! turns this test green alone.
//!
//! CASES.
//!
//! 1. `fmtwrite.rs` RUNS at -O0 and -O3 and its STDOUT must equal the LLVM
//!    control's, which must itself equal the literal below: a checksum and the
//!    length of the bytes `core::fmt::write` delivered to a custom sink (the
//!    hazard class is an `Arguments` nothing built — garbage template/args
//!    pointers — so the delivered bytes are the thing to assert), the program also
//!    exits non-zero on any byte mismatch, and the intercepted `println!` lane is
//!    checked unchanged.
//!
//! 2. The MIXED body (`Mixed::render`): one function containing BOTH a recognised
//!    -O3 `format!` consumer (`Option::<&str>::map_or_else`, decoded statically,
//!    its `as_str` niche switch replaced by a branch) AND two live
//!    `Formatter`-receiver `write!`s, each with its own `as_str` bit-test. The
//!    niche-switch replacement must claim only the switch whose arms fall straight
//!    into the recognised `map_or_else` (`compute_fmt_niche_switch_blocks`). A MIR
//!    guard asserts -O3 still produces that shape, so the case cannot silently
//!    stop exercising the interaction after an upstream MIR change.
//!
//! 3. `decline.rs`: `println!("{:?}", x)` reaches the recognised `_print`
//!    consumer, whose interception declines the `{:?}` placeholder. It used to be
//!    fail-closed only BY ACCIDENT (the type gate, `Ty::..ArgumentType`); it must
//!    refuse with `[TCG-FMT-DECLINED]` rather than hand std a never-built
//!    `Arguments`. The LLVM control proves the fixture itself is fine. If the
//!    interception ever learns `{:?}`, replace the placeholder with another shape
//!    it declines — do not delete the case.
//!
//! Known residual (NOT covered here, refuses by name at -O3): a placeholder over
//! a `&&T` inlines `Argument::new_display::<&T>` to `&raw const *r` of a
//! register-held reference local — outside the fmt seam.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

const FMTWRITE: &str = r#"
use std::fmt;
use std::hint::black_box;

/// A custom sink (never `Any`, never `String` — a `String` receiver IS
/// intercepted and would not exercise the seam). Bytes land in a fixed buffer so
/// the test asserts CONTENT, not merely that the program ran.
struct Sink { buf: [u8; 128], len: usize }
impl fmt::Write for Sink {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for &b in s.as_bytes() {
            if self.len >= self.buf.len() { return Err(fmt::Error); }
            self.buf[self.len] = b;
            self.len += 1;
        }
        Ok(())
    }
    // Overridden (ASCII only) so the `dyn Write` vtable this sink is dispatched
    // through does not carry the default `write_char` (`encode_utf8` into a stack
    // buffer), a separate memory-slice gap outside the fmt seam. `{:?}` of a
    // `char` DOES call it (the quotes), from precompiled core.
    fn write_char(&mut self, c: char) -> fmt::Result {
        let v = c as u32;
        if v >= 0x80 || self.len >= self.buf.len() { return Err(fmt::Error); }
        self.buf[self.len] = v as u8;
        self.len += 1;
        Ok(())
    }
}

/// A custom trait whose method takes the `Formatter` — the receiver shape under
/// test — so no std trait is the subject.
trait Render { fn render(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result; }

struct Nat(u64);
impl Render for Nat {
    // `<Nat as Debug>::fmt` in trust-bignum: one `{}` placeholder.
    fn render(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "Nat({})", self.0) }
}
struct Pair { a: u32, c: char }
impl Render for Pair {
    // Two placeholders, `Display` and `Debug`, of values behind `&self`.
    fn render(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "a={} c={:?}", self.a, self.c)
    }
}
struct Plain;
impl Render for Plain {
    // Zero placeholders: the tagged-literal `Arguments` encoding
    // (`args = (len << 1) | 1`), whose `as_str` bit-test TAKES the `write_str` arm.
    fn render(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "plain") }
}
struct Text(&'static str);
impl Render for Text {
    // A `&str` placeholder: a fat-pointer value behind the `Argument`.
    fn render(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "<{}>", self.0) }
}
struct Mixed(u64);
impl Render for Mixed {
    // The MIXED body: an intercepted -O3 `format!` (`map_or_else` consumer) and
    // two live `Formatter`-receiver `write!`s in ONE function. `v` is a value
    // local because the interception decodes a placeholder only over a value
    // local. The first `write!`'s result is deliberately ignored and the second is
    // the tail, so no user code branches on a result.
    #[inline(never)]
    fn render(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let v = self.0;
        let s = format!("m{}", v);
        f.write_str(&s)?;
        let _ = write!(f, "plain");
        write!(f, "<{}>", s.len())
    }
}

/// `Display` adapter so a `Render` value can be formatted by `core::fmt::write`.
struct Show<'a, T: ?Sized>(&'a T);
impl<T: Render + ?Sized> fmt::Display for Show<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.render(f) }
}

#[inline(never)]
fn render_all(sink: &mut Sink, n: u64) -> fmt::Result {
    // `core::fmt::write(&mut dyn Write, Arguments)` DIRECTLY: the same
    // un-intercepted consumer, one level up, with a user-type placeholder that
    // the interception could never synthesize.
    fmt::write(sink, format_args!("{}|", Show(&Nat(n))))?;
    fmt::write(sink, format_args!("{}|", Show(&Pair { a: 7, c: 'x' })))?;
    fmt::write(sink, format_args!("{}|", Show(&Plain)))?;
    fmt::write(sink, format_args!("{}|", Show(&Text("hi"))))?;
    fmt::write(sink, format_args!("{}", Show(&Mixed(n))))
}

fn main() {
    let mut sink = Sink { buf: [0; 128], len: 0 };
    if render_all(&mut sink, black_box(42)).is_err() { std::process::exit(2); }
    let got = &sink.buf[..sink.len];
    let want: &[u8] = b"Nat(42)|a=7 c='x'|plain|<hi>|m42plain<3>";
    if got != want {
        // A wrong LENGTH or wrong BYTES both mean an `Arguments` that was not
        // built (or a switch steered to the wrong arm); exit distinctly so the
        // failure names itself.
        std::process::exit(if got.len() != want.len() { 3 } else { 4 });
    }
    // A checksum of the collected bytes, printed so the test compares the VALUE
    // against the LLVM control's stdout, not only the exit status.
    let mut h: u64 = 0;
    let mut i = 0;
    while i < sink.len {
        h = h.wrapping_mul(31).wrapping_add(sink.buf[i] as u64);
        i += 1;
    }
    println!("{}", h);
    // Bound first: `println!` of a field place is a separate refused lane
    // ("format! arg reference does not trace to a value local").
    let len = sink.len;
    println!("{}", len);
    // The intercepted lane (`println!` of an integer) must be unchanged.
    println!("{}", 12345u64);
    println!("formatter write_fmt ok");
}
"#;

const DECLINE: &str = r#"
use std::hint::black_box;
// `{:?}` is a placeholder the `_print` interception does not synthesize.
#[inline(never)]
fn pd(x: u64) { println!("{:?}", x); }
fn main() { pd(black_box(7)); }
"#;

/// What `fmtwrite` prints (measured under the LLVM backend at -O0 and -O3):
/// checksum and length of `Nat(42)|a=7 c='x'|plain|<hi>|m42plain<3>`.
const FMTWRITE_STDOUT: &str = "299169633426683964\n40\n12345\nformatter write_fmt ok\n";

/// The MIR text of the first function whose signature contains `sig`.
fn mir_fn_body<'a>(mir: &'a str, sig: &str) -> &'a str {
    let start = mir.find(sig).unwrap_or_else(|| panic!("no MIR function matching `{sig}`"));
    let rest = &mir[start..];
    let end = rest.find("\n}\n").map(|i| i + 3).unwrap_or(rest.len());
    &rest[..end]
}

fn main() {
    rfs::write("fmtwrite.rs", FMTWRITE);
    rfs::write("decline.rs", DECLINE);

    // MIR GUARD: at -O3 the mixed body must still contain both lanes — the
    // intercepted `format!` consumer and live `core::fmt::write`s from inlined
    // `Formatter::write_fmt`s — and the Nat body the address-bit probe that was
    // refused. `--emit=mir` runs no codegen backend.
    rustc()
        .input("fmtwrite.rs")
        .crate_type("bin")
        .crate_name("fmtwrite")
        .opt_level("3")
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        .arg("-Cpanic=abort")
        .emit("mir")
        .output("fmtwrite3.mir")
        .run();
    let mir = rfs::read_to_string("fmtwrite3.mir");
    let mixed = mir_fn_body(&mir, "::render(_1: &Mixed");
    assert!(
        mixed.contains("map_or_else::<String"),
        "-O3 no longer inlines `format!` to the `map_or_else` consumer in the mixed body; \
         this case no longer exercises the interaction:\n{mixed}"
    );
    assert!(
        mixed.matches("std::fmt::write(").count() >= 2,
        "-O3 no longer inlines both `Formatter::write_fmt`s in the mixed body:\n{mixed}"
    );
    assert!(
        mixed.matches("BitAnd(").count() >= 3,
        "-O3 no longer emits the three `as_str` bit-tests in the mixed body:\n{mixed}"
    );
    let nat = mir_fn_body(&mir, "::render(_1: &Nat");
    assert!(
        nat.contains("as usize (Transmute)"),
        "-O3 no longer emits the refused `&args as usize` probe in `Nat::render`:\n{nat}"
    );

    for opt in ["0", "3"] {
        // NEGATIVE (case 3). The control first: the fixture is valid Rust that
        // the reference backend compiles and runs.
        let decline_control = format!("decline_llvm{opt}");
        rustc()
            .input("decline.rs")
            .crate_type("bin")
            .crate_name("decline")
            .output(&decline_control)
            .opt_level(opt)
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run();
        run(&decline_control).assert_stdout_equals("7\n");
        // A recognised consumer that declines refuses BY NAME, and not through
        // the type gate that used to hide it.
        rustc()
            .input("decline.rs")
            .crate_type("bin")
            .crate_name("decline")
            .output(&format!("decline{opt}"))
            .opt_level(opt)
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run_fail()
            .assert_stderr_contains("[TCG-FMT-DECLINED]")
            .assert_stderr_not_contains("Ty::core::fmt::rt::ArgumentType");

        // VALUES (cases 1 and 2). -O0 and -O3 take DIFFERENT lanes for the same
        // source and both must be right: at -O0 `Formatter::write_fmt` and
        // `Argument::new_display` are CALLS (a local `write_fmt` mono item whose
        // `dyn Write` arm writes `_0`); at -O3 they are inlined into each impl and
        // the `as_str` bit-test over the argument array's address appears.
        let control = format!("fmtwrite_llvm{opt}");
        rustc()
            .input("fmtwrite.rs")
            .crate_type("bin")
            .crate_name("fmtwrite")
            .output(&control)
            .opt_level(opt)
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .arg("-Cpanic=abort")
            .run();
        let want = run(&control).stdout_utf8();
        assert_eq!(
            want, FMTWRITE_STDOUT,
            "the LLVM control disagrees with the expected bytes at -O{opt}; the fixture changed"
        );

        let bin = format!("fmtwrite{opt}");
        rustc()
            .input("fmtwrite.rs")
            .crate_type("bin")
            .crate_name("fmtwrite")
            .output(&bin)
            .opt_level(opt)
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            // The verifier is a separate axis; this test is about codegen alone.
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            // Unwinding is not the subject.
            .arg("-Cpanic=abort")
            .run();
        // `run` also requires exit status 0: the fixture exits 2/3/4 when the
        // write fails or the delivered bytes differ from the literal.
        let got = run(&bin).stdout_utf8();
        assert_eq!(
            got, want,
            "trust-ir-cg -O{opt} output differs from the LLVM control: a `Formatter` \
             `write!` delivered the wrong bytes"
        );
    }
}
