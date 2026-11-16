//! Type-lowering refusals in trust-ir-cg name the rule that was broken and
//! enumerate the ways forward (design principle 10 / spec-surface v7/D3), instead
//! of the innermost `Ty::..` the descent happened to stop at — and every probe
//! still computes the LLVM backend's values.
//!
//! Each probe is a shape from the round-3 `library/std` census whose refusal is
//! CORRECT (admitting it would drop pointer metadata or mis-type a leaf), but whose
//! old text named the wrong thing:
//!
//! | probe        | old text                                   | real rule                                   |
//! |--------------|--------------------------------------------|---------------------------------------------|
//! | dst_tail     | `Ty::[u8]` (`Rc<[u8]>::copy_from_slice`)   | fat pointer to a slice-TAILED struct        |
//! | cell_slice   | `Ty::[u8]` (miniz `apply_match`)           | same, through GENERIC `Cell<[u8]>`          |
//! | dyn_cursor   | `Ty::dyn Debug` (`slice::Iter<&dyn Debug>`)| raw pointer whose pointee is `&dyn`         |
//! | enum_pointee | `Ty::Attributes` (gimli)                   | pointee lanes declined a Vec-owning enum    |
//! | union_part   | `Ty::Part` (flt2dec, -O3)                  | non-scalar union aggregate, fat enum field  |
//!
//! The test is written for BOTH futures. While a shape is refused, the refusal
//! must carry its tag and "Ways forward". The day a widening makes a probe
//! compile, the probe's binary must print exactly what the LLVM backend's does —
//! so this test can never pass on a silent miscompile.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

struct Probe {
    name: &'static str,
    lib: &'static str,
    main: &'static str,
    opt_levels: &'static [&'static str],
    // Substrings every refusal of this probe must carry.
    must_say: &'static [&'static str],
    extra: &'static [&'static str],
}

const PROBES: &[Probe] = &[
    Probe {
        name: "dst_tail",
        lib: r#"
use std::rc::Rc;
use std::sync::Arc;
#[inline(never)] pub fn mk_rc(v: &[u8]) -> Rc<[u8]> { Rc::from(v) }
#[inline(never)] pub fn mk_arc(v: &[u8]) -> Arc<[u8]> { Arc::from(v) }
"#,
        main: r#"
fn main() {
    let r = mk_rc(b"hello");
    let a = mk_arc(b"worlds");
    if r.len() != 5 || r[1] != b'e' { std::process::exit(1); }
    if a.len() != 6 || a[5] != b's' { std::process::exit(2); }
    println!("probe ok");
}
"#,
        opt_levels: &["0", "3"],
        must_say: &["[TCG-POINTEE-UNSIZED-TAIL]", "RcInner<[u8]>", "Ways forward"],
        extra: &[],
    },
    Probe {
        name: "cell_slice",
        lib: r#"
use core::cell::Cell;
#[inline(never)]
pub fn apply_match(out: &mut [u8], out_pos: usize, dist: usize, match_len: usize, mask: usize) {
    let source_pos = out_pos.wrapping_sub(dist) & mask;
    if match_len == 3 {
        let out = Cell::from_mut(out).as_slice_of_cells();
        if let Some(dst) = out.get(out_pos..out_pos + 3) {
            let src = out.get(source_pos).zip(out.get((source_pos + 1) & mask)).zip(out.get((source_pos + 2) & mask));
            if let Some(((a, b), c)) = src { dst[0].set(a.get()); dst[1].set(b.get()); dst[2].set(c.get()); }
        }
        return;
    }
    for i in 0..match_len { out[out_pos + i] = out[(source_pos + i) & mask]; }
}
"#,
        main: r#"
fn main() {
    let mut buf = [1u8, 2, 3, 0, 0, 0, 0, 0];
    apply_match(&mut buf, 3, 3, 3, 7);
    if buf != [1, 2, 3, 1, 2, 3, 0, 0] { std::process::exit(1); }
    apply_match(&mut buf, 6, 2, 2, 7);
    if buf != [1, 2, 3, 1, 2, 3, 2, 3] { std::process::exit(2); }
    println!("probe ok");
}
"#,
        opt_levels: &["0", "3"],
        must_say: &["[TCG-POINTEE-UNSIZED-TAIL]", "GENERIC `#[repr(transparent)]`", "Ways forward"],
        extra: &[],
    },
    Probe {
        name: "dyn_cursor",
        lib: r#"
use std::fmt::Debug;
#[inline(never)] pub fn into_it<'a, 'b>(v: &'b [&'a dyn Debug]) -> std::slice::Iter<'b, &'a dyn Debug> { v.into_iter() }
#[inline(never)] pub fn hint(it: &std::slice::Iter<'_, &dyn Debug>) -> (usize, Option<usize>) { it.size_hint() }
#[inline(never)] pub fn count(values: &[&dyn Debug]) -> usize { let mut n = 0; for _v in values { n += 1; } n }
"#,
        main: r#"
fn main() {
    let a = 1u32;
    let b = 2u64;
    let c = 'x';
    let vs: [&dyn std::fmt::Debug; 3] = [&a, &b, &c];
    if count(&vs) != 3 { std::process::exit(1); }
    let it = into_it(&vs[1..]);
    if hint(&it) != (2, Some(2)) { std::process::exit(2); }
    println!("probe ok");
}
"#,
        opt_levels: &["0", "3"],
        must_say: &["[TCG-POINTEE-DYN-VALUE]", "Ways forward"],
        // Keep the `Iter<&dyn Debug>` methods monomorphized in THIS crate.
        extra: &["-Zshare-generics=no"],
    },
    Probe {
        name: "enum_pointee",
        lib: r#"
use std::ops::Deref;
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Spec { name: u16, form: u16, value: i64 }
#[derive(Clone)]
pub enum Attributes { Inline { buf: [Spec; 5], len: usize }, Heap(Vec<Spec>) }
impl Attributes {
    pub fn new() -> Attributes { let d = Spec { name: 0, form: 0, value: 0 }; Attributes::Inline { buf: [d; 5], len: 0 } }
    #[inline(never)]
    pub fn push(&mut self, attr: Spec) {
        match self {
            Attributes::Heap(list) => list.push(attr),
            Attributes::Inline { buf, len: 5 } => { let mut list = buf.to_vec(); list.push(attr); *self = Attributes::Heap(list); }
            Attributes::Inline { buf, len } => { buf[*len] = attr; *len += 1; }
        }
    }
}
impl Deref for Attributes {
    type Target = [Spec];
    #[inline(never)]
    fn deref(&self) -> &[Spec] { match self { Attributes::Inline { buf, len } => &buf[..*len], Attributes::Heap(list) => list } }
}
impl PartialEq for Attributes { #[inline(never)] fn eq(&self, other: &Attributes) -> bool { **self == **other } }
"#,
        main: r#"
fn main() {
    let mut a = Attributes::new();
    for i in 0..7u16 { a.push(Spec { name: i, form: i * 2, value: -(i as i64) }); }
    if a.len() != 7 || a[6].value != -6 || a[4].form != 8 { std::process::exit(1); }
    let b = a.clone();
    if !(a == b) { std::process::exit(2); }
    println!("probe ok");
}
"#,
        opt_levels: &["0", "3"],
        must_say: &["[TCG-POINTEE-LANES]", "Ways forward"],
        extra: &[],
    },
    Probe {
        name: "union_part",
        lib: r#"
use std::mem::MaybeUninit;
#[derive(Clone, Copy)]
pub enum Part<'a> { Zero(usize), Num(u16), Copy(&'a [u8]) }
impl<'a> Part<'a> {
    pub fn len(&self) -> usize {
        match *self { Part::Zero(n) => n, Part::Num(v) => if v < 10 { 1 } else if v < 100 { 2 } else if v < 1000 { 3 } else if v < 10000 { 4 } else { 5 }, Part::Copy(buf) => buf.len() }
    }
}
#[inline(never)]
pub fn fill<'a>(buf: &'a [u8], exp: usize, parts: &'a mut [MaybeUninit<Part<'a>>]) -> usize {
    parts[0] = MaybeUninit::new(Part::Copy(&buf[..1]));
    parts[1] = MaybeUninit::new(Part::Copy(b"."));
    parts[2] = MaybeUninit::new(Part::Zero(exp));
    parts[3] = MaybeUninit::new(Part::Num(1234));
    let s = unsafe { &*(&parts[..4] as *const [MaybeUninit<Part<'a>>] as *const [Part<'a>]) };
    // An index loop, not `s.iter().map(|p| p.len()).sum()`: the iterator chain is
    // a separate lane (`[TCG-ITER-UNMODELED]`) that would refuse this probe for a
    // reason other than the union shape it exists to pin.
    let mut total = 0;
    let mut i = 0;
    while i < s.len() { total += s[i].len(); i += 1; }
    total
}
"#,
        main: r#"
fn main() {
    let mut parts = [MaybeUninit::<Part>::uninit(); 4];
    if fill(b"78", 3, &mut parts) != 9 { std::process::exit(1); }
    println!("probe ok");
}
"#,
        // -O3 is the std build's level and the level this spelling is reached at;
        // -O0 refuses the same program at the memory union lane instead.
        opt_levels: &["3"],
        must_say: &["[TCG-UNION-AGGREGATE-NONSCALAR]", "Ways forward"],
        extra: &[],
    },
];

fn main() {
    for probe in PROBES {
        let lib_file = format!("{}.rs", probe.name);
        let bin_file = format!("{}_main.rs", probe.name);
        rfs::write(&lib_file, probe.lib);
        rfs::write(&bin_file, format!("{}\n{}", probe.lib, probe.main));
        for opt in probe.opt_levels {
            // LLVM control: the probe's own asserts ARE the expected values.
            let llvm = format!("{}_llvm_o{opt}", probe.name);
            rustc()
                .edition("2021")
                .input(&bin_file)
                .crate_type("bin")
                .opt_level(opt)
                .arg("-Ztrust-verify=off")
                .arg("-Cdebuginfo=0")
                .output(&llvm)
                .run();
            run(&llvm).assert_stdout_contains("probe ok");

            // trust-ir-cg, as an rlib so every refused function is reported.
            let mut lib = rustc();
            // The probes are 2021-edition sources (`use core::..` in `cell_slice`
            // does not resolve under the 2015 default), exactly as the LLVM
            // control above is built.
            lib.edition("2021")
                .input(&lib_file)
                .crate_type("rlib")
                .crate_name(format!("{}_o{opt}", probe.name))
                .opt_level(opt)
                .arg("-Zcodegen-backend=trust-ir-cg")
                .arg("-Ztrust-verify=off")
                // Proof promotion is a separate axis; keep its unrelated refusals
                // out of the stderr this test reads.
                .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
                .arg("-Cdebuginfo=0")
                .out_dir(format!("{}_rlib_o{opt}", probe.name));
            for arg in probe.extra {
                lib.arg(*arg);
            }
            let out = lib.run_unchecked();
            if out.status().success() {
                // Widened since this test was written: the program must now RUN
                // to the LLVM values under trust-ir-cg.
                let tcg = format!("{}_tcg_o{opt}", probe.name);
                let mut bin = rustc();
                // `-Cpanic=abort`: a widened probe must RUN to the LLVM values;
                // the unwind cleanup edge of a call returning a fat pointer is a
                // separate lane (`[TCG-EH-CALL-EDGE]`), not the type rule pinned
                // here.
                bin.edition("2021")
                    .input(&bin_file)
                    .crate_type("bin")
                    .panic("abort")
                    .opt_level(opt)
                    .arg("-Zcodegen-backend=trust-ir-cg")
                    .arg("-Ztrust-verify=off")
                    .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
                    .arg("-Cdebuginfo=0")
                    .output(&tcg);
                for arg in probe.extra {
                    bin.arg(*arg);
                }
                bin.run();
                run(&tcg).assert_stdout_contains("probe ok");
            } else {
                let stderr = out.stderr_utf8();
                assert!(
                    !stderr.contains("internal compiler error") && !stderr.contains("panicked"),
                    "{} -O{opt}: crashed instead of refusing:\n{stderr}",
                    probe.name
                );
                for needle in probe.must_say {
                    assert!(
                        stderr.contains(needle),
                        "{} -O{opt}: refusal does not carry `{needle}`:\n{stderr}",
                        probe.name
                    );
                }
            }
        }
    }
}
