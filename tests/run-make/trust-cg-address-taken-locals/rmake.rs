//! A local that lives in memory must be current on EVERY path, whatever order the builtin
//! trust-cg MIR frontend lowers the blocks in.
//!
//! The bridge used to give a local a stack slot lazily: allocated, and stored with the local's
//! current SSA value, the first time lowering asked for its address, and returned WITHOUT a
//! store every later time. The store therefore sat in whichever block was lowered first, so a
//! sibling branch that took the same address read memory its own path never wrote (`k02`,
//! `k08`, the pointer written through in `ptr_arms`); an aggregate took a fresh slot per
//! definition, so a projection after a join read the slot of the arm lowered last
//! (`tuple_arms`); and a direct read after a write through `&mut` used the stale SSA value
//! (`mut_then_read`). `crates/trust-cg-bridge` now plans the memory-backed locals before
//! lowering: one slot each, stored at every definition, loaded at every read.
//!
//! A WHOLE copy of an aggregate of 16 bytes or more (`let u = t;`) was a separate defect with
//! the same symptom: the bridge moved the aggregate with a whole-aggregate LIR `Load`/`Store`,
//! which trust-cg selects as ONE 8-byte access, so the copy carried field 0 and left the rest
//! uninitialized (`field_arms_whole_copy` = `0 6455630270 …` against the host's `0 11 22 55 92
//! …` at `-O0`, before and after the slot fix). LIR carries an aggregate as the address of its
//! bytes; the bridge now copies it with one exact-width `Memcpy`.
//!
//! Only reachable under `-Ztrust-cg-output-gate=allow-unknown` (the strict gate refuses these
//! bodies), which is exactly why the fixture is execution-level: the wrong code was emitted
//! uncertified and only the printed values showed it. Each subject is built at `-Copt-level=0`
//! (MIR keeps every reference and temporary) and at `-Copt-level=3` (MIR opts reshape the
//! bodies), and every function runs in its own process so a crash in one cannot hide another.
//!
//! Provenance: this recipe run by hand on the unfixed compiler (a stage1 built at Trust `adfcd2c08b`, whose trust-cg-bridge is identical to `a99adf74c3`'s,
//! aarch64-apple-darwin) printed, at `-O0`, `k02` = `5 0 2 4 6 8 10 12` (host: `5 12 14 20 22 92
//! 410 2010`), `k08` = `1 4 101 102 103 104 250 249` (host: `1 4 107 116 119 224 678 2886`),
//! `tuple_arms` = `100 <garbage> <garbage> … 172 908` (host: `100 6 302 12 298 46 172 908`), and
//! `ptr_arms` and `mut_then_read` died with SIGSEGV; at `-O3`, `k02` = `0 12 …` (another run:
//! `45 12 …` — an uninitialized slot), `k08` = garbage from x = 2, and `ptr_arms` died with
//! SIGSEGV (`tuple_arms` and `mut_then_read` happened to be right). See
//! docs/issues/2026-09-29-trust-cg-mir-address-taken-locals-across-sibling-blocks.md.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{bin_name, rfs, run_with_args, rustc};

const SUBJECT: &str = r#"#![crate_name = "slot_subject"]

#[inline(never)]
fn rd(p: &u64) -> u64 {
    *p
}

/// k02: `y` is defined in the entry block and its address is taken in two sibling branches.
#[unsafe(no_mangle)]
pub extern "C" fn k02(x: u64) -> u64 {
    let y = x.wrapping_add(5);
    if x == 0 { rd(&y) } else { rd(&y).wrapping_mul(2) }
}

/// k08: a three-way `if`/`else if` chain taking `&y` in every arm.
#[unsafe(no_mangle)]
pub extern "C" fn k08(x: u64) -> u64 {
    let y = x.wrapping_mul(3).wrapping_add(1);
    if x < 2 {
        rd(&y)
    } else if x < 50 {
        rd(&y).wrapping_add(100)
    } else {
        rd(&y) ^ 0xff
    }
}

/// A tuple built in four match arms (one of them nested) and projected after the join.
#[unsafe(no_mangle)]
pub extern "C" fn tuple_arms(x: u64) -> u64 {
    let t = match x & 3 {
        0 => (x, 100),
        1 => {
            if x & 4 == 0 { (x, 7) } else { (x, 9) }
        }
        2 => (x, 300),
        _ => (x, 5),
    };
    t.1 ^ t.0
}

/// A pointer defined in two branches, then written through in two sibling branches.
#[unsafe(no_mangle)]
pub extern "C" fn ptr_arms(x: u64) -> u64 {
    let mut a = x;
    let mut b = x.wrapping_add(1000);
    let p: &mut u64 = if x & 1 == 0 { &mut a } else { &mut b };
    if x > 100 {
        *p = x.wrapping_mul(3);
    } else {
        *p = x.wrapping_add(11);
    }
    a.wrapping_add(b.wrapping_mul(7))
}

/// A local mutated through `&mut` in two sibling branches and then read directly.
#[unsafe(no_mangle)]
pub extern "C" fn mut_then_read(x: u64) -> u64 {
    let mut y = x.wrapping_mul(5);
    let r = &mut y;
    if x & 1 == 0 {
        *r = r.wrapping_add(3);
    } else {
        *r = r.wrapping_add(9);
    }
    y ^ x
}

/// n16: a tuple field written in one of two arms, then the whole tuple copied.
#[unsafe(no_mangle)]
pub extern "C" fn field_arms_whole_copy(x: u64) -> u64 {
    let mut t = (x, 2u64);
    if x > 5 { t.0 = 9; } else { t.1 = x; }
    let u = t;
    u.0.wrapping_mul(10).wrapping_add(u.1)
}

/// w1: a tuple built in two arms, then copied whole.
#[unsafe(no_mangle)]
pub extern "C" fn arms_whole_copy(x: u64) -> u64 {
    let t = if x > 5 { (x, 1u64) } else { (1u64, x) };
    let u = t;
    u.0.wrapping_mul(1000).wrapping_add(u.1)
}

/// w3: a 24-byte array built in two arms, copied whole, then destructured.
#[unsafe(no_mangle)]
pub extern "C" fn array_arms_whole_copy(x: u64) -> u64 {
    let a = if x > 5 { [x, 2, 3] } else { [1, x, 3] };
    let b = a;
    let [p, q, r] = b;
    p.wrapping_mul(10000).wrapping_add(q.wrapping_mul(100)).wrapping_add(r)
}

/// w5: a field written, the tuple copied whole, and the copy's fields read through `&`.
#[unsafe(no_mangle)]
pub extern "C" fn ref_to_field_of_copy(x: u64) -> u64 {
    let mut t = (x, 2u64);
    t.1 = x.wrapping_add(1);
    let u = t;
    rd(&u.1).wrapping_mul(10).wrapping_add(rd(&u.0))
}

/// w6: a whole copy of a tuple that the same loop iteration then overwrites field by field.
#[unsafe(no_mangle)]
pub extern "C" fn loop_whole_copy_swap(x: u64) -> u64 {
    let mut t = (x, 1u64);
    let mut i = 0u64;
    while i < (x & 7) {
        let u = t;
        t.0 = u.1;
        t.1 = u.0.wrapping_add(u.1);
        i = i.wrapping_add(1);
    }
    t.0.wrapping_mul(1000).wrapping_add(t.1)
}
"#;

const DRIVER: &str = r#"extern crate slot_subject;

unsafe extern "C" {
    fn k02(x: u64) -> u64;
    fn k08(x: u64) -> u64;
    fn tuple_arms(x: u64) -> u64;
    fn ptr_arms(x: u64) -> u64;
    fn mut_then_read(x: u64) -> u64;
    fn field_arms_whole_copy(x: u64) -> u64;
    fn arms_whole_copy(x: u64) -> u64;
    fn array_arms_whole_copy(x: u64) -> u64;
    fn ref_to_field_of_copy(x: u64) -> u64;
    fn loop_whole_copy_swap(x: u64) -> u64;
}

fn main() {
    let name = std::env::args().nth(1).expect("function name");
    let f: unsafe extern "C" fn(u64) -> u64 = match name.as_str() {
        "k02" => k02,
        "k08" => k08,
        "tuple_arms" => tuple_arms,
        "ptr_arms" => ptr_arms,
        "mut_then_read" => mut_then_read,
        "field_arms_whole_copy" => field_arms_whole_copy,
        "arms_whole_copy" => arms_whole_copy,
        "array_arms_whole_copy" => array_arms_whole_copy,
        "ref_to_field_of_copy" => ref_to_field_of_copy,
        "loop_whole_copy_swap" => loop_whole_copy_swap,
        other => panic!("unknown function {other}"),
    };
    let row: Vec<String> =
        [0_u64, 1, 2, 5, 6, 41, 200, 1000].iter().map(|&x| unsafe { f(x) }.to_string()).collect();
    println!("{}", row.join(" "));
}
"#;

const INPUTS: [u64; 8] = [0, 1, 2, 5, 6, 41, 200, 1000];

// The same bodies, computed on the host (`rd(&y)` is `y`).

fn k02(x: u64) -> u64 {
    let y = x.wrapping_add(5);
    if x == 0 { y } else { y.wrapping_mul(2) }
}

fn k08(x: u64) -> u64 {
    let y = x.wrapping_mul(3).wrapping_add(1);
    if x < 2 {
        y
    } else if x < 50 {
        y.wrapping_add(100)
    } else {
        y ^ 0xff
    }
}

fn tuple_arms(x: u64) -> u64 {
    let t = match x & 3 {
        0 => (x, 100),
        1 => {
            if x & 4 == 0 { (x, 7) } else { (x, 9) }
        }
        2 => (x, 300),
        _ => (x, 5),
    };
    t.1 ^ t.0
}

fn ptr_arms(x: u64) -> u64 {
    let mut a = x;
    let mut b = x.wrapping_add(1000);
    let p: &mut u64 = if x & 1 == 0 { &mut a } else { &mut b };
    if x > 100 {
        *p = x.wrapping_mul(3);
    } else {
        *p = x.wrapping_add(11);
    }
    a.wrapping_add(b.wrapping_mul(7))
}

fn mut_then_read(x: u64) -> u64 {
    let mut y = x.wrapping_mul(5);
    let r = &mut y;
    if x & 1 == 0 {
        *r = r.wrapping_add(3);
    } else {
        *r = r.wrapping_add(9);
    }
    y ^ x
}

fn field_arms_whole_copy(x: u64) -> u64 {
    let mut t = (x, 2u64);
    if x > 5 { t.0 = 9; } else { t.1 = x; }
    let u = t;
    u.0.wrapping_mul(10).wrapping_add(u.1)
}

fn arms_whole_copy(x: u64) -> u64 {
    let t = if x > 5 { (x, 1u64) } else { (1u64, x) };
    let u = t;
    u.0.wrapping_mul(1000).wrapping_add(u.1)
}

fn array_arms_whole_copy(x: u64) -> u64 {
    let a = if x > 5 { [x, 2, 3] } else { [1, x, 3] };
    let b = a;
    let [p, q, r] = b;
    p.wrapping_mul(10000).wrapping_add(q.wrapping_mul(100)).wrapping_add(r)
}

fn ref_to_field_of_copy(x: u64) -> u64 {
    let mut t = (x, 2u64);
    t.1 = x.wrapping_add(1);
    let u = t;
    u.1.wrapping_mul(10).wrapping_add(u.0)
}

fn loop_whole_copy_swap(x: u64) -> u64 {
    let mut t = (x, 1u64);
    let mut i = 0u64;
    while i < (x & 7) {
        let u = t;
        t.0 = u.1;
        t.1 = u.0.wrapping_add(u.1);
        i = i.wrapping_add(1);
    }
    t.0.wrapping_mul(1000).wrapping_add(t.1)
}

const FUNCTIONS: [(&str, fn(u64) -> u64); 10] = [
    ("k02", k02),
    ("k08", k08),
    ("tuple_arms", tuple_arms),
    ("ptr_arms", ptr_arms),
    ("mut_then_read", mut_then_read),
    ("field_arms_whole_copy", field_arms_whole_copy),
    ("arms_whole_copy", arms_whole_copy),
    ("array_arms_whole_copy", array_arms_whole_copy),
    ("ref_to_field_of_copy", ref_to_field_of_copy),
    ("loop_whole_copy_swap", loop_whole_copy_swap),
];

fn main() {
    rfs::write("slot_subject.rs", SUBJECT);
    rfs::write("driver.rs", DRIVER);

    for opt_level in ["0", "3"] {
        let out = format!("out{opt_level}");
        let driver = format!("driver{opt_level}");
        rfs::create_dir(&out);

        // SUBJECT: the builtin MIR frontend with the gate explicitly weakened (the strict gate
        // refuses these bodies, so `allow-unknown` is the only way they reach machine code).
        rustc()
            .input("slot_subject.rs")
            .crate_type("rlib")
            .edition("2021")
            .arg("-Cpanic=abort")
            .arg("-Ccodegen-units=1")
            .arg(format!("-Copt-level={opt_level}"))
            // `-O0` would otherwise add overflow checks; `-O3` has none by default.
            .arg("-Coverflow-checks=off")
            .arg("-Zunstable-options")
            .arg("-Zcodegen-backend=trust-cg")
            .arg("-Ztrust-verify=off")
            .arg("-Ztrust-cg-frontend=mir")
            .arg("-Ztrust-cg-output-gate=allow-unknown")
            .out_dir(&out)
            .run();

        // OBSERVER: built with the default backend, verify-off, like the sibling trust-cg
        // run-make observers.
        rustc()
            .input("driver.rs")
            .edition("2021")
            .arg("-Cpanic=abort")
            .arg("-Ztrust-verify=off")
            .extern_("slot_subject", format!("{out}/libslot_subject.rlib"))
            .library_search_path(&out)
            .output(bin_name(&driver))
            .run();

        for (name, host) in FUNCTIONS {
            let expected =
                INPUTS.iter().map(|&x| host(x).to_string()).collect::<Vec<_>>().join(" ");
            let ran = run_with_args(&driver, &[name]);
            assert_eq!(
                ran.stdout_utf8().trim(),
                expected,
                "`{name}` built by the trust-cg MIR frontend at -Copt-level={opt_level} must print \
                 the host values on every input"
            );
        }
    }
}
