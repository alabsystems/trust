// The E6 differential harness's SOURCE OF TRUTH
// (crates/trust-certify/tests/e6_differential.rs).
//
// Every function here exists twice: the test `include!`s this file and runs
// each function NATIVELY, and `regen.py` compiles this same file with a Trust
// compiler under `-Ztrust-dump=mir:` to capture the MIR the E6 readers actually
// see (`shapes.unopt.json`, `shapes.opt.json`). The harness imports each
// dumped body through `admit_function_into` and compares the kernel's
// evaluation of the minted image against the native result on EVERY u8/i8/bool
// input. Edit this file and the fixtures go stale: the harness checks the
// source hash recorded in them and fails until `regen.py` is re-run.
//
// Plain Rust only — no contracts — so the test's own compiler builds it.

// ---- constants -----------------------------------------------------------
pub fn k_const() -> u8 {
    7
}
pub fn k_const_param(_a: u8) -> u8 {
    200
}
pub fn k_neg_i8() -> i8 {
    -7
}

// ---- projections ---------------------------------------------------------
pub fn p_second(_a: u8, b: u8) -> u8 {
    b
}
pub fn p_bool(a: bool) -> bool {
    a
}
pub fn p_i8(a: i8) -> i8 {
    a
}

// ---- selects over parameters ---------------------------------------------
pub fn s_lt(a: u8, b: u8) -> u8 {
    if a < b { a } else { b }
}
pub fn s_le(a: u8, b: u8) -> u8 {
    if a <= b { b } else { a }
}
pub fn s_eq(a: u8, b: u8) -> u8 {
    if a == b { b } else { a }
}
pub fn s_lt_i8(a: i8, b: i8) -> i8 {
    if a < b { a } else { b }
}

// ---- selects against a literal -------------------------------------------
pub fn sl_lt(a: u8, b: u8) -> u8 {
    if a < 100 { a } else { b }
}
pub fn sl_eq(a: u8, b: u8) -> u8 {
    if a == 7 { b } else { a }
}

// ---- comparisons returned as bool ----------------------------------------
pub fn c_lt(a: u8, b: u8) -> bool {
    a < b
}
pub fn c_le(a: u8, b: u8) -> bool {
    a <= b
}
pub fn c_eq(a: u8, b: u8) -> bool {
    a == b
}
pub fn c_gt(a: u8, b: u8) -> bool {
    a > b
}
pub fn c_ge(a: u8, b: u8) -> bool {
    a >= b
}
pub fn c_ne(a: u8, b: u8) -> bool {
    a != b
}
pub fn c_lit(a: u8) -> bool {
    a <= 200
}
pub fn c_lit_left(a: u8) -> bool {
    17 < a
}
pub fn c_lt_i8(a: i8, b: i8) -> bool {
    a < b
}
pub fn c_ge_neg_i8(a: i8) -> bool {
    a >= -5
}

// ---- `&&` / `||` of two comparisons --------------------------------------
pub fn b_and(a: u8, b: u8) -> bool {
    a < b && b <= 200
}
pub fn b_or(a: u8, b: u8) -> bool {
    a == b || 100 < a
}
pub fn b_and_i8(a: i8, b: i8) -> bool {
    -3 <= a && a < b
}

// ---- marker-authenticated wrapping arithmetic ----------------------------
pub fn w_add(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}
pub fn w_sub(a: u8, b: u8) -> u8 {
    a.wrapping_sub(b)
}
pub fn w_mul(a: u8, b: u8) -> u8 {
    a.wrapping_mul(b)
}
pub fn w_add_lit(a: u8) -> u8 {
    a.wrapping_add(200)
}
pub fn w_chain(a: u8, b: u8) -> u8 {
    a.wrapping_add(b).wrapping_mul(3).wrapping_sub(a)
}

// ---- signed checked arithmetic -------------------------------------------
pub fn ck_add_i8(a: i8, b: i8) -> Option<i8> {
    a.checked_add(b)
}
pub fn ck_sub_i8(a: i8, b: i8) -> Option<i8> {
    a.checked_sub(b)
}
pub fn ck_mul_i8(a: i8, b: i8) -> Option<i8> {
    a.checked_mul(b)
}

// ---- the two monomorphic casts (fixed widths; sampled, not exhaustive) ----
pub fn gn_narrow(x: i128) -> Option<i64> {
    if x >= i64::MIN as i128 && x <= i64::MAX as i128 { Some(x as i64) } else { None }
}
pub fn we_eq(machine: i64, truth: i128) -> bool {
    machine as i128 == truth
}

// ---- comparisons over bool -----------------------------------------------
pub fn bb_eq(a: bool, b: bool) -> bool {
    a == b
}
pub fn bb_ne(a: bool, b: bool) -> bool {
    a != b
}
pub fn bb_lt(a: bool, b: bool) -> bool {
    a < b
}
pub fn bb_le(a: bool, b: bool) -> bool {
    a <= b
}
pub fn bb_gt(a: bool, b: bool) -> bool {
    a > b
}
pub fn bb_eq_true(a: bool) -> bool {
    a == true
}
pub fn bb_ne_false(a: bool, _b: bool) -> bool {
    false != a
}
pub fn bb_eq_false(a: bool, _b: bool) -> bool {
    a == false
}
pub fn bb_eq_mixed(a: bool, _n: u8) -> bool {
    a == a
}
pub fn bb_eq_of_cmps(a: u8, b: u8, c: bool) -> bool {
    (a < b) == c
}

// ---- E6 expansion I3′: bool connective trees ------------------------------
// `&&`/`||` arrive as rustc's SHORT-CIRCUIT control flow (a two-way
// `switchInt` on a `bool` per operand, joined by `goto`), `&`/`|`/`^`/`!` as
// single-block statements, and the leaves are `bool` parameters and
// comparisons of parameters and literals. The three `ay_*` bodies are ay's
// soundness gates VERBATIM (design note §7, R3–R5).
pub fn t_and(a: bool, b: bool) -> bool {
    a && b
}
pub fn t_or(a: bool, b: bool) -> bool {
    a || b
}
pub fn t_not(a: bool) -> bool {
    !a
}
pub fn t_or3(a: bool, b: bool, c: bool) -> bool {
    a || b || c
}
pub fn t_and3(a: bool, b: bool, c: bool) -> bool {
    a && b && c
}
pub fn ay_gate_keeps_sat(was_sat: bool, confirmed: bool, enforce: bool) -> bool {
    was_sat && (confirmed || !enforce)
}
pub fn ay_lemma_admitted_inductive(self_ind: bool, init_valid: bool, entry_ind: bool) -> bool {
    self_ind & init_valid & entry_ind
}
pub fn ay_xor_accumulate_parity(acc: bool, contribution: bool) -> bool {
    acc ^ contribution
}
pub fn t_bor(a: bool, b: bool) -> bool {
    a | b
}
pub fn t_not_and(a: bool, b: bool) -> bool {
    !(a && b)
}
pub fn t_not_or(a: bool, b: bool) -> bool {
    !a || b
}
pub fn t_and_not(a: bool, b: bool) -> bool {
    a && !b
}
pub fn t_nested(a: bool, b: bool, c: bool) -> bool {
    !(a || (b && !c))
}
pub fn t_and_or_mix(a: bool, b: bool, c: bool) -> bool {
    (a && b) || (!a && c)
}
pub fn t_let(a: bool, b: bool) -> bool {
    let x = a && b;
    x || a
}
pub fn t_eq_tree(a: bool, b: bool, c: bool) -> bool {
    (a == b) || c
}
pub fn t_ne_tree(a: bool, b: bool, c: bool) -> bool {
    a != b && c
}
pub fn t_xor_eq(a: bool, b: bool, c: bool) -> bool {
    (a ^ b) == c
}
pub fn t_cmp3(a: u8, b: u8) -> bool {
    a < 10 || a == b || b > 200
}
pub fn t_cmp6(x: u8) -> bool {
    x == 1 || x == 3 || x == 5 || x == 7 || x == 9 || x == 11
}
pub fn t_ne_lit(x: u8) -> bool {
    x != 0x7f && x >= 0x20
}
pub fn t_digit(x: u8) -> bool {
    x >= 0x30 && x <= 0x39
}
pub fn t_mixed(a: u8, b: u8, c: bool) -> bool {
    a < b && !c
}
pub fn t_i8(a: i8, b: i8) -> bool {
    a < b || a == -1
}
pub fn t_not_cmp(a: u8, b: u8) -> bool {
    !(a < b)
}
pub fn t_cmp3_u32(a: u32, b: u32) -> bool {
    a < 10 || a == b || b > 4_000_000_000
}
// Stay refused through I3′ and I4′: an ORDERING over `bool` inside a tree
// (no image; review H1), a bit operation over integers (I2′), and a
// comparison whose operand is computed rather than a parameter or literal.
pub fn t_bool_lt_tree(a: bool, b: bool, c: bool) -> bool {
    (a < b) || c
}
pub fn t_bit_u8(a: u8, b: u8) -> bool {
    a & b == 0 || a < b
}
pub fn t_cmp_of_select(a: bool, b: bool, x: u8) -> bool {
    (if a { x } else { 0 }) < 5 || b
}

// ---- E6 expansion I4′: decision trees, `match`, `matches!` ---------------
// `if`/`else` returning a value, `match` on a `bool`/`u8`/`i8` with literal
// arms and a wildcard (a multi-target `switchInt`), and `matches!` (a
// multi-value `switchInt` with `bool`-literal arms).
pub fn d_if_bool(c: bool, a: bool, b: bool) -> bool {
    if c { a } else { b }
}
pub fn d_if_u8(c: bool, a: u8, b: u8) -> u8 {
    if c { a } else { b }
}
pub fn d_if_const(c: bool) -> u8 {
    if c { 1 } else { 0 }
}
pub fn d_sel_const(a: u8) -> u8 {
    if a < 10 { 0 } else { 255 }
}
pub fn d_match_u8(x: u8) -> u8 {
    match x {
        0 => 10,
        1 => 20,
        7 => 30,
        _ => 0,
    }
}
pub fn d_match_bool(b: bool) -> u8 {
    match b {
        true => 3,
        false => 9,
    }
}
pub fn d_matches(x: u8) -> bool {
    matches!(x, 1 | 2 | 7)
}
pub fn d_match_i8(x: i8) -> i8 {
    match x {
        -1 => 1,
        0 => 0,
        _ => -1,
    }
}
pub fn d_matches_i8(x: i8) -> bool {
    matches!(x, -1 | 1 | -128)
}
pub fn d_chain(a: u8) -> u8 {
    if a < 10 {
        1
    } else if a < 100 {
        2
    } else {
        3
    }
}
pub fn d_max(a: u8, b: u8) -> u8 {
    if a > b { a } else { b }
}
pub fn d_ge_sel(a: u8, b: u8) -> u8 {
    if a >= b { b } else { a }
}
pub fn d_ne_sel(a: u8, b: u8) -> u8 {
    if a != b { a } else { 0 }
}
pub fn d_if_not(c: bool, a: u8) -> u8 {
    if !c { a } else { 5 }
}
pub fn d_range(x: u8) -> u8 {
    match x {
        0..=9 => 1,
        10..=99 => 2,
        _ => 3,
    }
}
pub fn d_match_u8_bool(x: u8) -> bool {
    match x {
        0 | 255 => true,
        _ => false,
    }
}
pub fn d_if_cmp_bool(a: u8, b: bool) -> bool {
    if a == 0 { b } else { !b }
}
pub fn d_match_param_arms(x: u8, a: u8) -> u8 {
    match x {
        0 => a,
        1 => 7,
        _ => x,
    }
}
pub fn d_if_i8(c: bool, a: i8) -> i8 {
    if c { a } else { -1 }
}
pub fn d_if_nested(a: bool, b: bool) -> u8 {
    if a {
        if b { 1 } else { 2 }
    } else {
        3
    }
}
pub fn d_guard(x: u8) -> u8 {
    match x {
        n if n > 5 => 1,
        _ => 0,
    }
}
pub fn d_bind(x: u8) -> u8 {
    match x {
        0 => 1,
        n => n,
    }
}
pub fn d_match_u64(x: u64) -> u64 {
    match x {
        0 => 10,
        1 => 20,
        u64::MAX => 30,
        _ => 0,
    }
}
pub fn d_sel_i32(a: i32) -> i32 {
    if a < -5 { -1 } else { 1 }
}
// Stays refused: an EXHAUSTIVE range `match` without a `_` arm lowers to an
// `Unreachable` arm (design note I4′, b03).
pub fn d_range_exh(x: u8) -> u8 {
    match x {
        0..=127 => 1,
        128..=255 => 2,
    }
}

// ---- every carrier the tree reader and producer admit (review P1-2) -------
// The reader reads `bool`, `uN` and `iN` for N in {8, 16, 32, 64, 128}; the
// producer mints all of them but `u128`. Each carrier gets a row that runs
// natively AND through its image: `u16`/`i16` exhaustively (a one-parameter
// row, 65 536 inputs), `u32`/`i32`/`u64`/`i64`/`i128` on the sample
// `domain_values` states. The signed ORDERINGS `>`/`>=`/`<=`/`!=` go through
// the TREE producer here (`t_i8_ord`, `d_sel_i8_ord`), exhaustively over two
// `i8`s; before these rows only `<` did, sampled, at `i32`.
pub fn d_match_i128(x: i128) -> i128 {
    match x {
        -1 => 1,
        i128::MIN => 2,
        i128::MAX => 3,
        _ => 0,
    }
}
pub fn d_sel_i128(a: i128) -> i128 {
    if a < -3 { a } else { 7 }
}
pub fn d_sel_i64(a: i64) -> i64 {
    if a >= -3 { a } else { -1 }
}
pub fn d_match_i64(x: i64) -> i64 {
    match x {
        -1 => 1,
        i64::MIN => 2,
        i64::MAX => 3,
        _ => 0,
    }
}
pub fn t_i8_ord(a: i8, b: i8) -> bool {
    (a > b && b >= -3) || (a <= -100 && b != 7)
}
pub fn d_sel_i8_ord(a: i8, b: i8) -> i8 {
    if a >= b {
        a
    } else if b != -1 {
        b
    } else {
        0
    }
}
pub fn d_match_u16(x: u16) -> u16 {
    match x {
        0 => 1,
        256 => 2,
        u16::MAX => 3,
        _ => 0,
    }
}
pub fn d_match_i16(x: i16) -> i16 {
    match x {
        -1 => 1,
        i16::MIN => 2,
        i16::MAX => 3,
        0 => 4,
        _ => 0,
    }
}
pub fn t_u16(x: u16) -> bool {
    (x >= 0x100 && x != 0x7fff) || x < 3
}
pub fn t_i16(x: i16) -> bool {
    (x > -300 && x <= 1000) || x == i16::MIN
}
pub fn d_match_u32(x: u32) -> u32 {
    match x {
        0 => 1,
        10 => 2,
        4_000_000_000 => 3,
        u32::MAX => 4,
        _ => 0,
    }
}
pub fn d_match_i32(x: i32) -> i32 {
    match x {
        -1 => 1,
        -5 => 2,
        i32::MIN => 3,
        i32::MAX => 4,
        _ => 0,
    }
}
// Read by the tree reader, REFUSED by the producer: `u128` has no decision or
// comparison image (`Domain::U128`).
pub fn d_match_u128(x: u128) -> u128 {
    match x {
        0 => 1,
        7 => 2,
        _ => 0,
    }
}
// Refused by the READER already: a `u128` label above `i128::MAX` has no
// `i128` spelling, and `Ty::decode_switch_label` fails closed on it.
pub fn d_match_u128_max(x: u128) -> u128 {
    match x {
        0 => 1,
        u128::MAX => 2,
        _ => 0,
    }
}
// A `char` scrutinee: the extraction the E6 lane reads lowers `char` to its
// `u32` scalar value, so this is read as a `u32` match. The harness feeds it
// VALID scalar values only (`CHAR_SHAPES`), the only ones a `char` can hold.
pub fn d_match_char(c: char) -> u8 {
    match c {
        'a' => 1,
        '\u{e9}' => 2,
        '\u{10ffff}' => 3,
        _ => 0,
    }
}
// The two `condition()` paths of the `ite` image no row reached: a `bool`
// `==` as the condition, and a NEGATED comparison. rustc folds `if !(a < b)`
// into the branch targets, so `d_if_not_lt` reaches the frozen `Select`
// (MEASURED; kept as a row of that shape) and the `let` form is what puts a
// `Not` under the switch.
pub fn d_if_bool_eq(a: bool, b: bool, c: bool) -> bool {
    if a == b { c } else { !c }
}
pub fn d_if_not_lt(a: u8, b: u8) -> u8 {
    if !(a < b) { a } else { b }
}
pub fn d_if_not_lt_let(a: u8, b: u8) -> u8 {
    let c = !(a < b);
    if c { b } else { a }
}

// ---- IMPURE operands in arm positions (review P1-3): expected REFUSED -----
// Every one of these puts an effect or a partial operation where the tree
// reader walks: the right operand of `||`/`&&`, a non-first `match` arm, the
// `else` of a select. The harness forces all four facets true, so only the
// readers stand between each body and an import.
pub fn i_or_call(a: bool, x: u8) -> bool {
    a || aux::helper(x)
}
pub fn i_and_add(a: bool, x: u8) -> bool {
    a && x + 1 > 3
}
pub fn i_or_div(a: bool, x: u8, y: u8) -> bool {
    a || x / y == 0
}
pub fn i_and_index(a: bool, arr: [bool; 4], i: usize) -> bool {
    a && arr[i]
}
pub fn i_and_const_index(a: bool, arr: [bool; 4]) -> bool {
    a && arr[1]
}
pub fn i_match_call(x: u8) -> u8 {
    match x {
        0 => 1,
        1 => aux::helper_u8(x),
        _ => 0,
    }
}
pub fn i_if_wrapping(c: bool, x: u8) -> u8 {
    if c { x } else { x.wrapping_add(1) }
}
// Callees for the rows above. Nested, so `regen.py` (which keeps only
// `e6_shapes::<fn>` paths) and the declared-function list (which reads
// unindented `pub fn` lines) do not treat them as shapes; `inline(never)` so
// `-O` keeps the call.
pub mod aux {
    #[inline(never)]
    pub fn helper(x: u8) -> bool {
        x > 3
    }
    #[inline(never)]
    pub fn helper_u8(x: u8) -> u8 {
        x >> 1
    }
}

// ---- the PARAMETER VIEW: `bool` fields read through a borrow --------------
// These are not imported as written: the harness builds each one's
// borrow-erased VIEW (`trust_types::e6_param_view`, over the frozen-field
// table the compiler records for `&Flags`) and mints it through
// `admit_view_function_into`, so the view's field reads arrive at the E6-only
// reader as single-assignment temporaries.
pub struct Flags {
    pub p: bool,
    pub q: bool,
}
pub fn v_ne(f: &Flags) -> bool {
    f.p != f.q
}
pub fn v_eq(f: &Flags) -> bool {
    f.p == f.q
}
pub fn v_ne_other(f: &Flags, o: bool) -> bool {
    f.p != o
}
pub fn v_ne_two(f: &Flags, g: &Flags) -> bool {
    f.p != g.q
}
pub fn v_lt(f: &Flags) -> bool {
    f.p < f.q
}
// E6 expansion I3′/I4′ through the view: a connective tree and a decision
// tree over the view's by-value field parameters.
pub fn v_and(f: &Flags) -> bool {
    f.p && f.q
}
pub fn v_tree(f: &Flags, o: bool) -> bool {
    f.p || (f.q && !o)
}
pub fn v_sel(f: &Flags, a: u8, b: u8) -> u8 {
    if f.p { a } else { b }
}
pub fn v_match(f: &Flags) -> u8 {
    match f.q {
        true => 1,
        false => 2,
    }
}
