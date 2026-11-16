// B2 repro: four false-refutation shapes plus a counter-program per shape
// that is a REAL defect and must keep refuting.

// ---- shape (a): hardened_panic_boundary drops type-range facts ----------
pub fn count_args(args: &[String]) -> usize {
    let mut i = 0;
    while i < args.len() {
        i += 1;
    }
    i
}

// counter (a): ZST slice may hold usize::MAX items -> `len + 1` overflows.
pub fn zst_len_plus_one(args: &[()]) -> usize {
    args.len() + 1
}

// counter (a'): after the loop `i == len`, and `+ k` overflows for large k.
pub fn after_loop_plus(args: &[u8], k: usize) -> usize {
    let mut i = 0;
    while i < args.len() {
        i += 1;
    }
    i + k
}

// ---- shape (b): slice-length / element symbol proliferation ------------
pub fn dec_first_nonzero(digits: &mut [u8]) {
    let mut i = 0;
    while i < digits.len() {
        if digits[i] > 0 {
            digits[i] -= 1;
            break;
        }
        digits[i] = 9;
        i += 1;
    }
}

// counter (b): unguarded decrement underflows on a zero digit.
pub fn dec_every(digits: &mut [u8]) {
    let mut i = 0;
    while i < digits.len() {
        digits[i] -= 1;
        i += 1;
    }
}

// counter (b'): guard on one element, decrement of ANOTHER one.
pub fn dec_neighbour(digits: &mut [u8]) {
    if digits.len() > 1 && digits[0] > 0 {
        digits[1] -= 1;
    }
}

// ---- shape (c): Box::new / Box deref in safe code ----------------------
pub enum Expr {
    Const(i64),
    Bin(u8, Box<Expr>, Box<Expr>),
}

pub fn bin(op: u8, a: Expr, b: Expr) -> Expr {
    Expr::Bin(op, Box::new(a), Box::new(b))
}

impl Expr {
    pub fn boxed(self) -> Box<Self> {
        Box::new(self)
    }
}

pub fn rhs_const(e: &Expr) -> Option<i64> {
    if let Expr::Bin(_, _, rhs) = e
        && let Expr::Const(k) = **rhs
    {
        Some(k)
    } else {
        None
    }
}

// counter (c): a raw pointer may be null.
/// # Safety
/// None claimed: this must refute.
pub unsafe fn deref_raw(p: *const u64) -> u64 {
    unsafe { *p }
}

// counter (c'): Box::from_raw of an arbitrary pointer.
/// # Safety
/// None claimed: this must refute.
pub unsafe fn from_raw_read(p: *mut u64) -> u64 {
    let b = unsafe { Box::from_raw(p) };
    *b
}

// ---- shape (d): i128::from(u64) ranged to [0, 2^64) ---------------------
pub fn wide_const() -> i128 {
    let wide = i128::from(u64::MAX) + 1;
    -wide
}

pub fn widen_inc(x: u64) -> i128 {
    i128::from(x) + 1
}

pub fn widen_neg(x: u64) -> i128 {
    -i128::from(x)
}

// counter (d): the From fact bounds x, not n.
pub fn widen_plus(x: u64, n: i128) -> i128 {
    i128::from(x) + n
}

// counter (d'): i128 + 1 with no range fact at all.
pub fn i128_inc(x: i128) -> i128 {
    x + 1
}

// ---- shape (b), terminator rows: a bounds assert in a block that stores ----
pub fn store_then_read(s: &mut [u8], i: usize) -> u8 {
    if i < s.len() {
        s[i] = 1;
        s[i]
    } else {
        0
    }
}

// counter (b''): the second index is unguarded — a real out-of-bounds read.
pub fn store_then_read_other(s: &mut [u8], i: usize, j: usize) -> u8 {
    if i < s.len() {
        s[i] = 1;
        s[j]
    } else {
        0
    }
}
