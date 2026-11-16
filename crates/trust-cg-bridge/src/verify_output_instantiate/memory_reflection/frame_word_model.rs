//! Pure transport statements for the ORIGINAL read/zero-extension/shift/OR
//! word syntax. Values and entry memory remain completely unrestricted.
use clean_kernel::{BinderInfo, Expr};

use super::frame_read_model as read;
fn nat(n: u32) -> Expr {
    match n {
        0 => Expr::const_str("Nat.zero"),
        1 | 2 => Expr::app(Expr::const_str("Nat.succ"), nat(n - 1)),
        _ => {
            let v = Expr::apps(Expr::const_str("Nat.mul"), [nat(2), nat(n / 2)]);
            if n % 2 == 0 { v } else { Expr::app(Expr::const_str("Nat.succ"), v) }
        }
    }
}
pub(crate) fn byte(value: Expr, shift: usize) -> Expr {
    let wide = Expr::apps(Expr::const_str("Clean.BVC.bvZeroExt"), [value, nat(56)]);
    if shift == 0 {
        return wide;
    }
    let amount = read::list(
        &(0..64)
            .map(|i| {
                Expr::const_str(if (((shift * 8) as u64 >> i) & 1) == 1 {
                    "Bool.true"
                } else {
                    "Bool.false"
                })
            })
            .collect::<Vec<_>>(),
    );
    Expr::apps(Expr::const_str("Clean.BVC.bvShl"), [wide, amount])
}
pub(crate) fn word(
    bits: &[Expr; 64],
    memory: Expr,
    values: &[Expr; 16],
    which: usize,
    count: usize,
    reads: bool,
) -> Option<Expr> {
    if which > 1 || !(1..=8).contains(&count) {
        return None;
    }
    let mut full = memory;
    for (i, v) in values.iter().enumerate() {
        full = read::store(full, read::address(bits, i)?, v.clone());
    }
    let value = |k: usize| -> Option<Expr> {
        let index = which * 8 + k;
        let v = if reads {
            read::select(full.clone(), read::address(bits, index)?)
        } else {
            values.get(index)?.clone()
        };
        Some(byte(v, k))
    };
    let mut out = value(0)?;
    for k in 1..count {
        out = Expr::apps(Expr::const_str("Clean.BVC.bvZipOr"), [out, value(k)?]);
    }
    Some(out)
}
pub(crate) fn statement(which: usize, count: usize) -> Option<Expr> {
    let bits = std::array::from_fn(|i| Expr::bvar(80 - i as u32));
    let values = std::array::from_fn(|i| Expr::bvar(15 - i as u32));
    let memory = Expr::bvar(16);
    let mut goal = read::eq(
        word(&bits, memory.clone(), &values, which, count, true)?,
        word(&bits, memory, &values, which, count, false)?,
    );
    for _ in 0..16 {
        goal = Expr::pi(BinderInfo::Default, read::lb(), goal);
    }
    goal = Expr::pi(BinderInfo::Default, read::array(), goal);
    for _ in 0..64 {
        goal = Expr::pi(BinderInfo::Default, read::bool_ty(), goal);
    }
    Some(goal)
}
pub(crate) fn name(which: usize, count: usize) -> String {
    format!("Clean.FrameWordTransportV1.word{which}_prefix{count}")
}
