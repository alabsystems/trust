//! Pure, closed mathematical statements for the bounded 16-byte frame grid.
//! No proof construction or assumption is present in this module.
use clean_kernel::{BinderInfo, Expr};

pub(crate) fn chain(index: usize) -> Option<Vec<i128>> {
    match index {
        0 => Some(vec![-16]),
        1..=7 => Some(vec![-16, index as i128]),
        8 => Some(vec![-16, 8]),
        9..=15 => Some(vec![-16, 8, (index - 8) as i128]),
        _ => None,
    }
}
pub(crate) fn index(chain: &[i128]) -> Option<usize> {
    (0..16).find(|i| self::chain(*i).as_deref() == Some(chain))
}
pub(crate) fn statement(left: usize, right: usize) -> Option<Expr> {
    if left <= right {
        return None;
    }
    let bits = std::array::from_fn(|i| Expr::bvar(63 - i as u32));
    let mut goal = super::frame_arithmetic::offset_goal(&bits, &chain(left)?, &chain(right)?);
    for _ in 0..64 {
        goal = Expr::pi(BinderInfo::Default, Expr::const_str("Bool"), goal);
    }
    Some(goal)
}
pub(crate) fn name(left: usize, right: usize) -> String {
    format!("Clean.FrameOffsetsV1.distinct{left}_{right}")
}
