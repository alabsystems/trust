#[derive(Clone, Copy, PartialEq)]
pub enum Op {
    Add,
    Sub,
    Mul,
}
pub fn apply(op: Op, a: i32, b: i32) -> Option<i32> {
    match op {
        Op::Add => a.checked_add(b),
        Op::Sub => a.checked_sub(b),
        Op::Mul => a.checked_mul(b),
    }
}
pub fn fold(ops: &[(Op, i32)], start: i32) -> Option<i32> {
    let mut acc = start;
    for (op, v) in ops {
        acc = apply(*op, acc, *v)?;
    }
    Some(acc)
}
