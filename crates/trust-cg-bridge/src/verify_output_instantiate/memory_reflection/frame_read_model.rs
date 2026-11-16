//! Pure statements: exact nested frame stores, unrestricted memory and values.
use clean_kernel::{BinderInfo, Expr, Level, Name};
pub(crate) fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}
pub(crate) fn lb() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), bool_ty())
}
pub(crate) fn array() -> Expr {
    Expr::arrow(lb(), lb())
}
pub(crate) fn list(bits: &[Expr]) -> Expr {
    bits.iter().rev().fold(
        Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), bool_ty()),
        |t, h| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [bool_ty(), h.clone(), t],
            )
        },
    )
}
pub(crate) fn address(bits: &[Expr; 64], index: usize) -> Option<Expr> {
    let mut value = list(bits);
    for k in super::frame_offset_model::chain(index)? {
        let constant = list(
            &(0..64)
                .map(|i| {
                    Expr::const_str(if ((k >> i) & 1) == 1 { "Bool.true" } else { "Bool.false" })
                })
                .collect::<Vec<_>>(),
        );
        value = Expr::apps(
            Expr::const_str("Clean.BVI.addRecM"),
            [value, constant, Expr::const_str("Bool.false")],
        );
    }
    Some(value)
}
pub(crate) fn store(m: Expr, a: Expr, v: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.bvStore"), [m, a, v])
}
pub(crate) fn select(m: Expr, a: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.bvSelect"), [m, a])
}
pub(crate) fn eq(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [lb(), a, b],
    )
}
pub(crate) fn body(
    bits: &[Expr; 64],
    memory: Expr,
    values: &[Expr; 16],
    query: usize,
) -> Option<Expr> {
    let mut memory = memory;
    for (i, v) in values.iter().enumerate() {
        memory = store(memory, address(bits, i)?, v.clone());
    }
    Some(eq(select(memory, address(bits, query)?), values.get(query)?.clone()))
}
pub(crate) fn statement(query: usize) -> Option<Expr> {
    let bits = std::array::from_fn(|i| Expr::bvar(80 - i as u32));
    let values = std::array::from_fn(|i| Expr::bvar(15 - i as u32));
    let mut goal = body(&bits, Expr::bvar(16), &values, query)?;
    for _ in 0..16 {
        goal = Expr::pi(BinderInfo::Default, lb(), goal);
    }
    goal = Expr::pi(BinderInfo::Default, array(), goal);
    for _ in 0..64 {
        goal = Expr::pi(BinderInfo::Default, bool_ty(), goal);
    }
    Some(goal)
}
pub(crate) fn name(query: usize) -> String {
    format!("Clean.FrameReadV1.byte{query}")
}
