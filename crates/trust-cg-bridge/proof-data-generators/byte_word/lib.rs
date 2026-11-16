//! Closed CIC data for the exact original BVC byte-shift operation.
//! No grade, axiom or semantic shortcut: every returned pair needs a fresh
//! real kernel check. All eight input Boolean parameters are unrestricted.
use clean_kernel::{BinderInfo, Expr, FVarId, Level, Name};
pub mod reassembly;
fn boolean() -> Expr {
    Expr::const_str("Bool")
}
fn list_ty() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), boolean())
}
fn lit(b: bool) -> Expr {
    Expr::const_str(if b { "Bool.true" } else { "Bool.false" })
}
fn nil() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]), boolean())
}
fn cons(h: Expr, t: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]), [boolean(), h, t])
}
fn list(bits: &[Expr]) -> Expr {
    bits.iter().rev().fold(nil(), |tail, head| cons(head.clone(), tail))
}
// Exact compact natural terms. These contain only existing Nat definitions,
// not untransportable native literals or an unchecked arithmetic annotation.
fn nat(n: u32) -> Expr {
    if n == 0 {
        return Expr::const_str("Nat.zero");
    }
    if n == 1 {
        return Expr::app(Expr::const_str("Nat.succ"), nat(0));
    }
    if n == 2 {
        return Expr::app(Expr::const_str("Nat.succ"), nat(1));
    }
    let twice = Expr::apps(Expr::const_str("Nat.mul"), [nat(2), nat(n / 2)]);
    if n % 2 == 0 { twice } else { Expr::app(Expr::const_str("Nat.succ"), twice) }
}
fn zeros(n: u32) -> Expr {
    Expr::app(Expr::const_str("Clean.BVC.bvReplF"), nat(n))
}
fn append(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.bvAppend"), [a, b])
}
fn shift_count(k: u32, width: u32) -> Expr {
    list(&(0..width).map(|i| lit(i < 32 && k & (1 << i) != 0)).collect::<Vec<_>>())
}
fn compact_original(byte: &[Expr; 8], k: u32) -> Expr {
    let widened = Expr::apps(Expr::const_str("Clean.BVC.bvZeroExt"), [list(byte), nat(56)]);
    Expr::apps(Expr::const_str("Clean.BVC.bvShl"), [widened, shift_count(k, 6)])
}
pub fn original(byte: &[Expr; 8], k: u32) -> Expr {
    let widened = Expr::apps(Expr::const_str("Clean.BVC.bvZeroExt"), [list(byte), nat(56)]);
    Expr::apps(Expr::const_str("Clean.BVC.bvShl"), [widened, shift_count(k, 64)])
}
pub fn padded(byte: &[Expr; 8], k: u32) -> Result<Expr, String> {
    if !matches!(k, 8 | 16 | 24 | 32 | 40 | 48 | 56) {
        return Err("unsupported exact byte-shift constant".into());
    }
    Ok(append(zeros(k), append(list(byte), zeros(56 - k))))
}
fn equality(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [list_ty(), a, b],
    )
}
fn refl(x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [list_ty(), x],
    )
}
fn statement(byte: &[Expr; 8], k: u32) -> Result<Expr, String> {
    Ok(equality(compact_original(byte, k), padded(byte, k)?))
}
fn cases(byte: &[Expr; 8], index: usize, k: u32) -> Result<Expr, String> {
    if index == 8 {
        return Ok(refl(padded(byte, k)?));
    }
    let id = FVarId::new(0x9000_0000 + index as u64);
    let mut motive_byte = byte.clone();
    motive_byte[index] = Expr::fvar(id);
    let motive =
        Expr::lam(BinderInfo::Default, boolean(), statement(&motive_byte, k)?.abstract_fvar(id));
    let mut low = byte.clone();
    low[index] = lit(false);
    let mut high = byte.clone();
    high[index] = lit(true);
    Ok(Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [motive, cases(&low, index + 1, k)?, cases(&high, index + 1, k)?, byte[index].clone()],
    ))
}
/// Universal closed theorem, not 256 sampled executions. Applying this proof
/// specializes arbitrary Boolean values; a wrong branch remains ill typed.
#[cfg(feature = "test-hooks")]
static FORBID_PRODUCTION: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
#[cfg(feature = "test-hooks")]
pub fn without_production<T>(action: impl FnOnce() -> T) -> T {
    struct Reset(bool);
    impl Drop for Reset {
        fn drop(&mut self) {
            FORBID_PRODUCTION.store(self.0, std::sync::atomic::Ordering::SeqCst);
        }
    }
    let _reset = Reset(FORBID_PRODUCTION.swap(true, std::sync::atomic::Ordering::SeqCst));
    action()
}
pub fn expected_type(k: u32) -> Result<Expr, String> {
    expected_type_with_target(k, k)
}
pub fn expected_type_with_target(k: u32, target_k: u32) -> Result<Expr, String> {
    if !matches!(k, 8 | 16 | 24 | 32 | 40 | 48 | 56) {
        return Err("unsupported exact byte-shift constant".into());
    }
    let ids: [FVarId; 8] = std::array::from_fn(|i| FVarId::new(0x8000_0000 + i as u64));
    let byte = ids.map(Expr::fvar);
    let mut goal = equality(original(&byte, k), padded(&byte, target_k)?);
    for id in ids.into_iter().rev() {
        goal = Expr::pi(BinderInfo::Default, boolean(), goal.abstract_fvar(id));
    }
    if goal.has_fvar_quick() {
        return Err("expected byte shift type has free variable".into());
    }
    Ok(goal)
}
pub fn proof_pair(k: u32) -> Result<(Expr, Expr), String> {
    #[cfg(feature = "test-hooks")]
    assert!(
        !FORBID_PRODUCTION.load(std::sync::atomic::Ordering::SeqCst),
        "byte-shift proof producer forbidden during retained replay"
    );
    if !matches!(k, 8 | 16 | 24 | 32 | 40 | 48 | 56) {
        return Err("unsupported exact byte-shift constant".into());
    }
    let ids: [FVarId; 8] = std::array::from_fn(|i| FVarId::new(0x8000_0000 + i as u64));
    let byte = ids.map(Expr::fvar);
    let mut goal = equality(original(&byte, k), padded(&byte, k)?);
    let mut proof = cases(&byte, 0, k)?;
    for id in ids.into_iter().rev() {
        goal = Expr::pi(BinderInfo::Default, boolean(), goal.abstract_fvar(id));
        proof = Expr::lam(BinderInfo::Default, boolean(), proof.abstract_fvar(id));
    }
    if goal.has_fvar_quick() || proof.has_fvar_quick() {
        return Err("byte shift proof has leaked data parameter".into());
    }
    Ok((goal, proof))
}
